#lang racket

(require rackunit
         racket/list
         racket/match
         racket/set
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../region.rkt"
         "../traits.rkt"
         "../typing.rkt")

(define (raw-result core callables)
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               '((1 Int)) callables '()
               (region-ctx ir '() (hash) (hash))))

(define (callable-summaries core callables)
  (define ir (build-region-ir core))
  (sixth (typing-inference (annotate-regions core ir)
                           '((1 Int)) callables '()
                           (region-ctx ir '() (hash) (hash)))))

(define (failure-key result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

(define (replace-symbol term target replacement)
  (cond
    [(eq? term target) replacement]
    [(pair? term)
     (cons (replace-symbol (car term) target replacement)
           (replace-symbol (cdr term) target replacement))]
    [else term]))

(define (raw-result/places core callables places)
  (define ir (build-region-ir core))
  (define filled
    (replace-symbol (fill-region-placeholders core ir) 'ph
                    (region->rho ir (region-at ir '()))))
  (type-of/raw (annotate-regions filled ir) places callables '()
               (region-ctx ir '() (for/hash ([place (in-list places)])
                                   (values (first place) (region-at ir '())))
                           (hash))))

(define (prepare-execution core callables)
  (match (prepare-borrow-term* core #:callables callables)
    [(list 'ok start sidecar ir type)
     (values start sidecar ir type)]
    [other
     (fail (format "Core が実行用に型付けされなかった: ~s" other))]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 300])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _rule next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (check-live-trace configs callables expected)
  (define rows
    (for/list ([config (in-list configs)])
      (runtime-row config callables expected)))
  (define start-index
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
  (check-not-false start-index
                   (format "trace に runtime-row がある config がある: ~s"
                           rows))
  (for ([config (in-list (drop configs start-index))]
        [row (in-list (drop rows start-index))]
        [index (in-naturals start-index)])
    (check-not-false row (format "config ~a の runtime-row: ~s" index config))))

(define (contains-core-form? core name)
  (or (match core
        [(list head _ ...) (eq? head name)]
        [_ #f])
      (and (pair? core)
           (or (contains-core-form? (car core) name)
               (contains-core-form? (cdr core) name)))))

(define (configuration-core config)
  (match config [`(cfg ,core ,_ ...) core]))

(define (formal-callable name parameter-type return-type body effects)
  (formal-callable/regions '(a) name parameter-type return-type body effects))

(define (formal-callable/regions regions name parameter-type return-type body effects)
  (define signature
    `(ForallRegion ,regions
       (NFn (,parameter-type) ,return-type () ,effects () User)))
  (values
   `(Scope (1) (RegionLam ,regions (Lam User ,name (x) ,body)))
   `((,name ,signature))))

(define shared-record
  '(Record ((inner (Borrowed Int (RParam a)) imm)
            (other (Borrowed Int (RParam a)) imm))))

(define transport-pair-formal
  '(Record ((inner (BorrowedMut Int (RParam a)) mut)
            (other (BorrowedMut Int (RParam b)) mut))))
(define transport-pair-actual
  '(Record ((inner (BorrowedMut Int (RVar 0)) mut)
            (other (BorrowedMut Int (RVar 1)) mut))))
(define transport-callables
  `((identity-record
     (ForallRegion (a b)
       (NFn (,transport-pair-formal) ,transport-pair-formal () () () User)))))
(define transport-discharge-callables
  `((identity-record
     (ForallRegion (a b)
       (NFn (,transport-pair-formal) ,transport-pair-formal
            () () (TypeNarrativeCap) User)))))
(define transport-recur-callables
  (append transport-callables
          `((loop-id
             (ForallRegion (a b)
               (NFn () Unit () () () User))))))
(define transport-option-formal `(Option ,transport-pair-formal))
(define transport-option-actual `(Option ,transport-pair-actual))
(define transport-option-callables
  `((identity-option
     (ForallRegion (a b)
       (NFn (,transport-option-formal) ,transport-option-formal
            () () () User)))))
(define (transport-function)
  `(RegionApp
    (RegionLam (a b)
      (Lam User identity-record (argument) argument))
    ((RVar 0) (RVar 1))))
(define (transport-apply)
  `(Apply ,(transport-function) pair))
(define (transport-option-function)
  `(RegionApp
    (RegionLam (a b)
      (Lam User identity-option (argument) argument))
    ((RVar 0) (RVar 1))))
(define (transport-wrapper kind)
  (define applied (transport-apply))
  (case kind
    [(scope) `(Scope () ,applied)]
    [(yield) `(Yield 0 ,applied)]
    [(unsafe) `(Unsafe ,applied)]
    [(discharge)
     `(Discharge (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
        ,applied)]
    [(apply-argument) `(Apply ,(transport-function) ,applied)]
    [(record) `(Proj (Rec ((wrapped imm ,applied))) wrapped)]
    [(construct)
     `(Eliminate (Construct (Option ,transport-pair-actual) some ,applied)
        ((none () -> pair)
         (some (unwrapped) -> unwrapped)))]
    [(union)
     `(UnionEliminate
       (UnionInject (Union ,transport-pair-actual Int)
                    ,transport-pair-actual ,applied)
       ((,transport-pair-actual unwrapped -> unwrapped)
        (Int ignored -> pair)))]
    [(perform)
     `(Handle (Return boundary ,transport-pair-actual)
        (returned -> returned)
        (Perform (Return boundary ,transport-pair-actual) ,applied))]
    [(recur)
     `(Recur loop-id loop () unit ,applied)]
    [else (error 'transport-wrapper "unknown kind: ~s" kind)]))

(define (transport-core kind write-target)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (y let (Owned Int)) 2
         (Scope ()
           (Let (source-inner let (BorrowedMut Int (RVar 0)))
                (BorrowMut x)
             (Scope ()
               (Let (source-other let (BorrowedMut Int (RVar 1)))
                    (BorrowMut y)
                 (Let (pair let ,transport-pair-actual)
                      (Rec ((inner mut source-inner)
                            (other mut source-other)))
                   (Let (result let ,transport-pair-actual)
                        ,(transport-wrapper kind)
                     (Let (child let (Borrowed Int ph))
                          (Reborrow (Proj result inner))
                       (Let (written let Unit)
                            (Assign ,(if (eq? write-target 'inner)
                                         'source-inner
                                         'source-other)
                                    7)
                         (Read child)))))))))))))

(test-case "record 仮引数の borrowed field を Read できる"
  (define-values (core callables)
    (formal-callable 'read-inner shared-record 'Int '(Read (Proj x inner)) '()))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "兄弟の borrowed field は別の formal key を持つ"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) imm)
              (other (BorrowedMut Int (RParam a)) imm))))
  (define body
    '(Let (read let Int) (Read (Proj x inner))
       (Assign (Proj x other) 7)))
  (define-values (core callables)
    (formal-callable 'read-write-fields parameter-type 'Unit body '(Mutation)))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "formal field の Option binder と sibling field の書込みが共存する"
  (define parameter-type
    '(Record ((inner (Option (BorrowedMut Int (RParam a))) imm)
              (other (BorrowedMut Int (RParam a)) imm))))
  (define body
    '(Eliminate (Proj x inner)
       ((none () -> (Assign (Proj x other) 1))
        (some (c) ->
          (Let (other-updated let Unit) (Assign (Proj x other) 3)
            (Assign c 2))))))
  (define-values (core callables)
    (formal-callable 'write-option-field parameter-type 'Unit body '(Mutation)))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "Union 仮引数の payload formal key を枝 binder へ渡す"
  (define parameter-type
    '(Union (BorrowedMut Int (RParam a)) Int))
  (define body
    '(UnionEliminate x
       (((BorrowedMut Int (RParam a)) c -> (Read c))
        (Int n -> n))))
  (define-values (core callables)
    (formal-callable 'read-union-payload parameter-type 'Int body '()))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "形式が違う関数仮引数の既存 formal key はそのまま"
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User useb (x)
           (Let (t let Int) (Read x) (Assign x 7))))))
  (define callables
    '((useb (ForallRegion (a)
             (NFn ((BorrowedMut Int (RParam a))) Unit
                  () (Mutation) () User)))))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "結果の借用 leaf ごとに対応する formal path を候補に持つ"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) imm)
              (other (BorrowedMut Int (RParam b)) imm))))
  (define signature
    `(ForallRegion (a b)
       (NFn (,parameter-type) ,parameter-type () () () User)))
  (define core
    '(Scope (1)
       (RegionLam (a b)
         (Lam User identity-record (x) x))))
  (define summaries
    (callable-summaries core `((identity-record ,signature))))
  (define summary (first summaries))
  (check-equal?
   (callable-summary-result-index summary)
   (hash '((record-field . inner))
         (list (cons 0 '((record-field . inner))))
         '((record-field . other))
         (list (cons 0 '((record-field . other)))))))

(test-case "Apply の結果欄は候補の実引数だけを保つ"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) mut)
              (other (BorrowedMut Int (RParam b)) mut))))
  (define actual-type
    '(Record ((inner (BorrowedMut Int (RVar 0)) mut)
              (other (BorrowedMut Int (RVar 1)) mut))))
  (define callables
    `((identity-record
       (ForallRegion (a b)
         (NFn (,parameter-type) ,parameter-type () () () User)))))
  (define (core write-target)
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (y let (Owned Int)) 2
           (Scope ()
             (Let (source-inner let (BorrowedMut Int (RVar 0)))
                  (BorrowMut x)
               (Scope ()
                 (Let (source-other let (BorrowedMut Int (RVar 1)))
                      (BorrowMut y)
                   (Let (pair let ,actual-type)
                        (Rec ((inner mut source-inner)
                              (other mut source-other)))
                     (Let (r let ,actual-type)
                          (Apply
                           (RegionApp
                            (RegionLam (a b)
                              (Lam User identity-record (x) x))
                            ((RVar 0) (RVar 1)))
                           pair)
                       (Let (inner let (BorrowedMut Int (RVar 0))) (Proj r inner)
                         (Let (other-ref let (BorrowedMut Int (RVar 1)))
                              (Proj r other)
                           (Let (child let (Borrowed Int ph)) (Reborrow inner)
                             (Let (written const Unit)
                                  (Assign ,(if (eq? write-target 'inner)
                                               'inner
                                               'other-ref)
                                           7)
                               (Read child)))))))))))))))
  (define source-core (core 'other))
  (define source-ir (build-region-ir source-core))
  (check-false
   (equal? (region-at source-ir '(0 1 1 0 0))
           (region-at source-ir '(0 1 1 0 1 0 0)))
   "二つの実引数 borrow は異なる Scope region にある")
  (define inner-write-result
    (raw-result/places (core 'inner) callables '()))
  (check-equal? (failure-key inner-write-result) 'borrow-conflicting-use
                (format "inner write の失敗: ~s" inner-write-result))
  (define observed-forwarding (box #f))
  (typing-inference
   (annotate-regions source-core source-ir)
   '((1 Int)) callables '()
   (region-ctx source-ir '() (hash 1 (region-at source-ir '())) (hash))
   #:forwarding-summaries observed-forwarding)
  (define result-forwarding (first (hash-values (unbox observed-forwarding))))
  (define result-fields (forwarding-summary-fields result-forwarding))
  (define inner-sources
    (capability-entry-source-alphas
     (hash-ref result-fields '(record-field . inner))))
  (define other-sources
    (capability-entry-source-alphas
     (hash-ref result-fields '(record-field . other))))
  (check-equal? inner-sources (set '(RVar 0)))
  (check-equal? other-sources (set '(RVar 1)))
  (check-true (set-empty? (set-intersect inner-sources other-sources)))
  (define-values (start sidecar ir expected)
    (prepare-execution source-core callables))
  (define configs (trace-g2 start))
  (define post-apply
    (for/first ([config (in-list configs)] [index (in-naturals)]
                #:unless (contains-core-form? (configuration-core config) 'Apply))
      index))
  (check-not-false post-apply "trace に Apply 完了後の config がある")
  (check-live-trace (drop configs post-apply) '() expected)
  (check-equal? (configuration-core (last configs)) 1)
  (check-equal? (check-borrow-execution start sidecar ir 300 (make-bcounters))
                'ok))

(test-case "Proj が直接受ける Apply の結果欄を部分式の point から引く"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) mut)
              (other (BorrowedMut Int (RParam b)) mut))))
  (define actual-type
    '(Record ((inner (BorrowedMut Int (RVar 0)) mut)
              (other (BorrowedMut Int (RVar 1)) mut))))
  (define callables
    `((identity-record
       (ForallRegion (a b)
         (NFn (,parameter-type) ,parameter-type () () () User)))))
  (define (core write-target)
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (y let (Owned Int)) 2
           (Scope ()
             (Let (source-inner let (BorrowedMut Int (RVar 0))) (BorrowMut x)
               (Scope ()
                 (Let (source-other let (BorrowedMut Int (RVar 1))) (BorrowMut y)
                   (Let (pair let ,actual-type)
                     (Rec ((inner mut source-inner)
                           (other mut source-other)))
                     (Let (child let (Borrowed Int ph))
                       (Reborrow
                        (Proj
                         (Apply
                          (RegionApp
                           (RegionLam (a b)
                             (Lam User identity-record (arg) arg))
                           ((RVar 0) (RVar 1)))
                          pair)
                         inner))
                       (Let (written let Unit)
                         (Assign ,(if (eq? write-target 'inner) 'source-inner
                                      'source-other) 7)
                         (Read child))))))))))))
  (define rejected (raw-result/places (core 'inner) callables '()))
  (check-equal? (failure-key rejected) 'borrow-conflicting-use
                (format "candidate field write is E-BOR-025: ~s" rejected))
  (define accepted-core (core 'other))
  (check-false (failure-key (raw-result/places accepted-core callables '())))
  (define-values (start sidecar ir expected)
    (prepare-execution accepted-core callables))
  (define configs (trace-g2 start))
  (check-live-trace configs callables expected)
  (check-equal? (check-borrow-execution start sidecar ir 300 (make-bcounters))
                'ok))

(test-case "Apply の結果欄は各 Core 経路を通って借用検査へ届く"
  (for ([kind (in-list '(scope yield unsafe discharge apply-argument
                         record construct union perform recur))])
    (define callables
      (case kind
        [(discharge) transport-discharge-callables]
        [(recur) transport-recur-callables]
        [else transport-callables]))
    (define rejected (transport-core kind 'inner))
    (define rejection (raw-result/places rejected callables '()))
    (check-equal? (failure-key rejection) 'borrow-conflicting-use
                  (format "~a の候補欄は E-BOR-025: ~s" kind rejection))
    (define accepted (transport-core kind 'other))
    (define acceptance (raw-result/places accepted callables '()))
    (check-false (failure-key acceptance)
                 (format "~a の非候補欄は受理: ~s" kind acceptance))
    (when (not (failure-key acceptance))
      (define-values (start sidecar ir expected)
        (prepare-execution accepted callables))
      (define configs (trace-g2 start))
      (check-live-trace configs callables expected)
      (when (eq? kind 'unsafe)
        (check-not-false
         (for/first ([config (in-list configs)]
                     #:when (member 'R-UnsafeExit
                                    (map first (raw-steps-g2/named config))))
           config)
         "Unsafe の透過試験が R-UnsafeExit を通る"))
      (check-equal?
       (check-borrow-execution start sidecar ir 300 (make-bcounters))
       'ok
       (format "~a の非候補欄は oracle も受理" kind)))))

(test-case "Apply を直接 Eliminate の scrutinee に置いても欄表を渡す"
  (define (core write-target)
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (y let (Owned Int)) 2
           (Scope ()
             (Let (source-inner let (BorrowedMut Int (RVar 0)))
                  (BorrowMut x)
               (Scope ()
                 (Let (source-other let (BorrowedMut Int (RVar 1)))
                      (BorrowMut y)
                   (Let (pair let ,transport-pair-actual)
                        (Rec ((inner mut source-inner)
                              (other mut source-other)))
                     (Eliminate
                      (Apply
                       (RegionApp
                        (RegionLam (a b)
                          (Lam User wrap-option (argument)
                            (Construct (Option ,transport-pair-formal)
                                       some argument)))
                        ((RVar 0) (RVar 1)))
                      pair)
                      ((none () -> 0)
                       (some (unwrapped) ->
                        (Let (child let (Borrowed Int ph))
                             (Reborrow (Proj unwrapped inner))
                          (Let (written let Unit)
                               (Assign ,(if (eq? write-target 'inner)
                                            'source-inner
                                            'source-other)
                                        7)
                            (Read child)))))))))))))))
  (define option-callables
    (append transport-callables
            `((wrap-option
               (ForallRegion (a b)
                 (NFn (,transport-pair-formal)
                      (Option ,transport-pair-formal) () () () User))))))
  (define rejected (raw-result/places (core 'inner) option-callables '()))
  (check-equal? (failure-key rejected) 'borrow-conflicting-use
                (format "EliminateAt の候補欄 write は E-BOR-025: ~s" rejected))
  (define accepted (core 'other))
  (define acceptance
    (raw-result/places accepted option-callables '()))
  (check-false (failure-key acceptance) (format "非候補欄 write: ~s" acceptance))
  (define-values (start sidecar ir expected)
    (prepare-execution accepted option-callables))
  (define (direct-apply-eliminate-at? term)
    (or (match term [`(EliminateAt (Apply ,_ ...) ,_) #t] [_ #f])
        (and (pair? term)
             (or (direct-apply-eliminate-at? (car term))
                 (direct-apply-eliminate-at? (cdr term))))))
  (check-true (direct-apply-eliminate-at? (configuration-core start)))
  (define configs (trace-g2 start))
  (check-live-trace configs option-callables expected)
  (check-equal? (check-borrow-execution start sidecar ir 300 (make-bcounters))
                'ok))

(test-case "Read は参照先の欄表を結果へ渡す"
  (define source-key '(source-owner . ()))
  (define inner-entry
    (capability-entry (set source-key) (set) #f #t (set 'source-alpha) #f))
  (define record-fields (hash '(record-field . inner) inner-entry))
  (define record-context
    (region-ctx-add-token (empty-region-ctx) 'owner
                          (set '(owner . ())) #f #f record-fields))
  (define read-record
    (capability-of record-context '(Read (BorrowRef owner () 0))))
  (check-equal? (capability-entry-keys read-record) (set source-key))
  (check-equal? (capability-entry-fields read-record) record-fields)
  (check-false (capability-entry-borrowed-view? read-record))
  (define read-projected
    (capability-of record-context
                   '(Read (ProjBorrowAt 0 (BorrowRef owner () 0) inner))))
  (check-equal? (capability-entry-keys read-projected) (set source-key))
  (check-true (capability-entry-borrowed-view? read-projected))
  (define union-context
    (region-ctx-add-token
     (empty-region-ctx) 'owner (set '(owner . ())) #f #f
     (hash 'Int inner-entry 'String (capability-entry (set) (set) #f #f (set) #f))))
  (define read-payload
    (capability-of union-context
                   '(Read (BorrowRef owner ((Payload)) 0))))
  (check-equal? (capability-entry-keys read-payload) (set source-key)))

(test-case "Apply capability の走査は各構成子の正確な child point を使う"
  (define leaf
    (capability-entry (set '(owner . ())) (set) #f #t (set 'source) #f))
  (define record-entry
    (capability-entry
     (set '(owner . ())) (set)
     (hash '(record-field . inner) leaf) #f (set 'source) #f))
  (define (point-of core)
    (define seen (box #f))
    (capability-of
     (empty-region-ctx) core
     #:apply-entry
     (lambda (Λ _node)
       (set-box! seen (region-ctx-point Λ))
       record-entry))
    (unbox seen))
  (for ([case (in-list
               (list
                (cons '(Scope () (Apply f x)) '(0))
                (cons '(Unsafe (Apply f x)) '(0))
                (cons '(Yield 0 (Apply f x)) '(1))
                (cons '(Discharge (ProofRep User TypeNarrativeCap) (Apply f x))
                      '(0))
                (cons '(Read (Apply f x)) '(0))
                (cons '(Proj (Apply f x) inner) '(0))
                (cons '(ProjOpt Int (Apply f x) inner) '(0))
                (cons '(ReborrowAt 0 (Apply f x)) '(0))
                (cons '(Let (r let Int) (Apply f x) r) '(0))
                (cons '(Let (r let Int) 0 (Apply f x)) '(1))
                (cons '(Rec ((field imm (Apply f x)))) '(0))
                (cons '(Construct Pair Pair (Apply f x)) '(0))
                (cons '(UnionInject (Union Pair Int) Pair (Apply f x)) '(0))
                (cons '(UnionVal (Union Pair Int) Pair (Apply f x)) '(0))
                (cons '(Eliminate (Apply f x) ((Pair (a) -> a))) '(0))
                (cons '(UnionEliminate (Apply f x) ((Pair a -> a))) '(0))
                (cons '(RecRewrite (Rec ((field imm 0)))
                                   ((field old Int imm Int (Apply f x))))
                      '(1))
                (cons '(RecRewriteOpen ((field imm (Apply f x)))) '(0))
                (cons '(Recur loop-id loop () 0 (Apply f x)) '(1))))])
    (check-equal? (point-of (car case)) (cdr case)
                  (format "~s" (car case))))
  (define flow-points (box '()))
  (capability-flow-of
   (empty-region-ctx)
   '(Handle op (returned -> (Apply handler-f returned))
      (Perform op (Apply payload-f payload)))
   #:apply-entry
   (lambda (Λ _node)
     (set-box! flow-points
               (append (unbox flow-points) (list (region-ctx-point Λ))))
     record-entry))
  (check-equal? (unbox flow-points) '((1 0) (0))))

(test-case "要約のない関数値も署名から借用欄の転送を記録する"
  (define leaf-a '(BorrowedMut Int (RParam a)))
  (define record-type `(Record ((inner ,leaf-a mut))))
  (define function-type `(NFn (,record-type) ,record-type () () () User))
  (define wrapper-signature
    `(ForallRegion (a)
       (NFn (,function-type ,record-type) ,record-type () () () User)))
  (define core
    `(Scope (1)
       (RegionLam (a)
         (Lam User apply-unknown-summary (f x) (Apply f x)))))
  (define callables `((apply-unknown-summary ,wrapper-signature)))
  (check-false (failure-key (raw-result core callables))))

(test-case "要約のない Apply の返却 borrow を Reborrow しても元の親へ書けない"
  (define leaf-a '(BorrowedMut Int (RParam a)))
  (define record-type `(Record ((inner ,leaf-a imm))))
  (define function-type `(NFn (,record-type) ,record-type () () () User))
  (define wrapper-signature
    `(ForallRegion (a)
       (NFn (,function-type ,record-type) ,record-type () () () User)))
  (define identity-signature
    `(ForallRegion (a) (NFn (,record-type) ,record-type () () () User)))
  (define actual-record-type
    '(Record ((inner (BorrowedMut Int (RVar 0)) imm))))
  (define wrapper-term
    `(RegionApp
      (RegionLam (a)
        (Lam User apply-unknown-summary (f x) (Apply f x)))
      ((RVar 0))))
  (define identity-term
    '(RegionApp
      (RegionLam (a) (Lam User identity-borrow (z) z))
      ((RVar 0))))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (source let (BorrowedMut Int (RVar 0))) (BorrowMut owner)
           (Let (argument let ,actual-record-type)
                (Rec ((inner imm source)))
             (Let (result let ,actual-record-type)
                  (Apply ,wrapper-term ,identity-term argument)
               (Let (inner let ,leaf-a) (Proj result inner)
                 (Let (child let (Borrowed Int (RParam %omitted)))
                      (Reborrow inner)
                   (Let (write let Unit) (Assign (Proj argument inner) 7)
                     (Read child))))))))))
  (define callables
    `((apply-unknown-summary ,wrapper-signature)
      (identity-borrow ,identity-signature)))
  (define direct-core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (source let (BorrowedMut Int (RVar 0))) (BorrowMut owner)
           (Let (argument let ,actual-record-type) (Rec ((inner imm source)))
             (Let (result let ,actual-record-type)
                  (Apply ,identity-term argument)
               (Let (inner let ,leaf-a) (Proj result inner)
                 (Let (child let (Borrowed Int (RParam %omitted)))
                      (Reborrow inner)
                   (Let (write let Unit) (Assign (Proj argument inner) 7)
                     (Read child))))))))))
  (define direct-result (raw-result direct-core callables))
  (check-equal? (failure-key direct-result) 'borrow-conflicting-use
                (format "既知の identity summary では親との衝突を検出する: ~s"
                        direct-result))
  (define result (raw-result core callables))
  (check-equal? (failure-key result) 'borrow-conflicting-use
                (format "要約のない Apply の返却 capability が親 owner へ戻る: ~s"
                        result)))

(test-case "再帰 data の結果は借用欄を保守的に追跡する"
  (define list-type '(List (BorrowedMut Int (RParam a))))
  (define signature
    `(ForallRegion (a)
       (NFn (,list-type) ,list-type () () () User)))
  (define callables `((identity-borrow-list ,signature)))
  (define actual-type '(List (BorrowedMut Int (RVar 0))))
  (define (core conflict?)
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (y let (Owned Int)) 2
           (Let (first-ref let (BorrowedMut Int (RVar 0))) (BorrowMut y)
             (Let (second-ref let (BorrowedMut Int (RVar 0))) (BorrowMut x)
               (Let (items let ,actual-type)
                 (Construct ,actual-type cons first-ref
                   (Construct ,actual-type cons second-ref
                     (Construct ,actual-type nil)))
                 (Let (result let ,actual-type)
                   (Apply (RegionApp (RegionLam (a)
                                    (Lam User identity-borrow-list (xs) xs))
                                    ((RVar 3)))
                          items)
                   (Eliminate result
                      ((nil () -> 0)
                       (cons (first tail) ->
                        ,(if conflict?
                             '(Eliminate tail
                                ((nil () -> 0)
                                 (cons (second rest) ->
                                   (Let (written let Unit)
                                        (Assign (BorrowMut x) 9)
                                     (Read second)))))
                             '(Read first)))))))))))))
  (define read-core (core #f))
  (define-values (start sidecar ir expected)
    (prepare-execution read-core callables))
  (define configs (trace-g2 start))
  (define post-apply
    (for/first ([config (in-list configs)] [index (in-naturals)]
                #:unless (contains-core-form? (configuration-core config) 'Apply))
      index))
  (check-not-false post-apply "再帰 List の identity 呼出し後の config がある")
  (check-live-trace (drop configs post-apply) callables expected)
  (check-equal? (check-borrow-execution start sidecar ir 300 (make-bcounters)) 'ok)
  (define conflict-result
    (raw-result/places (core #t) callables '((1 Int) (2 Int))))
  (check-equal? (failure-key conflict-result) 'borrow-conflicting-alias
                (format "2 番目の借用が生きている間の親への書込み: ~s"
                        conflict-result)))

(test-case "空の root keys を許しても不正な借用 path は拒む"
  (define failure
    (with-handlers ([exn:fail? exn-message])
      (capability-of (empty-region-ctx)
                     '(ProjBorrowAt 0 (BorrowMutRef 1 ((bad . path)) 0) invalid)
                     #:fail (lambda (key _node) (error 'probe "~a" key))
                     #:allow-empty-keys? #t)
      #f))
  (check-regexp-match #rx"unresolved-borrow-owner" failure))

(test-case "formal leaf API は宣言寿命と渡された source alpha を分ける"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) imm)
              (other (BorrowedMut Int (RParam b)) imm))))
  (define core
    '(Scope (1)
       (RegionLam (a b)
         (Lam User read-inner (x) (Read (Proj x inner))))))
  (define callables
    `((read-inner (ForallRegion (a b)
                    (NFn (,parameter-type) Int () () () User)))))
  (define summary (first (callable-summaries core callables)))
  (define-values (inner-lifetime inner-sources)
    (formal-leaf-info
     summary 0 '((record-field . inner))
     (capability-entry (set) (set) #f #f (set 'inner-source) #f)))
  (define-values (other-lifetime other-sources)
    (formal-leaf-info
     summary 0 '((record-field . other))
     (capability-entry (set) (set) #f #f (set 'other-source) #f)))
  (check-true (match inner-lifetime [(list 'RParam _) #t] [_ #f]))
  (check-true (match other-lifetime [(list 'RParam _) #t] [_ #f]))
  (check-not-equal? inner-lifetime other-lifetime)
  (check-equal? inner-sources (set 'inner-source))
  (check-equal? other-sources (set 'other-source)))

(test-case "Recur と RecurVal の frame に formal field の欄表を保つ"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) imm)
              (other (BorrowedMut Int (RParam b)) imm))))
  (define callables
    `((rec-formal (NFn (,parameter-type) Int () () () User))))
  (define recur-value
    '(Scope (1)
       (RegionLam (a b)
         (RecurVal rec-formal g (x) (Read (Proj x inner))))))
  (define summary (first (callable-summaries recur-value callables)))
  (define-values (lifetime sources)
    (formal-leaf-info
     summary 0 '((record-field . inner))
     (capability-entry (set) (set) #f #f (set 'recur-source) #f)))
  (check-true (match lifetime [(list 'RParam _) #t] [_ #f]))
  (check-equal? sources (set 'recur-source))
  (define recur
    '(Scope (1)
       (RegionLam (a b)
         (Recur rec-formal g (x) (Read (Proj x inner)) 0))))
  (check-equal? (failure-key (raw-result recur callables)) #f))

(test-case "Union member と data constructor の formal path は region ごとに異なる"
  (define union-type
    '(Union (BorrowedMut Int (RParam a))
            (BorrowedMut Bool (RParam b))))
  (define-values (union-core union-callables)
    (formal-callable/regions '(a b) 'read-union union-type 'Int 0 '()))
  (define union-summary (first (callable-summaries union-core union-callables)))
  (define union-leaves (first (callable-summary-formal-fields union-summary)))
  (define-values (union-capability _union-metadata)
    (formal-capability-entry union-type 'formal-root))
  (check-true
   (set-member? (capability-entry-keys union-capability)
                '(formal-root Payload)))
  (define union-paths (hash-keys union-leaves))
  (check-equal? (length union-paths) 2)
  (define union-lifetimes
    (for/list ([path (in-list union-paths)])
      (define-values (lifetime _sources)
        (formal-leaf-info
         union-summary 0 path
         (capability-entry (set) (set) #f #f (set) #f)))
      (define declared
        (match (first path)
          [`(BorrowedMut ,_ ,region) region]
          [_ #f]))
      (check-equal? lifetime declared)
      lifetime))
  (check-equal? (length (remove-duplicates union-lifetimes equal?)) 2)
  (define result-type
    '(Result (BorrowedMut Int (RParam a))
             (BorrowedMut Bool (RParam b))))
  (define-values (result-core result-callables)
    (formal-callable/regions '(a b) 'read-result result-type 'Int 0 '()))
  (define result-summary (first (callable-summaries result-core result-callables)))
  (define-values (result-capability _result-metadata)
    (formal-capability-entry result-type 'formal-root))
  (check-true
   (set-member? (capability-entry-keys result-capability)
                '(formal-root 0)))
  (define result-paths '(((ok . 0)) ((ng . 0))))
  (define result-lifetimes
    (for/list ([path (in-list result-paths)])
      (define-values (lifetime _sources)
        (formal-leaf-info
         result-summary 0 path
         (capability-entry (set) (set) #f #f (set) #f)))
      lifetime))
  (check-equal? (length (remove-duplicates result-lifetimes equal?)) 2))

(test-case "同じ formal path の a,b,a 寿命衝突は曖昧のまま fail closed"
  (define-values (_entry leaves)
    (formal-capability-entry
     '(Record ((same (BorrowedMut Int (RParam a)) imm)
               (same (BorrowedMut Int (RParam b)) imm)
               (same (BorrowedMut Int (RParam a)) imm)))
     'formal-root))
  (check-false (hash-ref leaves '((record-field . same)) 'missing)))

(test-case "集約値の root は borrowed view ではなく leaf view はそのまま"
  (define-values (root leaves)
    (formal-capability-entry
     '(Record ((view (BorrowedMut Int (RParam a)) imm)))
     'formal-root))
  (check-false (capability-entry-borrowed-view? root))
  (check-true
   (capability-entry-borrowed-view?
    (hash-ref leaves '((record-field . view)))))
  (define-values (borrowed-root _borrowed-leaves)
    (formal-capability-entry '(BorrowedMut Int (RParam a)) 'formal-root))
  (check-true (capability-entry-borrowed-view? borrowed-root)))

(test-case "非借用の再帰 field は Apply の capability 表を空で止める"
  (define formal-type
    '(Record ((r (BorrowedMut Int (RParam a)) imm)
              (xs (List Int) imm))))
  (define actual-type
    '(Record ((r (BorrowedMut Int (RVar 0)) imm)
              (xs (List Int) imm))))
  (define signature
    `(ForallRegion (a) (NFn (,formal-type) ,formal-type () () () User)))
  (define callables `((identity-borrow-record ,signature)))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (source let (BorrowedMut Int (RVar 0))) (BorrowMut owner)
           (Let (argument let ,actual-type)
             (Rec ((r imm source)
                   (xs imm (Construct (List Int) nil))))
             (Let (result let ,actual-type)
               (Apply
                (RegionApp
                 (RegionLam (a)
                   (Lam User identity-borrow-record (record) record))
                 ((RVar 0)))
                argument)
               (Read (Proj result r))))))))
  (define type-result (raw-result core callables))
  (check-false (failure-key type-result)
               (format "identity Apply の型検査: ~s" type-result))
  (when (not (failure-key type-result))
    (define-values (start sidecar ir expected)
      (prepare-execution core callables))
    (define configs (trace-g2 start))
    (check-live-trace configs callables expected)
    (check-equal? (check-borrow-execution start sidecar ir 300 (make-bcounters))
                  'ok)))

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

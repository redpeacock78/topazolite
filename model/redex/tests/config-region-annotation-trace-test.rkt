#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt"
         "../unsafe-oracle.rkt")

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 200])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (config-core cfg)
  (match cfg [`(cfg ,core ,_ ...) core]))

(define (config-type-result cfg callables)
  (match cfg
    [`(cfg ,core ,heap ,states ,_tokens ,_trace)
     (define places
       (derive-places heap callables #:declared (config-declared-types cfg)))
     (define borrow-types
       (and places (recover-runtime-borrow-types core heap states places)))
     (and borrow-types
          (parameterize ([config-runtime-borrow-types borrow-types])
            (with-config-typing
             (lambda () (type-of/raw core places callables)))))]
    [_ #f]))

(define (config-type-failure-key cfg callables)
  (match (config-type-result cfg callables)
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

(define (check-configs label start configs rules callables expected)
  (define start-row (runtime-row start callables expected))
  (check-not-false
   start-row
   (format "~a: 起点の runtime-row key=~s cfg=~s"
           label (config-type-result start callables) start))
  (define rows
    (for/list ([cfg (in-list configs)] [index (in-naturals)])
      (define row (runtime-row cfg callables expected))
      (check-not-false row
                       (format "~a: 構成 ~a runtime-row=#f key=~s cfg=~s"
                               label index
                               (config-type-failure-key cfg callables) cfg))
      (check-true (and row (config-ok? cfg callables expected row))
                  (format "~a: 構成 ~a config-ok?=#f key=~s cfg=~s"
                          label index (config-type-failure-key cfg callables) cfg))
      row))
  (for ([before (in-list rows)] [after (in-list (cdr rows))]
        [rule (in-list rules)] [index (in-naturals)])
      (check-true (row-subset? after before)
                  (format "~a: ~a 後の構成 ~a で row が増えた: ~s -> ~s"
                          label rule index before after)))
  (void))

(define (check-configs-and-oracle label start configs rules callables expected
                                  sidecar ir)
  (check-configs label start configs rules callables expected)
  (check-equal? (check-borrow-execution start sidecar ir 200 (make-bcounters))
                'ok
                (format "~a: 性質 8 oracle" label)))

(define (prepared-trace label source expected [callables '()])
  (match (prepare-borrow-term* source #:callables callables)
    [(list 'ok start sidecar ir inferred-type)
     (check-equal? inferred-type expected (format "~a: source の期待型" label))
     (define-values (configs rules) (trace-g2 start))
     (check-configs-and-oracle label start configs rules callables expected
                               sidecar ir)
     (values configs rules)]
    [other (fail (format "~a: source の準備に失敗: ~s; typing=~s"
                         label other
                         (borrow-source-typing-result source callables)))]))

(define (borrow-source-typing-result source callables)
  (define ir (build-region-ir source))
  (define annotated (annotate-regions (fill-region-placeholders source ir) ir))
  (type-of/raw*+borrows annotated '() callables '()
                        (region-ctx ir '() (hash) (hash))))

(define (typed-source-trace source callables places
                            [initial-place #f] [supplied-ir #f])
  (define ir (or supplied-ir (build-region-ir source)))
  (define annotated
    (annotate-regions (fill-region-placeholders source ir) ir))
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
  (match (type-of/raw*+borrows
          annotated places callables '() (region-ctx ir '() owners (hash))
          #:mut-types mut-types #:callable-contexts callable-contexts)
    [`(ok (,expected ,_row ,table ,sigma ,renamed ,sidecar))
     (define machine-core
       (annotate-callable-contexts
        (annotate-mut-binding-types
         (materialize-regions ir renamed table sigma) (unbox mut-types))
        (unbox callable-contexts) 'renamed))
     (define start
       (match (inject-g2m machine-core)
         [`(cfg ,core ,heap ,states ,tokens ,events)
          (if initial-place
              `(cfg ,core ((,initial-place 0 (declared Int)))
                    ((,initial-place Available)) ,tokens ,events)
              `(cfg ,core ,heap ,states ,tokens ,events))]))
     (define-values (configs rules) (trace-g2 start))
     (values expected start configs rules sidecar ir)]
    [other (fail (format "source 型検査に失敗: ~s" other))]))

(define (fill-unsafe-regions core ir)
  (let walk ([term core] [point '()])
    (match term
      [`(FromRawPtr ,operand ,_rho)
       `(FromRawPtr ,(walk operand (append point '(0)))
                    ,(region->rho ir (region-at ir point)))]
      [(? list?)
       (core-with-children
        term
        (for/list ([child (in-list (core-children term))]
                   [index (in-naturals)])
          (walk child (append point (list index)))))]
      [_ term])))

(define (typed-unsafe-trace source)
  (define ir (build-region-ir source))
  (define region-filled
    (fill-unsafe-regions (fill-region-placeholders source ir) ir))
  (define annotated (annotate-regions region-filled ir))
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (match (type-of/raw*+ptr
          annotated '() '() '() (region-ctx ir '() (hash) (hash))
          #:mut-types mut-types #:callable-contexts callable-contexts)
    [`(ok (,expected ,_row ,ptr-sidecar))
     (define machine-core
       (annotate-callable-contexts
        (annotate-mut-binding-types annotated (unbox mut-types))
        (unbox callable-contexts) 'source))
     (define start (inject-g2m machine-core))
     (define-values (configs rules) (trace-g2 start))
     (values expected start configs rules ptr-sidecar)]
    [other (fail (format "unsafe source 型検査に失敗: ~s" other))]))

(define (wrap-scopes count term)
  (if (zero? count) term
      `(Scope () ,(wrap-scopes (sub1 count) term))))

(define region-app-callables
  '((useb (ForallRegion (a)
            (NFn ((Borrowed Res (RParam a))) Unit () () () User)))))

(define region-app-function
  '(RegionLam (a) (Lam User useb (p) unit)))

(define (make-region-app-core depth borrow-rho owner-rho)
  `(Scope ()
     (Let (x let (Owned Res)) (resource 7)
       ,(wrap-scopes
         depth
         `(Let (b let (Borrowed Res ,borrow-rho)) (Borrow x)
            (Apply (RegionApp ,region-app-function (,owner-rho)) b))))))

(define (find-core-path term predicate [path '()])
  (cond
    [(predicate term) path]
    [(list? term)
     (for/first ([child (in-list (core-children term))]
                 [index (in-naturals)]
                 #:do [(define found
                         (find-core-path child predicate
                                         (append path (list index))))]
                 #:when found)
       found)]
    [else #f]))

(define (tree-any? term predicate)
  (or (predicate term)
      (and (pair? term)
           (or (tree-any? (car term) predicate)
               (tree-any? (cdr term) predicate)))))

(define (record-borrow-source)
  (define borrow-union
    '(Union (Borrowed Res (RVar 0))
            (Union (Borrowed Res (RVar 1)) String)))
  (define input '(UnionInject (Union Int Bool) Int 1))
  (define branch-a
    `(UnionInject ,borrow-union (Borrowed Res (RVar 0))
                  (Scope () (Borrow outer))))
  (define branch-b
    `(UnionInject ,borrow-union (Borrowed Res (RVar 1))
                  (Scope () (Borrow inner))))
  (define borrowed-value
    `(UnionEliminate ,input
                     ((Int i -> ,branch-a) (Bool b -> ,branch-b))))
  `(Scope ()
     (Let (outer let (Owned Res)) (resource 13)
       (Let (inner let (Owned Res)) (resource 14)
         (Let (discarded let ,borrow-union)
              (Proj (Rec ((borrow imm ,borrowed-value))) borrow)
           unit)))))

(define (region-app-depth-one-trace)
  (define skeleton (make-region-app-core 1 0 0))
  (define ir (build-region-ir skeleton))
  (define owner-rho (region->rho ir (owner-let-body-region ir '(0))))
  (define borrow-path
    (find-core-path skeleton (lambda (node) (equal? node '(Borrow x)))))
  (define borrow-rho (region->rho ir (region-at ir borrow-path)))
  (typed-source-trace (make-region-app-core 1 borrow-rho owner-rho)
                      region-app-callables '() #f ir))

(define repeated-callables
  '((polyuse (ForallRegion (a) (NFn () Unit () () () User)))))

(define repeated-region-app-source
  '(Scope ()
     (Let (f const (ForallRegion (a) (NFn () Unit () () () User)))
          (RegionLam (a) (Lam User polyuse () unit))
       (Scope ()
         (Let (first const Unit) (Apply (RegionApp f (ph)))
           (Scope () (Apply (RegionApp f (ph)))))))))

(test-case "BorrowAt は内側 Scope の外へ返した借用の寿命を保つ"
  (define-values (configs _rules)
    (prepared-trace
     "BorrowAt"
     '(Scope ()
        (Let (x let (Owned Int)) 7
          (Let (b let (Borrowed Int ph)) (Scope () (Borrow x))
            (Read b))))
     'Int))
  (check-not-false
   (for/or ([cfg (in-list configs)])
     (find-core-path
      (config-core cfg)
      (lambda (node)
        (match node [`(BorrowAt ,_ ,_ ,_) #t] [_ #f]))))))

(test-case "BorrowMutAt の trace は Assign 後も構成検査を保つ"
  (define-values (_configs _rules)
    (prepared-trace
     "BorrowMutAt"
     '(Scope ()
        (Let (x let (Owned Int)) 7
          (Let (b let (BorrowedMut Int ph)) (BorrowMut x)
            (Assign b 8))))
     'Unit))
  (void))

(test-case "一度取得した可変借用を二度 Read する形は性質 8 の oracle を通る"
  (define source
    '(Scope ()
       (Let (x let (Owned Int)) 7
         (Let (b let (BorrowedMut Int ph)) (BorrowMut x)
           (Let (u let Int) (Read b) (Read b))))))
  (match (prepare-borrow-term* source)
    [`(ok ,start ,sidecar ,ir ,expected)
     (check-equal? expected 'Int)
     (define-values (configs rules) (trace-g2 start))
     (check-configs "BorrowMut duplicated reference" start configs rules '()
                    expected)
     (check-equal?
      (check-borrow-execution start sidecar ir 200 (make-bcounters))
      'ok)]
    [other (fail (format "source の準備に失敗: ~s" other))]))

(test-case "ReborrowAt の trace は再借用と Read を保つ"
  (prepared-trace
   "ReborrowAt"
   '(Scope ()
      (Let (x let (Owned Int)) 7
        (Let (b let (BorrowedMut Int ph)) (BorrowMut x)
          (Scope ()
            (Let (c let (Borrowed Int ph)) (Reborrow b) (Read c))))))
   'Int))

(test-case "ProjBorrowAt の trace は nested Scope の外で読み取れる"
  (prepared-trace
   "ProjBorrowAt"
   '(Scope ()
      (Let (x let (Owned (Record ((a Int mut))))) (Rec ((a mut 7)))
        (Let (b let (BorrowedMut (Record ((a Int mut))) ph)) (BorrowMut x)
          (Scope () (Read (ProjBorrow b a))))))
   'Int))

(test-case "FromRawPtr の trace は AddressOf から戻した借用を検査する"
  (define source
    '(Scope ()
       (Let (x let (Owned Int)) 7
         (Unsafe (Read (FromRawPtr (AddressOf (BorrowMut x)) 0))))))
  (define-values (expected start configs rules ptr-sidecar)
    (typed-unsafe-trace source))
  (check-equal? expected 'Int)
  (check-not-false (memq 'R-FromRawPtrMut rules))
  (check-configs "FromRawPtr" start configs rules '() expected)
  ;; raw pointer の遷移は性質 9 の担当なので、この trace だけ性質 8 ではなく
  ;; 性質 9 の oracle に照合する。
  (check-equal? (check-unsafe-execution start ptr-sidecar 200 (make-ucounters))
                'ok))

(test-case "RegionApp の深さ 1 は全構成で型と row を保つ"
  (define-values (expected _start configs rules sidecar ir)
    (region-app-depth-one-trace))
  (check-equal? expected 'Unit)
  (check-configs-and-oracle "RegionApp depth 1" (first configs) configs rules
                            region-app-callables expected sidecar ir))

(test-case "同じ RegionLam を異なる region で二度適用する"
  (define-values (configs rules)
    (prepared-trace "RegionApp repeated" repeated-region-app-source
                    'Unit repeated-callables))
  (check-equal? (count (lambda (rule) (eq? rule 'R-RegionApp)) rules) 2)
  (check-equal? (length configs) (add1 (length rules))))

(define apply-callables
  '((read (ForallRegion (a)
            (NFn ((Borrowed Int (RParam a))) Int () () () User)))))

(define apply-borrow-source
  '(Scope ()
     (Let (x let (Owned Int)) 7
       (Let (b let (Borrowed Int ph)) (Borrow x)
         (Apply (RegionApp
                 (RegionLam (a) (Lam User read (p) (Read p)))
                 (ph))
                b)))))

(test-case "R-Beta は BorrowRef を Lam 本体の Read へ移す"
  (define-values (configs rules)
    (prepared-trace "Apply BorrowRef argument" apply-borrow-source 'Int
                    apply-callables))
  (define beta-index (index-of rules 'R-Beta))
  (check-not-false beta-index)
  (check-true (for/or ([cfg (in-list configs)] [index (in-naturals)]
                       #:when (<= index beta-index))
                (tree-any?
                 (config-core cfg)
                 (lambda (node)
                   (match node
                     [(list 'Apply
                            (list 'Lam 'User _ (list _) (list 'Read _))
                            (list 'BorrowRef _ _ _)) #t]
                     [_ #f]))))
              (format "R-Beta の直前で BorrowRef が実引数にある: ~s"
                      (map config-core (take configs (add1 beta-index)))))
  (check-true
   (tree-any?
    (config-core (list-ref configs (add1 beta-index)))
    (lambda (node)
      (match node [`(Read (BorrowRef ,_ ,_ ,_)) #t] [_ #f])))
   "R-Beta の直後で BorrowRef が Lam 本体にある"))

(test-case "Eliminate の枝は BorrowRef を読み取れる"
  (prepared-trace
   "Eliminate"
   '(Scope ()
      (Let (x let (Owned (List Int)))
        (Construct (List Int) cons 7 (Construct (List Int) nil))
        (Let (b let (Borrowed (List Int) ph)) (Borrow x)
          (Eliminate b ((nil () -> 0) (cons (h t) -> (Read h)))))))
   'Int))

(test-case "UnionEliminate の枝は BorrowRef を読み取れる"
  (prepared-trace
   "UnionEliminate"
   '(Scope ()
      (Let (x let (Owned (Union Int String)))
        (UnionInject (Union Int String) Int 7)
        (Let (b let (Borrowed (Union Int String) ph)) (Borrow x)
          (UnionEliminate b
            ((Int i -> (Read i)) (String s -> 0))))))
   'Int))

(test-case "UnionVal の借用 payload は実行時型を使って全 config を検査する"
  (define borrowed '(Borrowed Int (RParam %omitted)))
  (define union `(Union ,borrowed String))
  (prepared-trace
   "borrowed UnionVal"
   `(Scope ()
      (Let (owner let (Owned Int)) 7
        (Let (value let ,union)
             (UnionInject ,union ,borrowed (Borrow owner))
          (UnionEliminate value
            ((,borrowed borrowed -> (Read borrowed))
             (String text -> 0))))))
   'Int))

(test-case "UnionVal は region 以外が異なる payload を ill-typed のまま拒否する"
  (define result
    (type-of/raw
     '(UnionVal (Union Int String) Int "not an Int") '() '()))
  (check-match result `(fail ill-typed ,_ ,_ ...)))

(test-case "UnionVal の region だけ同形な候補が複数あると旧照合へ戻る"
  (define union '(Union (Borrowed Int 2)
                        (Union (Borrowed Int 3) String)))
  (define value `(UnionVal ,union (Borrowed Int 2) (BorrowRef 0 () 3)))
  (define cfg `(cfg ,value ((0 7 (declared (Owned Int))))
                    ((0 Available)) () ()))
  (check-equal? (config-type-failure-key cfg '()) 'ill-typed)
  (check-false (runtime-row cfg '() union)))

(test-case "UnionVal の concrete tag を outlive しない payload は拒否する"
  (define member '(Borrowed Int 10))
  (define union `(Union ,member String))
  (define value `(UnionVal ,union ,member (BorrowRef 0 () 11)))
  (define cfg `(cfg ,value ((0 7 (declared (Owned Int))))
                    ((0 Available)) () ()))
  (check-equal? (config-type-failure-key cfg '()) 'ill-typed)
  (check-false (runtime-row cfg '() union))
  (check-false (config-ok? cfg '() union '())))

(test-case "Record の欄の借用は合流した表で読み取れる"
  (define-values (configs _rules)
    (prepared-trace "Record borrow merge" (record-borrow-source) 'Unit))
  (define start (first configs))
  (check-false (config-type-failure-key start '()))
  (check-true (config-ok? start '() 'Unit (runtime-row start '() 'Unit)))
  (check-false (tree-any? (config-core start)
                          (lambda (node)
                            (match node [`(RVar ,_) #t] [_ #f])))))

(define recur-callables
  '((recf (ForallRegion (a)
            (NFn ((Option Int)) Int () () () User)))))

(define recur-source
  '(Scope (1)
     (Recur recf f (state)
       (Eliminate state
         ((none () -> 0)
          (some (item) ->
            (Apply f (Construct (Option Int) none)))))
       (Apply (RegionApp f (ph))
              (Construct (Option Int) some 1)))))

(define (recur-start)
  (typed-source-trace recur-source recur-callables '((1 Int)) 1))

(test-case "R-RegionAppRecur 前後と二度以上の RecurUnfold は検査を保つ"
  (define-values (expected start configs rules sidecar ir) (recur-start))
  (check-equal? expected 'Int)
  (check-configs-and-oracle "R-RegionAppRecur" start configs rules
                            recur-callables expected sidecar ir)
  (define app-index (index-of rules 'R-RegionAppRecur))
  (check-not-false app-index)
  (check-true (>= (count (lambda (rule) (eq? rule 'R-RecurUnfold)) rules) 2))
  (check-true (config-ok? (list-ref configs app-index) recur-callables
                          expected (runtime-row (list-ref configs app-index)
                                                recur-callables expected)))
  (check-true (config-ok? (list-ref configs (add1 app-index)) recur-callables
                          expected (runtime-row (list-ref configs (add1 app-index))
                                                recur-callables expected))))

(test-case "R-RecurBind の継続に残る BorrowRef は素通しとして照合する"
  (define callables
    '((rf (NFn (Int) Int () () () User))))
  (define-values (_configs rules)
    (prepared-trace
     "R-RecurBind passthrough"
     '(Scope ()
        (Let (x let (Owned Int)) 7
          (Let (b let (Borrowed Int ph)) (Borrow x)
            (Recur rf f (n) n (Read b)))))
     'Int callables))
  (check-not-false (memq 'R-RecurBind rules)))

#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../erase.rkt"
         "../driver.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../pr-machine.rkt"
         "../borrow.rkt"
         "../region.rkt"
         "../resource-type.rkt"
         "../span-core.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         "../type-shape.rkt"
         "../typing.rkt")

(define resource-record-type
  '(Record ((owned (Owned Res) imm))))
(define owned-record-value
  '(Rec ((owned imm (OwnedLeaf (tok 13) (resource 13))))))

(define (type-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok (list type _row)) type]
    [_ 'ill-typed]))

(define (row-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok (list _type row)) row]
    [_ 'ill-typed]))

(define (key-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok _) 'ok]
    [(list 'fail key _node _details ...) key]))

(define (type-of/with-ir core [callables '()] [environment '()])
  (define ir (build-region-ir (erase-core core)))
  (type-of/raw core '() callables environment
               (region-ctx ir '() (hash) (hash))))

(define (key-of/with-ir core [callables '()] [environment '()])
  (match (type-of/with-ir core callables environment)
    [(list 'ok _) 'ok]
    [(list 'fail key _node _details ...) key]))

(define resource-environment `((y ,resource-record-type)))
(define (typed-let body) `(Let (x ,resource-record-type) y ,body))

(define (test-ledger-fail reason kind key)
  (error 'test-ledger-fail "~s ~s ~s" reason kind key))
(define plain-data-ledger
  (make-trait-ledger canonical-trait-env
                     #:data '((Plain () ((plain (Int)))))
                     #:fail test-ledger-fail))
(define-syntax-rule (with-data body ...)
  (call-with-trait-ledger plain-data-ledger (lambda () body ...)))

(define (initial core [tokens '(((tok 13) Available))])
  `(cfg (Scope () ,core) () () ,tokens ()))

(define (g2-trace start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 60])
    (when (zero? fuel)
      (error 'g2-trace "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps (error 'g2-trace "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-config-trace configs callables expected)
  (define rows
    (for/list ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config callables expected))
      (check-not-false row
                       (format "runtime row を得られない config ~a: ~s"
                               index config))
      (check-true (config-ok? config callables expected row)
                  (format "不正な中間 config ~a: ~s" index config))
      row))
  (for ([before (in-list rows)] [after (in-list (cdr rows))]
        [index (in-naturals)])
    (check-true (row-subset? after before)
                (format "config ~a から次の config で row が増えた: ~s -> ~s"
                        index before after))))

(define (token-states config)
  (match config [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define two-token-table '(((tok 13) Available) ((tok 14) Available)))
(define owned-record-value-2
  '(Rec ((owned imm (OwnedLeaf (tok 14) (resource 14))))))

(define (core-final-trace core tokens expected)
  (define-values (configs _rules) (g2-trace (initial core tokens)))
  (check-config-trace configs '() expected)
  (match (last configs)
    [`(cfg ,_value ,_heap ,_states ,_tokens ,trace) trace]))

(define (pr-final-trace core)
  (define-values (status target) (lower core 'racket-cs))
  (check-eq? status 'ok (format "lower failed: ~s" target))
  (match (run-pr (inject-pr target) 1000)
    [`(pcfg ,_value ,_heap ,_states ,trace) trace]
    [other (error 'pr-final-trace "予期しない結果: ~s" other)]))

(define (fin-events trace)
  (filter (match-lambda [`(fin ,_) #t] [_ #f]) trace))

(define (fin-leaf-count trace)
  (count (match-lambda [`(finLeaf ,_ ,_) #t] [_ #f]) trace))

(define (first-let-type core)
  (let walk ([term (erase-core core)])
    (match term
      [`(Let (,_ ,type) ,_ ,_) type]
      [`(Let (,_ ,_ ,type) ,_ ,_) type]
      [(? list? terms) (for/or ([child (in-list terms)]) (walk child))]
      [_ #f])))

(define (first-let-core core)
  (let walk ([term (erase-core core)])
    (match term
      [`(Let ,_ ,_ ,_) term]
      [(? list? terms) (for/or ([child (in-list terms)]) (walk child))]
      [_ #f])))

(define aggregate-option-type
  '(Record ((owner (Option (Owned Res)) imm)
            (a Int imm))))
(define aggregate-option-value
  `(Rec ((owner imm
                 (Construct some (Types (Owned Res))
                            (Apply acquire 13)))
         (a imm 41))))
(define nested-aggregate-type
  `(Record ((n ,aggregate-option-type imm))))
(define nested-aggregate-value
  `(Rec ((n imm ,aggregate-option-value))))

(define optional-aggregate-type
  '(Record ((owner (Option (Owned Res)) imm)
            (maybe Int imm opt)
            (a Int imm))))
(define optional-aggregate-value
  `(Rec ((owner imm
                 (Construct some (Types (Owned Res))
                            (Apply acquire 13)))
         (a imm 41))))

(define (elaborate-compiled expression)
  (match (elab expression)
    [`(err ,diagnostic) diagnostic]
    [(list core type row callables)
     (define ledger (current-trait-ledger))
     (define executable
       (call-with-trait-ledger
        ledger
        (lambda () (execution-core core callables))))
     (compiled core type row callables ledger executable)]))

(define (check-compiled-source-core artifact)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (lambda ()
     (check-equal?
      (core-type-of (erase-core (compiled-core artifact)) '()
                    (compiled-callables artifact))
      (list (compiled-type artifact) (compiled-row artifact)))))
  artifact)

(define (run-compiled-execution-core artifact)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (lambda ()
     (define-values (configs rules)
       (g2-trace
        (initial (compiled-execution-core artifact) '())))
     (check-config-trace configs (compiled-callables artifact)
                         (compiled-type artifact))
     (list (last configs) rules))))

(define (apply-function input-type input-value body return-type row)
  `(Apply
    (Fn ((argument ,input-type)) ,return-type ,row ,body)
    ,input-value))

(define (contains-node? head tree)
  (or (match tree
        [(list (== head) _ ...) #t]
        [_ #f])
      (and (list? tree) (ormap (lambda (child) (contains-node? head child)) tree))))

(define (contains-drop-move? tree)
  (or (match tree [`(Drop (Move ,_)) #t] [_ #f])
      (and (list? tree) (ormap contains-drop-move? tree))))

(define (contains-nested-projection? tree)
  (or (match tree [`(Proj (Proj ,_ n) a) #t] [_ #f])
      (and (list? tree) (ormap contains-nested-projection? tree))))

(test-case "未使用の集約資源型 Let は scope 終了時に leaf を drop する"
  (define machine-core `(Let (x ,resource-record-type) ,owned-record-value 0))
  (define typing-core (typed-let 0))
  (define expected (type-of typing-core '() resource-environment))
  (define row (row-of typing-core '() resource-environment))
  (define-values (configs rules) (g2-trace (initial machine-core)))
  (check-not-false (member 'R-LetOwned rules))
  (check-false (member 'R-Let rules))
  (check-config-trace configs '() expected)
  (check-equal? (token-states (last configs)) '(((tok 13) Dropped))))

(test-case "集約資源型 Let の値は一度 Move でき、effect に Own を加える"
  (check-equal? (type-of (typed-let '(Move x)) '() resource-environment)
                resource-record-type)
  (check-equal? (row-of (typed-let '(Move x)) '() resource-environment) '(Own))
  (check-equal? (key-of '(Move y) '() resource-environment) 'move-non-owned)
  (check-equal? (key-of (typed-let '(Let (z Unit) unit x)) '() resource-environment)
                'owned-variable-requires-move))

(test-case "集約資源型 Let の値を Drop すると leaf を drop する"
  (define core
    `(Let (x ,resource-record-type) ,owned-record-value (Drop (Move x))))
  (define typing-core (typed-let '(Drop (Move x))))
  (define-values (configs rules) (g2-trace (initial core)))
  (check-equal? (type-of typing-core '() resource-environment) 'Unit)
  (check-equal? (row-of typing-core '() resource-environment) '(Own))
  (check-not-false (member 'R-LetOwned rules))
  (check-not-false (member 'R-Move rules))
  (check-config-trace configs '() 'Unit)
  (check-equal? (token-states (last configs)) '(((tok 13) Dropped))))

(test-case "Drop は Move 済みの root Owned と集約資源型を受け付ける"
  (define root-owned
    '(Let (x (Owned Res))
       (Apply (PrimVal (Reserved o-acquire) acquire) 13)
       (Drop (Move x))))
  (define aggregate (typed-let '(Drop (Move x))))
  (check-equal? (first (type-of/with-ir root-owned)) 'ok)
  (check-equal? (key-of/with-ir
                 '(Let (x (Owned Res))
                    (Apply (PrimVal (Reserved o-acquire) acquire) 13)
                    (Drop x)))
                'owned-variable-requires-move)
  (check-equal? (first (type-of/with-ir aggregate '() resource-environment)) 'ok)
  (check-equal? (key-of/with-ir (typed-let '(Drop x)) '() resource-environment)
                'owned-variable-requires-move))

(test-case "集約資源型の identity Let は値をそのまま返す"
  (define core `(Let (x ,resource-record-type) ,owned-record-value x))
  (define typing-core (typed-let 'x))
  (define-values (configs rules) (g2-trace (initial core)))
  (check-equal? (type-of typing-core '() resource-environment)
                resource-record-type)
  (check-not-false (member 'R-LetIdentity rules))
  (check-false (member 'R-LetOwned rules))
  (check-false (member 'R-Move rules))
  (check-config-trace configs '() resource-record-type)
  (check-equal? (match (last configs)
                  [`(cfg ,value () () ,_ ,_) value]
                  [_ #f])
                owned-record-value))

(test-case "root Owned の identity Let も place を作らない"
  (define core
    '(Let (x (Owned Res)) (Apply (PrimVal (Reserved o-acquire) acquire) 13) x))
  (define-values (configs rules) (g2-trace (initial core '())))
  (check-equal? (type-of core) '(Owned Res))
  (check-not-false (member 'R-LetIdentity rules))
  (check-false (member 'R-LetOwned rules))
  (check-config-trace configs '() '(Owned Res)))

(test-case "G2m の const identity Let は R-LetIdentityB を使う"
  (define core `(Let (x const ,resource-record-type) ,owned-record-value x))
  (define typed `(Let (x const ,resource-record-type) y x))
  (define-values (configs rules) (g2-trace (initial core)))
  (check-equal? (type-of typed '() resource-environment) resource-record-type)
  (check-not-false (member 'R-LetIdentityB rules))
  (check-false (member 'R-LetOwnedB rules))
  (check-config-trace configs '() resource-record-type))

(test-case "Let の規則分割は各形で決定的である"
  (define cases
    (list
     (list `(Let (x ,resource-record-type) ,owned-record-value 0)
           'R-LetOwned)
     (list `(Let (x ,resource-record-type) ,owned-record-value x)
           'R-LetIdentity)
     (list '(Let (x Int) 1 0) 'R-Let)
     (list '(Let (x mut Int) 1 0) 'R-LetMutB)
     (list `(Let (x const ,resource-record-type) ,owned-record-value x)
           'R-LetIdentityB)))
  (for ([case (in-list cases)])
    (define start (initial (first case)))
    (check-equal? (map first (raw-steps-g2/named start)) (list (second case)))))

(test-case "check 側の Let も資源型を注釈する"
  (define callables
    `((f (NFn (,resource-record-type) Int () () () User))))
  (define core
    `(Lam User f (y) (Let (x ,resource-record-type) y 0)))
  (define effective (box (hash)))
  (check-equal? (first (type-of/raw core '() callables '()
                                     #:mut-types effective))
                'ok)
  (check-equal? (hash-values (unbox effective)) (list resource-record-type)))

(test-case "mut Let の residual 型は machine へ注釈される"
  (define declared '(Record ()))
  (define actual '(Record ((owned (Owned Res) imm))))
  (define typing-core '(Let (x let (Record ())) y 0))
  (define effective (box (hash)))
  (define result
    (type-of/raw typing-core '() '() `((y ,actual)) #:mut-types effective))
  (check-equal? (first result) 'ok)
  (check-equal? (unbox effective) (hash '() actual))
  (define machine-core
    `(Let (x let ,declared) ,owned-record-value 0))
  (define annotated
    (annotate-mut-binding-types machine-core (unbox effective)))
  (check-equal? annotated `(Let (x let ,actual) ,owned-record-value 0))
  (define-values (configs rules) (g2-trace (initial annotated)))
  (check-not-false (member 'R-LetOwnedB rules))
  (check-false (member 'R-LetB rules))
  (check-config-trace configs '() 'Int)
  (check-equal? (token-states (last configs)) '(((tok 13) Dropped))))

(test-case "σ が同一化する借用 Union を資源 Let の有効型で正規化する"
  (define borrow-union
    '(Union (Borrowed Res (RVar 0))
            (Union (Borrowed Res (RVar 1)) String)))
  (define optional-owned '(Option (Owned Res)))
  (define declared
    `(Record ((borrow ,borrow-union imm) (owned ,optional-owned imm))))
  (define source `(UnionInject (Union Int Bool) Int 1))
  (define branch-a
    `(UnionInject ,borrow-union (Borrowed Res (RVar 0))
                  (Scope () (Borrow outer))))
  (define branch-b
    `(UnionInject ,borrow-union (Borrowed Res (RVar 1))
                  (Scope () (Borrow inner))))
  (define borrowed-value
    `(UnionEliminate ,source
                     ((Int i -> ,branch-a) (Bool b -> ,branch-b))))
  (define value
    `(Rec ((borrow imm ,borrowed-value)
           (owned imm (Construct ,optional-owned none)))))
  (define core
    `(Scope ()
       (Let (outer let (Owned Res)) (resource 13)
         (Let (inner let (Owned Res)) (resource 14)
           (Let (x ,declared) ,value 0)))))
  (define ir (build-region-ir core))
  (define effective-types (box (hash)))
  (define result
    (type-of/raw*+borrows core '() '() '()
                          (region-ctx ir '() (hash) (hash))
                          #:mut-types effective-types))
  (check-equal? (first result) 'ok)
  (define sigma (list-ref (second result) 3))
  (check-equal? (hash-ref sigma 0) (hash-ref sigma 1))
  (define common-region (region->rho ir (hash-ref sigma 0)))
  (define normalized-borrow-union
    (normalize-type `(Union (Borrowed Res ,common-region) String)))
  (define normalized-effective
    (normalize-type
     `(Record ((borrow ,normalized-borrow-union imm)
               (owned ,optional-owned imm)))))
  (check-equal? (hash-ref (unbox effective-types) '(0 1 1))
                normalized-effective)
  (check-true (type-normal? normalized-effective))
  (define runtime-value
    `(Rec ((borrow imm
           (UnionVal ,normalized-borrow-union
                            (Borrowed Res ,common-region)
                            (BorrowRef 0 () ,common-region)))
           (owned imm (Construct ,optional-owned none)))))
  (define config
    `(cfg 0
          ((0 (resource 13) (declared (Owned Res)))
           (1 ,runtime-value (declared ,normalized-effective)))
          ((0 Available) (1 Available))
          () ()))
  (check-equal? (first (second result)) 'Int)
  (check-equal? (second (second result)) '())
  (check-config-trace (list config) '() 'Int))

(test-case "Recur の固定点再走査は資源 Let の借用型を安定させる"
  (define declared '(Record ((owned (Option (Owned Res)) imm))))
  ;; Record の root-Owned 欄は通常の Rec では組み立てられないため、
  ;; Option 内の Owned leaf と Borrowed の残余欄で集約資源型を作る。
  (define value
    '(Rec ((borrow imm (Borrow 1))
          (owned imm (Construct (Option (Owned Res)) some
                                (OwnLeaf (resource 13)))))))
  ;; Borrow は最初の Ψ に capability を加えるため、Recur の本体は固定点まで
  ;; 少なくとも 2 回検査される。同じ Let 位置の RVar が走査ごとに変わると、
  ;; 有効型 side table の衝突 error になっていた。
  (define core
    `(Scope (1)
       (Recur recur-id f ()
         (Let (x let ,declared) ,value 0)
         0)))
  (define callables '((recur-id (NFn () Int () () () User))))
  (define ir (build-region-ir core))
  (define borrow-point '(0 0 0 0))
  (define borrow-rho (region->rho ir (region-at ir borrow-point)))
  (define Λ
    (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))
  (define effective (box (hash)))
  (define result
    (type-of/raw (annotate-regions core ir)
                 '((1 Int)) callables '() Λ
                 #:mut-types effective))
  (check-equal? (first result) 'ok)
  (check-equal? (second result) (list 'Int '()))
  (check-equal? (hash-count (unbox effective)) 1)
  (define expected-effective
    `(Record ((borrow (Borrowed Int ,borrow-rho) imm)
              (owned (Option (Owned Res)) imm))))
  (check-equal? (hash-values (unbox effective)) (list expected-effective))
  (check-true (type-normal? expected-effective)))

(test-case "注釈は spanful Core の Let の位置にも一致する"
  (define span '(#:span synthetic 0 1))
  (define core
    `(Let ,span ((#:bind x ,span) ,resource-record-type)
       y (#:lit 0 ,span)))
  (define effective (box (hash)))
  (check-equal? (first (type-of/raw core '() '() resource-environment
                                     #:mut-types effective))
                'ok)
  (check-equal? (hash-values (unbox effective)) (list resource-record-type))
  (check-equal? (annotate-mut-binding-types core (unbox effective))
                `(Let (x ,resource-record-type) y 0)))

(test-case "resource でない Data は台帳下で通常の Let と PLet を使う"
  (define type '(Data Plain ()))
  (define core `(Let (x ,type) (Construct ,type plain 1) 0))
  (with-data
    (check-false (runtime-resource-type? type))
    (check-equal? (map first (raw-steps-g2/named (initial core '())))
                  '(R-Let))
    (define-values (status target) (lower core 'racket-cs))
    (check-eq? status 'ok)
    (check-true (match target [`(PLet ,_ (PTagged ,_ 1) 0) #t] [_ #f])))
  (check-exn exn:fail? (lambda () (runtime-resource-type? type))))

(test-case "execution-core は失敗を内部 error にし、通常項を保つ"
  (check-equal? (execution-core '(Let (x Int) 1 x) '())
                '(Let (x Int) 1 x))
  (check-exn exn:fail?
             (lambda () (execution-core '(Move 0) '()))))

(test-case "compile-source は residual を含む有効型を実行用 Core へ注釈する"
  (define source
    (string-append
     "fn f(x: { owned: Owned<Int>, n: Int }) -> Int {\n"
     "  let y: { n: Int } = x\n"
     "  0\n"
     "}\n"
     "0"))
  (define result (compile-source/string 'affine-let source))
  (check-true (compiled? result))
  (define declared '(Record ((n Int imm))))
  (define effective
    '(Record ((n Int imm) (owned (Owned Int) imm))))
  (check-equal? (first-let-type (compiled-core result)) declared)
  (check-equal? (first-let-type (compiled-execution-core result)) effective)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (check-equal?
      (core-type-of (erase-core (compiled-core result)) '()
                    (compiled-callables result))
      (list (compiled-type result) (compiled-row result)))))
  (check-not-equal? (compiled-core result)
                    (compiled-execution-core result)))

(test-case "集約資源 Let の全中間状態で row と構成を検査する"
  (define actual
    '(Record ((n Int imm) (owned (Option (Owned Res)) imm))))
  (define declared '(Record ((n Int imm))))
  (define core
    `(Let (x ,actual)
       (Rec ((n imm 0)
             (owned imm (Construct (Option (Owned Res)) some
                                   (OwnLeaf (resource 13))))))
       (Let (y let ,declared) (Move x) 0)))
  (define executed (execution-core core '()))
  (define-values (configs rules) (g2-trace (initial executed '())))
  (check-not-false (member 'R-LetOwned rules))
  (check-not-false (member 'R-LetOwnedB rules))
  (check-config-trace configs '() 'Int))

(test-case "P は Let と Lam の同名 binder を正しく遮蔽する"
  (define shadowed
    `(Let (x ,resource-record-type) y (Let (x Int) 1 x)))
  (check-equal? (type-of shadowed '() resource-environment) 'Int)
  (define restored
    `(Let (x ,resource-record-type) y
       (Let (z Int) (Let (x Int) 1 x) x)))
  (check-equal? (key-of restored '() resource-environment)
                'owned-variable-requires-move)
  (define initialized-from-outer
    `(Let (x ,resource-record-type) y
       (Let (z ,resource-record-type) (Move x) (Move z))))
  (check-equal? (type-of initialized-from-outer '() resource-environment)
                resource-record-type)
  (define function-type
    `(NFn (Int ,resource-record-type) ,resource-record-type () () () User))
  (define callables `((f ,function-type)))
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y (Lam User f (n x) x))
            callables resource-environment)
   function-type)
  (check-equal?
   (key-of '(Lam User f (x) (Move x))
           `((f (NFn (,resource-record-type) ,resource-record-type () (Own) () User))))
   'move-non-owned))

(test-case "Eliminate と UnionEliminate の branch binder は P から除かれる"
  (define option-type `(Option ,resource-record-type))
  (define environment
    `((option ,option-type) (fallback ,resource-record-type)
      (y ,resource-record-type)))
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y
               (Let (z ,resource-record-type)
                 (Eliminate option ((some (x) -> x)
                                    (none () -> fallback)))
                 (Move x)))
            '() environment)
   resource-record-type)
  (define union-type
    (normalize-type `(Union ,resource-record-type Bool)))
  (define union-environment
    `((union ,union-type) (fallback ,resource-record-type) (y ,resource-record-type)))
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y
               (Let (z ,resource-record-type)
                 (UnionEliminate union
                   ((,resource-record-type x -> x)
                    (Bool b -> fallback)))
                 (Move x)))
            '() union-environment)
   resource-record-type))

(test-case "P は Recur、RecurVal、Handle の binder も遮蔽する"
  (define environment `((y ,resource-record-type)))
  (define recur-signature `(NFn () Int () () () User))
  (define recur-callables `((recur-id ,recur-signature)))
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y
               (Recur recur-id x () 0 (Apply x)))
            recur-callables environment)
   'Int)
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y
               (RecurVal recur-id x () (Apply x)))
            recur-callables environment)
   recur-signature)
  (define parameter-signature
    `(NFn (,resource-record-type) ,resource-record-type () () () User))
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y
               (RecurVal f f (x) x))
            `((f ,parameter-signature)) environment)
   parameter-signature)
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y
               (Handle (Return boundary ,resource-record-type)
                 (x -> (Let (z ,resource-record-type) x (Move z)))
                 (Perform (Return boundary ,resource-record-type) y)))
            '() environment)
   resource-record-type))

(test-case "複数 field binder の Eliminate も P の同名変数を遮蔽する"
  (define list-type `(List ,resource-record-type))
  (define environment
    `((y ,resource-record-type) (items ,list-type)
      (fallback ,resource-record-type)))
  (check-equal?
   (type-of `(Let (x ,resource-record-type) y
               (Let (z ,resource-record-type)
                 (Eliminate items ((nil () -> fallback)
                                   (cons (x tail) -> x)))
                 (Move x)))
            '() environment)
   resource-record-type))

(test-case "T-MovePlace は metadata の集約資源型を返す"
  (define config
    `(cfg (Scope (0) (Move 0))
          ((0 ,owned-record-value (declared ,resource-record-type)))
          ((0 Available))
          (((tok 13) Available))
          ()))
  (check-config-trace (list config) '() resource-record-type))

(test-case "T-MovePlace は metadata の root Owned 型を保持する"
  (define config
    '(cfg (Scope (0) (Move 0))
          ((0 (resource 13) (declared (Owned Res))))
          ((0 Available))
          ()
          ()))
  (check-config-trace (list config) '() '(Owned Res)))

(test-case "metadata の無い place は従来の Owned Ξ 型を返す"
  (define config
    '(cfg (Scope (0) (Move 0))
          ((0 (resource 13)))
          ((0 Available))
          ()
          ()))
  (check-config-trace (list config) '() '(Owned Res)))

(test-case "未使用の集約資源型 Let 二つは Core と PR で同じ順に drop する"
  (define core
    `(Let (x ,resource-record-type) ,owned-record-value
       (Let (z ,resource-record-type) ,owned-record-value-2 0)))
  (define typed
    `(Let (x ,resource-record-type) y
       (Let (z ,resource-record-type) y2 0)))
  (define environment
    `((y ,resource-record-type) (y2 ,resource-record-type)))
  (define expected (type-of typed '() environment))
  (define core-trace (core-final-trace core two-token-table expected))
  (check-equal? (fin-events (pr-final-trace core)) (fin-events core-trace))
  (check-equal? (fin-events core-trace) '((fin 1) (fin 0)))
  (check-equal? (fin-leaf-count core-trace) 2))

(test-case "root Owned identity Let の値と終端事象は Core と PR で一致する"
  (define core
    '(Let (x (Owned Res))
       (Apply (PrimVal (Reserved o-acquire) acquire) 13)
       x))
  (define core-trace (core-final-trace core '() '(Owned Res)))
  (define core-result
    (match (last (let-values ([(configs _rules)
                               (g2-trace (initial core '()))])
                   configs))
      [`(cfg ,value ,_heap ,_states ,_tokens ,_) value]))
  (define-values (lower-status lowered-value)
    (lower-value core-result 'racket-cs))
  (check-eq? lower-status 'ok)
  (define pr-result
    (match (run-pr (inject-pr (let-values ([(status target)
                                           (lower core 'racket-cs)])
                                (check-eq? status 'ok)
                                target))
                   1000)
      [`(pcfg ,value ,_heap ,_states ,_trace) value]))
  (check-equal? pr-result lowered-value)
  (check-equal? (fin-events core-trace) '())
  (check-equal? (fin-events (pr-final-trace core)) '()))

(test-case "Surface の資源型 let は裸の二度読みを E-OWN-010 で拒否する"
  (define duplicate-type
    `(Record ((left ,aggregate-option-type imm)
              (right ,aggregate-option-type imm))))
  (define source
    `(Fn ((argument ,aggregate-option-type)) ,duplicate-type ()
         (Let y argument
           (Rec ((left imm y) (right imm y))))))
  (match (elab source)
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-OWN-010")]
    [other (fail-check (format "二度読みを拒否しなかった: ~s" other))]))

(test-case "Surface の資源型 let は Move を二度通し、実行時に R-MoveError へ進む"
  (define body
    `(Let (y let ,aggregate-option-type) argument
       (Let (z let ,aggregate-option-type) (Move y) (Move y))))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function aggregate-option-type aggregate-option-value
                      body aggregate-option-type '(Own)))))
  (check-true (compiled? artifact))
  (define-values (configuration rules)
    (apply values (run-compiled-execution-core artifact)))
  (check-not-false (member 'R-MoveError rules))
  (check-true
   (match configuration
     [`(cfg (Error ,_) ,_heap ,_states ,_tokens ,_trace) #t]
     [_ #f])))

(test-case "Surface の Drop x は Drop (Move x) へ写り、leaf を Dropped にする"
  (define body
    `(Let (y let ,aggregate-option-type) argument (Drop y)))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function aggregate-option-type aggregate-option-value
                      body 'Unit '(Own)))))
  (check-true (contains-drop-move? (erase-core (compiled-core artifact))))
  (define-values (configuration _rules)
    (apply values (run-compiled-execution-core artifact)))
  (check-equal?
   (match configuration
     [`(cfg unit ,_heap ,_states ,tokens ,_trace) (map second tokens)]
     [other (list 'unexpected other)])
   '(Dropped)))

(test-case "Surface の資源型と集約資源型 identity let は両 phase で受理される"
  (define root
    (elaborate-compiled
     '(Let (x let (Owned Res))
        (Apply acquire 13)
        x)))
  (define aggregate
    (elaborate-compiled
     `(Let (x let ,aggregate-option-type) ,aggregate-option-value x)))
  (for ([artifact (in-list (list root aggregate))])
    (check-true (compiled? (check-compiled-source-core artifact)))))

(test-case "Surface の shadowing 後も外側の place 変数の P が復元される"
  (define inner-let-shadow
    `(Let (x let ,aggregate-option-type) ,aggregate-option-value
       (Let z (Let x 1 x) (Move x))))
  (define function-parameter-shadow
    `(Let (x let ,aggregate-option-type) ,aggregate-option-value
       (Let z (Apply (Fn ((x Int)) Int () x) 1) (Move x))))
  (for ([source (in-list (list inner-let-shadow function-parameter-shadow))])
    (check-true
     (compiled?
      (check-compiled-source-core (elaborate-compiled source))))))

(test-case "c1c1 の経過措置では仮引数を裸で読める（c1c2 で期待を反転する）"
  (define source
    `(Fn ((x ,aggregate-option-type)) Int () (Proj x a)))
  (define artifact
    (check-compiled-source-core (elaborate-compiled source)))
  (check-equal? (compiled-type artifact)
                (normalize-type
                 `(NFn (,aggregate-option-type) Int () () () User))))

(test-case "Surface の place 射影は x.a、z.n.a、optional 末端を両 phase で扱う"
  (define direct
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function
       aggregate-option-type aggregate-option-value
       `(Let (x let ,aggregate-option-type) argument (Proj x a))
       'Int '()))))
  (define nested
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function
       nested-aggregate-type nested-aggregate-value
       `(Let (z let ,nested-aggregate-type) argument
          (Proj (Proj z n) a))
       'Int '()))))
  (define optional
    (check-compiled-source-core
     (elaborate-compiled
      `(Let (x let ,optional-aggregate-type)
         ,optional-aggregate-value
         (Proj x maybe)))))
  (check-equal? (compiled-type direct) 'Int)
  (check-equal? (compiled-type nested) 'Int)
  (check-equal? (compiled-type optional) '(Option Int))
  (check-true
   (contains-node? 'ProjOpt (erase-core (compiled-core optional))))
  (check-true
   (contains-nested-projection? (erase-core (compiled-core nested))))
  (check-equal?
   (match (first (run-compiled-execution-core direct))
     [`(cfg ,value ,_heap ,_states ,_tokens ,_trace) value])
   41)
  (check-equal?
   (match (first (run-compiled-execution-core nested))
     [`(cfg ,value ,_heap ,_states ,_tokens ,_trace) value])
   41)
  (define-values (_nested-config nested-rules)
    (apply values (run-compiled-execution-core nested)))
  (check-equal? (count (lambda (rule) (eq? rule 'R-ProjPlace)) nested-rules) 1)
  (check-equal?
   (match (first (run-compiled-execution-core optional))
     [`(cfg ,value ,_heap ,_states ,_tokens ,_trace) value])
   '(Construct (Option Int) none)))

(test-case "Surface と Core は資源型 place の資源欄射影を E-OWN-010 で拒否する"
  (define source
    (apply-function
     aggregate-option-type aggregate-option-value
     `(Let (x let ,aggregate-option-type) argument (Proj x owner))
     '(Option (Owned Res)) '()))
  (match (elab source)
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-OWN-010")]
    [other (fail-check (format "資源欄射影を拒否しなかった: ~s" other))])
  (check-equal?
   (key-of `(Let (x ,(normalize-type aggregate-option-type)) y
              (Proj x owner))
           '() `((y ,(normalize-type aggregate-option-type))))
   'owned-variable-requires-move)
  (define nested-source
    `(Let (z let ,nested-aggregate-type) ,nested-aggregate-value
       (Proj (Proj z n) owner)))
  (match (elab nested-source)
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-OWN-010")]
    [other (fail-check (format "入れ子の資源欄射影を拒否しなかった: ~s" other))])
  (check-equal?
   (key-of `(Let (z ,(normalize-type nested-aggregate-type)) y
              (Proj (Proj z n) owner))
           '() `((y ,(normalize-type nested-aggregate-type))))
   'owned-variable-requires-move))

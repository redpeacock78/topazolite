#lang racket

(require racket/match
         redex/reduction-semantics
         rackunit
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../obs.rkt"
         "../origins.rkt"
         "../pr-obs.rkt"
         "../compat.rkt"
         "../search.rkt"
         "../ucore.rkt"
         "../typing.rkt")

(define e-type-mismatch
  (diagnostic-code-of 'elaborate 'type-mismatch))

(define (elaborate-ok source)
  (match (elab source)
    [(list core type row callables) (list core type row callables)]
    [other (fail-check (format "elaboration に失敗した: ~s" other))]))

(define (diagnostic-id-of source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [other (fail-check (format "失敗を期待したが成功した: ~s" other))]))

(define (tree-contains? tree predicate)
  (or (predicate tree)
      (and (pair? tree)
           (or (tree-contains? (car tree) predicate)
               (tree-contains? (cdr tree) predicate)))))

(define (find-adapter node)
  (match node
    [`(Let (,name let ,actual) ,_bound
           (Curry (Lam User ,callable ,binders ,body) ,argument))
     #:when (equal? name argument)
     (list name actual callable binders body
           `(Curry (Lam User ,callable ,binders ,body) ,argument))]
    [(? pair?)
     (or (find-adapter (car node)) (find-adapter (cdr node)))]
    [_ #f]))

(define (find-adapter-source node)
  (match node
    [`(Let (,name let ,_actual) ,bound
           (Curry (Lam User ,_callable ,_binders ,_body) ,argument))
     #:when (equal? name argument)
     bound]
    [(? pair?)
     (or (find-adapter-source (car node))
         (find-adapter-source (cdr node)))]
    [_ #f]))

(define (tree-count tree predicate)
  (+ (if (predicate tree) 1 0)
     (if (pair? tree)
         (+ (tree-count (car tree) predicate)
            (tree-count (cdr tree) predicate))
         0)))

(define (type-narrative-proofs tree)
  (match tree
    [`(Discharge (ProofRep (Reserved o-type-narrative) TypeNarrativeCap) ,inner)
     (cons '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
           (type-narrative-proofs inner))]
    [(? pair?)
     (append (type-narrative-proofs (car tree))
             (type-narrative-proofs (cdr tree)))]
    [_ '()]))

;; properties-lowering-test.rkt の compare-observations を公開面を増やさずに写す。
(define limits (read-bounds))
(define source-fuel (bounds-fuel limits))
(define fuel-attempts 4)

(define (obs-eval-pr/adaptive target depth start-fuel)
  (let loop ([fuel start-fuel] [remaining fuel-attempts])
    (define result (obs-eval-pr target depth fuel))
    (cond
      [(not (eq? (second result) 'timeout)) result]
      [(<= remaining 1) #f]
      [else (loop (* 2 fuel) (sub1 remaining))])))

(define (lowered-value value)
  (define-values (status result) (lower-value value 'racket-cs))
  (and (eq? status 'ok) result))

(define (compare-observations core target depth)
  (define source (obs-eval-g2 core depth source-fuel))
  (cond
    [(eq? (second source) 'timeout) 'discard]
    [else
     (define target-result (obs-eval-pr/adaptive target depth source-fuel))
     (cond
       [(not target-result) 'discard]
       [(and (equal? (map lowered-value (first source))
                     (first target-result))
             (eq? (second source) (second target-result)))
        'match]
       [else 'mismatch])]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 120])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule following))
       (loop following (append configs (list following))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (check-config-trace configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row
                     (format "config ~a の runtime row が無い: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "config ~a が不正: ~s" index configuration))))

(define adapter-source
  '(Let (adapted const (NFn (Int) (Union Int String) () ()))
        (Fn ((x (Union Int String))) Int () 7)
        (Apply adapted 1)))

(test-case "関数値の引数と返り値を変換する adapter を型付けして実行する"
  (match-define (list core type row callables)
    (elaborate-ok adapter-source))
  (check-equal? (list type row) '((Union Int String) ()))
  (check-equal? (core-type-of core '() callables) (list type row))
  (define execution
    (execution-core core callables))
  (match (run-g2 (inject-g2m execution) 1200)
    [`(cfg (UnionVal (Union Int String) Int 7) ,_heap ,_states ,_tokens ,_trace)
     (void)]
    [other (fail-check (format "adapter の実行値が不正: ~s" other))])
  (define erased (erase-core core))
  (define adapter (find-adapter erased))
  (check-not-false adapter)
  (match-define (list name actual callable _binders _body curry) adapter)
  (match _body
    [`(Handle (Return ,_ ,_)
              (,return-binder -> ,return-body)
              (Scope () ,_))
     (check-equal? return-body return-binder)]
    [other (fail-check (format "adapter の本体が Handle/Scope でない: ~s"
                               other))])
  (check-false
   (tree-contains? (erase-core core)
                   (lambda (node) (match node [`(Forward ,_) #t] [_ #f]))))
  (check-not-false (assoc callable callables))
  (match (core-type-of curry '() callables (list (list name actual)))
    [(list `(NFn (Int) (Union Int String) () () ()
                 (Derived User (Curry ,_))) '())
     (void)]
    [other (fail-check (format "adapter が素の NFn でない: ~s" other))])
  (check-equal? (term (verify-origins ,R0 ,(erase-core core))) 'ok)
  (define-values (status target) (lower erased 'racket-cs))
  (check-eq? status 'ok)
  (check-eq? (compare-observations execution target 1) 'match))

(test-case "資源の無い引数変換は ε_b を持たない"
  (match-define (list core type row callables)
    (elaborate-ok adapter-source))
  (define adapter (find-adapter (erase-core core)))
  (check-not-false adapter)
  (match-define (list name actual _callable _binders _body curry) adapter)
  (define-values (curry-type curry-row)
    (apply values
           (core-type-of curry '() callables (list (list name actual)))))
  (check-false (match curry-type [`(Owned ,_) #t] [_ #f]))
  (check-equal? (list type row curry-row)
                (list '(Union Int String) '() '())))

(test-case "effectful な変換元は一度だけ Let で評価する"
  (define actual '(NFn ((Union Int String)) Int () ()))
  (define expected '(NFn (Int) (Union Int String) () ()))
  (define source
    `(Fn () ,expected ((Yield Int))
         (Let (adapted const ,expected)
              (Apply
               (Fn () ,actual ((Yield Int))
                   (Yield 9 (Fn ((x (Union Int String))) Int () 7))))
              adapted)))
  (match-define (list core type row callables) (elaborate-ok source))
  (check-equal? (core-type-of core '() callables) (list type row))
  (check-equal?
   (core-type-of `(Apply ,core) '() callables)
   (list '(NFn (Int) (Union Int String) () () () User)
         '((Yield Int))))
  (define erased (erase-core core))
  (define adapter-source (find-adapter-source erased))
  (check-true (match adapter-source [`(Apply (Lam ,_ ,_ () ,_)) #t] [_ #f]))
  (check-equal?
   (tree-count erased
               (lambda (node)
                 (match node [`(Apply (Lam ,_ ,_ () ,_)) #t] [_ #f])))
   1)
  (match-define (list name _actual _callable _binders _body curry)
    (find-adapter erased))
  (match curry
    [`(Curry (Lam User ,_ ,_ ,_) ,fixed-argument)
     (check-equal? fixed-argument name)]
    [other (fail-check (format "Curry の固定引数が値でない: ~s" other))])
  (define-values (_configs rules)
    (trace-g2 (inject-g2m (execution-core `(Apply ,core) callables))))
  (check-equal? (count (lambda (rule) (eq? rule 'R-Yield)) rules) 1))

(test-case "Apply 前の引数変換と返り値変換は row を増やさない"
  (define actual '(NFn ((Union Int String)) Int ((Yield Int)) ()))
  (define expected '(NFn (Int) (Union Int String) ((Yield Int)) ()))
  (define typed-actual
    '(NFn ((Union Int String)) Int () ((Yield Int)) () User))
  (match-define (list core type row callables)
    (elaborate-ok
     `(Fn ((f ,actual)) ,expected ()
          (Let (adapted const ,expected) f adapted))))
  (define adapter (find-adapter (erase-core core)))
  (check-not-false adapter)
  (match-define (list _name _actual _callable binders body _curry) adapter)
  (match-define (list function-name parameter-name) binders)
  (check-equal?
   (core-type-of body '() callables
                 (list (list function-name typed-actual)
                       (list parameter-name 'Int)))
   '((Union Int String) ((Yield Int))))
  (check-equal? (core-type-of core '() callables) (list type row)))

(test-case "型が合わない関数値と arity 不一致は E-TYP-012"
  (check-equal?
   (diagnostic-id-of
    '(Let (f const (NFn (Int) Int () ()))
          (Fn ((x Bool)) Int () 1)
          f))
   e-type-mismatch)
  (check-equal?
   (diagnostic-id-of
    '(Let (f const (NFn (Int Int) Int () ()))
          (Fn ((x Int)) Int () 1)
          f))
   e-type-mismatch))

(test-case "TypeNarrativeCap の認可と ProofRep を adapter が増やさない"
  ;; elab と core-type-of は固定の Π0 で始まるため、authorization で拒否される
  ;; 文脈は公開入口から作れない。obligation の判定と ProofRep の搬送の一致で固定する。
  (define without-cap (initial-candidate-context '()))
  (check-equal? (obligation-proofs '(TypeNarrativeCap) without-cap) '(#f))
  (check-false (obligations-dischargeable? '(TypeNarrativeCap) without-cap))
  (define actual '(NFn ((Union Int String)) Int () (TypeNarrativeCap)))
  (define expected '(NFn (Int) Int () (TypeNarrativeCap)))
  (define direct-source
    `(Fn ((f ,actual)) Int () (Apply f 1)))
  (match-define (list direct-core direct-type direct-row direct-callables)
    (elaborate-ok direct-source))
  (check-equal? (core-type-of direct-core '() direct-callables)
                (list direct-type direct-row))
  (define proof '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
  (check-equal? (type-narrative-proofs (erase-core direct-core)) (list proof))

  (match-define (list core type row callables)
    (elaborate-ok
     `(Fn ((f ,actual)) ,expected ()
          (Let (adapted const ,expected) f adapted))))
  (check-equal? (core-type-of core '() callables) (list type row))
  (define adapter (find-adapter (erase-core core)))
  (check-not-false adapter)
  (match-define (list _name _actual _callable _binders body _curry) adapter)
  (check-equal? (type-narrative-proofs body) (list proof))
  (define through-source `(Fn ((f ,actual)) Int ()
                             (Let (adapted const ,expected) f
                               (Apply adapted 1))))
  (match-define (list through-core through-type through-row through-callables)
    (elaborate-ok through-source))
  (check-equal? (core-type-of through-core '() through-callables)
                (list through-type through-row))
  (check-equal? (type-narrative-proofs (erase-core through-core))
                (list proof proof))
  (check-equal? (term (verify-origins ,R0 ,(erase-core core))) 'ok))

(test-case "未供給の Q を要求する元の関数も adapter も capability を増やさない"
  (define actual '(NFn (Int) Int () (ValidNarrativeTrait)))
  (define adapted '(NFn (Int) (Union Int String) () (ValidNarrativeTrait)))
  (define direct
    `(Fn ((f ,actual)) Int () (Apply f 1)))
  (define through-adapter
    `(Fn ((f ,actual)) Int ()
         (Let (adapted const ,adapted) f (Apply adapted 1))))
  (check-equal?
   (diagnostic-id-of direct)
   (diagnostic-code-of 'elaborate 'unsatisfied-proof-obligation))
  (check-equal? (diagnostic-id-of through-adapter) e-type-mismatch))

(test-case "Borrowed payload の widening は互換でも tag 変換ではない"
  ;; UCore は Borrowed を受けないため、adapter の生成経路は静的入力から届かない。
  (define borrowed-int '(Borrowed Int 0))
  (define borrowed-union '(Borrowed (Union Int Bool) 0))
  (check-true (tag-compat? borrowed-int borrowed-int))
  (check-true (compat? borrowed-int borrowed-union))
  (check-false (tag-compat? borrowed-int borrowed-union))
  ;; convert に Borrowed の再構成節は無く、恒等以外は既定の拒否へ進む。
  (check-false (redex-match? UCore e
                             '(Fn ((f (NFn ((Borrowed Int 0)) Int () ())))
                                  Int () f))))

(test-case "Owned NFn の origin だけが違う対は adapter を作らない"
  (define source
    '(Fn ((p (Owned Res))) Unit (Own)
         (Let (g const (NFn ((Owned Res)) Unit (Own) ()))
              (Fn ((q (Owned Res))) Unit (Own) (Drop q))
              (Let (f const (Owned (NFn () Unit (Own) ())))
                   (Curry g (Move p))
                   (Drop f)))))
  (match-define (list core type row callables) (elaborate-ok source))
  (check-equal? (core-type-of core '() callables) (list type row))
  ;; Curry の Derived origin と注釈の User origin は Owned の型比較で消える。
  (check-false (find-adapter (erase-core core))))

(test-case "Owned NFn の signature が違う対は E-TYP-012"
  (define actual '(Owned (NFn (Int) Int () ())))
  (define targets
    (list '(Owned (NFn (Bool) Int () ()))
          '(Owned (NFn (Int) Bool () ()))
          '(Owned (NFn (Int) Int (Own) ()))
          '(Owned (NFn (Int) Int () (ValidNarrativeTrait)))))
  (for ([expected (in-list targets)])
    (check-equal?
     (diagnostic-id-of
      `(Fn ((f ,actual)) Unit (Own)
           (Let (adapted const ,expected) (Move f) unit)))
     e-type-mismatch)))

(test-case "資源仮引数を持つ内側 adapter は E-TYP-012 で拒否する"
  (define inner-actual '(NFn ((Owned Res)) (Union Int String) () ()))
  (define inner-expected '(NFn ((Owned Res)) Int () ()))
  (define actual `(NFn (,inner-actual) Int () ()))
  (define expected `(NFn (,inner-expected) Int () ()))
  (check-equal?
   (diagnostic-id-of
    `(Fn ((f ,actual)) ,expected ()
         (Let (adapted const ,expected) f adapted)))
   e-type-mismatch))

(test-case "返り値の変換が Own を作る adapter は E-EFF-002"
  (define owned-option '(Option (Owned Res)))
  (define wide-int `(Record ((o ,owned-option imm) (a Int imm))))
  (define wide-bool `(Record ((o ,owned-option imm) (a Bool imm))))
  (define actual
    `(NFn (Int) (Union ,wide-int ,wide-bool) () ()))
  (define expected
    `(NFn (Int) (Record ((o ,owned-option imm))) () ()))
  (define result
    (elab
     `(Fn ((f ,actual)) Int ()
          (Let (adapted const ,expected) f
            (Apply adapted 1)))))
  (match result
    [`(err ,diagnostic)
     (check-equal?
      (diagnostic-id diagnostic)
      (diagnostic-code-of 'elaborate 'undeclared-function-effect))]
    [other (fail-check (format "Own を持つ返り値 adapter を拒否しない: ~s"
                               other))]))

(test-case "引数か返り値に RSD を要する adapter は owned-narrowing-rejected で拒否する"
  (define wide '(Record ((owned (Owned Res) imm) (value Int imm))))
  (define narrow '(Record ((value Int imm))))
  (define cases
    (list (list `(NFn (,narrow) Int () ())
                `(NFn (,wide) Int () ()))
          (list `(NFn () ,wide () ())
                `(NFn () ,narrow () ()))))
  (for ([types (in-list cases)])
    (match-define (list actual expected) types)
    (check-equal?
     (diagnostic-id-of
      `(Fn ((f ,actual)) Int ()
           (Let (adapted const ,expected) f adapted)))
     (diagnostic-code-of 'elaborate 'owned-narrowing-rejected))))

(test-case "未選択の adapter 候補は callable と連番を消費しない"
  (define actual '(NFn (Int) Int () ()))
  (define widened '(NFn (Int) (Union Int String) () ()))
  (define tag-compatible '(NFn (Int) Int ((Yield Int)) ()))
  (define (source members)
    `(Fn ((f ,actual) (g ,actual)) ,widened ()
         (Let (selected const (Union ,(first members) ,(second members)))
              f
              (Let (next const ,widened) g next))))
  (define first-result
    (elaborate-ok (source (list tag-compatible widened))))
  (define second-result
    (elaborate-ok (source (list widened tag-compatible))))
  (for ([result (in-list (list first-result second-result))])
    (define callables (fourth result))
    (check-equal? (map first callables) '(callable0 callable1))
    (match-define (list name _actual _callable _binders body _curry)
      (find-adapter (erase-core (first result))))
    (check-true (regexp-match? #px"^union0" (symbol->string name)))
    (check-true
     (tree-contains? body
                     (lambda (node)
                       (and (symbol? node)
                            (regexp-match? #px"^boundary1"
                                           (symbol->string node))))))
    (check-false
     (tree-contains? body
                     (lambda (node)
                       (and (symbol? node)
                            (regexp-match? #px"^boundary2"
                                           (symbol->string node)))))))
  (check-equal? (erase-core (first first-result))
                (erase-core (first second-result)))
  (check-equal? (fourth first-result) (fourth second-result)))

(test-case "adapter の Handle は外側の Return を R-HandleSkip で通す"
  ;; boundary0 は外側 Lam の境界であり、f の row 注釈から参照する。
  (define actual
    '(NFn ((Union Int String)) Int ((Return boundary0 Int)) ()))
  (define expected
    '(NFn (Int) Int ((Return boundary0 Int)) ()))
  (match-define (list outer-core outer-type outer-row callables)
    (elaborate-ok
     `(Fn ((f ,actual)) Int ()
          (Let (adapted const ,expected) f (Apply adapted 1)))))
  (define entry-callable 'external-returner)
  (define entry-type
    '(NFn ((Union Int String)) Int () ((Return boundary0 Int)) () User))
  (define entry-value
    `(Lam User ,entry-callable (argument)
          (Perform (Return boundary0 Int) 42)))
  (define extended-callables
    (cons (list entry-callable entry-type) callables))
  (define program `(Apply ,(erase-core outer-core) ,entry-value))
  (check-equal? (core-type-of program '() extended-callables) '(Int ())
                (format "外側の Return programme が Core 型付けを通らない: ~s"
                        (type-of/raw program '() extended-callables)))
  (define-values (configs rules)
    (trace-g2 (inject-g2m (execution-core program extended-callables))))
  (check-config-trace configs extended-callables 'Int)
  (check-not-false (member 'R-HandleSkip rules))
  (match (last configs)
    [`(cfg 42 ,_heap ,_states ,_tokens ,_trace) (void)]
    [other (fail-check (format "外側の Return が adapter を越えない: ~s" other))]))

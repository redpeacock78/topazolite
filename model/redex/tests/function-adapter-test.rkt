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
         (only-in "../resource-type.rkt" resource-type?)
         "../search.rkt"
         "../type-equiv.rkt"
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

(define (find-adapters node)
  (match node
    [`(Let (,name let ,actual) ,bound
           (Curry (Lam User ,callable ,binders ,body) ,argument))
     #:when (equal? name argument)
     (append (list (list name actual callable binders body))
             (find-adapters bound)
             (find-adapters body))]
    [(? pair?)
     (append (find-adapters (car node)) (find-adapters (cdr node)))]
    [_ '()]))

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

(define (decompose-alias-count tree mode operation)
  (tree-count
   tree
   (lambda (node)
     (match node
       [`(Let (,name ,found-mode ,_)
              (UnionEliminate ,_scrutinee ,_branches)
              (,found-operation ,place))
        (and (eq? found-mode mode)
             (eq? found-operation operation)
             (equal? name place))]
       [_ #f]))))

(define (adapter-resource-transfer-binders body formal-binders)
  (define (walk node)
    (match node
      [`(Let (,name let ,type) ,bound ,inner)
       (append (if (and (resource-type? type)
                        (member bound formal-binders))
                   (list name)
                   '())
               (walk bound)
               (walk inner))]
      [(? pair?) (append (walk (car node)) (walk (cdr node)))]
      [_ '()]))
  (walk body))

(define (forward-count-range node binder)
  (match node
    [`(Forward ,name)
     (if (equal? name binder) (cons 1 1) (cons 0 0))]
    [`(UnionEliminate ,scrutinee ,branches)
     (define scrutinee-range (forward-count-range scrutinee binder))
     (define branch-ranges
       (map (lambda (branch) (forward-count-range branch binder)) branches))
     (if (null? branch-ranges)
         scrutinee-range
         (cons (+ (car scrutinee-range)
                  (apply min (map car branch-ranges)))
               (+ (cdr scrutinee-range)
                  (apply max (map cdr branch-ranges)))))]
    [(? pair?)
     (define ranges
       (list (forward-count-range (car node) binder)
             (forward-count-range (cdr node) binder)))
     (cons (apply + (map car ranges)) (apply + (map cdr ranges)))]
    [_ (cons 0 0)]))

(define (check-adapter-resource-forwards core expected-transfer-count)
  (define erased (erase-core core))
  (define uses
    (append*
     (for/list ([adapter (in-list (find-adapters erased))])
       (match-define (list _name _actual _callable binders body) adapter)
       (for/list ([binder (in-list
                           (adapter-resource-transfer-binders body binders))])
         (list binder body)))))
  (check-equal? (length uses) expected-transfer-count)
  (for ([use (in-list uses)])
    (match-define (list binder body) use)
    (check-equal? (forward-count-range body binder) '(1 . 1)
                  (format "仮引数 ~s の全経路で Forward は一度だけ" binder))))

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

(define (configuration-states configuration)
  (match configuration [`(cfg ,_ ,_ ,states ,_ ...) states]))

(define (state-transition-count configs rules from to [rule-filter #f])
  (for/sum ([before (in-list configs)]
            [rule (in-list rules)]
            [after (in-list (cdr configs))]
            #:when (or (not rule-filter) (eq? rule rule-filter)))
    (for/sum ([entry (in-list (configuration-states before))])
      (define following (assoc (first entry) (configuration-states after)))
      (if (and (eq? (second entry) from)
               following
               (eq? (second following) to))
          1
          0))))

(define (state-transition-place-ids configs rules from to rule-filter)
  (for/fold ([ids '()])
            ([before (in-list configs)]
             [rule (in-list rules)]
             [after (in-list (cdr configs))])
    (if (eq? rule rule-filter)
        (append
         ids
         (for/list ([entry (in-list (configuration-states before))]
                    #:when (let ([following
                                  (assoc (first entry)
                                         (configuration-states after))])
                             (and (eq? (second entry) from)
                                  following
                                  (eq? (second following) to))))
           (first entry)))
        ids)))

(define (resource-adapter-program source-parameter target-parameter argument
                                  [actual-result 'Unit]
                                  [expected-result actual-result]
                                  [actual-body '(Drop argument)])
  (define actual
    `(NFn (,target-parameter) ,actual-result (Own) ()))
  (define expected
    `(NFn (,source-parameter) ,expected-result (Own) ()))
  `(Apply
    (Fn ((f ,actual)) ,expected-result (Own)
      (Let (adapted const ,expected) f (Apply adapted ,argument)))
    (Fn ((argument ,target-parameter)) ,actual-result (Own) ,actual-body)))

(define (owned-option-value token)
  `(Construct some (Types (Owned Res)) (Apply acquire ,token)))

(define (resource-record-value label value token)
  `(Rec ((,label imm ,value) (owned imm ,(owned-option-value token)))))

(define adapter-site-owned-field '(Option (Owned Res)))
(define adapter-site-source-record
  `(Record ((a Int imm) (owned ,adapter-site-owned-field imm))))
(define adapter-site-target-record
  `(Record ((a (Union Int Bool) imm)
            (owned ,adapter-site-owned-field imm))))
(define adapter-site-actual-function
  `(NFn (,adapter-site-target-record) Unit (Own) ()))
(define adapter-site-expected-function
  `(NFn (,adapter-site-source-record) Unit (Own) ()))

(define (mut-field-conversion-source actual expected)
  `(Fn ((record ,actual)) Unit ()
       (Let (converted const ,expected) record unit)))

(define (adapter-site-worker)
  `(Fn ((argument ,adapter-site-target-record)) Unit (Own)
       (Drop argument)))

(define (adapter-site-argument token)
  (resource-record-value 'a 7 token))

(define (make-union-value member value union-type)
  `(Apply (Fn ((argument ,member)) ,union-type (Own) (Move argument)) ,value))

(define (check-resource-adapter-run source expected-forward-count
                                    [expected-transfer-count 1]
                                    [expected-final #f])
  (match-define (list core type row callables)
    (elaborate-ok source))
  (check-equal? (core-type-of core '() callables) (list type row))
  (define adapter (find-adapter (erase-core core)))
  (check-not-false adapter)
  (match-define (list _name _actual _callable _binders body _curry) adapter)
  (check-adapter-resource-forwards core expected-transfer-count)
  (check-true (tree-contains? body
                              (lambda (node)
                                (match node [`(Forward ,_) #t] [_ #f]))))
  (check-false (tree-contains? body
                               (lambda (node)
                                 (match node [`(Move ,_) #t] [_ #f]))))
  (define execution (execution-core core callables))
  (define-values (status target) (lower (erase-core execution) 'racket-cs))
  (check-eq? status 'ok)
  (check-eq? (compare-observations execution target 1) 'match)
  (define-values (configs rules)
    (trace-g2 `(cfg (Scope () ,execution) () () () ())))
  (check-config-trace configs callables type)
  (check-equal? (count (lambda (rule) (eq? rule 'R-Forward)) rules)
                expected-forward-count)
  (check-equal? (state-transition-count configs rules 'Available 'Moved
                                        'R-Forward)
                expected-forward-count)
  (define forwarded-place-ids
    (state-transition-place-ids configs rules 'Available 'Moved 'R-Forward))
  (check-equal? (length forwarded-place-ids) expected-forward-count)
  (check-equal? (length forwarded-place-ids)
                (length (remove-duplicates forwarded-place-ids)))
  (for ([rule (in-list rules)]
        [before (in-list configs)]
        [after (in-list (cdr configs))]
        #:when (eq? rule 'R-ScopeValue))
    (check-equal? (state-transition-count (list before after) (list rule)
                                          'Available 'Dropped)
                  0))
  (when expected-final
    (match (last configs)
      [`(cfg ,value ,_heap ,_states ,_tokens ,_trace)
       (check-equal? value expected-final)]
      [other (fail-check (format "最終 config の形が不正: ~s" other))]))
  (void))

(define (check-owned-return-adapter-run field-type token member-tag)
  (define wide-int
    (normalize-type `(Record ((a Int imm) (o ,field-type imm)))))
  (define wide-bool
    (normalize-type `(Record ((a Bool imm) (o ,field-type imm)))))
  (define actual-return (normalize-type `(Union ,wide-int ,wide-bool)))
  (define expected-return `(Record ((o ,field-type imm))))
  (define actual `(NFn (Unit) ,actual-return () ()))
  (define expected `(NFn (Unit) ,expected-return () ()))
  (define source
    `(Fn ((f ,actual)) Unit ()
         (Let (adapted const ,expected) f unit)))
  (match-define (list core _type _row callables) (elaborate-ok source))
  (define adapter (find-adapter (erase-core core)))
  (check-not-false adapter)
  (match-define (list _name _actual callable binders body _curry) adapter)
  (define adapter-lambda `(Lam User ,callable ,binders ,body))
  (define adapter-type (second (assoc callable callables)))
  (check-equal?
   (core-type-of adapter-lambda '() callables)
   (list adapter-type '()))
  (check-true (tree-contains? body (lambda (node)
                                     (match node [`(Forward ,_) #t] [_ #f]))))
  (check-false (tree-contains? body (lambda (node)
                                      (match node [`(Move ,_) #t] [_ #f]))))
  (define worker-callable (string->symbol (format "return-worker-~a" token)))
  (define union-member (if (eq? member-tag 'int) wide-int wide-bool))
  (define discriminator (if (eq? member-tag 'int) 1 '(Construct Bool true)))
  (define worker-type `(NFn (Unit) ,actual-return () () () User))
  (define worker
    `(Lam User ,worker-callable (ignored)
       (Handle (Return return-boundary ,actual-return)
               (answer -> answer)
         (Scope ()
           (UnionInject ,actual-return ,union-member
             (Rec ((a imm ,discriminator)
                   (o imm
                      (Construct ,field-type some
                                 (OwnLeaf (resource ,token)))))))))))
  (define extended-callables
    (cons (list worker-callable worker-type) callables))
  (check-equal? (core-type-of worker '() extended-callables)
                (list worker-type '()))
  (define adapter-value `(Curry (Lam User ,callable ,binders ,body) ,worker))
  (define application `(Apply ,adapter-value unit))
  (check-equal? (core-type-of application '() extended-callables)
                (list expected-return '()))
  (define program `(Drop ,application))
  (check-equal? (core-type-of program '() extended-callables)
                (list 'Unit '(Own)))
  (define execution (execution-core program extended-callables))
  (define-values (status target) (lower (erase-core execution) 'racket-cs))
  (check-eq? status 'ok)
  (check-eq? (compare-observations execution target 1) 'match)
  (define-values (configs rules)
    (trace-g2 `(cfg (Scope () ,execution) () () () ())))
  (check-config-trace configs extended-callables 'Unit)
  (check-equal? (count (lambda (rule) (eq? rule 'R-Forward)) rules) 3)
  (define forwarded-place-ids
    (state-transition-place-ids configs rules 'Available 'Moved 'R-Forward))
  (check-equal? (length forwarded-place-ids) 3)
  (check-equal? (length (remove-duplicates forwarded-place-ids)) 3)
  (match (last configs)
    [`(cfg ,_ ,_ ,_ ,tokens ,_)
     (check-equal? (map second tokens) '(Dropped))
     (check-equal? (length tokens) 1)]
    [other (fail-check (format "最終 config の形が不正: ~s" other))])
  (for ([rule (in-list rules)]
        [before (in-list configs)]
        [after (in-list (cdr configs))]
        #:when (eq? rule 'R-ScopeValue))
      (check-equal? (state-transition-count (list before after) (list rule)
                                            'Available 'Dropped)
                    0)))

(define (check-owned-return-adapter-static field-type)
  (define wide-int
    (normalize-type `(Record ((a Int imm) (o ,field-type imm)))))
  (define wide-bool
    (normalize-type `(Record ((a Bool imm) (o ,field-type imm)))))
  (define actual-return (normalize-type `(Union ,wide-int ,wide-bool)))
  (define expected-return `(Record ((o ,field-type imm))))
  (define actual `(NFn (,actual-return) ,actual-return () ()))
  (define expected `(NFn (,actual-return) ,expected-return () ()))
  (define source
    `(Fn ((f ,actual) (value ,actual-return)) ,expected-return (Own)
         (Let (adapted const ,expected) f
           (Apply adapted (Move value)))))
  (match-define (list core type row callables) (elaborate-ok source))
  (check-equal? (core-type-of core '() callables) (list type row))
  (define adapter (find-adapter (erase-core core)))
  (check-not-false adapter)
  (match-define (list _name _actual callable binders body _curry) adapter)
  (check-equal?
   (core-type-of `(Lam User ,callable ,binders ,body) '() callables)
   (list (second (assoc callable callables)) '()))
  (check-false (tree-contains? body
                               (lambda (node)
                                 (match node [`(Move ,_) #t] [_ #f]))))
  (check-true (tree-contains? body
                              (lambda (node)
                                (match node [`(Forward ,_) #t] [_ #f])))))

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

(test-case "Owned の関数引数を変換する内側 adapter も Forward で実行する"
  (define inner-actual '(NFn ((Owned Res)) (Union Int String) (Own) ()))
  (define inner-expected '(NFn ((Owned Res)) Int (Own) ()))
  (define actual `(NFn (,inner-actual) (Union Int String) (Own) ()))
  (define expected `(NFn (,inner-expected) (Union Int String) (Own) ()))
  (define source
    `(Apply
      (Fn ((f ,actual)) (Union Int String) (Own)
        (Let (adapted const ,expected) f
          (Apply adapted
                 (Fn ((argument (Owned Res))) Int (Own)
                   (Let (dropped let Unit) (Drop argument) 9)))))
      (Fn ((inner ,inner-actual)) (Union Int String) (Own)
        (Apply inner (Apply acquire 901)))))
  (check-resource-adapter-run source 1))

(test-case "Owned 引数と返り値の変換を持つ adapter は binder を Forward する"
  (check-resource-adapter-run
   (resource-adapter-program
    '(Owned Res) '(Owned Res) '(Apply acquire 902)
    'Int '(Union Int String)
    '(Let (dropped let Unit) (Drop argument) 7))
   1 1 '(UnionVal (Union Int String) Int 7)))

(test-case "Apply の引数 check-many は資源型関数を adapter に変換する"
  (check-resource-adapter-run
   `(Apply
     (Fn ((callback ,adapter-site-expected-function)) Unit (Own)
       (Apply callback ,(adapter-site-argument 952)))
     ,(adapter-site-worker))
   1 1 'unit))

(test-case "Construct の欄 check-many は資源型関数を adapter に変換する"
  (check-resource-adapter-run
   `(Apply
     (Fn () Unit (Own)
       (Eliminate
        (Construct some (Types ,adapter-site-expected-function)
                   ,(adapter-site-worker))
        ((some (callback) ->
         (Apply callback ,(adapter-site-argument 953)))
         (none () -> unit)))))
   1 1 'unit))

(test-case "rebuild-record は imm 欄の資源型関数を adapter に変換する"
  (define actual-record
    `(Record ((callback ,adapter-site-actual-function imm) (marker Int imm))))
  (define expected-record
    `(Record ((callback ,adapter-site-expected-function imm)
              (marker (Union Int Bool) imm))))
  (check-resource-adapter-run
   `(Apply
     (Fn ((callbacks ,actual-record)) Unit (Own)
       (Let (adapted const ,expected-record) callbacks
         (Apply (Proj adapted callback) ,(adapter-site-argument 954))))
     (Rec ((callback imm ,(adapter-site-worker)) (marker imm 1))))
   1 1 'unit))

(test-case "check-rec-against-union は Rec の imm 欄に adapter を作る"
  ;; Union payload は Surface Eliminate で開けないため、ここでは閉包と Union 値を実行する。
  (define actual-record
    `(Record ((callback ,adapter-site-actual-function imm) (marker Int imm))))
  (define expected-record
    `(Record ((callback ,adapter-site-expected-function imm)
              (marker (Union Int Bool) imm))))
  (define expected-union `(Union ,expected-record Bool))
  (define source
    `(Apply
      (Fn ((callbacks ,actual-record)) Unit ()
        (Let (wrapped const ,expected-union)
             (Rec ((callback imm (Proj callbacks callback)) (marker imm 1)))
          unit))
      (Rec ((callback imm ,(adapter-site-worker)) (marker imm 1)))))
  (match-define (list core type row callables) (elaborate-ok source))
  (check-equal? (core-type-of core '() callables) (list type row))
  (check-adapter-resource-forwards core 1)
  (check-not-false (find-adapter (erase-core core)))
  (define execution (execution-core core callables))
  (define-values (status target) (lower (erase-core execution) 'racket-cs))
  (check-eq? status 'ok)
  (check-eq? (compare-observations execution target 1) 'match)
  (define-values (configs _rules)
    (trace-g2 `(cfg (Scope () ,execution) () () () ())))
  (check-config-trace configs callables type)
  (match (last configs)
    [`(cfg unit ,_heap ,_states ,_tokens ,_trace) (void)]
    [other (fail-check (format "Union の Rec 構築結果が不正: ~s" other))]))

(test-case "関数の結果 check は資源型関数を adapter に変換する"
  (check-resource-adapter-run
   `(Apply
     (Apply (Fn ((callback ,adapter-site-actual-function))
                ,adapter-site-expected-function () callback)
            ,(adapter-site-worker))
     ,(adapter-site-argument 955))
   1 1 'unit))

(test-case "check-eliminate の枝は資源型関数を adapter に変換する"
  (check-resource-adapter-run
   `(Apply
     (Apply
      (Fn ((tag (Option Int)))
          ,adapter-site-expected-function ()
        (Eliminate tag
          ((some (ignored) -> ,(adapter-site-worker))
           (none () -> ,(adapter-site-worker)))))
      (Construct some (Types Int) 1))
     ,(adapter-site-argument 956))
   1 2 'unit))

(test-case "Return の payload check は資源型関数を adapter に変換する"
  (check-resource-adapter-run
   `(Apply
     (Apply
      (Fn ((callback ,adapter-site-actual-function))
          ,adapter-site-expected-function ()
        (Return callback))
      ,(adapter-site-worker))
     ,(adapter-site-argument 957))
   1 1 'unit))

(test-case "mut 欄の関数型は adapter を作らず E-TYP-012 で拒否する"
  (define actual
    `(Record ((callback ,adapter-site-actual-function mut))))
  (define expected
    `(Record ((callback ,adapter-site-expected-function mut))))
  (check-false (compat? (normalize-type actual) (normalize-type expected)))
  (check-equal?
   (diagnostic-id-of
    `(Fn ((record ,actual)) Unit ()
         (Let (converted const ,expected) record unit)))
   e-type-mismatch))

(test-case "mut 欄内の関数 adapter は Union injection 経由でも拒否する"
  (define actual
    `(Record ((callback ,adapter-site-actual-function mut))))
  (define expected
    `(Record ((callback (Union ,adapter-site-expected-function Int) mut))))
  (check-false (compat? (normalize-type actual) (normalize-type expected)))
  (check-equal?
   (diagnostic-id-of (mut-field-conversion-source actual expected))
   e-type-mismatch))

(test-case "mut 欄内の関数 adapter は Union decompose 経由でも拒否する"
  (define actual
    `(Record ((callback (Union ,adapter-site-actual-function Int) mut))))
  (define expected
    `(Record ((callback (Union ,adapter-site-expected-function Int) mut))))
  (check-false (compat? (normalize-type actual) (normalize-type expected)))
  (check-equal?
   (diagnostic-id-of (mut-field-conversion-source actual expected))
   e-type-mismatch))

(test-case "mut 欄の内側 Record にある関数 adapter も拒否する"
  (define actual-function-record
    `(Record ((callback ,adapter-site-actual-function imm))))
  (define expected-function-record
    `(Record ((callback ,adapter-site-expected-function imm))))
  (define actual `(Record ((nested ,actual-function-record mut))))
  (define expected `(Record ((nested ,expected-function-record mut))))
  (check-false (compat? (normalize-type actual) (normalize-type expected)))
  (check-equal?
   (diagnostic-id-of (mut-field-conversion-source actual expected))
   e-type-mismatch))

(test-case "型同値な mut 欄の関数型はそのまま受理する"
  (define actual
    `(Record ((callback ,adapter-site-actual-function mut))))
  (check-true (compat? (normalize-type actual) (normalize-type actual)))
  (match-define (list core type row callables)
    (elaborate-ok (mut-field-conversion-source actual actual)))
  (check-false (find-adapter (erase-core core)))
  (check-equal? (core-type-of core '() callables) (list type row)))

(test-case "synth Eliminate は異なる NFn を明示の Union に残す"
  (define source
    '(Eliminate (Construct some (Types Bool) (Construct true (Types)))
       ((some (ignored) -> (Fn ((number Int)) Int () 7))
        (none () -> (Fn ((truth Bool)) Bool () (Construct false (Types)))))))
  (match-define (list core type row callables) (elaborate-ok source))
  (match type
    [`(Union ,_ ,_) (void)]
    [other (fail-check (format "NFn の synth 合流が Union でない: ~s" other))])
  (define members (union-members type))
  (check-equal? (length members) 2)
  (check-true
   (ormap (lambda (member)
            (type-equiv? member '(NFn (Int) Int () () () User)))
          members))
  (check-true
   (ormap (lambda (member)
            (type-equiv? member '(NFn (Bool) Bool () () () User)))
          members))
  (check-false (find-adapter (erase-core core)))
  (check-equal? (core-type-of core '() callables) (list type row)))

(test-case "judgment-type と Core 型が異なる checked Curry の adapter も型付けされる"
  (define actual-g
    `(NFn (Int ,adapter-site-target-record) Unit (Own) ()))
  (define actual-g-core
    (normalize-type
     `(NFn (Int ,adapter-site-target-record) Unit (Own) () () User)))
  (define checked-function adapter-site-expected-function)
  (define checked-function-core
    (normalize-type
     `(NFn (,adapter-site-source-record) Unit (Own) () () User)))
  (define-values (curry-type _curry-row)
    (apply values
           (core-type-of '(Curry g 0) '() '()
                         (list (list 'g actual-g-core)))))
  ;; Curry の Core 型は Union 欄を受け、注釈の judgment-type は Int 欄を受ける。
  (check-false (type-equiv? curry-type checked-function-core))
  (check-true (compat? curry-type checked-function-core))
  (check-resource-adapter-run
   `(Apply
     (Fn ((g ,actual-g)) Unit (Own)
       (Let (checked const ,checked-function) (Curry g 0)
         (Apply checked ,(adapter-site-argument 958))))
     (Fn ((seed Int) (argument ,adapter-site-target-record)) Unit (Own)
       (Drop argument)))
   1 1 'unit))

(test-case "Record から Record への資源引数変換は Forward する"
  (define option-owned '(Option (Owned Res)))
  (define source-type
    `(Record ((a Int imm) (owned ,option-owned imm))))
  (define target-type
    `(Record ((a (Union Int Bool) imm) (owned ,option-owned imm))))
  (check-resource-adapter-run
   (resource-adapter-program
    source-type target-type
    (resource-record-value 'a 7 903))
   1))

(test-case "Union から Record への資源引数変換は alias と一時 place を Forward する"
  (define option-owned '(Option (Owned Res)))
  (define member-int
    `(Record ((a Int imm) (owned ,option-owned imm))))
  (define member-bool
    `(Record ((a Bool imm) (owned ,option-owned imm))))
  (define source-type `(Union ,member-int ,member-bool))
  (define target-type
    `(Record ((a (Union Int Bool) imm) (owned ,option-owned imm))))
  (for ([member (in-list (list member-int member-bool))]
        [value (in-list (list 11 '(Construct true (Types))))]
        [token (in-list '(904 905))])
    (check-resource-adapter-run
     (resource-adapter-program
      source-type target-type
      (make-union-value
       member (resource-record-value 'a value token) source-type))
     3)))

(test-case "Record から Union への資源引数変換は RecRewrite 内で Forward する"
  (define option-owned '(Option (Owned Res)))
  (define source-type
    `(Record ((a Int imm) (owned ,option-owned imm))))
  (define member
    `(Record ((a (Union Int Bool) imm) (owned ,option-owned imm))))
  (define target-type `(Union ,member String))
  (check-resource-adapter-run
   (resource-adapter-program
    source-type target-type
    (resource-record-value 'a 12 906))
   1))

(test-case "Union 資源引数の非 Record 分岐は転送 mode だけ let を使う"
  (define option-owned '(Option (Owned Res)))
  (define source-member
    `(Record ((a Int imm) (owned ,option-owned imm))))
  (define target-member
    `(Record ((a (Union Int Bool) imm) (owned ,option-owned imm))))
  (define source-type `(Union ,source-member String))
  (define target-type `(Union ,target-member String))
  (define record-source
    (resource-adapter-program
     source-type target-type
     (make-union-value source-member
                       (resource-record-value 'a 907 907)
                       source-type)))
  (define record-core (first (elaborate-ok record-source)))
  (check-resource-adapter-run record-source 3)
  (define record-adapter (find-adapter (erase-core record-core)))
  (check-equal? (decompose-alias-count (fifth record-adapter) 'let 'Forward) 1)
  (define string-source
    (resource-adapter-program
     source-type target-type
     `(Apply (Fn ((argument String)) ,source-type (Own) argument) "other")))
  (check-resource-adapter-run string-source 2)
  (define default-source
    `(Apply
      (Fn ((argument ,source-type)) ,target-type (Own) (Move argument))
      ,(make-union-value source-member
                         (resource-record-value 'a 908 908)
                         source-type)))
  (match-define (list default-core default-type default-row default-callables)
    (elaborate-ok default-source))
  (check-equal? (core-type-of default-core '() default-callables)
                (list default-type default-row))
  (check-equal? (decompose-alias-count (erase-core default-core)
                                       'const 'Move)
                1))

(test-case "c3a2: Owned 欄の返り値変換は空 row の Forward で受理する"
  ;; 通常の Rec は Owned 欄を生成できないため、この形は静的に検査する。
  (check-owned-return-adapter-static '(Owned Res)))

(test-case "c3a2: Option Record Owned 欄の返り値変換は空 row の Forward で受理する"
  (for ([tag '(int bool)] [token '(420 421)])
    (check-owned-return-adapter-run
     '(Option (Owned Res)) token tag)))

(test-case "通常の Rec は Forward を Owned 欄へ直接置けない"
  ;; Rec の root Owned 欄は owned-record-field で拒否されるため、実行可能な fixture は作れない。
  (define tag-union (normalize-type '(Union Int Bool)))
  (define resource '(Owned Res))
  (define wide-int (normalize-type `(Record ((a Int imm) (o ,resource imm)))))
  (define wide-bool (normalize-type `(Record ((a Bool imm) (o ,resource imm)))))
  (define actual-return (normalize-type `(Union ,wide-int ,wide-bool)))
  (define worker-callable 'owned-return-union-worker)
  (define worker-type
    `(NFn (,resource ,tag-union) ,actual-return () () () User))
  (define worker-branches
    (for/list ([member (in-list (union-members tag-union))])
      (match member
        ['Bool
         `(Bool boolean ->
           (UnionInject ,actual-return ,wide-bool
             (Rec ((a imm boolean) (o imm (Forward transferred))))))]
        ['Int
         `(Int integer ->
           (UnionInject ,actual-return ,wide-int
             (Rec ((a imm integer) (o imm (Forward transferred))))))])))
  (define worker
    `(Lam User ,worker-callable (owned-argument tag)
       (Handle (Return owned-return-boundary ,actual-return)
               (answer -> answer)
         (Scope ()
           (Let (transferred let ,resource) owned-argument
             (UnionEliminate tag ,worker-branches))))))
  (define worker-callables (list (list worker-callable worker-type)))
  (check-equal? (diagnostic-id
                 (core-type-of/diagnostic worker '() worker-callables))
                "E-OWN-016"))

(test-case "c3a2: 非 Record 分岐の返り値変換で E_tail の binder を Forward する"
  ;; 二つの資源 Record の Union を Union(Record, Int) へ分解し、両 tag を実行する。
  (define tag-union (normalize-type '(Union Int Bool)))
  (define option-owned '(Option (Owned Res)))
  (define wide-int
    (normalize-type `(Record ((a Int imm) (o ,option-owned imm)))))
  (define wide-bool
    (normalize-type `(Record ((a Bool imm) (o ,option-owned imm)))))
  (define actual-return (normalize-type `(Union ,wide-int ,wide-bool)))
  (define narrow-record (normalize-type `(Record ((o ,option-owned imm)))))
  (define expected-return (normalize-type `(Union ,narrow-record Int)))
  (define actual `(NFn (,tag-union) ,actual-return (Own) ()))
  (define expected `(NFn (,tag-union) ,expected-return (Own) ()))
  (define source
    `(Fn ((f ,actual) (tag ,tag-union)) Unit (Own)
         (Let (adapted const ,expected) f
           (Drop (Apply adapted tag)))))
  (match-define (list core type row callables) (elaborate-ok source))
  (check-equal? (core-type-of core '() callables) (list type row))
  (define adapter (find-adapter (erase-core core)))
  (check-not-false adapter)
  (match-define (list _name _actual _callable _binders body _curry) adapter)
  (check-equal? (decompose-alias-count body 'let 'Forward) 1)
  (check-false (tree-contains? body
                               (lambda (node)
                                 (match node [`(Move ,_) #t] [_ #f]))))
  (define worker-callable 'owned-return-union-worker)
  (define worker-type `(NFn (,tag-union) ,actual-return (Own) () () User))
  (define worker-branches
    `((Int integer ->
       (UnionInject ,actual-return ,wide-int
         (Rec ((a imm integer)
               (o imm (Construct ,option-owned some (OwnLeaf (resource 950))))))))
      (Bool boolean ->
       (UnionInject ,actual-return ,wide-bool
         (Rec ((a imm boolean)
               (o imm (Construct ,option-owned some (OwnLeaf (resource 951))))))))))
  (define worker
    `(Lam User ,worker-callable (tag)
       (Handle (Return owned-return-boundary ,actual-return)
               (answer -> answer)
         (Scope () (UnionEliminate tag ,worker-branches)))))
  (define worker-callables (cons (list worker-callable worker-type) callables))
  (check-equal? (core-type-of worker '() worker-callables)
                (list worker-type '()))
  (for ([tag '(Int Bool)] [tag-value (list 17 '(Construct Bool true))])
    (define tag-argument `(UnionInject ,tag-union ,tag ,tag-value))
    (define application `(Apply ,core ,worker ,tag-argument))
    (check-equal? (core-type-of application '() worker-callables)
                  (list 'Unit '(Own)))
    (define execution (execution-core application worker-callables))
    (define-values (status target) (lower (erase-core execution) 'racket-cs))
    (check-eq? status 'ok)
    (check-eq? (compare-observations execution target 1) 'match)
    (define-values (configs rules)
      (trace-g2 `(cfg (Scope () ,execution) () () () ())))
    (check-config-trace configs worker-callables 'Unit)
    (check-equal? (count (lambda (rule) (eq? rule 'R-Forward)) rules) 3)
    (define forwarded-place-ids
      (state-transition-place-ids configs rules 'Available 'Moved 'R-Forward))
    (check-equal? (length forwarded-place-ids) 3)
    (check-equal? (length forwarded-place-ids)
                  (length (remove-duplicates forwarded-place-ids)))
    (for ([before (in-list configs)] [rule (in-list rules)]
          [after (in-list (cdr configs))] #:when (eq? rule 'R-ScopeValue))
      (check-equal? (state-transition-count (list before after) (list rule)
                                            'Available 'Dropped)
                    0))
    (match (last configs)
      [`(cfg ,_ ,_ ,_ ,tokens ,_)
       (check-equal? (map second tokens) '(Dropped))
       (check-equal? (length tokens) 1)]
      [other (fail-check (format "最後の token を検査できない: ~s" other))])))

(test-case "c3a2: 資源引数と返り値の変換をともに Forward で実行する"
  (for ([tag '(int bool)] [token '(430 431)])
    (define owned '(Option (Owned Res)))
    (define wide-int
      (normalize-type `(Record ((a Int imm) (o ,owned imm)))))
    (define wide-bool
      (normalize-type `(Record ((a Bool imm) (o ,owned imm)))))
    (define actual-return (normalize-type `(Union ,wide-int ,wide-bool)))
    (define expected-return `(Record ((o ,owned imm))))
    (define tag-union (normalize-type '(Union Int Bool)))
    (define source-tag (if (eq? tag 'int) 'Int 'Bool))
    (define source-argument
      (if (eq? tag 'int)
          1
          '(Construct true (Types))))
    (define actual
      `(NFn ((Owned Res) ,tag-union) ,actual-return (Own) ()))
    (define expected
      `(NFn ((Owned Res) ,source-tag) ,expected-return (Own) ()))
    (define source
      `(Fn ((f ,actual)) Unit (Own)
           (Let (adapted const ,expected) f
             (Drop (Apply adapted (Apply acquire ,token) ,source-argument)))))
    (match-define (list core _type _row callables) (elaborate-ok source))
    (check-adapter-resource-forwards core 1)
    (define adapter (find-adapter (erase-core core)))
    (check-not-false adapter)
    (match-define (list _name _actual callable binders body _curry) adapter)
    (check-equal? (core-type-of `(Lam User ,callable ,binders ,body)
                                '() callables)
                  (list (second (assoc callable callables)) '()))
    (check-false (tree-contains? body
                                 (lambda (node)
                                   (match node [`(Move ,_) #t] [_ #f]))))
    (define worker-type
      `(NFn ((Owned Res) ,tag-union) ,actual-return () (Own) () User))
    (define worker
      `(Lam User ,(string->symbol (format "return-worker-~a" token))
            (owned-argument tag-value)
         (Handle (Return return-boundary ,actual-return)
                 (answer -> answer)
           (Scope ()
             (Let (forwarded let (Owned Res)) owned-argument
               (Let (discarded let Unit) (Drop (Move forwarded))
                 (UnionEliminate tag-value
                   ((Bool boolean ->
                      (UnionInject ,actual-return ,wide-bool
                        (Rec ((a imm boolean)
                              (o imm
                                 (Construct ,owned some
                                   (OwnLeaf (resource ,(+ token 1000)))))))))
                    (Int integer ->
                      (UnionInject ,actual-return ,wide-int
                        (Rec ((a imm integer)
                              (o imm
                                 (Construct ,owned some
                                   (OwnLeaf (resource ,(+ token 1000)))))))))))))))))
    (define worker-callables
      (cons (list (string->symbol (format "return-worker-~a" token))
                  worker-type)
            callables))
    (define worker-type-check
      (core-type-of/diagnostic worker '() worker-callables))
    (check-equal? worker-type-check (list worker-type '())
                  (format "worker の型検査に失敗: ~s" worker-type-check))
    (define application `(Apply ,core ,worker))
    (check-equal? (core-type-of application '() worker-callables)
                  (list 'Unit '(Own)))
    (define execution (execution-core application worker-callables))
    (define-values (status target) (lower (erase-core execution) 'racket-cs))
    (check-eq? status 'ok)
    (check-eq? (compare-observations execution target 1) 'match)
    (define-values (configs rules)
      (trace-g2 `(cfg (Scope () ,execution) () () () ())))
    (check-config-trace configs worker-callables 'Unit)
    (check-equal? (count (lambda (rule) (eq? rule 'R-Forward)) rules) 4)
    (define forwarded-place-ids
      (state-transition-place-ids configs rules 'Available 'Moved 'R-Forward))
    (check-equal? (length forwarded-place-ids) 4)
    (check-equal? (length (remove-duplicates forwarded-place-ids)) 4)
    (check-equal? (count (lambda (rule) (eq? rule 'R-OwnLeaf)) rules) 1)
    (check-equal? (count (lambda (rule) (eq? rule 'R-Drop)) rules) 2)
    (match (last configs)
      [`(cfg ,_ ,_ ,_ ,tokens ,_)
       ;; acquire の値は raw resource なので、追跡 token は返り値の OwnLeaf 分だけ作られる。
       (check-equal? (map second tokens) '(Dropped))
       (check-equal? (length tokens) 1)]
      [other (fail-check (format "出力資源の token が残る: ~s" other))])
    (for ([rule (in-list rules)]
          [before (in-list configs)]
          [after (in-list (cdr configs))]
          #:when (eq? rule 'R-ScopeValue))
      (check-equal? (state-transition-count (list before after) (list rule)
                                            'Available 'Dropped)
                    0))))

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

(test-case "資源引数の NFn 欄にある Union 損失は c3b まで E-OWN-029 で拒否する"
  ;; c3b で、資源引数内の NFn の返り値にある Union の Owned 損失を RSD で回収する。
  (define option-owned '(Option (Owned Res)))
  (define wide '(Record ((x (Owned Res) imm) (y Int imm))))
  (define narrow '(Record ((y Int imm))))
  (define source-function `(NFn (Unit) (Union ,wide Bool) (Own) ()))
  (define target-function `(NFn (Unit) (Union ,narrow Bool) (Own) ()))
  (define source-parameter
    `(Record ((value ,source-function imm) (owned ,option-owned imm))))
  (define target-parameter
    `(Record ((value ,target-function imm) (owned ,option-owned imm))))
  (define actual `(NFn (,target-parameter) Unit (Own) ()))
  (define expected `(NFn (,source-parameter) Unit (Own) ()))
  (check-equal?
   (diagnostic-id-of
    `(Fn ((f ,actual)) Unit ()
         (Let (adapted const ,expected) f unit)))
   (diagnostic-code-of 'elaborate 'owned-narrowing-rejected)))

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

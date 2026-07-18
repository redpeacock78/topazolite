#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "lang.rkt"
         "origins.rkt")

(provide UCore
         elab
         classify-stub)

;; S-expression encoding of the untyped reduced Core from specification §3.1.
;; Explicit constructor type arguments use (Types ...), and applied type specs
;; use (Spec head argument ...).
(define-extended-language UCore G1
  (T ::= variable-not-otherwise-mentioned)
  (A ::= Int Bool Unit String Never Res List Option Result T)
  (uτ ::= Int Bool Unit String Never Res
          T
          (List uτ)
          (Option uτ)
          (Result uτ uτ)
          (Owned uτ)
          (NFn (uτ ...) uτ tε Q)
          (TypeInfo κ)
          (Proof φ))
  (tℓ ::= (Return b uτ) (Yield uτ) Suspend Partial Compile Own)
  (tε ::= (tℓ ...))
  (uℓ ::= Return (Yield uτ) Suspend Partial Compile Own)
  (uε ::= (uℓ ...))
  (spec ::= A (Spec spec spec ...))
  (ubr ::= (K (x ...) -> e))
  (e ::= l
         x
         (Fn ((x uτ) ...) uτ uε e)
         (Apply e e ...)
         (Let x e e)
         (Construct K e ...)
         (Construct K (Types uτ ...) e ...)
         (Eliminate e (ubr ...))
         (Return e)
         (NarrativeExpr e)
         (Recur f ((x uτ) ...) uτ uε e e)
         (Yield e e)
         (Suspend e)
         (Move x)
         (Drop e)
         (Curry e e)
         (TypeMake spec)
         (LetType T (TypeMake spec) e)))

(struct judgment (core type row) #:transparent)
(struct exn:fail:elab exn:fail (reason) #:transparent)

(define (reject reason . details)
  (raise
   (exn:fail:elab
    (format "elaboration failed: ~a" reason)
    (current-continuation-marks)
    (if (null? details) reason (cons reason details)))))

(define (lookup table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

(define (extend environment names types)
  (append (map list names types) environment))

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

(define (type? value)
  (redex-match? G1 τ value))

(define (row-union left right)
  (term (row-∪ ,left ,right)))

(define (rows-union rows)
  (for/fold ([combined '()])
            ([row (in-list rows)])
    (row-union combined row)))

(define (row-difference row removed)
  (term (row-\\ ,row ,removed)))

(define (row-subset? left right)
  (term (row-⊆ ,left ,right)))

(define (row-member? label row)
  (term (row-∈ ,label ,row)))

(define (normalize-row row)
  (for/fold ([normalized '()])
            ([label (in-list row)])
    (row-union normalized (list label))))

(define (type-compatible? actual expected)
  ;; Task 11 replaces structural equality with type-equiv?.
  (or (equal? actual expected)
      (eq? actual 'Never)))

(define (resolve-annotation annotation delta)
  (define resolved
    (match annotation
      [`(List ,element)
       `(List ,(resolve-annotation element delta))]
      [`(Option ,element)
       `(Option ,(resolve-annotation element delta))]
      [`(Result ,ok-type ,error-type)
       `(Result ,(resolve-annotation ok-type delta)
                ,(resolve-annotation error-type delta))]
      [`(Owned ,inner)
       `(Owned ,(resolve-annotation inner delta))]
      [`(NFn (,parameters ...) ,return-type ,row ,obligations)
       `(NFn ,(for/list ([parameter (in-list parameters)])
                (resolve-annotation parameter delta))
             ,(resolve-annotation return-type delta)
             ,(resolve-type-row row delta)
             ,obligations)]
      [`(TypeInfo ,kind) `(TypeInfo ,kind)]
      [`(Proof ,proposition) `(Proof ,proposition)]
      [(? symbol? name)
       (match (lookup delta name)
         [`(TypeRep ,_ ,type-form Type)
          (if (type? type-form)
              type-form
              (reject 'invalid-type-representation name))]
         [`(TypeRep ,_ ,_ ,kind)
          (reject 'unsaturated-type name kind)]
         [_ (reject 'unknown-type name)])]
      [_ (reject 'invalid-type-annotation annotation)]))
  (if (type? resolved)
      resolved
      (reject 'invalid-resolved-type resolved)))

(define (resolve-type-row row delta)
  (normalize-row
   (for/list ([label (in-list row)])
     (match label
       [`(Return ,boundary ,type)
        `(Return ,boundary ,(resolve-annotation type delta))]
       [`(Yield ,type)
        `(Yield ,(resolve-annotation type delta))]
       [(or 'Suspend 'Partial 'Compile 'Own) label]
       [_ (reject 'invalid-effect-label label)]))))

(define (nearest-boundary boundaries)
  (and (pair? boundaries) (car boundaries)))

(define (resolve-declaration-row row delta boundaries)
  (normalize-row
   (for/list ([label (in-list row)])
     (match label
       ['Return
        (match (nearest-boundary boundaries)
          [`(,_ ,boundary ,type) `(Return ,boundary ,type)]
          [_ (reject 'return-label-outside-boundary)])]
       [`(Yield ,type)
        `(Yield ,(resolve-annotation type delta))]
       [(or 'Suspend 'Partial 'Compile 'Own) label]
       [_ (reject 'invalid-effect-label label)]))))

(define (kind-arity kind)
  (match kind
    ['Type 0]
    [`(Type -> ,rest) (add1 (kind-arity rest))]
    [_ (reject 'invalid-kind kind)]))

(define (apply-type-constructor type-form arguments)
  (match* (type-form arguments)
    [('List (list element)) `(List ,element)]
    [('Option (list element)) `(Option ,element)]
    [('Result (list ok-type error-type)) `(Result ,ok-type ,error-type)]
    [(_ _) (reject 'invalid-type-application type-form arguments)]))

(define (interpret-spec spec delta)
  (match spec
    [(? symbol? name)
     (match (lookup delta name)
       [`(TypeRep ,_ ,type-form ,kind) (list type-form kind)]
       [_ (reject 'unknown-type-spec name)])]
    [`(Spec ,head ,arguments ...)
     (match-define (list head-form head-kind)
       (interpret-spec head delta))
     (define arity (kind-arity head-kind))
     (unless (and (positive? arity)
                  (= arity (length arguments)))
       (reject 'kind-mismatch spec head-kind))
     (define interpreted
       (for/list ([argument (in-list arguments)])
         (interpret-spec argument delta)))
     (unless (andmap (lambda (result)
                       (and (equal? (second result) 'Type)
                            (type? (first result))))
                     interpreted)
       (reject 'kind-mismatch spec))
     (list (apply-type-constructor head-form (map first interpreted))
           'Type)]
    [_ (reject 'invalid-type-spec spec)]))

(define (authorized? propositions)
  (for/or ([entry (in-list propositions)])
    (match entry
      [`(,_ (TypeNarrativeCap ,_)) #t]
      [_ #f])))

(define (constructor-schema data-type)
  (match data-type
    ['Bool '((true ()) (false ()))]
    [`(List ,element)
     `((nil ()) (cons (,element (List ,element))))]
    [`(Option ,element)
     `((none ()) (some (,element)))]
    [`(Result ,ok-type ,error-type)
     `((ok (,ok-type)) (ng (,error-type)))]
    [_ #f]))

(define (constructor-result constructor type-arguments)
  (match (cons constructor type-arguments)
    [(list (or 'true 'false)) 'Bool]
    [(list (or 'nil 'cons) element) `(List ,element)]
    [(list (or 'none 'some) element) `(Option ,element)]
    [(list (or 'ok 'ng) ok-type error-type)
     `(Result ,ok-type ,error-type)]
    [_ (reject 'constructor-type-arity constructor type-arguments)]))

(define (sets-union sets)
  (for/fold ([combined (set)])
            ([item (in-list sets)])
    (set-union combined item)))

(define (free-vars expression)
  (match expression
    [(or (? integer?) (? string?) 'unit) (set)]
    [(? symbol? name) (set name)]
    [`(Fn ((,names ,_) ...) ,_ ,_ ,body)
     (set-subtract (free-vars body) (list->set names))]
    [`(Apply ,terms ...)
     (sets-union (map free-vars terms))]
    [`(Let ,name ,bound ,body)
     (set-union (free-vars bound)
                (set-remove (free-vars body) name))]
    [`(Construct ,_ (Types ,_ ...) ,fields ...)
     (sets-union (map free-vars fields))]
    [`(Construct ,_ ,fields ...)
     (sets-union (map free-vars fields))]
    [`(Eliminate ,scrutinee (,branches ...))
     (set-union
      (free-vars scrutinee)
      (sets-union
       (for/list ([branch (in-list branches)])
         (match branch
           [`(,_ (,parameters ...) -> ,body)
            (set-subtract (free-vars body) (list->set parameters))]
           [_ (set)]))))]
    [`(Return ,body) (free-vars body)]
    [`(NarrativeExpr ,body) (free-vars body)]
    [`(Recur ,function ((,parameters ,_) ...) ,_ ,_ ,body ,continuation)
     (set-union
      (set-subtract (free-vars body)
                    (list->set (cons function parameters)))
      (set-remove (free-vars continuation) function))]
    [`(Yield ,observed ,next)
     (set-union (free-vars observed) (free-vars next))]
    [`(Suspend ,body) (free-vars body)]
    [`(Move ,name) (set name)]
    [`(Drop ,body) (free-vars body)]
    [`(Curry ,function ,argument)
     (set-union (free-vars function) (free-vars argument))]
    [`(TypeMake ,_) (set)]
    [`(LetType ,_ (TypeMake ,_) ,body) (free-vars body)]
    [_ (set)]))

(define (captures-owned? expression locally-bound environment)
  (define visible-environment
    (for/fold ([visible '()])
              ([entry (in-list environment)])
      (if (assoc (first entry) visible)
          visible
          (cons entry visible))))
  (define outer-owned
    (for/set ([entry (in-list visible-environment)]
              #:when (owned-type? (second entry)))
      (first entry)))
  (not
   (set-empty?
    (set-intersect
     (set-subtract (free-vars expression) (list->set locally-bound))
     outer-owned))))

(define (classify-stub _core)
  'Unknown)

(define (elab expression)
  (with-handlers ([exn:fail:elab?
                   (lambda (failure)
                     `(err ,(exn:fail:elab-reason failure)))])
    (unless (redex-match? UCore e expression)
      (reject 'invalid-syntax expression))

    (define boundary-counter 0)
    (define callable-counter 0)
    (define reversed-callables '())

    (define (fresh-boundary)
      (define boundary
        (string->symbol (format "boundary~a" boundary-counter)))
      (set! boundary-counter (add1 boundary-counter))
      boundary)

    (define (fresh-callable signature)
      (define callable
        (string->symbol (format "callable~a" callable-counter)))
      (set! callable-counter (add1 callable-counter))
      (set! reversed-callables
            (cons (list callable signature) reversed-callables))
      callable)

    (define (check-many expressions types environment delta propositions boundaries)
      (unless (= (length expressions) (length types))
        (reject 'arity-mismatch (length types) (length expressions)))
      (for/list ([item (in-list expressions)]
                 [type (in-list types)])
        (check item type environment delta propositions boundaries)))

    (define (elaborate-constructor constructor fields expected
                                   environment delta propositions boundaries)
      (define schema (constructor-schema expected))
      (define field-types (and schema (lookup schema constructor)))
      (unless field-types
        (reject 'constructor-type-mismatch constructor expected))
      (when (ormap owned-type? field-types)
        (reject 'owned-constructor-field constructor))
      (define results
        (check-many fields field-types
                    environment delta propositions boundaries))
      (judgment `(Construct ,constructor
                            ,@(map judgment-core results))
                expected
                (rows-union (map judgment-row results))))

    (define (check-eliminate scrutinee branches expected
                             environment delta propositions boundaries)
      (define scrutinee-result
        (synth scrutinee environment delta propositions boundaries))
      (define schema (constructor-schema (judgment-type scrutinee-result)))
      (unless schema
        (reject 'non-data-eliminate (judgment-type scrutinee-result)))
      (define expected-constructors (map first schema))
      (define actual-constructors
        (for/list ([branch (in-list branches)])
          (match branch
            [`(,constructor (,_ ...) -> ,_) constructor]
            [_ (reject 'invalid-branch branch)])))
      (unless (and (= (length branches) (length schema))
                   (not (check-duplicates actual-constructors))
                   (andmap (lambda (constructor)
                             (member constructor actual-constructors))
                           expected-constructors))
        (reject 'non-exhaustive-eliminate actual-constructors))
      (define branch-results
        (for/list ([branch (in-list branches)])
          (match-define `(,constructor (,parameters ...) -> ,body) branch)
          (define field-types (lookup schema constructor))
          (unless (and field-types
                       (= (length parameters) (length field-types))
                       (not (check-duplicates parameters)))
            (reject 'invalid-branch-binders branch))
          (define result
            (check body expected
                   (extend environment parameters field-types)
                   delta propositions boundaries))
          (list `(,constructor (,parameters ...) -> ,(judgment-core result))
                (judgment-row result))))
      (judgment
       `(Eliminate ,(judgment-core scrutinee-result)
                   ,(map first branch-results))
       expected
       (rows-union
        (cons (judgment-row scrutinee-result)
              (map second branch-results)))))

    (define (synth expression environment delta propositions boundaries)
      (match expression
        [(? integer?) (judgment expression 'Int '())]
        [(? string?) (judgment expression 'String '())]
        ['unit (judgment 'unit 'Unit '())]

        [(? symbol? name)
         (define local-type (lookup environment name))
         (cond
           [local-type
            (if (owned-type? local-type)
                (reject 'owned-variable-requires-move name)
                (judgment name local-type '()))]
           [else
            (match (lookup Γ0 name)
              [(list type value) (judgment value type '())]
              [_ (reject 'unbound-variable name)])])]

        [`(Fn ((,parameters ,raw-parameter-types) ...)
              ,raw-return-type ,raw-row ,body)
         (when (check-duplicates parameters)
           (reject 'duplicate-parameter parameters))
         (define parameter-types
           (for/list ([type (in-list raw-parameter-types)])
             (resolve-annotation type delta)))
         (when (ormap owned-type? parameter-types)
           (reject 'owned-function-parameter))
         (when (captures-owned? body parameters environment)
           (reject 'owned-function-capture))
         (define return-type (resolve-annotation raw-return-type delta))
         (define declared-row
           (resolve-declaration-row raw-row delta boundaries))
         (define boundary (fresh-boundary))
         (define signature
           `(NFn ,parameter-types ,return-type ,declared-row ()))
         (define callable (fresh-callable signature))
         (define body-result
           (check body return-type
                  (extend environment parameters parameter-types)
                  delta propositions
                  (cons `(FunctionBoundary ,boundary ,return-type)
                        boundaries)))
         (define own-return `((Return ,boundary ,return-type)))
         (define residual-row
           (row-difference (judgment-row body-result) own-return))
         (unless (row-subset? residual-row declared-row)
           (reject 'undeclared-function-effect residual-row declared-row))
         (judgment
          `(Lam User ,callable ,parameters
                (Handle (Return ,boundary ,return-type)
                        (return-value -> return-value)
                        (Scope () ,(judgment-core body-result))))
          signature
          '())]

        [`(Apply ,function ,arguments ...)
         (define function-result
           (synth function environment delta propositions boundaries))
         (match (judgment-type function-result)
           [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
            (unless (for/and ([obligation (in-list obligations)])
                      (for/or ([entry (in-list propositions)])
                        (equal? obligation (first (second entry)))))
              (reject 'unsatisfied-proof-obligation obligations))
            (define argument-results
              (check-many arguments parameter-types
                          environment delta propositions boundaries))
            (judgment
             `(Apply ,(judgment-core function-result)
                     ,@(map judgment-core argument-results))
             return-type
             (rows-union
              (append (list (judgment-row function-result))
                      (map judgment-row argument-results)
                      (list latent-row))))]
           [_ (reject 'apply-non-function (judgment-type function-result))])]

        [`(Let ,name ,bound ,body)
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define body-result
           (synth body
                  (extend environment (list name)
                          (list (judgment-type bound-result)))
                  delta propositions boundaries))
         (judgment
          `(Let (,name ,(judgment-type bound-result))
                ,(judgment-core bound-result)
                ,(judgment-core body-result))
          (judgment-type body-result)
          (row-union (judgment-row bound-result)
                     (judgment-row body-result)))]

        [`(Construct ,constructor (Types ,raw-types ...) ,fields ...)
         (define type-arguments
           (for/list ([type (in-list raw-types)])
             (resolve-annotation type delta)))
         (define result-type
           (constructor-result constructor type-arguments))
         (elaborate-constructor constructor fields result-type
                                environment delta propositions boundaries)]

        [`(Construct ,_ ,_ ...)
         (reject 'constructor-needs-expected-type)]

        [`(Eliminate ,_ ,_)
         (reject 'eliminate-needs-expected-type)]

        [`(Return ,returned)
         (match (nearest-boundary boundaries)
           [`(,_ ,boundary ,return-type)
            (define returned-result
              (check returned return-type
                     environment delta propositions boundaries))
            (judgment
             `(Perform (Return ,boundary ,return-type)
                       ,(judgment-core returned-result))
             'Never
             (row-union `((Return ,boundary ,return-type))
                        (judgment-row returned-result)))]
           [_ (reject 'return-outside-boundary)])]

        [`(NarrativeExpr ,_)
         (reject 'narrative-expression-needs-expected-type)]

        [`(Recur ,function ((,parameters ,raw-parameter-types) ...)
                 ,raw-return-type ,raw-row ,body ,continuation)
         (when (check-duplicates (cons function parameters))
           (reject 'duplicate-recur-binder function parameters))
         (define parameter-types
           (for/list ([type (in-list raw-parameter-types)])
             (resolve-annotation type delta)))
         (when (ormap owned-type? parameter-types)
           (reject 'owned-recur-parameter))
         (when (captures-owned? body (cons function parameters) environment)
           (reject 'owned-recur-capture))
         (define return-type (resolve-annotation raw-return-type delta))
         (define declared-row
           (resolve-declaration-row raw-row delta boundaries))
         (define signature
           `(NFn ,parameter-types ,return-type ,declared-row ()))
         (define callable (fresh-callable signature))
         (define function-environment
           (extend environment (list function) (list signature)))
         (define body-environment
           (extend function-environment parameters parameter-types))
         (define body-result
           (check body return-type body-environment
                  delta propositions boundaries))
         (unless (row-subset? (judgment-row body-result) declared-row)
           (reject 'undeclared-recur-effect
                   (judgment-row body-result) declared-row))
         (define continuation-result
           (synth continuation function-environment
                  delta propositions boundaries))
         (define recur-core
           `(Recur ,callable ,function ,parameters
                   ,(judgment-core body-result)
                   ,(judgment-core continuation-result)))
         (define classification (classify-stub recur-core))
         (when (and (eq? classification 'Unknown)
                    (not (row-member? 'Partial declared-row)))
           (reject 'unknown-recur-requires-partial))
         (judgment
          recur-core
          (judgment-type continuation-result)
          (judgment-row continuation-result))]

        [`(Yield ,observed ,next)
         (define observed-result
           (synth observed environment delta propositions boundaries))
         (define next-result
           (synth next environment delta propositions boundaries))
         (judgment
          `(Yield ,(judgment-core observed-result)
                  ,(judgment-core next-result))
          (judgment-type next-result)
          (rows-union
           (list (judgment-row observed-result)
                 (judgment-row next-result)
                 `((Yield ,(judgment-type observed-result))))))]

        [`(Suspend ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (judgment `(Suspend ,(judgment-core result))
                   (judgment-type result)
                   (row-union (judgment-row result) '(Suspend)))]

        [`(Move ,name)
         (match (lookup environment name)
           [`(Owned ,inner)
            (judgment `(Move ,name) `(Owned ,inner) '(Own))]
           [_ (reject 'move-non-owned name)])]

        [`(Drop ,name)
         #:when (and (symbol? name)
                     (owned-type? (lookup environment name)))
         (judgment `(Drop (Move ,name)) 'Unit '(Own))]

        [`(Drop ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (unless (owned-type? (judgment-type result))
           (reject 'drop-non-owned (judgment-type result)))
         (judgment `(Drop ,(judgment-core result))
                   'Unit
                   (row-union (judgment-row result) '(Own)))]

        [`(Curry ,function ,argument)
         (define function-result
           (synth function environment delta propositions boundaries))
         (match (judgment-type function-result)
           [`(NFn (,first-type ,remaining-types ...)
                  ,return-type ,latent-row ,obligations)
            (when (owned-type? first-type)
              (reject 'owned-curry-argument))
            (define argument-result
              (check argument first-type
                     environment delta propositions boundaries))
            (judgment
             `(Curry ,(judgment-core function-result)
                     ,(judgment-core argument-result))
             `(NFn ,remaining-types ,return-type ,latent-row ,obligations)
             (row-union (judgment-row function-result)
                        (judgment-row argument-result)))]
           [_ (reject 'curry-non-function (judgment-type function-result))])]

        [`(TypeMake ,spec)
         (unless (authorized? propositions)
           (reject 'missing-type-narrative-capability))
         (match-define (list type-form kind)
           (interpret-spec spec delta))
         (judgment
          `(TypeRep (Derived (Reserved o-type-narrative)
                             (Make ,type-form))
                    ,type-form
                    ,kind)
          `(TypeInfo ,kind)
          '(Compile))]

        [`(LetType ,name (TypeMake ,spec) ,body)
         (unless (authorized? propositions)
           (reject 'missing-type-narrative-capability))
         (match-define (list type-form kind)
           (interpret-spec spec delta))
         (define representation
           `(TypeRep (Derived (Reserved o-type-narrative)
                              (Make ,type-form))
                     ,type-form
                     ,kind))
         (define body-result
           (synth body
                  environment
                  (cons (list name representation) delta)
                  propositions
                  boundaries))
         (judgment (judgment-core body-result)
                   (judgment-type body-result)
                   (row-union (judgment-row body-result) '(Compile)))]

        [_ (reject 'cannot-synthesize expression)]))

    (define (check expression expected environment delta propositions boundaries)
      (match expression
        [`(Construct ,constructor (Types ,_ ...) ,_ ...)
         (define result
           (synth expression environment delta propositions boundaries))
         (unless (type-compatible? (judgment-type result) expected)
           (reject 'type-mismatch (judgment-type result) expected))
         (judgment (judgment-core result) expected (judgment-row result))]

        [`(Construct ,constructor ,fields ...)
         (elaborate-constructor constructor fields expected
                                environment delta propositions boundaries)]

        [`(Eliminate ,scrutinee (,branches ...))
         (check-eliminate scrutinee branches expected
                          environment delta propositions boundaries)]

        [`(NarrativeExpr ,body)
         (define boundary (fresh-boundary))
         (define body-result
           (check body expected environment delta propositions
                  (cons `(ExpressionBoundary ,boundary ,expected)
                        boundaries)))
         (define own-return `((Return ,boundary ,expected)))
         (judgment
          `(Handle (Return ,boundary ,expected)
                   (return-value -> return-value)
                   (Scope () ,(judgment-core body-result)))
          expected
          (row-difference (judgment-row body-result) own-return))]

        [_
         (define result
           (synth expression environment delta propositions boundaries))
         (unless (type-compatible? (judgment-type result) expected)
           (reject 'type-mismatch (judgment-type result) expected))
         (judgment (judgment-core result) expected (judgment-row result))]))

    (define result (synth expression '() Δ0 Π0 '()))
    (list (judgment-core result)
          (judgment-type result)
          (judgment-row result)
          (reverse reversed-callables))))

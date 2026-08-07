#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "annotate.rkt"
         "classify.rkt"
         "compat.rkt"
         "erase.rkt"
         "lang.rkt"
         "origins.rkt"
         "rows.rkt"
         "schema.rkt"
         "search.rkt"
         "span-core.rkt"
         "type-equiv.rkt"
         "type-shape.rkt"
         "ucore.rkt"
         "validators.rkt")

(provide UCore
         elab)

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

;; span.md §7.4: 節点の照合は span を剥いだ形の上で行い、子は spanful のまま残す。
;; 節ごとの pattern を二重に持たないため、剥がしをこの 1 箇所へ寄せる。
(define (span-of node)
  (match node
    [(list (or '#:var '#:lit) _ s) s]
    [(list _ (and s (list '#:span _ _ _)) _ ...) s]
    [_ (error 'span-of "span を持たない節点である: ~s" node)]))

(define (peel-node node)
  (match node
    [(list '#:lit l _) l]
    [(list '#:var x _) x]
    [(list head (list '#:span _ _ _) rest ...) (cons head rest)]
    [_ node]))

;; ubr は span を先頭へ持つ。head を持たないため peel-node と別に扱う。
(define (branch-span branch)
  (match branch
    [(list (and s (list '#:span _ _ _)) _ ...) s]
    [_ (error 'branch-span "span を持たない分岐である: ~s" branch)]))

(define (peel-branch branch)
  (match branch
    [(list (list '#:span _ _ _) rest ...) rest]
    [_ branch]))

;; 型注釈・束縛・label・作用 row の包み。spanless な入力にも使えるよう、
;; 包みでない値はそのまま返す。resolve-annotation は入れ子の型からも呼ばれ、
;; 内側の型は §4.2 の通り包みを持たないためである。
(define (peel-ty t)   (match t [(list '#:ty type _) type] [_ t]))
(define (peel-bind t) (match t [(list '#:bind x _) x] [_ t]))
(define (peel-lbl t)  (match t [(list '#:lbl label _) label] [_ t]))
(define (peel-ef t)   (match t [(list '#:ef row _) row] [_ t]))

;; span.md §7.4: Γ0 の値は表の項であり span を持たない。参照した位置の
;; span を head の直後へ付け、G1+ の値へ戻す。
(define (attach-span value s)
  (match value
    [(list head rest ...) (list* head s rest)]
    [_ (error 'attach-span "Γ0 の値が項ではない: ~s" value)]))

;; 包みの span。(#:ty τ s)、(#:bind x s)、(#:lbl label s)、(#:ef ε s) は
;; いずれも第 3 要素へ span を持つ。span-of は節点の第 2 要素を読むため
;; 包みには使えない。両者を 1 つの関数へまとめると、節点の第 2 要素が
;; 偶然 span に見える包みを取り違える余地が残るので、別の名前で分ける。
(define (wrapper-span t)
  (match t
    [(list (or '#:ty '#:bind '#:lbl '#:ef) _ (and s (list '#:span _ _ _))) s]
    [_ (error 'wrapper-span "span を持たない包みである: ~s" t)]))

;; span.md §3: 文法は startByte <= endByte を書けない。UCore+ に属する項でも
;; 座標が逆順なら span として妥当でない。入口で一度だけ再帰的に検査する。
;; 判定は span-core.rkt の span-ok? が持ち、ここは走査だけを行う。
(define (spans-ok? t)
  (cond
    [(and (pair? t) (eq? (car t) '#:span)) (span-ok? t)]
    [(list? t) (andmap spans-ok? t)]
    [else #t]))

(define (extend environment names types)
  (append (map list names types) environment))

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

(define (type? value)
  (and (redex-match? G2 τ value)
       (type-shape-ok? value)))

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

;; RFN-003: elaboration では、その位置で見えている命題文脈を候補へ変換して
;; 渡す。typing の Γ_pc⁰ に対応する。
(define (type-compatible? actual expected propositions)
  (compat? actual expected (initial-candidate-context propositions)))

;; RFN-001/002: 表層注釈に書いてよい命題。判定表の (Prop id) と G1 の 2 命題を
;; 許し、(Presence label) は許さない。文法でも外しているが、注釈は Redex の
;; パターンを経ずに渡る経路があるため、解決時にも同じ線引きを課す。
(define (annotation-proposition? proposition)
  (match proposition
    [(or 'ValidNarrativeTrait 'TypeNarrativeCap) #t]
    [`(Prop ,_) (and (validator-row-by-proposition proposition) #t)]
    [`(ValidNarrativeTrait ,_) #t]
    [`(Implements ,_ ,_) #t]
    [`(RequiresBoth ,_ ,_) #t]
    [_ #f]))

(define (resolve-proposition proposition delta invalid-reason)
  (unless (annotation-proposition? proposition)
    (reject invalid-reason proposition))
  (define resolved
    (match proposition
      [`(Implements ,type ,trait)
       `(Implements ,(resolve-annotation type delta) ,trait)]
      [_ proposition]))
  (or (normalize-proposition resolved)
      (reject invalid-reason proposition)))

(define (resolve-obligations obligations delta)
  (for/list ([proposition (in-list obligations)])
    (resolve-proposition proposition delta 'invalid-obligation)))

(define (resolve-annotation raw-annotation delta)
  (define annotation (peel-ty raw-annotation))
  (define resolved
    (match annotation
      [`(Record ,row)
       (unless (field-row-unique? row)
         (reject 'duplicate-record-label row))
       `(Record
         ,(for/list ([field (in-list row)])
            (match-define `(,label ,type ,mutability) field)
            `(,label ,(resolve-annotation type delta) ,mutability)))]
      [`(List ,element)
       `(List ,(resolve-annotation element delta))]
      [`(Option ,element)
       `(Option ,(resolve-annotation element delta))]
      [`(Result ,ok-type ,error-type)
       `(Result ,(resolve-annotation ok-type delta)
                ,(resolve-annotation error-type delta))]
      [`(Owned ,inner)
       `(Owned ,(resolve-annotation inner delta))]
      [`(Untrusted ,inner)
       `(Untrusted ,(resolve-annotation inner delta))]
      [`(Refined ,inner ,proposition)
       `(Refined
         ,(resolve-annotation inner delta)
         ,(resolve-proposition proposition delta 'invalid-proposition))]
      [`(Union ,left ,right)
       `(Union ,(resolve-annotation left delta)
               ,(resolve-annotation right delta))]
      [`(Intersection ,left ,right)
       `(Intersection ,(resolve-annotation left delta)
                      ,(resolve-annotation right delta))]
      [`(NFn (,parameters ...) ,return-type ,row ,obligations)
       `(NFn ,(for/list ([parameter (in-list parameters)])
                (resolve-annotation parameter delta))
             ,(resolve-annotation return-type delta)
             ,(resolve-type-row row delta)
             ,(resolve-obligations obligations delta))]
      [`(TypeInfo ,kind) `(TypeInfo ,kind)]
      [`(Proof ,proposition)
       `(Proof
         ,(resolve-proposition proposition delta 'invalid-proposition))]
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
  (define normalized (normalize-type resolved))
  (if (and normalized (type? normalized))
      normalized
      (reject 'invalid-resolved-type resolved)))

(define (resolve-type-row raw-row delta)
  (define row (peel-ef raw-row))
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

(define (resolve-declaration-row raw-row delta boundaries)
  (define row (peel-ef raw-row))
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

(define (interpret-spec raw-spec delta)
  (define spec (peel-ty raw-spec))
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

(define (free-vars raw-expression)
  (define expression (erase-surface raw-expression))
  (free-vars/erased expression))

(define (free-vars/erased expression)
  (match expression
    [(or (? integer?) (? string?) 'unit) (set)]
    [(? symbol? name) (set name)]
    [`(Fn ((,names ,_) ...) ,_ ,_ ,body)
     (set-subtract (free-vars/erased body) (list->set names))]
    [`(Apply ,terms ...)
     (sets-union (map free-vars/erased terms))]
    [`(Let (,name ,_ ,_) ,bound ,body)
     (set-union (free-vars/erased bound)
                (set-remove (free-vars/erased body) name))]
    [`(Let ,name ,bound ,body)
     (set-union (free-vars/erased bound)
                (set-remove (free-vars/erased body) name))]
    [`(Rec (,fields ...))
     (sets-union
      (for/list ([field (in-list fields)])
        (match field
          [`(,_ ,_ ,body) (free-vars/erased body)]
          [_ (set)])))]
    [`(Proj ,record ,_) (free-vars/erased record)]
    [`(Construct ,_ (Types ,_ ...) ,fields ...)
     (sets-union (map free-vars/erased fields))]
    [`(Construct ,_ ,fields ...)
     (sets-union (map free-vars/erased fields))]
    [`(Eliminate ,scrutinee (,branches ...))
     (set-union
      (free-vars/erased scrutinee)
      (sets-union
       (for/list ([branch (in-list branches)])
         (match branch
           [`(,_ (,parameters ...) -> ,body)
            (set-subtract (free-vars/erased body) (list->set parameters))]
           [_ (set)]))))]
    [`(Return ,body) (free-vars/erased body)]
    [`(NarrativeExpr ,body) (free-vars/erased body)]
    [`(Recur ,function ((,parameters ,_) ...) ,_ ,_ ,body ,continuation)
     (set-union
      (set-subtract (free-vars/erased body)
                    (list->set (cons function parameters)))
      (set-remove (free-vars/erased continuation) function))]
    [`(Yield ,observed ,next)
     (set-union (free-vars/erased observed) (free-vars/erased next))]
    [`(Suspend ,body) (free-vars/erased body)]
    [`(Move ,name) (set name)]
    [`(Drop ,body) (free-vars/erased body)]
    [`(Curry ,function ,argument)
     (set-union (free-vars/erased function) (free-vars/erased argument))]
    [`(TypeMake ,_) (set)]
    [`(LetType ,_ (TypeMake ,_) ,body) (free-vars/erased body)]
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

(define (elab raw-expression)
  (with-handlers ([exn:fail:elab?
                   (lambda (failure)
                     `(err ,(exn:fail:elab-reason failure)))])
    ;; span.md §7.4: UCore+ と UCore は交わらない。spanless な入力は
    ;; annotate-surface で UCore+ へ正規化し、以後は 1 つの形だけを扱う。
    ;; span を一部だけ持つ項はどちらにも属さず、ここで落ちる。
    (define expression
      (cond
        [(redex-match? UCore+ e raw-expression)
         (if (spans-ok? raw-expression)
             raw-expression
             (reject 'invalid-syntax raw-expression))]
        [(redex-match? UCore e raw-expression) (annotate-surface raw-expression)]
        [else (reject 'invalid-syntax raw-expression)]))

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

    (define (elaborate-constructor constructor fields expected type-span
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
      (judgment `(Construct ,type-span (#:ty ,expected ,type-span) ,constructor
                            ,@(map judgment-core results))
                expected
                (rows-union (map judgment-row results))))

    (define (check-eliminate scrutinee branches expected eliminate-span
                             environment delta propositions boundaries)
      (define scrutinee-result
        (synth scrutinee environment delta propositions boundaries))
      (define schema (constructor-schema (judgment-type scrutinee-result)))
      (unless schema
        (reject 'non-data-eliminate (judgment-type scrutinee-result)))
      (define expected-constructors (map first schema))
      (define actual-constructors
        (for/list ([raw-branch (in-list branches)])
          (match (peel-branch raw-branch)
            [`(,constructor (,_ ...) -> ,_) constructor]
            [_ (reject 'invalid-branch raw-branch)])))
      (unless (and (= (length branches) (length schema))
                   (not (check-duplicates actual-constructors))
                   (andmap (lambda (constructor)
                             (member constructor actual-constructors))
                           expected-constructors))
        (reject 'non-exhaustive-eliminate actual-constructors))
      (define branch-results
        (for/list ([raw-branch (in-list branches)])
          (match-define `(,constructor (,raw-parameters ...) -> ,body)
            (peel-branch raw-branch))
          (define parameters (map peel-bind raw-parameters))
          (define field-types (lookup schema constructor))
          (unless (and field-types
                       (= (length parameters) (length field-types))
                       (not (check-duplicates parameters)))
            (reject 'invalid-branch-binders raw-branch))
          (define result
            (check body expected
                   (extend environment parameters field-types)
                   delta propositions boundaries))
            (list `(,(branch-span raw-branch) ,constructor ,raw-parameters
                    -> ,(judgment-core result))
                  (judgment-row result))))
      (judgment
       `(Eliminate ,eliminate-span
                   ,(judgment-core scrutinee-result)
                   ,(map first branch-results))
       expected
       (rows-union
        (cons (judgment-row scrutinee-result)
              (map second branch-results)))))

    (define (synth expression environment delta propositions boundaries)
      (define result
        (synth/raw expression environment delta propositions boundaries))
      (define normalized (normalize-type (judgment-type result)))
      (unless normalized
        (reject 'non-normalizable-type (judgment-type result)))
      (judgment (judgment-core result)
                normalized
                (judgment-row result)))

    (define (synth/raw expression environment delta propositions boundaries)
      (define s (span-of expression))
      (match (peel-node expression)
        [(? integer? literal) (judgment `(#:lit ,literal ,s) 'Int '())]
        [(? string? literal) (judgment `(#:lit ,literal ,s) 'String '())]
        ['unit (judgment `(#:lit unit ,s) 'Unit '())]

        [(? symbol? name)
         (define local-type (lookup environment name))
         (cond
           [local-type
            (if (owned-type? local-type)
                (reject 'owned-variable-requires-move name)
                (judgment `(#:var ,name ,s) local-type '()))]
           [else
            (match (lookup Γ0 name)
              [(list type value) (judgment (attach-span value s) type '())]
              [_ (reject 'unbound-variable name)])])]

        [`(Fn ((,parameter-binders ,raw-parameter-types) ...)
              ,raw-return-type ,raw-row ,body)
         (define parameters (map peel-bind parameter-binders))
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
          `(Lam ,s User ,callable ,parameter-binders
                (Handle ,s (Return ,boundary (#:ty ,return-type ,s))
                        (,s (#:bind return-value ,s) ->
                            (#:var return-value ,s))
                        (Scope ,s () ,(judgment-core body-result))))
          signature
          '())]

        [`(Apply ,function ,arguments ...)
         (define function-result
           (synth function environment delta propositions boundaries))
         (match (judgment-type function-result)
           [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
            ;; PRF-004: 判定と搬送で探索を二重に走らせない。obligation-proofs は
            ;; 各義務を一度だけ解き、充足できない義務と搬送できない P をどちらも
            ;; #f で返す。obligations-dischargeable? の呼び出しはここから外す。
            (define proofs
              (obligation-proofs
               obligations
               (initial-candidate-context propositions)))
            (when (memq #f proofs)
              (reject 'unsatisfied-proof-obligation obligations))
            (define argument-results
              (check-many arguments parameter-types
                          environment delta propositions boundaries))
            (define applied
              `(Apply ,s ,(judgment-core function-result)
                      ,@(map judgment-core argument-results)))
            (judgment
             ;; 義務列の先頭を最も外側にする。逆順に畳むと (φ_1 φ_2) が
             ;; (Discharge P_1 (Discharge P_2 (Apply ...))) になる。
             (for/fold ([core applied]) ([proof (in-list (reverse proofs))])
               `(Discharge ,s ,proof ,core))
             return-type
             (rows-union
              (append (list (judgment-row function-result))
                      (map judgment-row argument-results)
                      (list latent-row))))]
           [_ (reject 'apply-non-function (judgment-type function-result))])]

        [`(Rec (,raw-fields ...))
         (define raw-labels (map first raw-fields))
         (define fields
           (for/list ([field (in-list raw-fields)])
             (match-define `(,raw-label ,mutability ,field-expression) field)
             (list (peel-lbl raw-label) mutability field-expression)))
         (unless (field-row-unique? fields)
           (reject 'duplicate-record-label fields))
         (define field-results
           (for/list ([field (in-list fields)])
             (match-define `(,label ,mutability ,field-expression) field)
             (define result
               (synth field-expression environment delta propositions boundaries))
             (when (owned-type? (judgment-type result))
               (reject 'owned-record-field label))
             (list label mutability result)))
         (judgment
          `(Rec ,s
            ,(for/list ([field (in-list field-results)]
                        [raw-label (in-list raw-labels)])
               (match-define (list label mutability result) field)
               `(,raw-label ,mutability ,(judgment-core result))))
          `(Record
            ,(for/list ([field (in-list field-results)])
               (match-define (list label mutability result) field)
               `(,label ,(judgment-type result) ,mutability)))
          (rows-union
           (for/list ([field (in-list field-results)])
             (judgment-row (third field)))))]

        [`(Proj ,record ,raw-label)
         (define label (peel-lbl raw-label))
         (define record-result
           (synth record environment delta propositions boundaries))
         (match (judgment-type record-result)
           [`(Record ,row)
            (match (field-row-lookup row label)
              [(list field-type _)
               (judgment `(Proj ,s ,(judgment-core record-result) ,raw-label)
                         field-type
                         (judgment-row record-result))]
              [_ (reject 'unknown-record-label label)])]
           [_ (reject 'project-non-record (judgment-type record-result))])]

        ;; 注釈なし Let の (#:bind x s) を注釈あり Let の 3 つ組として
        ;; 誤って分解しないよう、binder の包みの形で分岐する。
        [`(Let (,raw-name ,binding-mode ,raw-type) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
         (define name (peel-bind raw-name))
         (define declared-type (resolve-annotation raw-type delta))
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define actual-type (judgment-type bound-result))
         (define binding-type
           (cond
             [(eq? actual-type 'Never) declared-type]
             [else
              (unless (type-compatible? actual-type declared-type propositions)
                (reject 'type-mismatch actual-type declared-type))
              (match declared-type
                [`(Record ,declared-row)
                 (match-define `(Record ,actual-row) actual-type)
                 (define residual
                   (field-row-residual actual-row declared-row))
                 (when (and (eq? binding-mode 'const)
                            (pair? residual))
                   (reject 'const-record-residual residual))
                 (if (eq? binding-mode 'let)
                     `(Record ,(append declared-row residual))
                     declared-type)]
                [_ declared-type])]))
         (define body-result
           (synth body
                  (extend environment (list name) (list binding-type))
                  delta propositions boundaries))
         (judgment
          `(Let ,s (,raw-name ,binding-mode
                              (#:ty ,declared-type ,(wrapper-span raw-type)))
                ,(judgment-core bound-result)
                ,(judgment-core body-result))
          (judgment-type body-result)
          (row-union (judgment-row bound-result)
                     (judgment-row body-result)))]

        [`(Let ,raw-name ,bound ,body)
         (define name (peel-bind raw-name))
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define body-result
           (synth body
                  (extend environment (list name)
                          (list (judgment-type bound-result)))
                  delta propositions boundaries))
         (judgment
          `(Let ,s (,raw-name (#:ty ,(judgment-type bound-result) ,s))
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
                                s
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
             `(Perform ,s (Return ,boundary (#:ty ,return-type ,s))
                       ,(judgment-core returned-result))
             'Never
             (row-union `((Return ,boundary ,return-type))
                        (judgment-row returned-result)))]
           [_ (reject 'return-outside-boundary)])]

        [`(NarrativeExpr ,_)
         (reject 'narrative-expression-needs-expected-type)]

        [`(Recur ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                 ,raw-return-type ,raw-row ,body ,continuation)
         (define function (peel-bind raw-function))
         (define parameters (map peel-bind parameter-binders))
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
           `(Recur ,s ,callable ,raw-function ,parameter-binders
                   ,(judgment-core body-result)
                   ,(judgment-core continuation-result)))
         (define classification
           (classify recur-core environment
                     (reverse reversed-callables)))
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
          `(Yield ,s ,(judgment-core observed-result)
                  ,(judgment-core next-result))
          (judgment-type next-result)
          (rows-union
           (list (judgment-row observed-result)
                 (judgment-row next-result)
                 `((Yield ,(judgment-type observed-result))))))]

        [`(Suspend ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (judgment `(Suspend ,s ,(judgment-core result))
                   (judgment-type result)
                   (row-union (judgment-row result) '(Suspend)))]

        [`(Move ,raw-name)
         (define name (peel-node raw-name))
         (match (lookup environment name)
           [`(Owned ,inner)
            (judgment `(Move ,s ,raw-name) `(Owned ,inner) '(Own))]
           [_ (reject 'move-non-owned name)])]

        [`(Drop ,raw-name)
         #:when (let ([name (peel-node raw-name)])
                  (and (symbol? name)
                       (owned-type? (lookup environment name))))
         (judgment `(Drop ,s (Move ,s ,raw-name)) 'Unit '(Own))]

        [`(Drop ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (unless (owned-type? (judgment-type result))
           (reject 'drop-non-owned (judgment-type result)))
         (judgment `(Drop ,s ,(judgment-core result))
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
             `(Curry ,s ,(judgment-core function-result)
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
          `(TypeRep ,s (Derived (Reserved o-type-narrative)
                             (Make ,type-form))
                    ,type-form
                    ,kind)
          `(TypeInfo ,kind)
          '(Compile))]

        [`(LetType ,name (TypeMake ,_ ,spec) ,body)
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
      (define s (span-of expression))
      (match (peel-node expression)
        [`(Construct ,constructor (Types ,_ ...) ,_ ...)
         (define result
           (synth expression environment delta propositions boundaries))
         (unless (type-compatible? (judgment-type result) expected
                                   propositions)
           (reject 'type-mismatch (judgment-type result) expected))
         (judgment (judgment-core result) expected (judgment-row result))]

        [`(Construct ,constructor ,fields ...)
         (elaborate-constructor constructor fields expected
                                s
                                environment delta propositions boundaries)]

        [`(Eliminate ,scrutinee (,branches ...))
         (check-eliminate scrutinee branches expected
                          s
                          environment delta propositions boundaries)]

        [`(NarrativeExpr ,body)
         (define boundary (fresh-boundary))
         (define body-result
           (check body expected environment delta propositions
                  (cons `(ExpressionBoundary ,boundary ,expected)
                        boundaries)))
         (define own-return `((Return ,boundary ,expected)))
         (judgment
          `(Handle ,s (Return ,boundary (#:ty ,expected ,s))
                   (,s (#:bind return-value ,s) -> (#:var return-value ,s))
                   (Scope ,s () ,(judgment-core body-result)))
          expected
          (row-difference (judgment-row body-result) own-return))]

        [_
         (define result
           (synth expression environment delta propositions boundaries))
         (unless (type-compatible? (judgment-type result) expected
                                   propositions)
           (reject 'type-mismatch (judgment-type result) expected))
         (judgment (judgment-core result) expected (judgment-row result))]))

    (define result (synth expression '() Δ0 Π0 '()))
    (list (judgment-core result)
          (judgment-type result)
          (judgment-row result)
          (reverse reversed-callables))))

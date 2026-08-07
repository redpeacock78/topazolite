#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "annotate.rkt"
         "classify.rkt"
         "compat.rkt"
         "diagnostic.rkt"
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
(struct exn:fail:elab exn:fail (primary-span reason details) #:transparent)

;; primary-span は第 1 引数であり既定値を持たない。既定値を持たせると渡し忘れ
;; が黙って通り、DIA-002 の契約が静かに崩れる。span-ok? と registry の検査で
;; 渡し忘れ、引数の逆順、registry に無い reason を実行時に落とす。
(define (reject primary-span reason . details)
  (unless (span-ok? primary-span)
    (error 'reject "span として妥当でない値を primary-span に受けた: ~s"
           primary-span))
  (unless (diagnostic-code-of 'elaborate reason)
    (error 'reject "registry に無い reason である: ~s" reason))
  (raise
   (exn:fail:elab
    (format "elaboration failed: ~a" reason)
    (current-continuation-marks)
    primary-span
    reason
    details)))

;; §6: details を expected と found へ配る。既定は件数だけで決まり、意味を
;; 推測しない。意味が全呼出しで一致する 5 つの reason だけを例外表で扱う。
;; 例外表の reason でも details の長さが想定と違えば既定へ落ちる。
(define (distribute-details reason details)
  (match* (reason details)
    [('type-mismatch (list actual expected)) (values expected actual)]
    [('arity-mismatch (list expected actual)) (values expected actual)]
    [('constructor-type-mismatch (list constructor expected))
     (values expected constructor)]
    [('undeclared-function-effect (list residual declared))
     (values declared residual)]
    [('undeclared-recur-effect (list residual declared))
     (values declared residual)]
    [(_ '()) (values #f #f)]
    [(_ (list only)) (values #f only)]
    [(_ _) (values #f details)]))

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

;; 包みが span を持つならそれを、持たないなら親から引き継いだ span を返す。
;; wrapper-span は span を持たない包みで error を出すため、形の判定を先に行う。
(define (nearest-span t inherited)
  (match t
    [(list (or '#:ty '#:bind '#:lbl '#:ef) _ (and s (list '#:span _ _ _))) s]
    [_ inherited]))

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

(define (resolve-proposition proposition delta invalid-reason span)
  (unless (annotation-proposition? proposition)
    (reject span invalid-reason proposition))
  (define resolved
    (match proposition
      [`(Implements ,type ,trait)
       `(Implements ,(resolve-annotation type delta span) ,trait)]
      [_ proposition]))
  (or (normalize-proposition resolved)
      (reject span invalid-reason proposition)))

(define (resolve-obligations obligations delta span)
  (for/list ([proposition (in-list obligations)])
    (resolve-proposition proposition delta 'invalid-obligation span)))

(define (resolve-annotation raw-annotation delta inherited-span)
  (define span (nearest-span raw-annotation inherited-span))
  (define annotation (peel-ty raw-annotation))
  (define resolved
    (match annotation
      [`(Record ,row)
       (unless (field-row-unique? row)
         (reject span 'duplicate-record-label row))
       `(Record
         ,(for/list ([field (in-list row)])
            (match-define `(,label ,type ,mutability) field)
            `(,label ,(resolve-annotation type delta span) ,mutability)))]
      [`(List ,element)
       `(List ,(resolve-annotation element delta span))]
      [`(Option ,element)
       `(Option ,(resolve-annotation element delta span))]
      [`(Result ,ok-type ,error-type)
       `(Result ,(resolve-annotation ok-type delta span)
                ,(resolve-annotation error-type delta span))]
      [`(Owned ,inner)
       `(Owned ,(resolve-annotation inner delta span))]
      [`(Untrusted ,inner)
       `(Untrusted ,(resolve-annotation inner delta span))]
      [`(Refined ,inner ,proposition)
       `(Refined
         ,(resolve-annotation inner delta span)
         ,(resolve-proposition proposition delta 'invalid-proposition span))]
      [`(Union ,left ,right)
       `(Union ,(resolve-annotation left delta span)
               ,(resolve-annotation right delta span))]
      [`(Intersection ,left ,right)
       `(Intersection ,(resolve-annotation left delta span)
                      ,(resolve-annotation right delta span))]
      [`(NFn (,parameters ...) ,return-type ,row ,obligations)
       `(NFn ,(for/list ([parameter (in-list parameters)])
                (resolve-annotation parameter delta span))
             ,(resolve-annotation return-type delta span)
             ,(resolve-type-row row delta span)
             ,(resolve-obligations obligations delta span))]
      [`(TypeInfo ,kind) `(TypeInfo ,kind)]
      [`(Proof ,proposition)
       `(Proof
         ,(resolve-proposition proposition delta 'invalid-proposition span))]
      [(? symbol? name)
       (match (lookup delta name)
         [`(TypeRep ,_ ,type-form Type)
          (if (type? type-form)
              type-form
              (reject span 'invalid-type-representation name))]
         [`(TypeRep ,_ ,_ ,kind)
          (reject span 'unsaturated-type name kind)]
         [_ (reject span 'unknown-type name)])]
      [_ (reject span 'invalid-type-annotation annotation)]))
  (define normalized (normalize-type resolved))
  (if (and normalized (type? normalized))
      normalized
      (reject span 'invalid-resolved-type resolved)))

(define (resolve-type-row raw-row delta inherited-span)
  (define span (nearest-span raw-row inherited-span))
  (define row (peel-ef raw-row))
  (normalize-row
   (for/list ([label (in-list row)])
     (match label
       [`(Return ,boundary ,type)
        `(Return ,boundary ,(resolve-annotation type delta span))]
       [`(Yield ,type)
        `(Yield ,(resolve-annotation type delta span))]
       [(or 'Suspend 'Partial 'Compile 'Own) label]
       [_ (reject span 'invalid-effect-label label)]))))

(define (nearest-boundary boundaries)
  (and (pair? boundaries) (car boundaries)))

(define (resolve-declaration-row raw-row delta boundaries inherited-span)
  (define span (nearest-span raw-row inherited-span))
  (define row (peel-ef raw-row))
  (normalize-row
   (for/list ([label (in-list row)])
     (match label
       ['Return
        (match (nearest-boundary boundaries)
          [`(,_ ,boundary ,type) `(Return ,boundary ,type)]
          [_ (reject span 'return-label-outside-boundary)])]
       [`(Yield ,type)
        `(Yield ,(resolve-annotation type delta span))]
       [(or 'Suspend 'Partial 'Compile 'Own) label]
       [_ (reject span 'invalid-effect-label label)]))))

(define (kind-arity kind span)
  (match kind
    ['Type 0]
    [`(Type -> ,rest) (add1 (kind-arity rest span))]
    [_ (reject span 'invalid-kind kind)]))

(define (apply-type-constructor type-form arguments span)
  (match* (type-form arguments)
    [('List (list element)) `(List ,element)]
    [('Option (list element)) `(Option ,element)]
    [('Result (list ok-type error-type)) `(Result ,ok-type ,error-type)]
    [(_ _) (reject span 'invalid-type-application type-form arguments)]))

(define (interpret-spec raw-spec delta inherited-span)
  (define span (nearest-span raw-spec inherited-span))
  (define spec (peel-ty raw-spec))
  (match spec
    [(? symbol? name)
     (match (lookup delta name)
       [`(TypeRep ,_ ,type-form ,kind) (list type-form kind)]
       [_ (reject span 'unknown-type-spec name)])]
    [`(Spec ,head ,arguments ...)
     (match-define (list head-form head-kind)
       (interpret-spec head delta span))
     (define arity (kind-arity head-kind span))
     (unless (and (positive? arity)
                  (= arity (length arguments)))
       (reject span 'kind-mismatch spec head-kind))
     (define interpreted
       (for/list ([argument (in-list arguments)])
         (interpret-spec argument delta span)))
     (unless (andmap (lambda (result)
                       (and (equal? (second result) 'Type)
                            (type? (first result))))
                     interpreted)
       (reject span 'kind-mismatch spec))
     (list (apply-type-constructor head-form (map first interpreted) span)
           'Type)]
    [_ (reject span 'invalid-type-spec spec)]))

(define (authorized? propositions)
  (for/or ([entry (in-list propositions)])
    (match entry
      [`(,_ (TypeNarrativeCap ,_)) #t]
      [_ #f])))

(define (constructor-result constructor type-arguments span)
  (match (cons constructor type-arguments)
    [(list (or 'true 'false)) 'Bool]
    [(list (or 'nil 'cons) element) `(List ,element)]
    [(list (or 'none 'some) element) `(Option ,element)]
    [(list (or 'ok 'ng) ok-type error-type)
     `(Result ,ok-type ,error-type)]
    [_ (reject span 'constructor-type-arity constructor type-arguments)]))

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

;; §8: 判断節点の span を取れるならそれを、取れないときだけ synthetic へ
;; 落ちる。順序を逆にすると source span があるのに synthetic を返す実装になる。
(define (entry-span term)
  (define s
    (with-handlers ([exn:fail? (lambda (_) #f)])
      (span-of term)))
  (if (and s (span-ok? s)) s '(#:span #:synthetic 0 0)))

;; §5: Diagnostic の生成は 1 箇所へ集約する。reject は struct を組み立てず、
;; registry の引き当てと欄の検証を通る経路をここへ揃える。
(define (elab-failure->diagnostic failure)
  (define reason (exn:fail:elab-reason failure))
  (define row (diagnostic-code-row (diagnostic-code-of 'elaborate reason)))
  (define title (diagnostic-code-title row))
  (define-values (expected found)
    (distribute-details reason (exn:fail:elab-details failure)))
  (make-diagnostic #:id (diagnostic-code-code row)
                   #:title title
                   #:message title
                   #:primary-span (exn:fail:elab-primary-span failure)
                   #:expected expected
                   #:found found))

(define (elab raw-expression)
  (with-handlers ([exn:fail:elab?
                   (lambda (failure)
                     `(err ,(elab-failure->diagnostic failure)))])
    ;; span.md §7.4: UCore+ と UCore は交わらない。spanless な入力は
    ;; annotate-surface で UCore+ へ正規化し、以後は 1 つの形だけを扱う。
    ;; span を一部だけ持つ項はどちらにも属さず、ここで落ちる。
    (define expression
      (cond
        [(redex-match? UCore+ e raw-expression)
         (if (spans-ok? raw-expression)
             raw-expression
             (reject (entry-span raw-expression)
                     'invalid-syntax raw-expression))]
        [(redex-match? UCore e raw-expression) (annotate-surface raw-expression)]
        [else (reject (entry-span raw-expression)
                      'invalid-syntax raw-expression)]))

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

    (define (check-many expressions types environment delta propositions boundaries span)
      (unless (= (length expressions) (length types))
        (reject span 'arity-mismatch (length types) (length expressions)))
      (for/list ([item (in-list expressions)]
                 [type (in-list types)])
        (check item type environment delta propositions boundaries)))

    (define (elaborate-constructor constructor fields expected type-span
                                   environment delta propositions boundaries)
      (define schema (constructor-schema expected))
      (define field-types (and schema (lookup schema constructor)))
      (unless field-types
        (reject type-span 'constructor-type-mismatch constructor expected))
      (when (ormap owned-type? field-types)
        (reject type-span 'owned-constructor-field constructor))
      (define results
        (check-many fields field-types
                    environment delta propositions boundaries type-span))
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
        (reject eliminate-span 'non-data-eliminate (judgment-type scrutinee-result)))
      (define expected-constructors (map first schema))
      (define actual-constructors
        (for/list ([raw-branch (in-list branches)])
          (match (peel-branch raw-branch)
            [`(,constructor (,_ ...) -> ,_) constructor]
            [_ (reject eliminate-span 'invalid-branch raw-branch)])))
      (unless (and (= (length branches) (length schema))
                   (not (check-duplicates actual-constructors))
                   (andmap (lambda (constructor)
                             (member constructor actual-constructors))
                           expected-constructors))
        (reject eliminate-span 'non-exhaustive-eliminate actual-constructors))
      (define branch-results
        (for/list ([raw-branch (in-list branches)])
          (match-define `(,constructor (,raw-parameters ...) -> ,body)
            (peel-branch raw-branch))
          (define parameters (map peel-bind raw-parameters))
          (define field-types (lookup schema constructor))
          (unless (and field-types
                       (= (length parameters) (length field-types))
                       (not (check-duplicates parameters)))
            (reject eliminate-span 'invalid-branch-binders raw-branch))
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
      (define s (span-of expression))
      (define result
        (synth/raw expression environment delta propositions boundaries))
      (define normalized (normalize-type (judgment-type result)))
      (unless normalized
        (reject s 'non-normalizable-type (judgment-type result)))
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
                (reject s 'owned-variable-requires-move name)
                (judgment `(#:var ,name ,s) local-type '()))]
           [else
            (match (lookup Γ0 name)
              [(list type value) (judgment (attach-span value s) type '())]
              [_ (reject s 'unbound-variable name)])])]

        [`(Fn ((,parameter-binders ,raw-parameter-types) ...)
              ,raw-return-type ,raw-row ,body)
         (define parameters (map peel-bind parameter-binders))
         (when (check-duplicates parameters)
           (reject s 'duplicate-parameter parameters))
         (define parameter-types
           (for/list ([type (in-list raw-parameter-types)])
             (resolve-annotation type delta s)))
         (when (ormap owned-type? parameter-types)
           (reject s 'owned-function-parameter))
         (when (captures-owned? body parameters environment)
           (reject s 'owned-function-capture))
         (define return-type (resolve-annotation raw-return-type delta s))
         (define declared-row
           (resolve-declaration-row raw-row delta boundaries s))
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
           (reject s 'undeclared-function-effect residual-row declared-row))
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
              (reject s 'unsatisfied-proof-obligation obligations))
            (define argument-results
              (check-many arguments parameter-types
                          environment delta propositions boundaries s))
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
           [_ (reject s 'apply-non-function (judgment-type function-result))])]

        [`(Rec (,raw-fields ...))
         (define raw-labels (map first raw-fields))
         (define fields
           (for/list ([field (in-list raw-fields)])
             (match-define `(,raw-label ,mutability ,field-expression) field)
             (list (peel-lbl raw-label) mutability field-expression)))
         (unless (field-row-unique? fields)
           (reject s 'duplicate-record-label fields))
         (define field-results
           (for/list ([field (in-list fields)])
             (match-define `(,label ,mutability ,field-expression) field)
             (define result
               (synth field-expression environment delta propositions boundaries))
             (when (owned-type? (judgment-type result))
               (reject s 'owned-record-field label))
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
              [_ (reject s 'unknown-record-label label)])]
           [_ (reject s 'project-non-record (judgment-type record-result))])]

        ;; 注釈なし Let の (#:bind x s) を注釈あり Let の 3 つ組として
        ;; 誤って分解しないよう、binder の包みの形で分岐する。
        [`(Let (,raw-name ,binding-mode ,raw-type) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
         (define name (peel-bind raw-name))
         (define declared-type (resolve-annotation raw-type delta s))
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define actual-type (judgment-type bound-result))
         (define binding-type
           (cond
             [(eq? actual-type 'Never) declared-type]
             [else
              (unless (type-compatible? actual-type declared-type propositions)
                (reject s 'type-mismatch actual-type declared-type))
              (match declared-type
                [`(Record ,declared-row)
                 (match-define `(Record ,actual-row) actual-type)
                 (define residual
                   (field-row-residual actual-row declared-row))
                 (when (and (eq? binding-mode 'const)
                            (pair? residual))
                   (reject s 'const-record-residual residual))
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
             (resolve-annotation type delta s)))
         (define result-type
           (constructor-result constructor type-arguments s))
         (elaborate-constructor constructor fields result-type
                                s
                                environment delta propositions boundaries)]

        [`(Construct ,_ ,_ ...)
         (reject s 'constructor-needs-expected-type)]

        [`(Eliminate ,_ ,_)
         (reject s 'eliminate-needs-expected-type)]

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
           [_ (reject s 'return-outside-boundary)])]

        [`(NarrativeExpr ,_)
         (reject s 'narrative-expression-needs-expected-type)]

        [`(Recur ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                 ,raw-return-type ,raw-row ,body ,continuation)
         (define function (peel-bind raw-function))
         (define parameters (map peel-bind parameter-binders))
         (when (check-duplicates (cons function parameters))
           (reject s 'duplicate-recur-binder function parameters))
         (define parameter-types
           (for/list ([type (in-list raw-parameter-types)])
             (resolve-annotation type delta s)))
         (when (ormap owned-type? parameter-types)
           (reject s 'owned-recur-parameter))
         (when (captures-owned? body (cons function parameters) environment)
           (reject s 'owned-recur-capture))
         (define return-type (resolve-annotation raw-return-type delta s))
         (define declared-row
           (resolve-declaration-row raw-row delta boundaries s))
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
           (reject s 'undeclared-recur-effect
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
           (reject s 'unknown-recur-requires-partial))
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
           [_ (reject s 'move-non-owned name)])]

        [`(Drop ,raw-name)
         #:when (let ([name (peel-node raw-name)])
                  (and (symbol? name)
                       (owned-type? (lookup environment name))))
         (judgment `(Drop ,s (Move ,s ,raw-name)) 'Unit '(Own))]

        [`(Drop ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (unless (owned-type? (judgment-type result))
           (reject s 'drop-non-owned (judgment-type result)))
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
              (reject s 'owned-curry-argument))
            (define argument-result
              (check argument first-type
                     environment delta propositions boundaries))
            (judgment
             `(Curry ,s ,(judgment-core function-result)
                     ,(judgment-core argument-result))
             `(NFn ,remaining-types ,return-type ,latent-row ,obligations)
             (row-union (judgment-row function-result)
                        (judgment-row argument-result)))]
           [_ (reject s 'curry-non-function (judgment-type function-result))])]

        [`(TypeMake ,spec)
         (unless (authorized? propositions)
           (reject s 'missing-type-narrative-capability))
         (match-define (list type-form kind)
           (interpret-spec spec delta s))
         (judgment
          `(TypeRep ,s (Derived (Reserved o-type-narrative)
                             (Make ,type-form))
                    ,type-form
                    ,kind)
          `(TypeInfo ,kind)
          '(Compile))]

        [`(LetType ,name (TypeMake ,_ ,spec) ,body)
         (unless (authorized? propositions)
           (reject s 'missing-type-narrative-capability))
         (match-define (list type-form kind)
           (interpret-spec spec delta s))
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

        [_ (reject s 'cannot-synthesize expression)]))

    (define (check expression expected environment delta propositions boundaries)
      (define s (span-of expression))
      (match (peel-node expression)
        [`(Construct ,constructor (Types ,_ ...) ,_ ...)
         (define result
           (synth expression environment delta propositions boundaries))
         (unless (type-compatible? (judgment-type result) expected
                                   propositions)
           (reject s 'type-mismatch (judgment-type result) expected))
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
           (reject s 'type-mismatch (judgment-type result) expected))
         (judgment (judgment-core result) expected (judgment-row result))]))

    (define result (synth expression '() Δ0 Π0 '()))
    (list (judgment-core result)
          (judgment-type result)
          (judgment-row result)
          (reverse reversed-callables))))

;; reject は primary-span を必須の第 1 引数に取る。渡し忘れと引数の逆順、
;; registry に無い reason を、どれも実行時に落として fail-loud にする。
;; reject は provide しないため、内部から検査する。
(module+ test
  (require rackunit)

  (define ok-span '(#:span src 3 7))

  ;; primary-span を渡し忘れると reason が span の位置へ入る。
  (check-exn #px"arity mismatch"
             (lambda () (reject 'unknown-type)))

  ;; primary-span と reason を逆順に渡した場合も同じ検査で落ちる。
  (check-exn #px"span として妥当でない"
             (lambda () (reject 'unknown-type ok-span)))

  ;; 座標が逆順の span は span-ok? を満たさない。
  (check-exn #px"span として妥当でない"
             (lambda () (reject '(#:span src 9 2) 'unknown-type)))

  ;; registry に無い reason は汎用 code へ落とさず error にする。
  (check-exn #px"registry に無い reason"
             (lambda ()
               (reject ok-span 'no-such-reason)))

  ;; 正しい呼び出しは exn:fail:elab を投げ、3 欄を保つ。
  (define failure
    (with-handlers ([exn:fail:elab? values])
      (reject ok-span 'unknown-type 'Foo)))
  (check-pred exn:fail:elab? failure)
  (check-equal? (exn:fail:elab-primary-span failure) ok-span)
  (check-equal? (exn:fail:elab-reason failure) 'unknown-type)
  (check-equal? (exn:fail:elab-details failure) '(Foo)))

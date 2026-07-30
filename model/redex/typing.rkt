#lang racket

(require racket/match
         redex/reduction-semantics
         "compat.rkt"
         "lang.rkt"
         "origins.rkt"
         "rows.rkt"
         "schema.rkt"
         "search.rkt"
         "type-equiv.rkt"
         "type-shape.rkt"
         "validators.rkt")

(provide core-type-of
         core-check
         core-check-row
         config-ok?
         join-types
         merge-field
         presence-binding-name
         field-type-binding-name
         merge-record-types
         merge-witnesses-dischargeable?)

(define (lookup table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

(define (record-type? type)
  (match type
    [`(Record ,_) #t]
    [_ #f]))

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

(define (row=? left right)
  (row-equiv? left right))

;; VAR-001..003: checking は elaboration と同じ compat? を全型で共有する。
;; Never の bottom 受理は compat? の Never 分岐が担う。
;; RFN-003: discharge に使う文脈は大域の Γ_pc⁰ に限る。merge の W は渡さない。
(define (type-compatible? actual expected)
  (compat? actual expected Γ-pc0))

(define (type? value)
  (and (redex-match? G2m τ value)
       (type-shape-ok? value)
       (type-normal? value)))

(define (row? value)
  (and (redex-match? G2m ε value)
       (effect-row-normal? value)))

(define (callable-id? value)
  (redex-match? G1 cid value))

(define (unique-table? table)
  (and (list? table)
       (andmap (λ (entry)
                 (and (list? entry) (= (length entry) 2)))
               table)
       (not (check-duplicates (map first table)))))

(define (valid-places? places)
  (and (unique-table? places)
       (for/and ([entry (in-list places)])
         (match entry
           [(list (? exact-nonnegative-integer?) type)
            (type? type)]
           [_ #f]))))

(define (valid-callables? callables)
  (and (unique-table? callables)
       (for/and ([entry (in-list callables)])
         (match entry
           [(list callable `(NFn ,_ ,_ ,_ ,_))
            (and (callable-id? callable)
                 (type? (second entry)))]
           [_ #f]))))

(define (valid-environment? environment)
  (and (list? environment)
       (for/and ([entry (in-list environment)])
         (match entry
           [(list (? symbol?) type) (type? type)]
           [_ #f]))))

(define (extend environment names types)
  (append (map list names types) environment))

(define (without-owned environment)
  (filter (λ (entry) (not (owned-type? (second entry))))
          environment))

(define (check-many cores types environment places callables)
  (and (= (length cores) (length types))
       (let ([rows
              (for/list ([core (in-list cores)]
                         [type (in-list types)])
                (check-as core type environment places callables))])
         (and (andmap identity rows) rows))))

(define (check-construct constructor fields data-type
                         environment places callables)
  (define schema (constructor-schema data-type))
  (define field-types (and schema (lookup schema constructor)))
  (and field-types
       (not (ormap owned-type? field-types))
       (let ([rows (check-many fields field-types
                               environment places callables)])
         (and rows (rows-union rows)))))

(define (branch-contexts branches data-type environment)
  (define schema (constructor-schema data-type))
  (define expected-constructors (and schema (map first schema)))
  (define actual-constructors
    (for/list ([branch (in-list branches)])
      (match branch
        [`(,constructor (,parameters ...) -> ,_) constructor]
        [_ #f])))
  (and schema
       (= (length branches) (length schema))
       (not (member #f actual-constructors))
       (not (check-duplicates actual-constructors))
       (andmap (λ (constructor)
                 (member constructor actual-constructors))
               expected-constructors)
       (for/and ([branch (in-list branches)])
         (match branch
           [`(,constructor (,parameters ...) -> ,_)
            (define field-types (lookup schema constructor))
            (and field-types
                 (= (length parameters) (length field-types))
                 (not (check-duplicates parameters)))]
           [_ #f]))
       (for/list ([branch (in-list branches)])
         (match-define `(,constructor (,parameters ...) -> ,body)
           branch)
         (list body
               (extend environment
                       parameters
                       (lookup schema constructor))))))

(define (check-eliminate scrutinee branches expected
                         environment places callables)
  (define scrutinee-result
    (infer scrutinee environment places callables))
  (and scrutinee-result
       (let* ([data-type (first scrutinee-result)]
              [contexts (branch-contexts branches data-type environment)])
         (and contexts
              (let ([branch-rows
                     (for/list ([context (in-list contexts)])
                       (check-as (first context)
                                 expected
                                 (second context)
                                 places
                                 callables))])
                (and (andmap identity branch-rows)
                     (rows-union
                      (cons (second scrutinee-result)
                            branch-rows))))))))

;; CMP-001: 2 つの型を Union で合わせ、同値な構成要素を正規化で畳む。
(define (join-types left right)
  (normalize-type `(Union ,left ,right)))

;; CMP-001/ROW-004: 同じ label と可変性を持つ field を合わせる。
;; 異型を join できるのは imm だけであり、異型 mut と可変性不一致は落とす。
(define (merge-field left right)
  (merge-fields (list left right)))

(define (presence-binding-name label)
  (string->symbol (format "presence-~a" label)))

(define (field-type-binding-name label index)
  (string->symbol (format "field-type-~a-~a" label index)))

(define (merge-witness-binding name proposition)
  (list name
        (list proposition '(Reserved o-merge)
              name 'root 'default '())))

;; branch 型を正規化し、Union 正規化と同じ順序・同値判定で重複を畳む。
(define (distinct-normal-types types)
  (define normalized (map normalize-type types))
  (and (andmap values normalized)
       (sort-then-dedup normalized)))

;; RFN-002/CMP-001: merge が立てる局所 witness 文脈。
;; 各 field の Presence に加え、異型 join には branch 型ごとの FieldType を置く。
(define (merge-witness-context types merged-row)
  (append-map
   (lambda (field)
     (define label (first field))
     (define branch-types
       (for/list ([type (in-list types)])
         (first (field-row-lookup (second type) label))))
     (define distinct-types (distinct-normal-types branch-types))
     (define presence-name (presence-binding-name label))
     (cons
      (merge-witness-binding presence-name `(Presence ,label))
      (if (> (length distinct-types) 1)
          (for/list ([type (in-list distinct-types)]
                     [index (in-naturals)])
            (define name (field-type-binding-name label index))
            (merge-witness-binding name `(FieldType ,label ,type)))
          '())))
   merged-row))

(define (merge-fields fields)
  (define first-field (first fields))
  (define label (first first-field))
  (define mutability (third first-field))
  (define types (distinct-normal-types (map second fields)))
  (and
   (for/and ([field (in-list fields)])
     (and (eq? (first field) label)
          (eq? (third field) mutability)))
   types
   (cond
     [(null? (rest types))
      (list label (first types) mutability)]
     [(eq? mutability 'imm)
      (define joined
        (for/fold ([joined (first types)])
                  ([type (in-list (rest types))])
          (join-types joined type)))
      (and joined (list label joined 'imm))]
     ;; #f は merge 全体の失敗ではなく、この field の脱落を表す。
     [else #f])))

(define (merge-common-field types first-field)
  (define label (first first-field))
  (define fields
    (for/list ([type (in-list types)])
      (assoc label (second type))))
  (and (andmap values fields)
       (merge-fields fields)))

;; RFN-002/CMP-001: 全 branch に常在する field を合わせる。異型 imm は Union
;; join し、異型 mut と可変性不一致は field 単位で落とす。
;; types は空でないことを呼び出し側が保証する。
(define (merge-record-types types)
  (define merged-row
    (filter-map
     (lambda (field) (merge-common-field types field))
     (second (first types))))
  (define merged-type (normalize-type `(Record ,merged-row)))
  (if merged-type
      (values merged-type
              (merge-witness-context types (second merged-type)))
      (values #f '())))

;; RFN-002: merge の局所検査。その merge が立てた W だけを候補文脈として、
;; 要求された常在性の義務が充足できるかを見る。型付けの受理条件ではなく、
;; merge ごとに成り立つ性質として検査する。
(define (merge-witnesses-dischargeable? types obligations)
  (define-values (merged witnesses) (merge-record-types types))
  (and merged
       (obligations-dischargeable? obligations witnesses)))

(define (infer-eliminate scrutinee branches environment places callables)
  (define scrutinee-result
    (infer scrutinee environment places callables))
  (and scrutinee-result
       (let* ([data-type (first scrutinee-result)]
              [contexts (branch-contexts branches data-type environment)])
         (and contexts
              (let* ([attempts
                      (for/list ([context (in-list contexts)])
                        (infer (first context)
                               (second context)
                               places
                               callables))]
                     [non-never
                      (and (andmap identity attempts)
                           (filter (lambda (result)
                                     (not (eq? (first result) 'Never)))
                                   attempts))]
                     [types (and non-never (map first non-never))]
                     [result-type
                      (cond
                        [(not types) #f]
                        [(null? types) 'Never]
                        [(andmap record-type? types)
                         ;; RFN-002: W は merge の局所検査だけで使う。型へは
                         ;; 載せないため、ここでは捨てる。
                         (define-values (merged _witnesses)
                           (merge-record-types types))
                         merged]
                        [(ormap record-type? types) #f]
                        [else (first types)])])
                (and result-type
                     (let ([branch-rows
                            (for/list ([context (in-list contexts)])
                              (check-as (first context)
                                        result-type
                                        (second context)
                                        places
                                        callables))])
                       (and (andmap identity branch-rows)
                            (list result-type
                                  (rows-union
                                   (cons (second scrutinee-result)
                                         branch-rows)))))))))))

(define (infer-lam callable parameters body
                   environment places callables)
  (define signature (lookup callables callable))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,_)
     (and (= (length parameters) (length parameter-types))
          (not (check-duplicates parameters))
          (not (ormap owned-type? parameter-types))
          (let* ([body-environment
                  (extend (without-owned environment)
                          parameters
                          parameter-types)]
                 [body-row
                  (check-as body return-type body-environment
                            places callables)])
            (and body-row
                 (row-subset? body-row latent-row)
                 (list signature '()))))]
    [_ #f]))

(define (infer-recur-value callable function parameters body
                           environment places callables)
  (define signature (lookup callables callable))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,_)
     (and (= (length parameters) (length parameter-types))
          (not (check-duplicates (cons function parameters)))
          (not (ormap owned-type? parameter-types))
          (let* ([body-environment
                  (extend
                   (extend (without-owned environment)
                           (list function)
                           (list signature))
                   parameters
                   parameter-types)]
                 [body-row
                  (check-as body return-type body-environment
                            places callables)])
            (and body-row
                 (row-subset? body-row latent-row)
                 (list signature '()))))]
    [_ #f]))

(define (recur-context callable function parameters body
                       environment places callables)
  (define signature (lookup callables callable))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,_)
     (and (= (length parameters) (length parameter-types))
          (not (check-duplicates (cons function parameters)))
          (not (ormap owned-type? parameter-types))
          (let* ([function-environment
                  (extend environment
                          (list function)
                          (list signature))]
                 [body-environment
                  (extend (without-owned function-environment)
                          parameters
                          parameter-types)]
                 [body-row
                  (check-as body return-type body-environment
                            places callables)])
            (and body-row
                 (row-subset? body-row latent-row)
                 function-environment)))]
    [_ #f]))

(define (binding-context binding-mode declared-type bound
                         environment places callables)
  (match declared-type
    [`(Record ,declared-row)
     (match (infer bound environment places callables)
       [(list 'Never bound-row)
        (list bound-row declared-type)]
       [(list `(Record ,actual-row) bound-row)
        (and (compat? `(Record ,actual-row) declared-type Γ-pc0)
             (let* ([residual
                     (field-row-residual actual-row declared-row)]
                    [binding-row
                     (case binding-mode
                       [(const) (and (null? residual) declared-row)]
                       [(let) (field-row-⊕ declared-row residual)]
                       [else #f])])
               (and binding-row
                    (list bound-row `(Record ,binding-row)))))]
       [_ #f])]
    [_
     (define bound-row
       (check-as bound declared-type environment places callables))
     (and bound-row (list bound-row declared-type))]))

(define (infer core environment places callables)
  (match core
    [(? integer?) (list 'Int '())]
    [(? string?) (list 'String '())]
    ['unit (list 'Unit '())]

    [`(Lam ,_ ,callable (,parameters ...) ,body)
     (infer-lam callable parameters body
                environment places callables)]

    [`(PrimVal ,_ ,name)
     (match (assoc name Γ0)
       [(list _ (list type canonical-value))
        (and (equal? canonical-value core)
             (list type '()))]
       [_ #f])]

    [`(CurryVal ,_ ,function ,argument)
     (match (infer function environment places callables)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              function-row)
        (define argument-row
          (check-as argument first-type environment places callables))
        (and (null? function-row)
             (not (owned-type? first-type))
             argument-row
             (null? argument-row)
             (list `(NFn ,remaining-types
                         ,return-type
                         ,latent-row
                         ,obligations)
                   '()))]
       [_ #f])]

    [`(RecurVal ,callable ,function (,parameters ...) ,body)
     (infer-recur-value callable function parameters body
                        environment places callables)]

    [`(TypeRep ,_ ,_ ,kind)
     (list `(TypeInfo ,kind) '())]

    [`(ProofRep ,_ ,proposition)
     (list `(Proof ,proposition) '())]

    [`(Construct ,data-type ,constructor ,fields ...)
     (define row
       (check-construct constructor fields data-type
                        environment places callables))
     (and row (list data-type row))]

    [`(resource ,_) (list '(Owned Res) '())]

    [`(Rec (,fields ...))
     (and (field-row-unique? fields)
          (let ([results
                 (for/list ([field (in-list fields)])
                   (infer (third field) environment places callables))])
            (and (andmap identity results)
                 (not (ormap (lambda (result)
                               (owned-type? (first result)))
                             results))
                 (list
                  `(Record
                    ,(for/list ([field (in-list fields)]
                                [result (in-list results)])
                       `(,(first field) ,(first result) ,(second field))))
                  (rows-union (map second results))))))]

    ;; RFN-001: 未検証の値。ペイロードの型をそのまま Untrusted で包む。
    ;; effect row はペイロードのものを引き継ぐ。
    [`(UVal ,value)
     (match (infer value environment places callables)
       [(list value-type value-row)
        (and (owned-free? value-type)
             (list `(Untrusted ,value-type) value-row))]
       [_ #f])]

    ;; RFN-001: 検証済みの値。witness の命題を型へ持ち上げる。発行者が正当か
    ;; どうかは成果物検証（verify-origins）の担当であり、ここでは見ない。
    [`(RVal (ProofRep ,_ ,proposition) ,value)
     (match (infer value environment places callables)
       [(list value-type value-row)
        (and (owned-free? value-type)
             (list `(Refined ,value-type ,proposition) value-row))]
       [_ #f])]

    [`(Proj ,record ,label)
     (match (infer record environment places callables)
       [(list `(Record ,row) record-row)
        (match (field-row-lookup row label)
          [(list field-type _) (list field-type record-row)]
          [_ #f])]
       [_ #f])]

    [`(Apply ,function ,arguments ...)
     (match (infer function environment places callables)
       [(list `(NFn ,parameter-types
                    ,return-type ,latent-row ,obligations)
              function-row)
        (define argument-rows
          (check-many arguments parameter-types
                      environment places callables))
        (and (obligations-dischargeable? obligations Γ-pc0)
             argument-rows
             (list return-type
                   (rows-union
                    (append (list function-row)
                            argument-rows
                            (list latent-row)))))]
       [_ #f])]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode type bound
                             environment places callables)
       [(list bound-row binding-type)
        (match (infer body
                      (extend environment (list name) (list binding-type))
                      places
                      callables)
          [(list body-type body-row)
           (list body-type (row-union bound-row body-row))]
          [_ #f])]
       [_ #f])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-row
       (check-as bound type environment places callables))
     (and bound-row
          (match (infer body
                        (extend environment (list name) (list type))
                        places
                        callables)
            [(list body-type body-row)
             (list body-type (row-union bound-row body-row))]
            [_ #f]))]

    [`(Eliminate ,scrutinee (,branches ...))
     (infer-eliminate scrutinee branches
                      environment places callables)]

    [`(Perform (Return ,boundary ,type) ,argument)
     (define argument-row
       (check-as argument type environment places callables))
     (and argument-row
          (list 'Never
                (row-union argument-row
                           `((Return ,boundary ,type)))))]

    [`(Handle (Return ,boundary ,type)
              (,name -> ,handler)
              ,body)
     (define body-row
       (check-as body type environment places callables))
     (define handler-row
       (check-as handler
                 type
                 (extend environment (list name) (list type))
                 places
                 callables))
     (and body-row
          handler-row
          (list type
                (row-union
                 (row-difference body-row
                                 `((Return ,boundary ,type)))
                 handler-row)))]

    [`(Scope (,managed-places ...) ,body)
     (and (andmap (λ (place) (assoc place places))
                  managed-places)
          (infer body environment places callables))]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable function parameters body
                      environment places callables))
     (and continuation-environment
          (infer continuation
                 continuation-environment
                 places
                 callables))]

    [`(Yield ,observed ,next)
     (match* ((infer observed environment places callables)
              (infer next environment places callables))
       [((list observed-type observed-row)
         (list next-type next-row))
        (list next-type
              (rows-union
               (list observed-row
                     next-row
                     `((Yield ,observed-type)))))]
       [(_ _) #f])]

    [`(Suspend ,body)
     (match (infer body environment places callables)
       [(list type row)
        (list type (row-union row '(Suspend)))]
       [_ #f])]

    [`(Move ,place)
     #:when (exact-nonnegative-integer? place)
     (define type (lookup places place))
     (and type (list `(Owned ,type) '(Own)))]

    [`(Move ,name)
     (match (lookup environment name)
       [`(Owned ,type) (list `(Owned ,type) '(Own))]
       [_ #f])]

    [`(Drop ,argument)
     (define argument-result
       (infer argument environment places callables))
     (cond
       [(and argument-result
             (owned-type? (first argument-result)))
        (list 'Unit
              (row-union (second argument-result) '(Own)))]
       [else
        (define argument-row
          (check-as argument '(Owned Res)
                    environment places callables))
        (and argument-row
             (list 'Unit (row-union argument-row '(Own))))])]

    [`(Curry ,function ,argument)
     (match (infer function environment places callables)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              function-row)
        (define argument-row
          (check-as argument first-type environment places callables))
        (and (not (owned-type? first-type))
             argument-row
             (list `(NFn ,remaining-types
                         ,return-type
                         ,latent-row
                         ,obligations)
                   (row-union function-row argument-row)))]
       [_ #f])]

    [`(Error ,_) #f]

    [(? symbol? name)
     (define type (lookup environment name))
     (and type
          (not (owned-type? type))
          (list type '()))]

    [_ #f]))

(define (check-as core expected environment places callables)
  (match core
    [`(Construct ,data-type ,constructor ,fields ...)
     (and (type-equiv? data-type expected)
          (check-construct constructor fields data-type
                           environment places callables))]

    [`(Error ,place)
     (and (exact-nonnegative-integer? place)
          (assoc place places)
          '())]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode type bound
                             environment places callables)
       [(list bound-row binding-type)
        (define body-row
          (check-as body
                    expected
                    (extend environment (list name) (list binding-type))
                    places
                    callables))
        (and body-row (row-union bound-row body-row))]
       [_ #f])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-row
       (check-as bound type environment places callables))
     (define body-row
       (check-as body
                 expected
                 (extend environment (list name) (list type))
                 places
                 callables))
     (and bound-row body-row (row-union bound-row body-row))]

    [`(Eliminate ,scrutinee (,branches ...))
     (check-eliminate scrutinee branches expected
                      environment places callables)]

    [`(Scope (,managed-places ...) ,body)
     (and (andmap (λ (place) (assoc place places))
                  managed-places)
          (check-as body expected environment places callables))]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable function parameters body
                      environment places callables))
     (and continuation-environment
          (check-as continuation
                    expected
                    continuation-environment
                    places
                    callables))]

    [`(Yield ,observed ,next)
     (define observed-result
       (infer observed environment places callables))
     (define next-row
       (check-as next expected environment places callables))
     (and observed-result
          next-row
          (rows-union
           (list (second observed-result)
                 next-row
                 `((Yield ,(first observed-result))))))]

    [`(Suspend ,body)
     (define body-row
       (check-as body expected environment places callables))
     (and body-row (row-union body-row '(Suspend)))]

    [_
     (match (infer core environment places callables)
       [(list actual row)
        (and (type-compatible? actual expected) row)]
       [_ #f])]))

(define (core-type-of core places callables [environment '()])
  (if (and (redex-match? G2m c core)
           (core-types-normal? core)
           (valid-environment? environment)
           (valid-places? places)
           (valid-callables? callables))
      (match (infer core environment places callables)
        [(list type row)
         (define normalized (normalize-type type))
         (if normalized (list normalized row) 'ill-typed)]
        [_ 'ill-typed])
      'ill-typed))

(define (core-check-row core places callables expected [environment '()])
  (and (redex-match? G2m c core)
       (core-types-normal? core)
       (valid-environment? environment)
       (valid-places? places)
       (valid-callables? callables)
       (type? expected)
       (check-as core expected environment places callables)))

(define (core-check core places callables expected row [environment '()])
  (and (row? row)
       (let ([actual-row
              (core-check-row core places callables expected environment)])
         (and actual-row (row=? actual-row row)))))

(define (config-ok? configuration callables expected row)
  (and (redex-match? G2m config configuration)
       (core-types-normal? configuration)
       (valid-callables? callables)
       (type? expected)
       (row? row)
       (match configuration
         [`(cfg ,core ,heap ,states ,_)
          (and (unique-table? heap)
               (unique-table? states)
               (equal? (sort (map first heap) <)
                       (sort (map first states) <))
               ;; G1 has only resource(n) : Owned<Res>.  G5 must derive Ξ
               ;; from richer heap value types instead of this constant map.
               (let ([places
                      (for/list ([entry (in-list heap)])
                        (list (first entry) 'Res))])
                 (and
                  (for/and ([entry (in-list heap)])
                    (define value-row
                      (check-as (second entry)
                                '(Owned Res)
                                '()
                                places
                                callables))
                    (and value-row (null? value-row)))
                  (let ([actual-row
                         (check-as core expected '()
                                   places callables)])
                    (and actual-row (row=? actual-row row))))))]
         [_ #f])))

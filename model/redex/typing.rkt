#lang racket

(require racket/match
         redex/reduction-semantics
         "compat.rkt"
         "diagnostic.rkt"
         "erase.rkt"
         "lang.rkt"
         "origins.rkt"
         "policy.rkt"
         "rows.rkt"
         "schema.rkt"
         "search.rkt"
         "span-core.rkt"
         "type-equiv.rkt"
         "type-shape.rkt"
         "validators.rkt")

(provide core-type-of
         core-type-of/diagnostic
         core-check
         core-check-row
         config-ok?
         join-types
         merge-field
         presence-binding-name
         field-type-binding-name
         merge-record-types
         check-merge-return
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

(define (check-many cores types environment places callables node fail)
  (unless (= (length cores) (length types))
    (fail 'arity-mismatch node (length types) (length cores)))
  (for/list ([core (in-list cores)]
             [type (in-list types)])
    (check-as core type environment places callables fail)))

(define (check-construct constructor fields data-type
                         environment places callables node fail)
  ;; 呼び出し側は G2+ の ts、つまり (#:ty τ s) を包みのまま渡す。
  ;; 剥がす位置をここに 1 つだけ置き、以降は実型だけを使う。
  (define actual-type (peel-ty data-type))
  (define schema (constructor-schema actual-type))
  (unless schema (fail 'unknown-data-type node actual-type))
  (define field-types (lookup schema constructor))
  (unless field-types (fail 'unknown-constructor node constructor))
  (for ([field-type (in-list field-types)])
    (when (owned-type? field-type)
      (fail 'owned-constructor-field node field-type)))
  (define rows
    (check-many fields field-types environment places callables node fail))
  (rows-union rows))

(define (branch-contexts branches data-type environment node scrutinee fail)
  (define schema (constructor-schema data-type))
  (unless schema (fail 'non-data-eliminate scrutinee))
  (unless (= (length branches) (length schema))
    (fail 'non-exhaustive-eliminate node))
  (define plain-branches (map peel-branch branches))
  (for ([branch (in-list branches)]
        [plain (in-list plain-branches)])
    (unless (redex-match? G2m br plain)
      (fail 'ill-typed branch)))
  (define expected-constructors (map first schema))
  (define actual-constructors (map first plain-branches))
  (when (check-duplicates actual-constructors)
    (fail 'duplicate-branch-constructor node))
  (for ([constructor (in-list expected-constructors)])
    (unless (member constructor actual-constructors)
      (fail 'non-exhaustive-eliminate node)))
  (for ([branch (in-list plain-branches)])
    (match-define `(,constructor (,parameters ...) -> ,_) branch)
    (define field-types (lookup schema constructor))
    (unless field-types (fail 'unknown-constructor branch constructor))
    (unless (= (length parameters) (length field-types))
      (fail 'branch-binder-arity branch (length field-types) (length parameters)))
    (when (check-duplicates (map peel-bind parameters))
      (fail 'duplicate-branch-binder branch)))
  (for/list ([branch (in-list plain-branches)])
    (match-define `(,constructor (,parameters ...) -> ,body) branch)
    (list body
          (extend environment
                  (map peel-bind parameters)
                  (lookup schema constructor)))))

(define (check-eliminate scrutinee branches expected
                         environment places callables node fail)
  (define scrutinee-result
    (infer scrutinee environment places callables fail))
  (define data-type (first scrutinee-result))
  (define contexts
    (branch-contexts branches data-type environment node scrutinee fail))
  (define branch-rows
    (for/list ([context (in-list contexts)])
      (check-as (first context)
                expected
                (second context)
                places
                callables
                fail)))
  (rows-union (cons (second scrutinee-result) branch-rows)))

;; CMP-001: 2 つの型を Union で合わせ、同値な構成要素を正規化で畳む。
(define (join-types left right)
  (normalize-type `(Union ,left ,right)))

;; CMP-001/ROW-005: 同じ label を持つ field を合わせる。
;; 異型があれば mut を imm へ降格したうえで Union join する。
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
  ;; 全枝が mut のときにだけ mut を保つ。1 枝でも imm なら、書き込みが
  ;; imm 枝の不変性を破りうるため imm へ落とす。
  (define all-mutable?
    (for/and ([field (in-list fields)]) (eq? (third field) 'mut)))
  (define types (distinct-normal-types (map second fields)))
  (and
   (for/and ([field (in-list fields)])
     (eq? (first field) label))
   types
   (cond
     [(null? (rest types))
      (list label (first types) (if all-mutable? 'mut 'imm))]
     ;; 異型は可変性によらず imm へ降格して join する。降格後は read-only で
     ;; あり、join 型の値を書き戻して枝の型を破る経路が無い。
     [else
      (define joined
        (for/fold ([joined (first types)])
                  ([type (in-list (rest types))])
          (join-types joined type)))
      (and joined (list label joined 'imm))])))

;; ROW-005: 返り値は 3 状態である。field 行なら合流成功、'absent は「どれかの
;; branch にこの field が無い」正常な脱落、#f は正規化または join の失敗であり
;; merge 全体の fail-closed へ伝播する。
;; 両者を #f で兼ねると、失敗が脱落として黙って握り潰される。
(define (merge-common-field types first-field)
  (define label (first first-field))
  (define fields
    (for/list ([type (in-list types)])
      (assoc label (second type))))
  (if (andmap values fields)
      (merge-fields fields)
      'absent))

;; RFN-002/CMP-001/ROW-005: 全 branch に常在する field を合わせる。異型は imm
;; へ降格して Union join する。どれかの branch に無い field だけが落ちる。
;; types は空でないことを呼び出し側が保証する。
(define (merge-record-types/impl types)
  (define merged-fields
    (for/list ([field (in-list (second (first types)))])
      (merge-common-field types field)))
  (cond
    [(memq #f merged-fields) (values #f '())]
    [else
     (define merged-row
       (filter (lambda (field) (not (eq? field 'absent))) merged-fields))
     (define merged-type (normalize-type `(Record ,merged-row)))
     (if merged-type
         (values merged-type
                 (merge-witness-context types (second merged-type)))
         (values #f '()))]))

;; POL-002/ROW-004: 合流 row の label は一意で昇順、witness 列は wf-context? を
;; 満たし束縛名が重複しない。#f だけが fail-closed 返却である。(Record ()) は
;; 共通 field が残らない正常な合流であり、成功返却として不変条件を適用する。
;; 両者を同じ形と見なすと、正規化失敗が「空 row の合流に成功した」として素通り
;; する。
;; ROW-005 以降、#f は merge-common-field から伝播した正規化・join の失敗と、
;; 合流 row 自身の正規化失敗の 2 経路で立つ。
(define (check-merge-return args returns)
  (match returns
    [(list #f '()) #t]
    [(list `(Record ,row) witnesses)
     (define labels (map first row))
     (define names (map first witnesses))
     (and (field-row-unique? row)
          (equal? labels (sort labels symbol<?))
          (wf-context? witnesses)
          (= (length names) (length (remove-duplicates names))))]
    [_ #f]))

(define merge-record-types
  (policy-wrap 'RowPolicy 'merge-record-types
               merge-record-types/impl
               check-merge-return))

;; RFN-002: merge の局所検査。その merge が立てた W だけを候補文脈として、
;; 要求された常在性の義務が充足できるかを見る。型付けの受理条件ではなく、
;; merge ごとに成り立つ性質として検査する。
(define (merge-witnesses-dischargeable? types obligations)
  (define-values (merged witnesses) (merge-record-types/impl types))
  (and merged
       (obligations-dischargeable? obligations witnesses)))

(define (infer-eliminate scrutinee branches environment places callables node fail)
  (define scrutinee-result
    (infer scrutinee environment places callables fail))
  (define data-type (first scrutinee-result))
  (define contexts
    (branch-contexts branches data-type environment node scrutinee fail))
  (define attempts
    (for/list ([context (in-list contexts)])
      (infer (first context)
             (second context)
             places
             callables
             fail)))
  (define non-never
    (filter (lambda (result)
              (not (eq? (first result) 'Never)))
            attempts))
  (define types (map first non-never))
  (define result-type
    (cond
      [(null? types) 'Never]
      [(andmap record-type? types)
       ;; RFN-002: W は merge の局所検査だけで使う。型へは載せない。
       (define-values (merged _witnesses)
         (merge-record-types/impl types))
       (unless merged (fail 'unmergeable-branch-records node))
       merged]
      [(ormap record-type? types)
       (fail 'incompatible-branch-types node)]
      [else (first types)]))
  (define branch-rows
    (for/list ([context (in-list contexts)])
      (check-as (first context)
                result-type
                (second context)
                places
                callables
                fail)))
  (list result-type
        (rows-union
         (cons (second scrutinee-result) branch-rows))))

(define (infer-lam callable parameters body
                   environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,_)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates parameters)
       (fail 'duplicate-parameter node))
     (when (ormap owned-type? parameter-types)
       (fail 'owned-function-parameter node))
     (define body-environment
       (extend (without-owned environment)
               parameters
               parameter-types))
     (define body-row
       (check-as body return-type body-environment
                 places callables fail))
     (unless (row-subset? body-row latent-row)
       (fail 'undeclared-function-effect body body-row latent-row))
     (list signature '())]
    ;; valid-callables? が表の各行を (NFn ...) に限るため、入口を通った呼び出しは
    ;; ここへ到達しない。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

(define (infer-recur-value callable function parameters body
                           environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,_)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates (cons function parameters))
       (fail 'duplicate-parameter node))
     (when (ormap owned-type? parameter-types)
       (fail 'owned-function-parameter node))
     (define body-environment
       (extend
        (extend (without-owned environment)
                (list function)
                (list signature))
        parameters
        parameter-types))
     (define body-row
       (check-as body return-type body-environment
                 places callables fail))
     (unless (row-subset? body-row latent-row)
       (fail 'undeclared-function-effect body body-row latent-row))
     (list signature '())]
    ;; valid-callables? が表の各行を (NFn ...) に限るため、入口を通った呼び出しは
    ;; ここへ到達しない。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

(define (recur-context callable function parameters body
                       environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,_)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates (cons function parameters))
       (fail 'duplicate-parameter node))
     (when (ormap owned-type? parameter-types)
       (fail 'owned-function-parameter node))
     (define function-environment
       (extend environment
               (list function)
               (list signature)))
     (define body-environment
       (extend (without-owned function-environment)
               parameters
               parameter-types))
     (define body-row
       (check-as body return-type body-environment
                 places callables fail))
     (unless (row-subset? body-row latent-row)
       (fail 'undeclared-function-effect body body-row latent-row))
     function-environment]
    ;; valid-callables? が表の各行を (NFn ...) に限るため、入口を通った呼び出しは
    ;; ここへ到達しない。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

(define (binding-context binding-mode declared-type bound
                         environment places callables node fail)
  (match declared-type
    [`(Record ,declared-row)
     (match (infer bound environment places callables fail)
       [(list 'Never bound-row)
        (list bound-row declared-type)]
       [(list `(Record ,actual-row) bound-row)
        (unless (compat? `(Record ,actual-row) declared-type Γ-pc0)
          (fail 'record-binding-incompatible bound))
        (define residual
          (field-row-residual actual-row declared-row))
        (define binding-row
          (case binding-mode
            [(const)
             (if (null? residual)
                 declared-row
                 (fail 'const-record-residual bound residual))]
            [(let)
             (field-row-⊕ declared-row residual)]
            [else (fail 'ill-typed node)]))
        ;; field-row-residual は declared-row のラベルを除いた残余を返すため、
        ;; field-row-⊕ の重複検査はここでは破れない。表の整合を保つため、
        ;; 到達しないこの位置は先の compat? 検査と key を共有する。
        (unless binding-row (fail 'record-binding-incompatible bound))
        (list bound-row `(Record ,binding-row))]
       [(list actual-type _)
        (fail 'type-mismatch bound actual-type declared-type)])]
    [_
     (define bound-row
       (check-as bound declared-type environment places callables fail))
     (list bound-row declared-type)]))

;; PRF-004: Discharge の連なりを外側から剥がし、(φ 列, 基底) を返す。
;; 型付けを連なりの全体で見るため、節の側では再帰しない。
(define (peel-discharge core)
  (let loop ([core core] [propositions '()])
    (match (peel-node core)
      [`(Discharge ,proof-rep ,inner)
       (match (peel-node proof-rep)
         [`(ProofRep ,_ ,phi)
          (loop inner (cons phi propositions))]
         [_ (values (reverse propositions) core)])]
      [_ (values (reverse propositions) core)])))

;; spec §6: 失敗は返り値ではなく脱出継続で運ぶ。struct を返すと真値になり、
;; 既存の and と andmap と for/and の短絡が失敗を成功として通す。
;; lowering.rkt:88 の with-diagnostics と同じ機構である。
;; 局所回復の callback も同じ検査を通すため、key 検査を単独の手続きにする。
;; callback の中へ書き写すと、片方だけ直したときに未登録 key が素通りする。
(define (assert-typing-key key)
  (unless (diagnostic-code-of 'typing key)
    (error 'fail "registry に無い typing の key である: ~s" key)))

(define (with-typing proc)
  (let/ec escape
    (define (fail key node . details)
      (assert-typing-key key)
      (escape (list 'fail key node details)))
    (list 'ok (proc fail))))

;; 脱出を捕まえて従来の #f へ潰す。core-check-row と config-ok? が使う。
(define (check-as/boolean core expected environment places callables)
  (match (with-typing
          (lambda (fail)
            (check-as core expected environment places callables fail)))
    [(list 'ok row) row]
    [_ #f]))

(define (infer core environment places callables fail)
  (match (peel-node core)
    [(? integer?) (list 'Int '())]
    [(? string?) (list 'String '())]
    ['unit (list 'Unit '())]

    [`(Lam ,_ ,callable (,parameters ...) ,body)
     (infer-lam callable (map peel-bind parameters) body
                environment places callables core fail)]

    [`(PrimVal ,_ ,name)
     (match (assoc name Γ0)
       [(list _ (list type canonical-value))
        (unless (equal? canonical-value (peel-node core))
          (fail 'non-canonical-primitive core))
        (list type '())]
       [_ (fail 'unknown-primitive core)])]

    [`(CurryVal ,_ ,function ,argument)
     (match (infer function environment places callables fail)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              function-row)
        (unless (null? function-row)
          (fail 'effectful-curry-operand function))
        (when (owned-type? first-type)
          (fail 'owned-curry-argument argument))
        (define argument-row
          (check-as argument first-type environment places callables fail))
        (unless (null? argument-row)
          (fail 'effectful-curry-operand argument))
        (list `(NFn ,remaining-types
                    ,return-type
                    ,latent-row
                    ,obligations)
              '())]
       [_ (fail 'curry-non-function function)])]

    [`(RecurVal ,callable ,function (,parameters ...) ,body)
     (infer-recur-value callable (peel-bind function)
                        (map peel-bind parameters) body
                        environment places callables core fail)]

    [`(TypeRep ,_ ,_ ,kind)
     (list `(TypeInfo ,kind) '())]

    [`(ProofRep ,_ ,proposition)
     (list `(Proof ,proposition) '())]

    [`(Construct ,data-type ,constructor ,fields ...)
     (define row
       (check-construct constructor fields data-type
                        environment places callables core fail))
     (list (peel-ty data-type) row)]

    [`(resource ,_) (list '(Owned Res) '())]

    [`(Rec (,fields ...))
     (define plain-fields
       (for/list ([field (in-list fields)])
         (list (peel-lbl (first field))
               (second field)
               (third field))))
     (unless (field-row-unique? plain-fields)
       (fail 'duplicate-record-label core))
     (define results
       (for/list ([field (in-list plain-fields)])
         (infer (third field) environment places callables fail)))
     (for ([field (in-list plain-fields)]
           [result (in-list results)])
       (when (owned-type? (first result))
         (fail 'owned-record-field (third field))))
     (list
      `(Record
        ,(for/list ([field (in-list plain-fields)]
                    [result (in-list results)])
           `(,(first field) ,(first result) ,(second field))))
      (rows-union (map second results)))]

    ;; RFN-001: 未検証の値。ペイロードの型をそのまま Untrusted で包む。
    ;; effect row はペイロードのものを引き継ぐ。
    [`(UVal ,value)
     (match (infer value environment places callables fail)
       [(list value-type value-row)
        (unless (owned-free? value-type)
          (fail 'owned-untrusted-payload value))
        (list `(Untrusted ,value-type) value-row)])]

    ;; RFN-001: 検証済みの値。witness の命題を型へ持ち上げる。発行者が正当か
    ;; どうかは成果物検証（verify-origins）の担当であり、ここでは見ない。
    [`(RVal ,proof-rep ,value)
     (match (peel-node proof-rep)
       [`(ProofRep ,_ ,proposition)
        (match (infer value environment places callables fail)
          [(list value-type value-row)
           (unless (owned-free? value-type)
             (fail 'owned-refined-payload value))
           (list `(Refined ,value-type ,proposition) value-row)])]
       [_ (fail 'ill-typed core)])]

    [`(Proj ,record ,label)
     (match (infer record environment places callables fail)
       [(list `(Record ,row) record-row)
        (match (field-row-lookup row (peel-lbl label))
          [(list field-type _) (list field-type record-row)]
          [_ (fail 'unknown-record-label core)])]
       [_ (fail 'project-non-record record)])]

    [`(Apply ,function ,arguments ...)
     (match (infer function environment places callables fail)
       [(list `(NFn ,parameter-types
                    ,return-type ,latent-row ,obligations)
              function-row)
        (define argument-rows
          (check-many arguments parameter-types
                      environment places callables core fail))
        (unless (obligations-dischargeable? obligations Γ-pc0)
          (fail 'unsatisfied-proof-obligation core))
        (list return-type
              (rows-union
               (append (list function-row)
                       argument-rows
                       (list latent-row))))]
       [_ (fail 'apply-non-function function)])]

    [`(Discharge ,_ ,_)
     ;; 包み先を直接の Apply に限る形は採れない。複数義務では外側の Discharge
     ;; の包み先が Discharge になり、生成する形を自分で拒否してしまう。
     ;; 素通しの規則も採れない。当該の Apply と無関係な正当な ProofRep を手書き
     ;; で包んだ項が検証を通る。PRF-004 が要求するのは選択した Proof の
     ;; provenance であるから、φ 列と義務列の対応をここで固定する。
     (define-values (propositions base) (peel-discharge core))
     (match (peel-node base)
       [`(Apply ,function ,_ ...)
        (match (infer function environment places callables fail)
          [(list `(NFn ,_ ,_ ,_ ,obligations) _)
           (unless (= (length propositions) (length obligations))
             (fail 'discharge-obligation-count core))
           (for ([phi (in-list propositions)]
                 [obligation (in-list obligations)])
             (unless (proposition-equiv? phi obligation)
               (fail 'discharge-proposition-mismatch core)))
           ;; 型と Effect 行は基底の Apply のものを返す。
           (infer base environment places callables fail)]
          [_ (fail 'apply-non-function function)])]
       [_ (fail 'discharge-target-not-apply base)])]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound
                             environment places callables core fail)
       [(list bound-row binding-type)
        (match (infer body
                      (extend environment (list (peel-bind name))
                              (list binding-type))
                      places
                      callables
                      fail)
          [(list body-type body-row)
           (list body-type (row-union bound-row body-row))])])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-row
       (check-as bound (peel-ty type) environment places callables fail))
     (match (infer body
                   (extend environment
                           (list (peel-bind name))
                           (list (peel-ty type)))
                   places
                   callables
                   fail)
       [(list body-type body-row)
        (list body-type (row-union bound-row body-row))])]

    [`(Eliminate ,scrutinee (,branches ...))
     (infer-eliminate scrutinee branches
                      environment places callables core fail)]

    [`(Perform (Return ,boundary ,type) ,argument)
     (define type* (peel-ty type))
     (define argument-row
       (check-as argument type* environment places callables fail))
     (list 'Never
           (row-union argument-row
                      `((Return ,boundary ,type*))))]

    [`(Handle (Return ,boundary ,type) ,handler-clause ,body)
     (define type* (peel-ty type))
     (define body-row
       (check-as body type* environment places callables fail))
     (define handler-row
       (match (peel-branch handler-clause)
         [`(,name -> ,handler)
          (check-as handler
                    type*
                    (extend environment (list (peel-bind name)) (list type*))
                    places
                    callables
                    fail)]
         [_ (fail 'ill-typed core)]))
     (list type*
           (row-union
            (row-difference body-row
                            `((Return ,boundary ,type*)))
            handler-row))]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (infer body environment places callables fail)]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      environment places callables core fail))
     (infer continuation continuation-environment places callables fail)]

    [`(Yield ,observed ,next)
     (define observed-result
       (infer observed environment places callables fail))
     (define next-result
       (infer next environment places callables fail))
     (list (first next-result)
           (rows-union
            (list (second observed-result)
                  (second next-result)
                  `((Yield ,(first observed-result))))))]

    [`(Suspend ,body)
     (define result (infer body environment places callables fail))
     (list (first result) (row-union (second result) '(Suspend)))]

    [`(Move ,place)
     #:when (exact-nonnegative-integer? place)
     (define type (lookup places place))
     (unless type (fail 'unknown-place core))
     (list `(Owned ,type) '(Own))]

    [`(Move ,name)
     (define type (lookup environment (peel-node name)))
     (unless type (fail 'unbound-variable core))
     (match type
       [`(Owned ,inner-type) (list `(Owned ,inner-type) '(Own))]
       [_ (fail 'move-non-owned core)])]

    [`(Drop ,argument)
     (define argument-result
       (let/ec recover
         (infer argument environment places callables
                (lambda (key node . details)
                  (assert-typing-key key)
                  (recover #f)))))
     (cond
       [(and argument-result
             (owned-type? (first argument-result)))
        (list 'Unit
              (row-union (second argument-result) '(Own)))]
       [else
        (define argument-row
          (check-as argument '(Owned Res)
                    environment places callables
                    (lambda (key node . details)
                      (assert-typing-key key)
                      (if (and (eq? key 'type-mismatch)
                               (eq? node argument))
                          (fail 'drop-non-owned argument)
                          (apply fail key node details)))))
        (list 'Unit (row-union argument-row '(Own)))])]

    [`(Curry ,function ,argument)
     (match (infer function environment places callables fail)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              function-row)
        (when (owned-type? first-type)
          (fail 'owned-curry-argument argument))
        (define argument-row
          (check-as argument first-type environment places callables fail))
        (list `(NFn ,remaining-types
                    ,return-type
                    ,latent-row
                    ,obligations)
              (row-union function-row argument-row))]
       [_ (fail 'curry-non-function function)])]

    [`(Error ,_) (fail 'error-needs-expected-type core)]

    [(? symbol? name)
     (define type (lookup environment name))
     (unless type (fail 'unbound-variable core))
     (when (owned-type? type) (fail 'owned-variable-requires-move core))
     (list type '())]

    [_ (fail 'ill-typed core)]))

(define (check-as core expected environment places callables fail)
  (match (peel-node core)
    [`(Construct ,data-type ,constructor ,fields ...)
     (define actual (peel-ty data-type))
     (unless (type-equiv? actual expected)
       (fail 'type-mismatch core actual expected))
     (check-construct constructor fields data-type
                      environment places callables core fail)]

    [`(Error ,place)
     (unless (and (exact-nonnegative-integer? place)
                  (assoc place places))
       (fail 'unknown-place core))
     '()]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound
                             environment places callables core fail)
       [(list bound-row binding-type)
        (define body-row
          (check-as body
                    expected
                    (extend environment (list (peel-bind name))
                            (list binding-type))
                    places
                    callables
                    fail))
        (row-union bound-row body-row)])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-row
       (check-as bound (peel-ty type) environment places callables fail))
     (define body-row
       (check-as body
                 expected
                 (extend environment
                         (list (peel-bind name))
                         (list (peel-ty type)))
                 places
                 callables
                 fail))
     (row-union bound-row body-row)]

    [`(Eliminate ,scrutinee (,branches ...))
     (check-eliminate scrutinee branches expected
                      environment places callables core fail)]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (check-as body expected environment places callables fail)]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      environment places callables core fail))
     (check-as continuation
               expected
               continuation-environment
               places
               callables
               fail)]

    [`(Yield ,observed ,next)
     (define observed-result
       (infer observed environment places callables fail))
     (define next-row
       (check-as next expected environment places callables fail))
     (rows-union
      (list (second observed-result)
            next-row
            `((Yield ,(first observed-result)))))]

    [`(Suspend ,body)
     (define body-row
       (check-as body expected environment places callables fail))
     (row-union body-row '(Suspend))]

    [_
     (match (infer core environment places callables fail)
       [(list actual row)
        (unless (type-compatible? actual expected)
          (fail 'type-mismatch core actual expected))
        row])]))

(define (type-of/raw core-in places callables [environment '()])
  (with-typing
   (lambda (fail)
     ;; span.md §7.3: 入口検査だけ投影し、走査は spanful な項へ行う。
     (define core (erase-core core-in))
     (unless (redex-match? G2m c core)
       (fail 'not-core-term core-in))
     (unless (core-types-normal? core)
       (fail 'non-normal-type core-in))
     (unless (valid-environment? environment)
       (fail 'invalid-environment core-in environment))
     (unless (valid-places? places)
       (fail 'invalid-places core-in places))
     (unless (valid-callables? callables)
       (fail 'invalid-callables core-in callables))
     (match (infer core-in environment places callables fail)
       [(list type row)
        (define normalized (normalize-type type))
        (unless normalized
          (fail 'non-normalizable-result-type core-in type))
        (list normalized row)]))))

(define (core-type-of core-in places callables [environment '()])
  (match (type-of/raw core-in places callables environment)
    [(list 'ok result) result]
    [_ 'ill-typed]))

;; spec §8: Diagnostic を組む位置はここ 1 箇所だけである。
;; expected と found の分配は G4d spec §6 の既定に従い、意味が確定している key
;; だけを例外表で扱う。引数順は elaborate.rkt:50-60 の同名 key に揃える。
(define (typing-expected/found key details)
  (match* (key details)
    [('type-mismatch (list actual expected)) (values expected actual)]
    [((or 'arity-mismatch 'parameter-arity-mismatch 'branch-binder-arity)
      (list expected actual))
     (values expected actual)]
    [('undeclared-function-effect (list residual declared))
     (values declared residual)]
    [(_ '()) (values #f #f)]
    [(_ (list only)) (values #f only)]
    [(_ _) (values #f details)]))

(define (typing-diagnostic key node details)
  (define-values (expected found) (typing-expected/found key details))
  (diagnostic-of 'typing key
                #:primary-span (entry-span node)
                #:expected expected
                #:found found))

;; spec §3: G4d2 の公開 Diagnostic 境界はこの adapter である。
;; core-type-of は 'ill-typed を返す低レベルの判定として残し、判定 API と診断 API
;; を混ぜない。
;; primary-span は fail が運ぶ棄却節点から取る。entry-span が span を取れないときだけ
;; synthetic fallback へ落ちる。
(define (core-type-of/diagnostic core-in places callables [environment '()])
  (match (type-of/raw core-in places callables environment)
    [(list 'ok (list type row)) (list type row)]
    [(list 'fail key node details) (typing-diagnostic key node details)]))

(define (core-check-row core-in places callables expected [environment '()])
  ;; span.md §7.3: core-type-of と同じく、既存の型走査へ渡す前に投影する。
  (define core (erase-core core-in))
  (and (redex-match? G2m c core)
       (core-types-normal? core)
       (valid-environment? environment)
       (valid-places? places)
       (valid-callables? callables)
       (type? expected)
       (check-as/boolean core-in expected environment places callables)))

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
                      (check-as/boolean (second entry)
                                        '(Owned Res)
                                        '()
                                        places
                                        callables))
                    (and value-row (null? value-row)))
                  (let ([actual-row
                         (check-as/boolean core expected '()
                                           places callables)])
                    (and actual-row (row=? actual-row row))))))]
         [_ #f])))

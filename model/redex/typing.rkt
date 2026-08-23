#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "borrow.rkt"
         "compat.rkt"
         "diagnostic.rkt"
         "erase.rkt"
         "lang.rkt"
         "origins.rkt"
         "policy.rkt"
         "region.rkt"
         "region-param.rkt"
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
         type-of/raw
         typing-visited-points
         config-ok?
         join-types
         merge-field
         presence-binding-name
         field-type-binding-name
         merge-record-types/impl
         merge-record-types
         check-merge-return
         merge-witnesses-dischargeable?
         lifetime-unify-context
         unify-borrow-lifetimes
         with-lifetime-unify
         merge-position
         merge-alpha-sources
         lifetime-counter
         alpha-table
         register-owner
         lifetime-collector
         emit-constraint!
         collected-constraints
         with-lifetime-collector
         collect-use-regions!
         typing-inference
         typing-solve
         sigma-ref
         subst-type-regions
         capability-source
         contains-lifetime-var?
         materialize-fail-result
         core-type-of/materialized)

;; 段 1 の試験専用。既定は何もしない。
;; 本体の走査へ観測を混ぜないため、probe の呼出しは infer と check-as の入口、
;; および Discharge の層を降りる loop の 3 箇所に限る。
(define typing-point-probe (make-parameter void))

;; 制約の収集器（spec §5.2）。既定は #f であり、その場合は何も記録しない。
;; G4b が入れた typing-point-probe と同じ形の記録先である。
;; 走査の各段へ手を入れず、infer の出口 1 か所で集める。
(define lifetime-collector (make-parameter #f))

(define (emit-constraint! c)
  (define b (lifetime-collector))
  (when b (set-box! b (cons c (unbox b)))))

(define (collected-constraints)
  (define b (lifetime-collector))
  (if b (reverse (unbox b)) '()))

(define (with-lifetime-collector thunk)
  (define b (box '()))
  (parameterize ([lifetime-collector b]) (thunk))
  (reverse (unbox b)))

;; 判定の要求の収集器（spec §7.3）。既定は #f であり、その場合は何も記録しない。
(define request-collector (make-parameter #f))

(define (emit-request! r)
  (define b (request-collector))
  (when b (set-box! b (cons r (unbox b)))))

(define (collected-requests)
  (define b (request-collector))
  (if b (reverse (unbox b)) '()))

;; 使用の要求を立てる。ir が無い形では借用も無いので何もしない。
;; fp/operation/source/node/kind は要求の契約なので必須にする。
(define (emit-use-request! Λ w fp operation source node kind [otherwise #f])
  (define ir (region-ctx-ir Λ))
  (when ir
    (emit-request!
     (use-request w fp operation source
                  (region-at ir (region-ctx-point Λ)) node kind otherwise))))

;; 段 2。下限制約から σ を作る。spec §6.1。
;; ir が無い形では借用が立たないので、制約も空であり σ も空である。
(define (typing-solve ir constraints)
  (if ir
      (region-solve ir constraints)
      (list 'ok (hash))))

;; σ を読む唯一の窓口。寿命変数なら引き、具体的な region ならそのまま返す。
(define (sigma-ref σ t)
  (if (lifetime-var? t)
      (hash-ref σ (lifetime-var-index t))
      t))

;; 型が運び手である（spec §5.1）。
;; point π で推論した型の中に α が現れるなら region-at ir π は α の下限である。
;; 値の流れを別に追う解析を書くと、型の側と二重に管理することになる。
(define (collect-use-regions! type ir point)
  (when (and ir (lifetime-collector))
    (define ρ (region-at ir point))
    (let walk ([t type])
      (match t
        [`(RVar ,k)
         (emit-constraint!
          (region-constraint 'contains `(RVar ,k) ρ point #f))]
        [(? list? ts) (for-each walk ts)]
        [_ (void)]))))

;; 寿命変数の採番（spec §3.2）。借用の項 1 つにつき 1 つ作る。
;; 番号は走査の順に依存するため、診断の本文へ番号を出してはならない
;; （region.md §2 の識別子の不透明性）。
(define lifetime-counter (make-parameter #f))
(define alpha-table (make-parameter #f))

(define (fresh-lifetime! point)
  (define c (lifetime-counter))
  (define k (unbox c))
  (set-box! c (add1 k))
  (unless (and (pair? point) (eq? (car point) 'merge))
    (define t (alpha-table))
    (when t (set-box! t (hash-set (unbox t) point `(RVar ,k)))))
  `(RVar ,k))

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
;; region どうしの関係は current-region-relation から取る。既定は equal? で
;; あり、region 引数を書かない programme の判定は変わらない。
(define (type-compatible? actual expected)
  (compat? actual expected Γ-pc0 (current-region-relation)))

;; ROW-005。Eliminate が作った Union の導入点だけで、各枝の具体型を
;; 合流型の成分として再照合する。一般の mut field 互換性は不変のままにし、
;; Assign の全成分検査へこの緩和を漏らさない。
;; mut の否定側は fail-closed の番人である。infer-eliminate の expected は
;; 常に枝型の merge なので、well-formed な枝では member 性が構造的に成り立つ。
;; この側は将来の不正な拡張を黙って受理しないために残す。
(define (merge-branch-compatible? actual expected)
  (define (union-type? type)
    (and (pair? type) (eq? (first type) 'Union)))
  (define (union-members-compatible? actual expected)
    (and (union-type? expected)
         (for/and ([actual-member
                    (in-list (if (union-type? actual)
                                 (union-members actual)
                                 (list actual)))])
           (for/or ([expected-member (in-list (union-members expected))])
             (type-equiv? actual-member expected-member)))))
  (match* (actual expected)
    [('Never _) #t]
    [((list 'Record actual-row) (list 'Record expected-row))
     (for/and ([field (in-list expected-row)])
       (match field
         [`(,label ,expected-type ,expected-mode)
          (match (field-row-lookup actual-row label)
            [`(,actual-type ,actual-mode)
             (case expected-mode
               [(imm) (and (memq actual-mode '(imm mut))
                           (type-compatible? actual-type expected-type))]
               [(mut) (and (eq? actual-mode 'mut)
                           (or (type-equiv? actual-type expected-type)
                               (union-members-compatible?
                                actual-type expected-type)))]
               [else #f])]
            [_ #f])]
         [_ #f]))]
    [(_ _) (type-compatible? actual expected)]))

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

(define (check-many cores types Λ Ψ environment places callables node fail
                    [start-index 0])
  (unless (= (length cores) (length types))
    (fail 'arity-mismatch node (length types) (length cores)))
  (let loop ([cores cores]
             [types types]
             [i start-index]
             [current-psi Ψ]
             [rows '()])
    (if (null? cores)
        (list (reverse rows) current-psi)
        (match (check-as (first cores)
                         (first types)
                         (enter-child Λ i)
                         current-psi
                         environment places callables fail)
          [(list row next-psi)
           (loop (rest cores)
                 (rest types)
                 (add1 i)
                 next-psi
                 (cons row rows))]))))

(define (check-construct constructor fields data-type
                         Λ Ψ environment places callables node fail)
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
  (match (check-many fields field-types Λ Ψ environment places callables node fail)
    [(list rows next-psi)
     (list (rows-union rows) next-psi)]))

(define (branch-contexts branches data-type Λ environment node scrutinee fail)
  (define schema (constructor-schema data-type))
  (unless schema (fail 'non-data-eliminate scrutinee))
  (unless (= (length branches) (length schema))
    (fail 'non-exhaustive-eliminate node))
  (define plain-branches (map peel-branch branches))
  (for ([branch (in-list branches)]
        [plain (in-list plain-branches)])
    ;; 枝の形だけを spanless な文法で検査し、本文は spanful のまま子へ渡す。
    ;; 本文までそのまま G2m へ照合すると、子の span が理由なく不一致になる。
    (unless (redex-match? G2m br (erase-core plain))
      (fail 'ill-typed branch)))
  (define expected-constructors (map first schema))
  (define actual-constructors (map first plain-branches))
  (when (check-duplicates actual-constructors)
    (fail 'duplicate-branch-constructor node))
  (for ([constructor (in-list expected-constructors)])
    (unless (member constructor actual-constructors)
      (fail 'non-exhaustive-eliminate node)))
  (for ([branch (in-list branches)]
        [plain (in-list plain-branches)])
    (match-define `(,constructor (,parameters ...) -> ,_) plain)
    (define field-types (lookup schema constructor))
    (unless field-types (fail 'unknown-constructor branch constructor))
    (unless (= (length parameters) (length field-types))
      (fail 'branch-binder-arity branch (length field-types) (length parameters)))
    (when (check-duplicates (map peel-bind parameters))
      (fail 'duplicate-branch-binder branch)))
  (for/list ([branch (in-list plain-branches)]
             [i (in-naturals 1)])
    (match-define `(,constructor (,parameters ...) -> ,body) branch)
    (define field-types (lookup schema constructor))
    (define Λ_branch
      (for/fold ([Λ_acc Λ])
                ([p (in-list parameters)] [τ (in-list field-types)])
        (region-ctx-add-token (register-owner Λ_acc (peel-bind p) τ)
                              (peel-bind p)
                              (set))))
    (list body
          (extend environment
                  (map peel-bind parameters)
                  field-types)
          (enter-child Λ_branch i))))

(define (check-eliminate scrutinee branches expected
                         Λ Ψ environment places callables node fail
                         [compatible? type-compatible?])
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define data-type (first scrutinee-result))
  (define contexts
    (branch-contexts branches data-type Λ environment node scrutinee fail))
  (define branch-results
    (for/list ([context (in-list contexts)])
      (check-as/full (first context)
                     expected
                     (third context)
                     (third scrutinee-result)
                     (second context)
                     places
                     callables
                     fail
                     compatible?)))
  (define branch-psi
    (for/fold ([joined (third scrutinee-result)])
              ([result (in-list branch-results)])
      (psi-join joined (second result))))
  ;; 分岐ごとに別の α を持つ借用を 1 本へ合流する。合流しなかったときは
  ;; expected を返し、分岐 0 の型を根拠なく選ばない。
  (define unified
    (parameterize ([merge-position
                    (list (region-ctx-ir Λ) (region-ctx-point Λ) node)])
      (with-lifetime-unify
       (lambda ()
         (unify-borrow-lifetimes
          (map (lambda (result) (normalize-type (third result)))
               branch-results))))))
  (define merged (if (= (length unified) 1) (first unified) expected))
  (list (rows-union
         (cons (second scrutinee-result)
               (map first branch-results)))
        branch-psi
        merged))

;; CMP-001: 2 つの型を Union で合わせ、同値な構成要素を正規化で畳む。
(define (join-types left right)
  (normalize-type `(Union ,left ,right)))

;; §10.1。合流の memo。merge-record-types/impl が 1 回の合流につき 1 つ張る。
;; merge-fields と merge-witness-context が同じ型の並びへ同じ α_m を得るための共有である。
(define lifetime-unify-context (make-parameter #f))

;; 合流の制約の診断位置。分岐を型付けする側が張る（§10.2）。
;; 値は `(list ir point node)` か `#f` である。
;; `#f` のときは制約を立てない。span を引けない節点で診断を出さないためである。
;; ir を持つのは、α_m の下限に合流位置の region を置くためである。
(define merge-position (make-parameter #f))

;; §8.1。合流した α から、その合流が受け取った分岐の ρ の集合への対応。
;; lifetime-counter や alpha-table と同じく、寿命を 1 つの typing の文脈に限る。
(define merge-alpha-sources (make-parameter #f))

(define (with-lifetime-unify thunk)
  (parameterize ([lifetime-unify-context (box (hash))]) (thunk)))

;; 借用の寿命だけを合流する。payload が一致する借用が 2 つ以上あるときに働く。
;; 文脈が無いとき（合流の外から呼ばれたとき）は何もしない。
(define (unify-borrow-lifetimes types)
  (define memo (lifetime-unify-context))
  (cond
    [(not memo) types]
    [(hash-ref (unbox memo) types #f) => values]
    [else
     (define result (unify-borrow-lifetimes/fresh types))
     (set-box! memo (hash-set (unbox memo) types result))
     result]))

(define (borrow-shape t)
  (match t
    [`(Borrowed ,payload ,ρ) (list 'Borrowed payload ρ)]
    [`(BorrowedMut ,payload ,ρ) (list 'BorrowedMut payload ρ)]
    [_ #f]))

(define (unify-borrow-lifetimes/fresh types)
  (define shapes (map borrow-shape types))
  (cond
    ;; 全てが借用であり、構築子と payload が一致し、
    ;; かつ少なくとも 1 つの枝が寿命変数を持つときだけ合流する。
    ;; 全ての枝が具体的な region のときは G5b のままにする（§3.1）。
    [(and (andmap values shapes)
          (> (length shapes) 1)
          (for/and ([s (in-list (rest shapes))])
            (and (eq? (first s) (first (first shapes)))
                 (equal? (second s) (second (first shapes)))))
          (for/or ([s (in-list shapes)]) (lifetime-var? (third s))))
     (define ctor (first (first shapes)))
     (define payload (second (first shapes)))
     (define α_m (fresh-lifetime! (list 'merge (length shapes))))
     ;; §8.1。合流した α が受け取った分岐の ρ を記録する。
     ;; capability-source はこれを葉まで展開する。
     (hash-set! (merge-alpha-sources) α_m
                (for/set ([s (in-list shapes)]) (third s)))
     (define pos (merge-position))
     ;; 位置が無い呼び出しでは制約を立てない。§10.2。
     (when (and pos (first pos))
       (define ir (first pos))
       (define point (second pos))
       (define node (third pos))
       ;; α_m の下限を必ず 1 本立てる。合流した値は合流位置で生きている。
       (emit-constraint!
        (region-constraint 'contains α_m (region-at ir point) point node))
       (for ([s (in-list shapes)])
         (define ρ (third s))
         (if (lifetime-var? ρ)
             ;; 合流した値は両分岐の寿命に収まる。§10.1。
             (emit-constraint!
              (region-constraint 'merge ρ α_m point node))
             ;; 具体の側は下限である。§3.1。
             (emit-constraint!
              (region-constraint 'contains α_m (rho->region ir ρ)
                                 point node)))))
     (list (list ctor payload α_m))]
    [else types]))

;; CMP-001/ROW-005: 同じ label を持つ field を合わせる。
;; 異型があれば可変性を保ったまま Union join する。
;; 可変性が枝の間で食い違う field だけを imm へ落とす。
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
       (unify-borrow-lifetimes (sort-then-dedup normalized))))

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
     ;; 異型でも可変性は保つ。field の型を Union にしたまま mut で残す
     ;; （spec §9.1、ホワイトペーパー §4.5.3）。書き戻しの安全性は
     ;; Assign の側が受け持ち、Union の全成分と両立しない値を拒む
     ;; （spec §9.2 の infer-assign）。
     [else
      (define joined
        (for/fold ([joined (first types)])
                  ([type (in-list (rest types))])
          (join-types joined type)))
      (and joined (list label joined (if all-mutable? 'mut 'imm)))])))

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

;; RFN-002/CMP-001/ROW-005: 全 branch に常在する field を合わせる。異型は
;; 可変性を保ったまま Union join する。どれかの branch に無い field だけが落ちる。
;; types は空でないことを呼び出し側が保証する。
(define (merge-record-types/impl types)
  (with-lifetime-unify
   (lambda ()
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
            (values #f '()))]))))

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

(define (infer-eliminate scrutinee branches Λ Ψ environment places callables node fail)
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define data-type (first scrutinee-result))
  ;; branch-contexts は data type から field の型だけを配り、能力の owner を
  ;; branch binder へ運ばない。能力を含む scrutinee/field は、label 表を持つ
  ;; 段まで黙って受理せず fail-closed にする（spec §4.2）。
  (define schema (constructor-schema data-type))
  (when (or (type-carries-capability? data-type)
            (and schema
                 (ormap type-carries-capability?
                        (append* (map second schema)))))
    (fail 'capability-in-eliminate node))
  (define contexts
    (branch-contexts branches data-type Λ environment node scrutinee fail))
  (define attempts
    (for/list ([context (in-list contexts)])
      (infer (first context)
             (third context)
             (third scrutinee-result)
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
         (parameterize ([merge-position
                         (list (region-ctx-ir Λ) (region-ctx-point Λ) node)])
           (merge-record-types/impl types)))
       (unless merged (fail 'unmergeable-branch-records node))
       merged]
      [(ormap record-type? types)
       (fail 'incompatible-branch-types node)]
      [else (first types)]))
  (define branch-rows
    (for/list ([context (in-list contexts)])
      (check-as (first context)
                result-type
                (third context)
                (third scrutinee-result)
                (second context)
                places
                callables
                fail
                merge-branch-compatible?)))
  (define branch-psi
    (for/fold ([joined (third scrutinee-result)])
              ([result (in-list branch-rows)])
      (psi-join joined (second result))))
  (list result-type
        (rows-union
         (cons (second scrutinee-result)
               (map first branch-rows)))
        branch-psi))

;; [REQ: BOR-001] spec §14。関数境界で Borrowed と BorrowedMut を禁じる。
;; 仮引数、結果、証明義務の Q、捕捉を同じ入口で検査する。
(define (check-function-boundary parameter-types return-type obligations body
                                 bound-names environment node fail)
  (when (ormap unbound-borrowed-type? parameter-types)
    (fail 'borrowed-function-parameter node))
  (when (unbound-borrowed-type? return-type)
    (fail 'borrowed-function-result node))
  (when (unbound-borrowed-type? obligations)
    (fail 'borrowed-function-result node obligations))
  ;; 関数自身の束縛子は同名の外側の項目を遮蔽するため、自由変数から引く。
  (define free
    (set-subtract (core-free-vars body) (list->set bound-names)))
  ;; environment は連想リストであり、前方の項目が遮蔽後の有効な項目である。
  (define visible
    (for/fold ([entries '()]) ([entry (in-list environment)])
      (if (assoc (first entry) entries)
          entries
          (cons entry entries))))
  (for ([entry (in-list visible)])
    (when (and (unbound-borrowed-type? (second entry))
               (set-member? free (first entry)))
      (fail 'borrowed-function-capture node))))

(define (infer-lam callable parameters body Λ Ψ
                   environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates parameters)
       (fail 'duplicate-parameter node))
     (check-function-boundary parameter-types return-type obligations
                              body parameters environment node fail)
     (when (ormap owned-type? parameter-types)
       (fail 'owned-function-parameter node))
     (define body-environment
       (extend (without-owned environment)
               parameters
               parameter-types))
     (define body-result
       (check-as body return-type (enter-child Λ 0) Ψ body-environment
                 places callables fail))
     (unless (row-subset? (first body-result) latent-row)
       (fail 'undeclared-function-effect body latent-row (first body-result)))
     (list signature '() Ψ)]
    ;; valid-callables? が表の各行を (NFn ...) に限るため、入口を通った呼び出しは
    ;; ここへ到達しない。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

(define (infer-recur-value callable function parameters body Λ Ψ
                           environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates (cons function parameters))
       (fail 'duplicate-parameter node))
     (check-function-boundary parameter-types return-type obligations
                              body (cons function parameters) environment node fail)
     (when (ormap owned-type? parameter-types)
       (fail 'owned-function-parameter node))
     (define body-environment
       (extend
        (extend (without-owned environment)
                (list function)
                (list signature))
        parameters
        parameter-types))
     (define body-result
       (check-as body return-type (enter-child Λ 0) Ψ body-environment
                 places callables fail))
     (unless (row-subset? (first body-result) latent-row)
       (fail 'undeclared-function-effect body latent-row (first body-result)))
     (list signature '() Ψ)]
    ;; valid-callables? が表の各行を (NFn ...) に限るため、入口を通った呼び出しは
    ;; ここへ到達しない。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

(define (recur-context callable function parameters body Λ Ψ
                       environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates (cons function parameters))
       (fail 'duplicate-parameter node))
     (check-function-boundary parameter-types return-type obligations
                              body (cons function parameters) environment node fail)
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
     ;; body は Recur の子 0 である（region.md §3）。
     ;; 環境は既存の body-environment をそのまま使う。
     ;; 仮引数は owners へ入れないため（spec §3.1）、Λ は enter-child だけを掛ける。
     (define Λ_body (enter-child Λ 0))
     ;; 本体を Ψ が動かなくなるまで解析し直す。集合は単調に増えるため停止する。
     (define (fixpoint Ψ_in)
       (match (check-as body return-type Λ_body Ψ_in body-environment
                        places callables fail)
         [(list body-row Ψ_1)
          (define Ψ_next (psi-join Ψ_in Ψ_1))
          (if (equal? Ψ_next Ψ_in)
              (list body-row Ψ_next)
              (fixpoint Ψ_next))]))
     (match-define (list body-row Ψ_body) (fixpoint Ψ))
     (unless (row-subset? body-row latent-row)
       (fail 'undeclared-function-effect body latent-row body-row))
     (list function-environment Ψ_body)]
    ;; valid-callables? が表の各行を (NFn ...) に限るため、入口を通った呼び出しは
    ;; ここへ到達しない。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

;; spec §3.1。宣言型の借用の region 欄は書き手が書いた起点であり、
;; 推論した型のそれは寿命である。語彙が違うので照合しない。
;; 両方が同じ構成子の借用である位置だけ、宣言型の欄を推論した欄へ写す。
;; 形が食い違う位置は宣言型のまま残し、後段の type-compatible? に落とさせる。
(define (adopt-inferred-lifetimes declared actual)
  (match* (declared actual)
    [(`(Borrowed ,d-payload ,_) `(Borrowed ,a-payload ,a-rho))
     `(Borrowed ,(adopt-inferred-lifetimes d-payload a-payload) ,a-rho)]
    [(`(BorrowedMut ,d-payload ,_) `(BorrowedMut ,a-payload ,a-rho))
     `(BorrowedMut ,(adopt-inferred-lifetimes d-payload a-payload) ,a-rho)]
    [((? list?) (? list?))
     #:when (= (length declared) (length actual))
     (for/list ([d (in-list declared)] [a (in-list actual)])
       (adopt-inferred-lifetimes d a))]
    [(_ _) declared]))

(define (binding-context binding-mode declared-type bound Λ Ψ
                         environment places callables node fail)
  (match declared-type
    [`(Record ,declared-row)
     (match (infer bound (enter-child Λ 0) Ψ environment places callables fail)
       [(list 'Never bound-row bound-psi)
        (list bound-row declared-type bound-psi)]
       [(list `(Record ,actual-row) bound-row bound-psi)
        (unless (compat? `(Record ,actual-row) declared-type Γ-pc0
                         (current-region-relation))
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
        (list bound-row `(Record ,binding-row) bound-psi)]
       [(list actual-type _ _)
        (fail 'type-mismatch bound declared-type actual-type)])]
    [_
     (match (check-as/full bound declared-type (enter-child Λ 0)
                           Ψ environment places callables fail)
       [(list row bound-psi actual)
        ;; 束縛の型には推論した寿命を持つ側を置く。
        ;; 宣言型を置くと spec §5.1 の下限収集が (RVar k) を見つけられず、
        ;; 束縛した名前を使う位置の region が σ に入らない。
        (list row (adopt-inferred-lifetimes declared-type actual) bound-psi)])]))

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
(define (check-as/boolean core expected environment places callables
                          [Λ (empty-region-ctx)])
  (match (with-typing
          (lambda (fail)
            (check-as core expected Λ
                      (empty-psi)
                      environment places callables fail)))
    [(list 'ok (list row _psi)) row]
    [_ #f]))

;; spec §3.1。所有値の束縛子だけを owners へ入れる。
;; ρ は束縛子の節点で有効な region である。Λ.point がその節点を指すため、
;; enter-child を掛ける前の Λ をここへ渡す。
;; ir が無い Λ、すなわち公開入口の既定の空 Λ では何もしない。
(define (register-owner Λ w binding-type)
  (define ir (region-ctx-ir Λ))
  (cond
    [(not ir) Λ]
    [(match (normalize-type binding-type)
       [`(Owned ,_) #t]
       [_ #f])
     (region-ctx-add-owner Λ w (region-at ir (region-ctx-point Λ)))]
    [else Λ]))

;; 借用の対象の payload を引く。p は places が直接 τ を与え、
;; x は environment が (Owned τ) を与える。
(define (borrow-target-payload w environment places node fail)
  (cond
    [(exact-nonnegative-integer? w)
     (define type (lookup places w))
     (unless type (fail 'unknown-place node))
     type]
    [else
     (define type (lookup environment (peel-node w)))
     (unless type (fail 'unbound-variable node))
     (match type
       [`(Owned ,payload) payload]
       [_ (fail 'borrow-non-owned node)])]))

;; [REQ: BOR-001] 借用の region は owner の region に含まれていなければならない。
;; [REQ: BOR-002] 可変借用の有効期間中、競合する alias を作れない。
;;
;; G5c1 では判定を行わない。α を作り、制約と判定の要求だけを記録する。
;; 判定は解決の後、検査の段が行う（spec §7.3）。
(define (infer-borrow core w mutable? Λ Ψ environment places callables fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-unknown-owner-region core))
  (define payload (borrow-target-payload w environment places core fail))
  (define key (if (exact-nonnegative-integer? w) w (peel-node w)))
  (define ρ_owner (region-ctx-owner Λ key))
  ;; 所有者の region が引けないのは制約の違反ではなく入力の情報不足である。
  ;; 解決を待つ理由が無いため、ここで落とす（spec §8.1）。
  (unless ρ_owner (fail 'borrow-unknown-owner-region core))
  (define point (region-ctx-point Λ))
  (define ρ_borrow (region-at ir point))
  (define α (fresh-lifetime! point))
  ;; 借用の起点は α の下限である。使わない借用の解はこの 1 本で決まり、
  ;; G5b の ρ_borrow と一致する（spec §5.3）。
  (emit-constraint!
   (region-constraint 'contains α ρ_borrow point #f))
  ;; BOR-001 は上限制約になる（spec §8.1）。
  (emit-constraint!
   (region-constraint 'outlives ρ_owner α point core))
  (emit-request!
   (borrow-request key '() (if mutable? 'mut 'shared) α core))
  (define Ψ_out
    (if mutable?
        (psi-add-mut Ψ key '() α)
        (psi-add-shared Ψ key '() α)))
  (list (list (if mutable? 'BorrowedMut 'Borrowed)
              payload
              α)
        '()
        Ψ_out))

;; [REQ: BOR-002] Reborrow は可変借用を子 region の共有借用へ落とし、
;; 親 capability を子の生存期間だけ停止する。判定は段 3 で行う。
(define (infer-reborrow core operand Λ Ψ environment places callables fail)
  (match-define (list τ_operand ε_operand Ψ_1)
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-unknown-owner-region core))
  (match (normalize-type τ_operand)
    [`(BorrowedMut ,τ ,α_parent)
     (define point (region-ctx-point Λ))
     (define α_child (fresh-lifetime! point))
     ;; 型の region 欄は未解決の RVar または concrete な ρ を運ぶ。
     ;; RVar はそのまま制約へ渡し、concrete な欄だけ per-IR bridge で
     ;; region 項へ戻して、制約の寿命項の表現を揃える。
     (define parent-term
       (if (lifetime-var? α_parent)
           α_parent
           (rho->region ir α_parent)))
     (emit-constraint!
      (region-constraint 'contains α_child (region-at ir point) point core))
     (emit-constraint!
      (region-constraint 'reborrow parent-term α_child point core))
     (define tokens (borrow-token-key Λ operand #:fail fail))
     (when (set-empty? tokens)
       (error 'infer-reborrow
              "親の token を特定できない operand: ~s"
              operand))
     ;; 外部から渡された concrete な可変借用は、借用要求を core 内で
     ;; 生成していない。各 token を親の要求として記録し、境界の先でも
     ;; Move/Drop の判定へ届かせる。
     (when (not (lifetime-var? α_parent))
       (for ([cap (in-set tokens)])
         (define w (car cap))
         (define fp (cdr cap))
         (emit-request! (borrow-request w fp 'mut parent-term core))))
     ;; Reborrow の結果そのものも共有借用として判定要求へ記録する。
     ;; 親を停止窓から除いたあとも、子と別の可変借用との衝突は残す必要がある。
     (for ([cap (in-set tokens)])
       (define w (car cap))
       (define fp (cdr cap))
       (emit-request! (borrow-request w fp 'shared α_child core)))
     ;; concrete な親は Ψ に元の mut 項目が無い環境由来の借用である。
     ;; synthetic request と親子除外を同じ規則へ揃えるため、判定用の
     ;; suspension tuple だけは実在する mut capability として張る。
     (define Ψ_seed
       (if (lifetime-var? α_parent)
           Ψ_1
           (for/fold ([Ψ_acc Ψ_1]) ([cap (in-set tokens)])
             (psi-add-mut Ψ_acc (car cap) (cdr cap) parent-term))))
     (define Ψ_2
       (for/fold ([Ψ_acc Ψ_seed]) ([cap (in-set tokens)])
         (psi-suspend Ψ_acc (car cap) (cdr cap) parent-term α_child)))
     (list `(Borrowed ,τ ,α_child) ε_operand Ψ_2)]
    [_ (fail 'reborrow-non-mutable core)]))

;; §8.1。合流した α を、借用の項が直接採番した α だけの集合へ展開する。
;; 中間の合流 α を残してはならない。循環は不変条件の破れとして error にする。
(define (alpha-set ρ)
  (cond
    [(not (lifetime-var? ρ)) (set)]
    [else
     (let expand ([α ρ] [seen (set)])
       (cond
         [(set-member? seen α)
          (error 'alpha-set "合流した α の対応が循環している: ~s" α)]
         [(hash-ref (merge-alpha-sources) α #f)
          => (lambda (branches)
               (for/fold ([acc (set)]) ([β (in-set branches)])
                 (if (lifetime-var? β)
                     (set-union acc (expand β (set-add seen α)))
                     acc)))]
         [else (set α)]))]))

;; §8.1。capability の起点となる借用の α の集合を返す。
;; 具体的な ρ と借用でない型は起点の寿命を運ばないので空集合である。
(define (capability-source type)
  (match (normalize-type type)
    [`(Borrowed ,_ ,ρ) (alpha-set ρ)]
    [`(BorrowedMut ,_ ,ρ) (alpha-set ρ)]
    [_ (set)]))

;; [REQ: BOR-004] 借用の field 射影。親の α をそのまま使い、
;; 新しい α と borrow-request は作らない（spec §5.1）。
(define (infer-projborrow core operand label Λ Ψ environment places callables fail)
  (match-define (list τ_operand ε_operand Ψ_1)
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define-values (m_parent τ_inner α)
    (match (normalize-type τ_operand)
      [`(Borrowed ,τ ,α) (values 'Borrowed τ α)]
      [`(BorrowedMut ,τ ,α) (values 'BorrowedMut τ α)]
      [_ (fail 'projborrow-non-record core)]))
  (define row
    (match (normalize-type τ_inner)
      [`(Record ,r) r]
      [_ (fail 'projborrow-non-record core)]))
  (define field
    (or (assoc label row)
        (fail 'projborrow-unknown-field core)))
  (match-define (list _ τ_f m_f) field)
  ;; spec §5.4 の例外。直接の Owned payload は Borrowed の禁止形になる。
  (when (match (normalize-type τ_f) [`(Owned ,_) #t] [_ #f])
    (fail 'borrowed-owned-payload core))
  (define source (capability-source τ_operand))
  (for ([cap (in-set (borrow-token-key Λ operand #:fail fail))])
    (emit-use-request! Λ (car cap) (append (cdr cap) (list label)) 'read source
                       core 'borrow-conflicting-use))
  (list `(,(proj-borrow-mode m_parent m_f) ,τ_f ,α) ε_operand Ψ_1))

;; [REQ: BOR-005] 借用が指す先の値を複製する。結果は借用でも所有値でもない。
;; ρ は結果の型に現れない（spec §6.1）。
(define (infer-read core operand Λ Ψ environment places callables fail)
  (match-define (list τ_operand ε_operand Ψ_1)
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_payload
    (match (normalize-type τ_operand)
      [`(Borrowed ,τ ,_) τ]
      [`(BorrowedMut ,τ ,_) τ]
      [_ (fail 'read-non-borrow core)]))
  (unless (copy-out-ok? τ_payload)
    (fail 'read-uncopyable-payload core))
  (define source (capability-source τ_operand))
  (for ([cap (in-set (borrow-token-key Λ operand #:fail fail))])
    (emit-use-request! Λ (car cap) (cdr cap) 'read source
                       core 'borrow-conflicting-use))
  (list τ_payload ε_operand Ψ_1))

;; [REQ: BOR-004] 可変借用 capability を通じた代入だけを許す。
;; target の payload が Union のときは、実行時の全成分と互換でなければならない。
(define (infer-assign core target value Λ Ψ environment places callables fail)
  (match-define (list τ_target ε_target Ψ_1)
    (infer target (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_target* (normalize-type τ_target))
  (define τ_payload
    (match τ_target*
      [`(BorrowedMut ,τ ,_) τ]
      [`(Borrowed ,_ ,_) (fail 'assign-through-shared core)]
      [_ (fail 'assign-non-borrow core)]))
  (unless (copy-out-ok? τ_payload)
    (fail 'assign-owned-payload core))
  (match-define (list τ_value ε_value Ψ_2)
    (infer value (enter-child Λ 1) Ψ_1 environment places callables fail))
  (for ([τ_i (in-list (union-members τ_payload))])
    (unless (type-compatible? τ_value τ_i)
      (fail 'assign-union-variant core)))
  (define source (capability-source τ_target))
  (for ([cap (in-set (borrow-token-key Λ target #:fail fail))])
    (emit-use-request! Λ (car cap) (cdr cap) 'assign source
                       core 'borrow-conflicting-use))
  (list 'Unit (row-union ε_target ε_value) Ψ_2))

(define (infer core Λ Ψ environment places callables fail)
  ((typing-point-probe) (region-ctx-point Λ))
  (define result
    (infer/body core Λ Ψ environment places callables fail))
  (collect-use-regions! (first result)
                        (region-ctx-ir Λ)
                        (region-ctx-point Λ))
  result)

(define (infer/body core Λ Ψ environment places callables fail)
  (match (peel-node core)
    [(? integer?) (list 'Int '() Ψ)]
    [(? string?) (list 'String '() Ψ)]
    ['unit (list 'Unit '() Ψ)]

    [`(Lam ,_ ,callable (,parameters ...) ,body)
     (infer-lam callable (map peel-bind parameters) body Λ
                Ψ
                environment places callables core fail)]

    [`(PrimVal ,_ ,name)
     (match (assoc name Γ0)
       [(list _ (list type canonical-value))
        (unless (equal? canonical-value (peel-node core))
          (fail 'non-canonical-primitive core))
        (list type '() Ψ)]
       [_ (fail 'unknown-primitive core)])]

    [`(CurryVal ,_ ,function ,argument)
     (match (infer function (enter-child Λ 0)
                    Ψ environment places callables fail)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              function-row function-psi)
        (unless (null? function-row)
          (fail 'effectful-curry-operand function))
        (when (owned-type? first-type)
          (fail 'owned-curry-argument argument))
        (define argument-row
          (check-as argument first-type (enter-child Λ 1)
                    function-psi
                    environment places callables fail))
        (unless (null? (first argument-row))
          (fail 'effectful-curry-operand argument))
        (list `(NFn ,remaining-types
                    ,return-type
                    ,latent-row
                    ,obligations)
              (row-union function-row (first argument-row))
              (second argument-row))]
       [_ (fail 'curry-non-function function)])]

    [`(RecurVal ,callable ,function (,parameters ...) ,body)
     (infer-recur-value callable (peel-bind function)
                        (map peel-bind parameters) body Λ
                        Ψ
                        environment places callables core fail)]

    [`(TypeRep ,_ ,_ ,kind)
     (list `(TypeInfo ,kind) '() Ψ)]

    [`(ProofRep ,_ ,proposition)
     (list `(Proof ,proposition) '() Ψ)]

    [`(Construct ,data-type ,constructor ,fields ...)
     (define result
       (check-construct constructor fields data-type Λ
                        Ψ
                        environment places callables core fail))
     (list (peel-ty data-type) (first result) (second result))]

    [`(resource ,_) (list '(Owned Res) '() Ψ)]

    [`(Rec (,fields ...))
     (define plain-fields
       (for/list ([field (in-list fields)])
         (list (peel-lbl (first field))
               (second field)
               (third field))))
     (unless (field-row-unique? plain-fields)
       (fail 'duplicate-record-label core))
     (define-values (results final-psi)
       (for/fold ([results '()] [current-psi Ψ])
                 ([field (in-list plain-fields)]
                  [i (in-naturals)])
         (define result
           (infer (third field) (enter-child Λ i)
                  current-psi environment places callables fail))
         (values (append results (list result)) (third result))))
     (for ([field (in-list plain-fields)]
           [result (in-list results)])
       (when (owned-type? (first result))
         (fail 'owned-record-field (third field))))
     (list
      `(Record
        ,(for/list ([field (in-list plain-fields)]
                    [result (in-list results)])
           `(,(first field) ,(first result) ,(second field))))
      (rows-union (map second results))
      final-psi)]

    ;; RFN-001: 未検証の値。ペイロードの型をそのまま Untrusted で包む。
    ;; effect row はペイロードのものを引き継ぐ。
    [`(UVal ,value)
     (match (infer value (enter-child Λ 0)
                    Ψ
                    environment places callables fail)
       [(list value-type value-row value-psi)
        (unless (owned-free? value-type)
          (fail 'owned-untrusted-payload value))
        (list `(Untrusted ,value-type) value-row value-psi)])]

    ;; RFN-001: 検証済みの値。witness の命題を型へ持ち上げる。発行者が正当か
    ;; どうかは成果物検証（verify-origins）の担当であり、ここでは見ない。
    [`(RVal ,proof-rep ,value)
     (match (peel-node proof-rep)
       [`(ProofRep ,_ ,proposition)
        (match (infer value (enter-child Λ 0)
                       Ψ
                       environment places callables fail)
          [(list value-type value-row value-psi)
           (unless (owned-free? value-type)
             (fail 'owned-refined-payload value))
           (list `(Refined ,value-type ,proposition) value-row value-psi)])]
       [_ (fail 'ill-typed core)])]

    [`(Proj ,record ,label)
     (match (infer record (enter-child Λ 0)
                    Ψ environment places callables fail)
       [(list `(Record ,row) record-row record-psi)
        (match (field-row-lookup row (peel-lbl label))
          [(list field-type _) (list field-type record-row record-psi)]
          [_ (fail 'unknown-record-label core)])]
       [_ (fail 'project-non-record record)])]

    [`(Apply ,function ,arguments ...)
     (match (infer function (enter-child Λ 0)
                    Ψ environment places callables fail)
       [(list `(NFn ,parameter-types
                    ,return-type ,latent-row ,obligations)
              function-row function-psi)
        (when (ormap unbound-borrowed-type? parameter-types)
          (fail 'borrowed-function-parameter function))
        (when (unbound-borrowed-type? return-type)
          (fail 'borrowed-function-result function))
        (when (unbound-borrowed-type? obligations)
          (fail 'borrowed-function-result function obligations))
        (define argument-rows
          (check-many arguments parameter-types Λ function-psi
                      environment places callables core fail 1))
        (unless (obligations-dischargeable? obligations Γ-pc0)
          (fail 'unsatisfied-proof-obligation core))
        (list return-type
              (rows-union
               (append (list function-row)
                       (first argument-rows)
                       (list latent-row)))
              (second argument-rows))]
       [_ (fail 'apply-non-function function)])]

    [`(Discharge ,_ ,_)
     ;; 包み先を直接の Apply に限る形は採れない。複数義務では外側の Discharge
     ;; の包み先が Discharge になり、生成する形を自分で拒否してしまう。
     ;; 素通しの規則も採れない。当該の Apply と無関係な正当な ProofRep を手書き
     ;; で包んだ項が検証を通る。PRF-004 が要求するのは選択した Proof の
     ;; provenance であるから、φ 列と義務列の対応をここで固定する。
     (define-values (propositions base) (peel-discharge core))
     (define base-Λ
       (let loop ([node (peel-node core)] [ctx Λ])
         ;; Discharge の proof 欄は子ではないが、各包みの inner は child 0
         ;; である。base へ跳ぶ前に中間層も観測して point 集合を欠かさない。
         ((typing-point-probe) (region-ctx-point ctx))
         (match node
           [`(Discharge ,_ ,inner)
            (loop (peel-node inner) (enter-child ctx 0))]
           [_ ctx])))
     (match (peel-node base)
       [`(Apply ,function ,_ ...)
        (match (infer function (enter-child base-Λ 0)
                       Ψ environment places callables fail)
          [(list `(NFn ,_ ,_ ,_ ,obligations) _ function-psi)
           (unless (= (length propositions) (length obligations))
             (fail 'discharge-obligation-count core))
           (for ([phi (in-list propositions)]
                 [obligation (in-list obligations)])
             (unless (proposition-equiv? phi obligation)
               (fail 'discharge-proposition-mismatch core)))
           ;; 型と Effect 行は基底の Apply のものを返す。
           (infer base base-Λ function-psi environment places callables fail)]
          [_ (fail 'apply-non-function function)])]
       [_ (fail 'discharge-target-not-apply base)])]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound Λ
                             Ψ environment places callables core fail)
       [(list bound-row binding-type bound-psi)
        (define x (peel-bind name))
        (define Λ_owner (register-owner Λ x binding-type))
        (define token
          (if (borrow-typed? (normalize-type binding-type))
              (borrow-token-key Λ bound #:fail fail)
              (set)))
        (define Λ_token (region-ctx-add-token Λ_owner x token))
        (define Λ_body (enter-child Λ_token 1))
        (match (infer body
                      Λ_body
                      bound-psi
                      (extend environment (list x)
                              (list binding-type))
                      places
                      callables
                      fail)
          [(list body-type body-row body-psi)
           (list body-type (row-union bound-row body-row) body-psi)])])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-result
       (check-as bound (peel-ty type) (enter-child Λ 0)
                 Ψ environment places callables fail))
     (define x (peel-bind name))
     (define binding-type (peel-ty type))
     (define Λ_owner (register-owner Λ x binding-type))
     (define token
       (if (borrow-typed? (normalize-type binding-type))
           (borrow-token-key Λ bound #:fail fail)
           (set)))
     (define Λ_token (region-ctx-add-token Λ_owner x token))
     (define Λ_body (enter-child Λ_token 1))
     (match (infer body
                   Λ_body
                   (second bound-result)
                   (extend environment
                           (list x)
                           (list binding-type))
                   places
                   callables
                   fail)
       [(list body-type body-row body-psi)
        (list body-type
              (row-union (first bound-result) body-row)
              body-psi)])]

    [`(Eliminate ,scrutinee (,branches ...))
     (infer-eliminate scrutinee branches Λ
                      Ψ
                      environment places callables core fail)]

    [`(Perform (Return ,boundary ,type) ,argument)
     (define type* (peel-ty type))
     (define argument-row
       (check-as argument type* (enter-child Λ 0)
                 Ψ environment places callables fail))
     (list 'Never
           (row-union (first argument-row)
                      `((Return ,boundary ,type*)))
           (second argument-row))]

    [`(Handle (Return ,boundary ,type) ,handler-clause ,body)
     (define type* (peel-ty type))
     (define body-result
       (check-as body type* (enter-child Λ 1)
                 Ψ environment places callables fail))
     (define handler-result
       (match (peel-branch handler-clause)
         [`(,name -> ,handler)
          (check-as handler
                    type*
                    (enter-child Λ 0)
                    (psi-join Ψ (second body-result))
                    (extend environment (list (peel-bind name)) (list type*))
                    places
                    callables
                    fail)]
         [_ (fail 'ill-typed core)]))
     (list type*
           (row-union
            (row-difference (first body-result)
                            `((Return ,boundary ,type*)))
            (first handler-result))
           (psi-join (second body-result) (second handler-result)))]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (infer body (enter-child Λ 0) Ψ environment places callables fail)]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      Λ
                      Ψ
                      environment places callables core fail))
     (infer continuation (enter-child Λ 1)
           (second continuation-environment)
           (first continuation-environment)
           places callables fail)]

    [`(Yield ,observed ,next)
     (define observed-result
       (infer observed (enter-child Λ 0)
             Ψ environment places callables fail))
     (define next-result
       (infer next (enter-child Λ 1)
             (third observed-result)
             environment places callables fail))
     (list (first next-result)
           (rows-union
            (list (second observed-result)
                  (second next-result)
                  `((Yield ,(first observed-result)))))
           (third next-result))]

    [`(Suspend ,body)
     (define result (infer body (enter-child Λ 0)
                               Ψ
                               environment places callables fail))
     (list (first result) (row-union (second result) '(Suspend))
           (third result))]

    [`(Move ,place)
     #:when (exact-nonnegative-integer? place)
     (define type (lookup places place))
     (unless type (fail 'unknown-place core))
     (emit-use-request! Λ place '() 'move (set) core 'move-borrowed)
     (list `(Owned ,type) '(Own) Ψ)]

    [`(Move ,name)
     (define w (peel-node name))
     (define type (lookup environment w))
     (unless type (fail 'unbound-variable core))
     (emit-use-request! Λ w '() 'move (set) core 'move-borrowed)
     (when (borrow-typed? type) (fail 'move-borrowed core))
     (match type
       [`(Owned ,inner-type) (list `(Owned ,inner-type) '(Own) Ψ)]
       [_ (fail 'move-non-owned core)])]

    [`(Drop ,argument)
     (define dropped
       (match (peel-node argument)
         [`(Move ,w) (peel-node w)]
         [(? symbol? w) w]
         [_ #f]))
     ;; spec §7.5。Move を通さない裸の名前で、型が Owned のとき、
     ;; 段 1 は答えを決められない。借用が生きていれば drop-borrowed、
     ;; 生きていなければ owned-variable-requires-move である。
     ;; 段 1 で後者を出すと段 3 の判定を潰すので、両方を段 3 へ渡す。
     ;; ir が無いときは借用が無いので答えが段 1 で確定する。
     ;; そのとき渡してしまうと要求が記録されず、どちらも出ずに受理してしまう。
     (define dropped-type (and dropped (lookup environment dropped)))
     (define bare-owned?
       (and dropped
            (region-ctx-ir Λ)
            (symbol? (peel-node argument))
            dropped-type
            (owned-type? dropped-type)))
     (when dropped
       (emit-use-request! Λ dropped '() 'move (set) argument 'drop-borrowed
                          (and bare-owned? 'owned-variable-requires-move)))
     (when (and dropped
                (borrow-typed? (or (lookup environment dropped) '())))
       (fail 'drop-borrowed argument))
     (define argument-Λ (enter-child Λ 0))
     (define argument-result
       (if bare-owned?
           (list dropped-type '() Ψ)
           (let/ec recover
             (infer argument argument-Λ Ψ environment places callables
                    (lambda (key node . details)
                      (assert-typing-key key)
                      (recover #f))))))
     (cond
       [(and argument-result
             (owned-type? (first argument-result)))
        (list 'Unit
              (row-union (second argument-result) '(Own))
              (third argument-result))]
       [else
        (define argument-row
          (check-as argument '(Owned Res) argument-Λ
                    Ψ
                    environment places callables
                    (lambda (key node . details)
                      (assert-typing-key key)
                      (if (and (eq? key 'type-mismatch)
                               (eq? node argument))
                          (fail 'drop-non-owned argument)
                          (apply fail key node details)))))
        (list 'Unit (row-union (first argument-row) '(Own))
              (second argument-row))])]

    [`(Curry ,function ,argument)
     (match (infer function (enter-child Λ 0)
                    Ψ environment places callables fail)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              function-row function-psi)
        (when (unbound-borrowed-type? first-type)
          (fail 'borrowed-function-parameter argument))
        (when (ormap unbound-borrowed-type? remaining-types)
          (fail 'borrowed-function-parameter argument))
        (when (unbound-borrowed-type? return-type)
          (fail 'borrowed-function-result argument))
        (when (unbound-borrowed-type? obligations)
          (fail 'borrowed-function-result argument obligations))
        (when (owned-type? first-type)
          (fail 'owned-curry-argument argument))
        (define argument-row
          (check-as argument first-type (enter-child Λ 1)
                    function-psi
                    environment places callables fail))
        (list `(NFn ,remaining-types
                    ,return-type
                    ,latent-row
                    ,obligations)
              (row-union function-row (first argument-row))
              (second argument-row))]
       [_ (fail 'curry-non-function function)])]

    [`(Error ,_) (fail 'error-needs-expected-type core)]

    [(? symbol? name)
     (define type (lookup environment name))
     (unless type (fail 'unbound-variable core))
     (when (owned-type? type) (fail 'owned-variable-requires-move core))
     (list type '() Ψ)]

    [`(Borrow ,w)
     (infer-borrow core w #f Λ Ψ environment places callables fail)]
    [`(BorrowMut ,w)
     (infer-borrow core w #t Λ Ψ environment places callables fail)]
    [`(BorrowAt ,ρ ,_ ,w)
     (check-region-annotation Λ ρ core fail)
     (infer-borrow core w #f Λ Ψ environment places callables fail)]
    [`(BorrowMutAt ,ρ ,_ ,w)
     (check-region-annotation Λ ρ core fail)
     (infer-borrow core w #t Λ Ψ environment places callables fail)]
    [`(Reborrow ,c_operand)
     (infer-reborrow core c_operand Λ Ψ environment places callables fail)]
    [`(ReborrowAt ,ρ ,_ ,c_operand)
     (check-region-annotation Λ ρ core fail)
     (infer-reborrow core c_operand Λ Ψ environment places callables fail)]
    [`(ProjBorrowAt ,_ ,_ ,operand ,label)
     (infer-projborrow core operand label Λ Ψ environment places callables fail)]
    [`(Read ,operand)
     (infer-read core operand Λ Ψ environment places callables fail)]
    [`(Assign ,target ,value)
     (infer-assign core target value Λ Ψ environment places callables fail)]

    [_ (fail 'ill-typed core)]))

;; 段 1 だけを走らせる。試験と、Task 7 の解決の段が使う。
;; with-typing は成功を (list 'ok <本体の返り値>) で包むので、ここで剥がす。
;; 返すのは裸の 4 つ組であり、Task 5 の 3 つ組へ要求の並びを足す。
;; 段 1 で棄却されたときは error を上げる。3 つ組と取り違える形を残さないためである。
(define (typing-inference core-in places callables [environment '()]
                          [Λ (empty-region-ctx)])
  (define cs (box '()))
  (define rs (box '()))
  (define tbl (box (hash)))
  (define result
    (parameterize ([lifetime-collector cs]
                   [request-collector rs]
                   [lifetime-counter (box 0)]
                   [alpha-table tbl]
                   [merge-alpha-sources (make-hash)])
      (with-typing
       (lambda (fail)
         (match-define (list type _row _Ψ)
           (infer core-in Λ (empty-psi) environment places callables fail))
         (list type (unbox tbl) (reverse (unbox cs)) (reverse (unbox rs)))))))
  (match result
    [(list 'ok value) value]
    [(list 'fail key _node details)
     (error 'typing-inference "段 1 が棄却した: ~a ~a" key details)]))

(define (check-as/full core expected Λ Ψ environment places callables fail
                       [compatible? type-compatible?])
  ((typing-point-probe) (region-ctx-point Λ))
  (match (peel-node core)
    [`(Construct ,data-type ,constructor ,fields ...)
     (define actual (peel-ty data-type))
     (unless (type-equiv? actual expected)
       (fail 'type-mismatch core expected actual))
     (match (check-construct constructor fields data-type
                              Λ
                              Ψ
                              environment places callables core fail)
       [(list row psi) (list row psi actual)])]

    [`(Error ,place)
     (unless (and (exact-nonnegative-integer? place)
                  (assoc place places))
       (fail 'unknown-place core))
     (list '() Ψ expected)]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound
                             Λ
                             Ψ environment places callables core fail)
       [(list bound-row binding-type bound-psi)
        (define x (peel-bind name))
        (define Λ_owner (register-owner Λ x binding-type))
        (define token
          (if (borrow-typed? (normalize-type binding-type))
              (borrow-token-key Λ bound #:fail fail)
              (set)))
        (define Λ_token (region-ctx-add-token Λ_owner x token))
        (define Λ_body (enter-child Λ_token 1))
        (define body-result
          (check-as/full body
                        expected
                        Λ_body
                        bound-psi
                        (extend environment (list x)
                                (list binding-type))
                        places
                        callables
                        fail
                        compatible?))
        (list (row-union bound-row (first body-result))
              (second body-result)
              (third body-result))])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-result
       (check-as/full bound (peel-ty type) (enter-child Λ 0)
                      Ψ environment places callables fail compatible?))
     (define x (peel-bind name))
     (define binding-type (peel-ty type))
     (define Λ_owner (register-owner Λ x binding-type))
     (define token
       (if (borrow-typed? (normalize-type binding-type))
           (borrow-token-key Λ bound #:fail fail)
           (set)))
     (define Λ_token (region-ctx-add-token Λ_owner x token))
     (define Λ_body (enter-child Λ_token 1))
     (define body-result
       (check-as/full body
                     expected
                     Λ_body
                     (second bound-result)
                     (extend environment
                             (list x)
                             (list binding-type))
                     places
                     callables
                     fail
                     compatible?))
     (list (row-union (first bound-result) (first body-result))
           (second body-result)
           (third body-result))]

    [`(Eliminate ,scrutinee (,branches ...))
     (check-eliminate scrutinee branches expected
                      Λ
                      Ψ
                      environment places callables core fail
                      compatible?)]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (check-as/full body expected (enter-child Λ 0)
                    Ψ environment places callables fail compatible?)]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      Λ
                      Ψ
                      environment places callables core fail))
     (check-as/full continuation
                    expected
                    (enter-child Λ 1)
                    (second continuation-environment)
                    (first continuation-environment)
                    places
                    callables
                    fail
                    compatible?)]

    [`(Yield ,observed ,next)
     (define observed-result
       (infer observed (enter-child Λ 0)
             Ψ environment places callables fail))
     (define next-result
       (check-as/full next expected (enter-child Λ 1)
                      (third observed-result)
                      environment places callables fail compatible?))
     (list (rows-union
            (list (second observed-result)
                  (first next-result)
                  `((Yield ,(first observed-result)))))
           (second next-result)
           (third next-result))]

    [`(Suspend ,body)
     (define body-result
       (check-as/full body expected (enter-child Λ 0)
                      Ψ environment places callables fail compatible?))
     (list (row-union (first body-result) '(Suspend))
           (second body-result)
           (third body-result))]

    [_
     (match (infer core Λ Ψ environment places callables fail)
       [(list actual row result-psi)
        (unless (compatible?
                 actual
                 (adopt-inferred-lifetimes expected actual))
          (fail 'type-mismatch core expected actual))
        (list row result-psi actual)])]))

;; 既存の呼び出しは結果の型を要らない。第 3 要素を落として渡す。
(define (check-as core expected Λ Ψ environment places callables fail
                  [compatible? type-compatible?])
  (match (check-as/full core expected Λ Ψ environment places callables fail
                        compatible?)
    [(list row psi _) (list row psi)]))

;; 入口検査は type-of/raw と core-check-row が共有する。片方だけ直す事故を
;; 避けるため、検査の順と key をここへ寄せる。
;; core は投影済みの項を受け取る。返り値は最初に破れた検査の
;; (list key details ...) か、すべて通ったときの #f である。
(define (borrowed-owned-payload-type subject)
  ;; core の型注釈を走査し、Borrowed または BorrowedMut の payload が直接
  ;; Owned である最初の型を返す。無ければ #f。
  (let search ([t subject])
    (match t
      [`(Borrowed (Owned ,_) ,_) t]
      [`(BorrowedMut (Owned ,_) ,_) t]
      [(? list?) (for/or ([e (in-list t)]) (search e))]
      [_ #f])))

(define (entry-violation core places callables environment)
  (cond
    [(not (redex-match? G2m c core)) '(not-core-term)]
    [(own-annotation-violation core)
     => (lambda (found) (list 'own-designator-mismatch found))]
    [(borrowed-owned-payload-type core)
     => (lambda (found) (list 'borrowed-owned-payload found))]
    [(not (core-types-normal? core)) '(non-normal-type)]
    [(not (valid-environment? environment))
     (list 'invalid-environment environment)]
    [(not (valid-places? places)) (list 'invalid-places places)]
    [(not (valid-callables? callables)) (list 'invalid-callables callables)]
    [else #f]))

(define (type-of/raw* core-in places callables environment Λ)
  (define cs (box '()))
  (define rs (box '()))
  (define tbl (box (hash)))
  (define result
    (parameterize ([lifetime-collector cs]
                   [request-collector rs]
                   [lifetime-counter (box 0)]
                   [alpha-table tbl]
                   [merge-alpha-sources (make-hash)])
      (with-typing
       (lambda (fail)
         ;; span.md §7.3: 入口検査だけ投影し、走査は spanful な項へ行う。
         (define core (erase-core core-in))
         (define violation (entry-violation core places callables environment))
         (when violation
           (apply fail (first violation) core-in (rest violation)))
         ;; 段 1。
         (match-define (list type row Ψ)
           (infer core-in Λ (empty-psi) environment places callables fail))
         ;; 段 2。
         (define ir (region-ctx-ir Λ))
         (define solved (typing-solve ir (reverse (unbox cs))))
         (match solved
           [(list 'error broken)
            (define c (first broken))
            (fail (constraint-key c) (constraint-node c))]
           [(list 'ok σ)
            ;; 段 3。
            (check-borrows ir σ Ψ (reverse (unbox rs)) sigma-ref fail)
            ;; 型の中の α を σ で解いてから正規化する。materialize が core の
            ;; 注釈へ行う置換と同じ σ を、型の側へも行う（spec §6.3）。
            ;; 置換を正規化より先に置くのは、Union の重複除去が置換の後で
            ;; なければ効かないためである。σ(α_1) と σ(α_2) が同じ region に
            ;; なる形では、正規化を先に置くと正規形の不変が破れる。
            (define substituted (subst-type-regions type σ ir))
            (define normalized (normalize-type substituted))
            (unless normalized
              (fail 'non-normalizable-result-type core-in substituted))
            ;; row も同じ σ で解く。Yield は観測値の型を (Yield τ) として、
            ;; Perform は (Return boundary τ) として row へ入れるため、
            ;; 借用をこれらで返すと row が α を運ぶ。
            (list normalized
                  (subst-type-regions row σ ir)
                  (unbox tbl)
                  σ)])))))
  ;; 失敗の details も同じ σ の下へ置く。段 1 の fail は脱出継続で
  ;; with-typing の外へ出るため、σ を掛ける位置はここしかない。
  (materialize-fail-result (region-ctx-ir Λ) (reverse (unbox cs)) result))

;; 既存の呼び出しは結果の型を要らない。第 3 要素と σ を落として渡す。
(define (type-of/raw core-in places callables [environment '()]
                     [Λ (empty-region-ctx)])
  (match (type-of/raw* core-in places callables environment Λ)
    [(list 'ok (list type row _table _σ)) (list 'ok (list type row))]
    [other other]))

;; 機械へ渡すため、型付けと同じ σ で core の注釈を materialize する。
(define (core-type-of/materialized core-in places callables
                                   [environment '()]
                                   [Λ (empty-region-ctx)])
  (match (type-of/raw* core-in places callables environment Λ)
    [(list 'ok (list type _row table σ))
     (define ir (region-ctx-ir Λ))
     (list 'ok type (if ir (materialize-regions ir core-in table σ) core-in))]
    [other other]))

;; 失敗の details は、型と effect row に続く 3 つ目の σ の経路である（spec §6.3）。
;; 段 1 の fail は推論の途中の型を details へ入れる。typing.rkt:1346 の
;; typing-expected/found がそれを diagnostic-of の expected と found へ
;; そのまま渡すので、α が残ると Task 3 の寿命変数の検査が型検査を
;; 異常終了させる。返す前に必ず解くか捨てるかする。
(define (materialize-fail-result ir cs result)
  (match result
    [(list 'fail key node details)
     (match (and ir (pair? cs) (typing-solve ir cs))
       [(list 'ok σ)
        (list 'fail key node
              (map (lambda (d) (subst-type-regions d σ ir)) details))]
       ;; ir が無い形と制約が空の形では α を採らない。details はそのままでよい。
       [#f result]
       ;; 段 1 が棄却した時点の制約集合は不完全である。出口の下限が欠けると
       ;; σ(α) は本来より狭くなり、α を左辺に持つ Reborrow と分岐合流の制約が
       ;; 偽に破れる。左辺が具体的な region の BOR-001 だけは向きが逆になるが、
       ;; 制約の種別で健全性が変わる規則は置かない。段 1 の key と node を保ち、
       ;; 解けない details だけを捨てる。失われるのは expected と found であり、
       ;; 診断の分類と位置は残る（spec §6.3）。
       [_ (list 'fail key node '())])]
    [_ result]))

;; 破れた上限制約から診断の key と節点を引く。
;; Task 12 が合流の制約を足すとき、ここに 1 行足せば済む形にする。
(define (constraint-key c)
  (case (region-constraint-kind c)
    [(outlives) 'borrow-escapes-owner]
    [(reborrow) 'reborrow-region-escapes]
    [else
     (error 'constraint-key "未知の region constraint kind: ~s"
            (region-constraint-kind c))]))

(define (constraint-node c) (region-constraint-node c))

;; 型の中の `(RVar k)` を σ の解へ置き換える（spec §6.3）。
;; α が現れるのは借用の 3 つ目の欄だけだが、Union や Record や NFn の中へ
;; 入れ子になるため木全体を歩く。
;; これを通さないと、`type-of` の返り値に α が残り、spec §11 の不変性が破れる。
;; effect row も同じ関数で解く。row の要素は (Return boundary τ) と (Yield τ) と
;; 記号であり、型を運ぶ欄はこの走査で覆える。validators.rkt の
;; effect-owned-free? が row の同じ 2 形から型を取り出しているのと対応する。
(define (subst-type-regions t σ ir)
  (match t
    [`(RVar ,_) (region->rho ir (sigma-ref σ t))]
    [(? list? ts) (map (lambda (x) (subst-type-regions x σ ir)) ts)]
    [_ t]))

;; 段 3 の出口で α が残っていないことを試験が見るための述語。
(define (contains-lifetime-var? t)
  (cond
    [(lifetime-var? t) #t]
    [(list? t) (ormap contains-lifetime-var? t)]
    [else #f]))

;; 段 1 の試験専用。typing の走査が訪れた point を集める。
;; 型検査の成否は問わず、走査の網羅だけを観測する。
(define (typing-visited-points core places callables [environment '()])
  (define seen (box '()))
  (parameterize ([typing-point-probe
                  (lambda (point)
                    (set-box! seen (cons point (unbox seen))))])
    (with-typing
     (lambda (fail)
       (infer core (empty-region-ctx) (empty-psi)
              environment places callables fail))))
  (unbox seen))

(define (core-type-of core-in places callables [environment '()]
                      [Λ (empty-region-ctx)])
  (match (type-of/raw core-in places callables environment Λ)
    [(list 'ok result) result]
    [_ 'ill-typed]))

;; spec §8: Diagnostic を組む位置はここ 1 箇所だけである。
;; producer は details の先頭へ expected、次へ actual を渡す
;; （G4e2 spec §3）。elaborate.rkt の distribute-details と同じ規則である。
;; key の allowlist は残す。表に無い key の details 2 件は
;; expected と actual の対ではない。
(define (typing-expected/found key details)
  (match* (key details)
    [((or 'type-mismatch
          'arity-mismatch
          'parameter-arity-mismatch
          'branch-binder-arity
          'undeclared-function-effect)
      (list expected actual))
     (values expected actual)]
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
(define (core-type-of/diagnostic core-in places callables [environment '()]
                                 [Λ (empty-region-ctx)])
  (match (type-of/raw core-in places callables environment Λ)
    [(list 'ok (list type row)) (list type row)]
    [(list 'fail key node details) (typing-diagnostic key node details)]))

(define (core-check-row core-in places callables expected [environment '()]
                        [Λ (empty-region-ctx)])
  ;; span.md §7.3: core-type-of と同じく、既存の型走査へ渡す前に投影する。
  (define core (erase-core core-in))
  (and (not (entry-violation core places callables environment))
       (type? expected)
       (check-as/boolean core-in expected environment places callables Λ)))

(define (core-check core places callables expected row [environment '()]
                    [Λ (empty-region-ctx)])
  (and (row? row)
       (let ([actual-row
              (core-check-row core places callables expected environment Λ)])
         (and actual-row (row=? actual-row row)))))

(define (config-ok? configuration callables expected row)
  ;; 検査集合は entry-violation（判定 API と診断 API の入口）と揃える。
  ;; ここは G2m config を見る別の入口であり、places を heap から導出するため
  ;; entry-violation をそのまま呼べない。あちらへ検査を足すときは同時に直す。
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

(module+ test
  (require rackunit)

  ;; fail は key ill-typed を未登録として error にしない。
  (check-equal? (with-typing (lambda (fail) (fail 'ill-typed 1)))
                '(fail ill-typed 1 ()))

  ;; registry に無い key は error になる。
  (check-exn #px"registry に無い typing の key"
             (lambda ()
               (with-typing (lambda (fail) (fail 'no-such-key 1))))))

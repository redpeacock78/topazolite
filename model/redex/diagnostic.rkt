#lang racket

(provide (struct-out diagnostic-code)
         diagnostic-code-rx
         diagnostic-registry
         diagnostic-registry-version
         diagnostic-code-of
         diagnostic-code-row)

;; error code の書式。ホワイトペーパー §13.4 の error[E-RET-003] を継承する。
(define diagnostic-code-rx #px"^E-[A-Z]{3}-[0-9]{3}$")

;; code 集合に付ける版。code を足すか廃止するサイクルごとに上げる。
;; Diagnostic の欄の形に付ける diagnostic-schema-version とは別物である。
(define diagnostic-registry-version 1)

;; registry の 1 行。
;; key は phase が診断を識別するのに使う記号であり、phase ごとに意味が違う。
;;   elaborate: reject が第 1 引数に取る reason 記号
;;   typing:    core-type-of が返す 'ill-typed
;;   origins:   verify-initial-origins が返す (forged ...) の頭
;;   lowering:  backend-matrix.rkt の diagnostic-ids の第 1 要素
;; lowering の key は feature-id であり、capability-diagnostic の reason
;; 文字列ではない。列名を reason としないのはこの取り違えを防ぐためである。
(struct diagnostic-code (code phase key title since deprecated-in)
  #:transparent)

;; 同じサイクルで入る行をまとめて作る。廃止する行が出たら、その行だけ
;; diagnostic-code を直に書いて deprecated-in を入れる。
(define (rows phase since entries)
  (for/list ([entry (in-list entries)])
    (diagnostic-code (first entry) phase (second entry) (third entry)
                     since #f)))

;; 分類内の番号は、初回割当に限り key 記号の辞書順で振る。
;; 以後の追加は分類の末尾へ続ける。番号自体に意味は無い。
(define elaborate-entries
  '(("E-SYN-001" invalid-branch "Eliminate の branch の形が不正である")
    ("E-SYN-002" invalid-branch-binders "branch の束縛子の形が不正である")
    ("E-SYN-003" invalid-syntax "Surface 式の形が不正である")
    ("E-TYP-002" cannot-synthesize "期待型なしでは型を合成できない")
    ("E-TYP-003" constructor-needs-expected-type "構築子は期待型を必要とする")
    ("E-TYP-004" eliminate-needs-expected-type "Eliminate は期待型を必要とする")
    ("E-TYP-005" invalid-resolved-type "解決した型が正規形でない")
    ("E-TYP-006" invalid-type-annotation "型注釈の形が不正である")
    ("E-TYP-007" invalid-type-application "型適用の形が不正である")
    ("E-TYP-008" invalid-type-representation "型の内部表現が不正である")
    ("E-TYP-009" invalid-type-spec "型指定の形が不正である")
    ("E-TYP-010" narrative-expression-needs-expected-type
                 "Narrative 式は期待型を必要とする")
    ("E-TYP-011" non-normalizable-type "型が正規化できない")
    ("E-TYP-012" type-mismatch "型が期待と一致しない")
    ("E-TYP-013" unknown-type "未知の型名である")
    ("E-TYP-014" unknown-type-spec "未知の型指定である")
    ("E-TYP-015" unsaturated-type "型構築子が飽和していない")
    ("E-KND-001" invalid-kind "kind の形が不正である")
    ("E-KND-002" kind-mismatch "kind が期待と一致しない")
    ("E-EFF-001" invalid-effect-label "効果ラベルの形が不正である")
    ("E-EFF-002" undeclared-function-effect "関数が宣言していない効果を残す")
    ("E-EFF-003" undeclared-recur-effect "recur が宣言していない効果を残す")
    ("E-RET-001" return-label-outside-boundary "return ラベルが境界の外にある")
    ("E-RET-002" return-outside-boundary "return が境界の外にある")
    ("E-OWN-001" drop-non-owned "Drop の対象が owned でない")
    ("E-OWN-002" move-non-owned "Move の対象が owned でない")
    ("E-OWN-003" owned-constructor-field "構築子の field に owned を置けない")
    ("E-OWN-004" owned-curry-argument "Curry の引数に owned を置けない")
    ("E-OWN-005" owned-function-capture "関数が owned を捕捉している")
    ("E-OWN-006" owned-function-parameter "関数の仮引数に owned を置けない")
    ("E-OWN-007" owned-record-field "record の field に owned を置けない")
    ("E-OWN-008" owned-recur-capture "recur が owned を捕捉している")
    ("E-OWN-009" owned-recur-parameter "recur の仮引数に owned を置けない")
    ("E-OWN-010" owned-variable-requires-move "owned 変数の参照には Move が要る")
    ("E-VAR-001" duplicate-parameter "仮引数名が重複している")
    ("E-VAR-002" unbound-variable "束縛されていない変数である")
    ("E-REC-001" duplicate-recur-binder "recur の束縛子が重複している")
    ("E-REC-002" unknown-recur-requires-partial
                 "分類 Unknown の recur は Partial の宣言を要する")
    ("E-ARI-001" arity-mismatch "与えた式の個数が期待と一致しない")
    ("E-DAT-001" constructor-type-arity "構築子の型引数の個数が合わない")
    ("E-DAT-002" constructor-type-mismatch "構築子が期待型の data 型に属さない")
    ("E-DAT-003" non-data-eliminate "Eliminate の対象が data 型でない")
    ("E-DAT-004" non-exhaustive-eliminate "Eliminate が構築子を尽くしていない")
    ("E-RCD-001" const-record-residual "const 束縛の record に残余 field がある")
    ("E-RCD-002" duplicate-record-label "record のラベルが重複している")
    ("E-RCD-003" project-non-record "Project の対象が record でない")
    ("E-RCD-004" unknown-record-label "record に無いラベルである")
    ("E-APP-001" apply-non-function "Apply の対象が関数でない")
    ("E-APP-002" curry-non-function "Curry の対象が関数でない")
    ("E-PRF-001" invalid-obligation "義務の命題が解決できない")
    ("E-PRF-002" invalid-proposition "命題が解決できない")
    ("E-PRF-003" missing-type-narrative-capability "TypeNarrativeCap を欠く")
    ("E-PRF-004" unsatisfied-proof-obligation "満たされない Proof 義務が残る")))

;; E-TYP-001 は恒久の汎用 fallback である。適用条件は「型検査に失敗したが、
;; より具体的な安定 code を割り当てられない場合」に固定する。G4d1 が
;; E-TYP-016 以降の細分類を足しても、この条件は狭めない。
(define typing-entries
  '(("E-TYP-001" ill-typed "型検査に失敗した")))

(define origins-entries
  '(("E-ORG-001" forged "origin が初期成果物に由来しない")))

;; この 4 行の並び順は backend-matrix.rkt の diagnostic-ids の並びである。
;; diagnostic-ids はこの列の射影であり、順序を変えると既存の期待値が動く。
;; title は diagnostic-ids の第 2 要素をそのまま移したものである。
(define lowering-entries
  '(("E-LOW-001" kernel-primitive
                 "Typed Core の kernel primitive は写し先を持たない")
    ("E-LOW-002" trait-primitive
                 "trait primitive は Phase 2 以降の emitter を待つ")
    ("E-LOW-003" unknown-core-form "対応表に無い Typed Core の形")
    ("E-LOW-004" unknown-core-type "op-code の入力が Typed Core の τ でない")))

(define diagnostic-registry
  (append (rows 'elaborate 1 elaborate-entries)
          (rows 'typing 1 typing-entries)
          (rows 'origins 1 origins-entries)
          (rows 'lowering 1 lowering-entries)))

;; 見つからなければ #f を返す。G4d1 は key から Diagnostic を作る関数で
;; この #f を error に変え、握り潰さない形にする。
(define (diagnostic-code-of phase key)
  (for/first ([row (in-list diagnostic-registry)]
              #:when (and (eq? (diagnostic-code-phase row) phase)
                          (eq? (diagnostic-code-key row) key)))
    (diagnostic-code-code row)))

(define (diagnostic-code-row code)
  (for/first ([row (in-list diagnostic-registry)]
              #:when (equal? (diagnostic-code-code row) code))
    row))

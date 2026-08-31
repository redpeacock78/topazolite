#lang racket

(provide (struct-out diagnostic-code)
         diagnostic-code-rx
         diagnostic-registry
         diagnostic-registry-version
         diagnostic-code-of
         diagnostic-code-row
         (struct-out diagnostic)
         make-diagnostic
         diagnostic-of
         diagnostic-schema-version
         diagnostic-valid?
         diagnostic-schema-errors)

(require racket/match
         "span-core.rkt")

;; error code の書式。ホワイトペーパー §13.4 の error[E-RET-003] を継承する。
(define diagnostic-code-rx #px"^E-[A-Z]{3}-[0-9]{3}$")

;; code 集合に付ける版。code を足すか廃止するサイクルごとに上げる。
;; Diagnostic の欄の形に付ける diagnostic-schema-version とは別物である。
(define diagnostic-registry-version 9)

;; registry の 1 行。
;; key は phase が診断を識別するのに使う記号であり、phase ごとに意味が違う。
;;   elaborate: reject が第 2 引数に取る reason 記号
;;   typing:    core-type-of/diagnostic が fail から受け取る key
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
    ("E-OWN-007" owned-record-field "record の field に owned を置けない")
    ("E-OWN-008" owned-recur-capture "recur が owned を捕捉している")
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
;; より具体的な安定 code を割り当てられない場合」に固定する。G4d4a が性質別の
;; typing 細分類を足しても、この条件は狭めない。細分類は分類部をまたいで足される
;; ため、番号の範囲では書かない。
;; 現行の G2m には、この既定経路の 5 箇所（infer の catch-all、branch-contexts
;; の br の形の検査、binding-context の bmode の else 分岐、infer の RVal の
;; 非 ProofRep 分岐、infer の Handle の非 handler 分岐）へ到達する入力が無い。
;; この行は producer に未分類時の明示分岐があり、G2m を拡張したときに実際に
;; 返りうるため置く。
(define typing-entries-v1
  '(("E-TYP-001" ill-typed "型検査に失敗した")))

(define typing-entries-v2
  '(("E-APP-003" apply-non-function "Apply の対象が関数でない")
    ("E-APP-004" curry-non-function "Curry の対象が関数でない")
    ("E-APP-005" unknown-callable "callable 表に無い callable である")
    ("E-ARI-002" arity-mismatch "与えた式の個数が期待と一致しない")
    ("E-ARI-003" branch-binder-arity "branch の束縛子の個数が構築子と合わない")
    ("E-ARI-004" parameter-arity-mismatch "仮引数の個数が宣言と一致しない")
    ("E-DAT-005" duplicate-branch-constructor "branch の構築子が重複している")
    ("E-DAT-006" non-data-eliminate "Eliminate の対象が data 型でない")
    ("E-DAT-007" non-exhaustive-eliminate "Eliminate が構築子を尽くしていない")
    ("E-DAT-008" unknown-constructor "data 型に無い構築子である")
    ("E-DAT-009" unknown-data-type "schema に無い data 型である")
    ("E-EFF-004" effectful-curry-operand "CurryVal の被演算子が効果を残す")
    ("E-EFF-005" undeclared-function-effect "関数が宣言していない効果を残す")
    ("E-OWN-011" drop-non-owned "Drop の対象が owned でない")
    ("E-OWN-012" move-non-owned "Move の対象が owned でない")
    ("E-OWN-013" owned-constructor-field "構築子の field に owned を置けない")
    ("E-OWN-016" owned-record-field "record の field に owned を置けない")
    ("E-OWN-017" owned-refined-payload "Refined の中身に owned を置けない")
    ("E-OWN-018" owned-untrusted-payload "Untrusted の中身に owned を置けない")
    ("E-OWN-019" owned-variable-requires-move "owned 変数の参照には Move が要る")
    ("E-OWN-020" unknown-place "場所表に無い場所である")
    ("E-OWN-021" unmanaged-place "Scope が管理を宣言した場所が場所表に無い")
    ("E-PRF-005" discharge-obligation-count "Discharge の証明の個数が義務と合わない")
    ("E-PRF-006" discharge-proposition-mismatch "Discharge の命題が義務と一致しない")
    ("E-PRF-007" discharge-target-not-apply "Discharge の基底が Apply でない")
    ("E-PRF-008" unsatisfied-proof-obligation "満たされない Proof 義務が残る")
    ("E-RCD-005" const-record-residual "const 束縛の record に残余 field がある")
    ("E-RCD-006" duplicate-record-label "record のラベルが重複している")
    ("E-RCD-007" project-non-record "Proj の対象が record でない")
    ("E-RCD-008" record-binding-incompatible "record 束縛の型が期待と一致しない")
    ("E-RCD-009" unknown-record-label "record に無いラベルである")
    ("E-RCD-010" unmergeable-branch-records "branch の record が統合できない")
    ("E-SYN-004" not-core-term "入力が Typed Core の項でない")
    ("E-TYP-016" error-needs-expected-type "Error は期待型を必要とする")
    ("E-TYP-017" incompatible-branch-types "branch の型が統合できない")
    ("E-TYP-018" invalid-callables "callable 表の形が不正である")
    ("E-TYP-019" invalid-environment "型環境の形が不正である")
    ("E-TYP-020" invalid-places "場所表の形が不正である")
    ("E-TYP-021" non-normal-type "入力の型が正規形でない")
    ("E-TYP-022" non-normalizable-result-type "推論した型が正規化できない")
    ("E-TYP-023" type-mismatch "型が期待と一致しない")
    ("E-VAR-003" duplicate-branch-binder "branch の束縛子が重複している")
    ("E-VAR-004" duplicate-parameter "仮引数名が重複している")
    ("E-VAR-005" non-canonical-primitive "primitive が Γ0 の canonical 値と一致しない")
    ("E-VAR-006" unbound-variable "束縛されていない変数である")
    ("E-VAR-007" unknown-primitive "Γ0 に無い primitive である")))

;; G5b の借用。分類 E-BOR を新設する。
;; 番号は実 producer が現れる段の順に連番で振る。辞書順は各段の中だけで効く。
(define typing-entries-v3
  '(("E-BOR-001" borrowed-owned-payload "Borrowed の中身に owned を置けない")
    ("E-BOR-002" borrow-region-mismatch "注釈された region が走査位置と一致しない")
    ("E-BOR-003" borrow-conflicting-alias "借用が競合する alias を作る")
    ("E-BOR-004" borrow-escapes-owner "借用が owner より長生きする")
    ("E-BOR-005" borrow-non-owned "借用の対象が owned でない")
    ("E-BOR-006" borrow-unknown-owner-region "借用の対象の所有 region が定まらない")
    ("E-BOR-007" drop-borrowed "借用中の値を Drop できない")
    ("E-BOR-008" move-borrowed "借用中の値を Move できない")
    ("E-BOR-009" reborrow-non-mutable "Reborrow の対象が可変借用でない")
    ("E-BOR-010" reborrow-region-escapes "reborrow の子 region が親を超える")
    ("E-BOR-011" borrowed-function-capture "関数が borrowed を捕捉している")
    ("E-BOR-012" borrowed-function-parameter "関数の仮引数に borrowed を置けない")
    ("E-BOR-013" borrowed-function-result "関数の結果型と証明義務に borrowed を置けない")))

;; G5c2 の place と読み書き。Task 2 で producer が現れる 3 件を先に置く。
(define typing-entries-v4
  '(("E-BOR-014" read-uncopyable-payload "読み出しの payload が複製できない型を含む")
    ("E-BOR-015" assign-through-shared "共有借用を通じて代入できない")
    ("E-BOR-016" projborrow-non-record "射影の operand が record の借用でない")
    ("E-BOR-017" projborrow-unknown-field "射影の label が row に無い")
    ("E-BOR-018" read-non-borrow "読み出しの operand が借用でない")
    ("E-BOR-019" assign-non-borrow "借用でない値へ代入できない")
    ("E-BOR-020" unresolved-borrow-owner "借用の所有者を辿れない")
    ("E-BOR-021" assign-owned-payload "所有値を含む capability へ代入できない")
    ("E-BOR-022" assign-union-variant "Union の全成分と両立しない値を代入できない")
    ("E-BOR-023" own-designator-mismatch "own の欄と designator が別の capability を指す")
    ("E-BOR-025" borrow-conflicting-use "使用が生きている借用と競合する")))

;; G5c3 段 A。分類 E-REG を新設し、E-OWN の続きを 1 件足す。
;; 分類内の番号は、初回割当に限り key 記号の辞書順で振る。
;; region-app-arity < region-app-non-forall < region-arg-not-live である。
;; E-OWN は既存の分類の続きであり、E-OWN-021 の次の番号を取る。
(define typing-entries-v5
  '(("E-REG-001" region-app-arity "region の実引数の数が束縛の数と合わない")
    ("E-REG-002" region-app-non-forall "RegionApp の関数側が region 多相でない")
    ("E-REG-003" region-arg-not-live "region の実引数が適用の位置で生きていない")
    ("E-OWN-022" own-binding-borrowed-payload "Owned の束縛の payload に借用が入る")))

;; G5c5b1。Owned の仮引数は生名と Let の連なりで符号化する。壊れた符号化を
;; 仮引数の位置ではなく本体の形で落とす。分類内の番号は E-OWN-022 の次を
;; 取る。key 記号の辞書順は
;; owned-parameter-missing-binding < owned-raw-parameter-misuse である。
(define typing-entries-v7
  '(("E-OWN-023" owned-parameter-missing-binding
                 "Owned の仮引数に対応する Let が本体に無い")
    ("E-OWN-024" owned-raw-parameter-misuse
                 "Owned の仮引数の名前が対応する Let の右辺の外に現れる")))

;; G5c5b2。Owned<NFn ...> を関数の位置へ置くときは Move または CurryVal
;; を経由する形に限る。
(define typing-entries-v8
  '(("E-OWN-025" owned-function-requires-move
                 "Owned の関数は Move を経由してのみ関数の位置へ置ける")))

;; G5c5b3b。値の内部の所有資源は producer 位置の OwnLeaf を通してのみ
;; token を得る。位置違いと wrapper の欠落を別の code で分ける。
(define typing-entries-v9
  '(("E-OWN-026" unexpected-ownleaf
                 "producer 位置でない場所に OwnLeaf が現れた")
    ("E-OWN-027" missing-ownleaf-root
                 "producer 位置の Owned が OwnLeaf で包まれていない")))

;; G5c4 と G5c5b1 で廃止した行。E-BOR-024 は表を持つ形では発火する場所が
;; 無くなり、辿れない scrutinee は E-BOR-020 で落ちる。E-OWN-015 は Owned の
;; 仮引数を本体の形で符号化して受けるため、仮引数の位置で落とす場所が
;; 無くなる。行は registry に残す。番号の再利用と意味の付け替えを凍結
;; fixture が検出できるようにするためである。
(define deprecated-typing-entries
  (list (diagnostic-code "E-BOR-024" 'typing 'capability-in-eliminate
                         "分岐の仮引数へ能力を配る形は未対応" 4 6)
        (diagnostic-code "E-OWN-014" 'typing 'owned-curry-argument
                         "Curry の引数に owned を置けない" 2 8)
        (diagnostic-code "E-OWN-015" 'typing 'owned-function-parameter
                         "関数の仮引数に owned を置けない" 2 7)))

;; G5c5b1 と G5c5b2 で廃止した行。Owned の仮引数は本体の形で符号化して
;; 受け、Owned の捕捉は Curry の固定引数へ変換して受けるため、該当位置で
;; 落とす場所が無くなる。行は registry に残す。番号の再利用と意味の付け替え
;; を凍結 fixture が検出できるようにするためである。
(define deprecated-elaborate-entries
  (list (diagnostic-code "E-OWN-004" 'elaborate 'owned-curry-argument
                         "Curry の引数に owned を置けない" 1 8)
        (diagnostic-code "E-OWN-005" 'elaborate 'owned-function-capture
                         "関数が owned を捕捉している" 1 8)
        (diagnostic-code "E-OWN-006" 'elaborate 'owned-function-parameter
                         "関数の仮引数に owned を置けない" 1 7)
        (diagnostic-code "E-OWN-009" 'elaborate 'owned-recur-parameter
                         "recur の仮引数に owned を置けない" 1 7)))

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
          deprecated-elaborate-entries
          (rows 'typing 1 typing-entries-v1)
          (rows 'typing 2 typing-entries-v2)
          (rows 'typing 3 typing-entries-v3)
          (rows 'typing 4 typing-entries-v4)
          (rows 'typing 5 typing-entries-v5)
          (rows 'typing 7 typing-entries-v7)
          (rows 'typing 8 typing-entries-v8)
          (rows 'typing 9 typing-entries-v9)
          deprecated-typing-entries
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

;; Diagnostic の欄の形に付ける版。欄の追加、削除、欄が受け付ける形の変更で
;; 上げる。code 集合に付ける diagnostic-registry-version とは別物である。
;; G4e が source-chain へ要素形を与え backend 欄を足したため 2 になった。
;; G4f1 が related へ要素形を与えたため 3 になる。
(define diagnostic-schema-version 3)

;; ホワイトペーパー §13.4 の17欄に、G4e が backend を足した18欄である。
(struct diagnostic
  (id severity category title message
   primary-span secondary-labels notes help
   expected found
   source-chain expansion-trace
   effect-context proof-context
   related fixes
   backend)
  #:transparent)

;; category は引数に取らない。2 つの入口から与えると食い違いうるため、
;; id の分類部から導出する。
(define (category-of id)
  (and (string? id)
       (regexp-match? diagnostic-code-rx id)
       (string->symbol (substring id 2 5))))

(define (make-diagnostic #:id id
                         #:severity [severity 'error]
                         #:title title
                         #:message message
                         #:primary-span primary-span
                         #:secondary-labels [secondary-labels '()]
                         #:notes [notes '()]
                         #:help [help '()]
                         #:expected [expected #f]
                         #:found [found #f]
                         #:source-chain source-chain
                         #:expansion-trace [expansion-trace '()]
                         #:effect-context [effect-context #f]
                         #:proof-context [proof-context #f]
                         #:related [related '()]
                         #:fixes [fixes '()]
                         #:backend [backend #f])
  (diagnostic id severity (category-of id) title message
              primary-span secondary-labels notes help
              expected found
              source-chain expansion-trace
              effect-context proof-context
              related fixes
              backend))

;; diagnostic.md §13: Diagnostic の生成を phase ごとに 1 箇所へ集約するための
;; 共通部分である。registry の引き当てに失敗したら既定の code へ落とさず error に
;; する。落とすと registry へ行を足し忘れたまま診断が出てしまう。
;; message へ title を入れるのは Phase 0 の暫定であり、文案との書き分けは G4f が
;; 定める。ここへ寄せておけば G4f の変更は 1 箇所で済む。
(define (span->source-chain span)
  (define kind
    (match span
      [(list '#:span '#:synthetic _ _) 'synthetic-span]
      [_ 'verbatim]))
  (list (list 'surface kind span)))

;; 寿命変数は推論の内部の名前であり、読み手へ見せる語彙ではない（spec §3.1）。
;; 印字される欄へ漏れたら、それは段 3 で σ を通し忘れた誤りである。
;; 誤りは Diagnostic を作った箇所の error として現れてほしいので、
;; 検証器ではなく producer である diagnostic-of で落とす。
(define (lifetime-var-free? v)
  (match v
    [`(RVar ,_) #f]
    [(? list? vs) (andmap lifetime-var-free? vs)]
    [_ #t]))

(define (diagnostic-of phase key
                       #:primary-span primary-span
                       #:expected [expected #f]
                       #:found [found #f]
                       #:source-chain [source-chain #f]
                       #:backend [backend #f])
  (define code (diagnostic-code-of phase key))
  (unless code
    (error 'diagnostic-of "registry に無い phase と key である: ~s ~s" phase key))
  ;; RVar は typing 相の推論内部にだけ現れる。elaborate 相の found は
  ;; 書き手が書いた surface 項をそのまま持ち得るため、相を限らないと
  ;; 構文誤りが処理系の異常終了へ変わる。
  (when (eq? phase 'typing)
    (unless (and (lifetime-var-free? expected)
                 (lifetime-var-free? found))
      (error 'diagnostic-of "診断へ寿命変数が漏れた: ~s ~s" expected found)))
  ;; spec §10: 検証器は Diagnostic 単体を受けるため phase を知らない。
  ;; phase と backend の対応はここでしか検査できない。
  (if (eq? phase 'lowering)
      (unless (memq backend '(racket-cs racketscript))
        (error 'diagnostic-of "lowering の診断は backend を要求する: ~s" backend))
      (when backend
        (error 'diagnostic-of "~a の診断は backend を取らない: ~s" phase backend)))
  (define row (diagnostic-code-row code))
  (define title (diagnostic-code-title row))
  (make-diagnostic #:id code
                   #:title title
                   #:message title
                   #:primary-span primary-span
                   #:expected expected
                   #:found found
                   #:source-chain (or source-chain
                                      (span->source-chain primary-span))
                   #:backend backend))

(define (non-empty-string? v)
  (and (string? v) (> (string-length v) 0)))

;; renderer が 1 行として出す欄は改行を含んではならない（spec §4）。
;; renderer 側で escape しないのは、escape が表示を壊さないだけで、1 行の欄へ
;; 複数行が入るという producer 側の誤りを隠すためである。入口で弾けば、誤りは
;; Diagnostic を作った箇所の error として現れる。
(define (one-line-string? v)
  (and (non-empty-string? v)
       (not (regexp-match? #rx"[\n\r]" v))))

;; relation は記号だが、Racket の記号は改行を含む綴りを取れる。語彙を制限しない
;; ことと綴りに何も要求しないことは別である。
(define (one-line-symbol? v)
  (and (symbol? v)
       (not (regexp-match? #rx"[\n\r]" (symbol->string v)))))

;; secondary-labels の要素は (list span ラベル) の 2 要素である。
;; ラベルは terminal の位置行へ 1 行として出るため改行を含めない。
(define (secondary-label-ok? v)
  (and (list? v)
       (= (length v) 2)
       (span-ok? (first v))
       (one-line-string? (second v))))

;; expected、found、effect-context、proof-context は形を検査しない。
;; phase ごとに入る値の種類が違い、共通の述語を置くと phase を跨ぐたびに
;; 緩めることになるためである。
;; expansion-trace と fixes は schema version 3 でも空を要求する。
;; related は G4f1 が要素形を定めたため、空でない list も受ける。
;; source-chain は spec §3 の frame の空でない list を要求する。
(define (source-frame-ok? v)
  (and (list? v)
       (= (length v) 3)
       (memq (first v) '(surface elaborate))
       (memq (second v) '(verbatim synthesized synthetic-span))
       (span-ok? (third v))
       #t))

(define (source-chain-ok? v)
  (and (list? v)
       (pair? v)
       (andmap source-frame-ok? v)
       (eq? (first (first v)) 'surface)
       (andmap (lambda (frame)
                 (eq? (first frame) 'elaborate))
               (rest v))))

;; related の要素は (list relation span description) の 3 要素である。
;; relation の語彙は固定しない。renderer は未知の relation を捨てず記号を
;; そのまま出すため、綴りの制約は Task 2 で 1 行に限定する。
(define (related-ref-ok? v)
  (and (list? v)
       (= (length v) 3)
       (one-line-symbol? (first v))
       (span-ok? (second v))
       (one-line-string? (third v))))

(define (diagnostic-schema-errors d)
  (define (check ok? message) (if ok? '() (list message)))
  (append
   (check (and (string? (diagnostic-id d))
               (diagnostic-code-row (diagnostic-id d)))
          "id は registry にある code でなければならない")
   (check (memq (diagnostic-severity d) '(error warning note))
          "severity は error、warning、note のいずれかでなければならない")
   (check (and (symbol? (diagnostic-category d))
               (eq? (diagnostic-category d)
                    (category-of (diagnostic-id d))))
          "category は id の分類部を記号にした値でなければならない")
   (check (one-line-string? (diagnostic-title d))
          "title は改行を含まない空でない文字列でなければならない")
   (check (non-empty-string? (diagnostic-message d))
          "message は空でない文字列でなければならない")
   (check (span-ok? (diagnostic-primary-span d))
          "primary-span は span-ok? を満たさなければならない")
   (check (and (list? (diagnostic-secondary-labels d))
               (andmap secondary-label-ok? (diagnostic-secondary-labels d)))
          "secondary-labels は (span ラベル) の list でなければならない")
   (check (and (list? (diagnostic-notes d))
               (andmap one-line-string? (diagnostic-notes d)))
          "notes は改行を含まない空でない文字列の list でなければならない")
   (check (and (list? (diagnostic-help d))
               (andmap one-line-string? (diagnostic-help d)))
          "help は改行を含まない空でない文字列の list でなければならない")
   (check (source-chain-ok? (diagnostic-source-chain d))
          "source-chain は surface で始まる frame の空でない list でなければならない")
   (check (memq (diagnostic-backend d) '(racket-cs racketscript #f))
          "backend は racket-cs、racketscript、#f のいずれかでなければならない")
   (check (null? (diagnostic-expansion-trace d))
          "schema version 3 は expansion-trace へ空を要求する")
   (check (and (list? (diagnostic-related d))
               (andmap related-ref-ok? (diagnostic-related d)))
          "related は (relation span description) の list でなければならない")
   (check (null? (diagnostic-fixes d))
          "schema version 3 は fixes へ空を要求する")))

;; primary-span が最小原因を指すかは判定しない。それは DIA-002 の内容であり、
;; G4d1 以降が phase ごとの test で示す。
(define (diagnostic-valid? d)
  (null? (diagnostic-schema-errors d)))

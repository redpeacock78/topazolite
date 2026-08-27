# Topazolite 用語集

**状態**：G2f 改訂版
**参照**：`draft/topazolite_whitepaper_draft_0.4.md` 付録 A（以下、ホワイトペーパー）
**関連文書**：`docs/specification/core-calculus.md`、`docs/specification/structural-row.md`、`docs/specification/proof-search.md`、`docs/specification/proof-value.md`、`docs/specification/trait.md`、`docs/specification/requirements.md`

## 1. 本用語集の位置づけ

本ファイルは、ホワイトペーパー付録 A の用語を基礎に、Core calculus 仕様が使う記法を加えた用語集である。
各項目には定義、ホワイトペーパーの参照節、関連する要件 ID（あれば）を書く。
要件 ID の本文は `requirements.md` を正とする。

## 2. 言語の中核用語

### Narrative

- **定義**：型、Effect、Proof、origin、展開規則を伴う意味論的関数群。単なる関数集合ではなく、実行可能な phase と権限を含む意味論的能力の束として扱う。
- **参照**：ホワイトペーパー §2.1、付録 A。
- **関連要件 ID**：NAR-001、NAR-002。

### Reserved Narrative

- **定義**：処理系の信頼済み生成関数から作られ、ユーザーが forge できない Narrative trait。`LanguageNarrative` と `TypeNarrative` の二つがある。
- **参照**：ホワイトペーパー §2.1.1 から §2.1.3、付録 A。
- **関連要件 ID**：NAR-001。

### Narrative Sugar

- **定義**：予約 Narrative を curry、compose、macro projection して作られた派生機能。第三の信頼済み根源ではない。
- **参照**：ホワイトペーパー §2.1.4、付録 A。
- **関連要件 ID**：NAR-002、CUR-002。

### TypeInfo

- **定義**：型 phase で利用可能な、kind を持つ不透明な型情報値。`TypeInfo<κ>` と書き、κ はその kind を表す。
- **参照**：ホワイトペーパー §4.1、付録 A。
- **関連要件 ID**：TYP-001、TYP-002。

### Origin / Provenance

- **定義**：Narrative、TypeInfo、Proof がどの信頼済み生成経路から派生したかを示す forge 不可能な情報。
- **参照**：ホワイトペーパー §2.1、§11.5.3、付録 A。
- **関連要件 ID**：NAR-001、NAR-002、CUR-002、PRF-001。

### Finite

- **定義**：有限ステップで正規化できることが証明された計算。
- **参照**：ホワイトペーパー §7.1、§11.5.6、付録 A。
- **関連要件 ID**：REC-001。

### Productive

- **定義**：停止しないが、任意の有限観測を有限ステップで生成できることが証明された計算。
- **参照**：ホワイトペーパー §7.1、§11.5.6、付録 A。
- **関連要件 ID**：REC-002。

### Unknown

- **定義**：有限性も生産性も証明できない計算。非安全とは限らないが、型同値と Proof 正規化には無条件で使用しない。
- **参照**：ホワイトペーパー §7.1、§7.3、付録 A。
- **関連要件 ID**：REC-001、PRF-002。

### Owned

- **定義**：高々一度 move でき、scope exit または明示操作で drop される affine resource mode。
- **参照**：ホワイトペーパー §4.7、§4.9、付録 A。
- **関連要件 ID**：OWN-001、OWN-002、OWN-003。

### Shared

- **定義**：GC、reference count、persistent data structure 等により複数箇所から安全に共有可能な値 mode。
- **参照**：ホワイトペーパー §4.7、付録 A。
- **関連要件 ID**：なし（G1 対象外）。

### Borrowed / BorrowedMut

- **定義**：owner を移動せず一時的な access capability を表す region 付き TypeInfo。`BorrowedMut` は排他的 access を要求する。
- **参照**：ホワイトペーパー §4.8、§11.5.8、付録 A。
- **関連要件 ID**：BOR-001、BOR-002（G5）。

### Region

- **定義**：borrow の有効範囲と owner の生存関係を表す静的情報。表面の lifetime parameter より一般的な内部表現として用いる。
- **参照**：ホワイトペーパー §4.8、付録 A。
- **関連要件 ID**：BOR-003（G5）。

### RawPtr

- **定義**：safe reference の lifetime / alias guarantee を持たない低レベル pointer TypeInfo。dereference には `Unsafe` Effect と Proof を要求する。
- **参照**：ホワイトペーパー §4.10、付録 A。
- **関連要件 ID**：PTR-001、PTR-002（G5）。

### Unsafe boundary

- **定義**：未解決の低レベル Proof obligation を局所的に引き受ける Narrative boundary。安全性検査を全面停止するものではない。
- **参照**：ホワイトペーパー §4.10、付録 A。
- **関連要件 ID**：PTR-001（G5）。

### User Structural Type

- **定義**：`type` により定義され、ユーザーがフィールド row を参照、合成、射影できる構造型。
- **参照**：ホワイトペーパー §4.5.1、付録 A。
- **関連要件 ID**：TYP-003（G2）。

### Field row

- **定義**：record の field ラベル、field 型、可変性からなる有限集合。
  Effect row とは別の sort であり、ラベル一意性と順序独立性を満たす。
- **参照**：ホワイトペーパー §4.5、structural-row.md §2。
- **関連要件 ID**：TYP-003、ROW-001、ROW-002、ROW-003、ROW-004（G2a）。

### 構造互換性

- **定義**：実際の型が期待型の構造上の要求を満たすかを判定する方向付きの関係。
  record では期待側の field をすべて要求し、実際側の余剰 field を許す。
- **参照**：ホワイトペーパー §4.5.1、structural-row.md §3.3。
- **関連要件 ID**：TYP-003、ROW-002、ROW-004（G2a）。

### 共変

- **定義**：合成型の互換方向が成分型の互換方向と同じ向きになる位置の性質。
  関数型の返り値と latent Effect row が該当する。
- **参照**：ホワイトペーパー §4.5.2、structural-row.md §6.1、§6.2。
- **関連要件 ID**：VAR-001、VAR-002（G2c）。

### 反変

- **定義**：合成型の互換方向が成分型の互換方向と逆向きになる位置の性質。
  関数型の引数と Proof obligation 集合が該当する。
- **参照**：ホワイトペーパー §4.5.2、structural-row.md §6.1、§6.2。
- **関連要件 ID**：VAR-001、VAR-002（G2c）。

### Substitutability

- **定義**：期待型の値が使える文脈で、実際の型の値を代わりに使っても安全であるという、互換判定の意味論的根拠。
  関数 variance の引数反変と返り値共変はこの根拠から導かれる。
- **参照**：ホワイトペーパー §4.5.2、structural-row.md §6。
- **関連要件 ID**：VAR-001（G2c）。

### 関数 variance

- **定義**：関数型どうしの構造互換性の判定規則。
  引数は反変、返り値は共変、latent Effect は共変の集合包含、Proof obligation は反変の集合包含で照合する。
- **参照**：ホワイトペーパー §4.5.2、structural-row.md §6。
- **関連要件 ID**：VAR-001、VAR-002、VAR-003（G2c）。

### Binding policy

- **定義**：型注釈が要求する field を除いた残余 row を、束縛時に拒否するか contextual type として保持するかを決める静的規則。
  G2a では `const` が拒否し、`let` が保持する。
- **参照**：ホワイトペーパー §4.5.2、structural-row.md §3.2。
- **関連要件 ID**：ROW-001、ROW-002（G2a）。

### 残余 row

- **定義**：bound の field row から注釈型と同名の field を除いた row。
  `residual(r_b, r_T)` と書き、`let` binding の現在の flow で保持する。
- **参照**：ホワイトペーパー §4.5.2、structural-row.md §2.2、§3.2。
- **関連要件 ID**：ROW-001、ROW-002（G2a）。

### Proof-bearing User Trait

- **定義**：予約 Narrative が継承した正規 trait constructor から生成され、要求 shape、Narrative origin、`ValidNarrativeTrait` Proof を持つユーザー定義 trait。
- **参照**：ホワイトペーパー §8.1、付録 A。
- **関連要件 ID**：NAR-003（Phase 1 以降）。

### Closed Row / Contextual Open Row

- **定義**：型注釈付き `const` は残余 field を許さない closed row、型注釈付き `let` は衝突しない残余 field を flow-sensitive に保持する contextual open row として検査する。
- **参照**：ホワイトペーパー §4.5.2、付録 A。
- **関連要件 ID**：ROW-001、ROW-002（G2）。

### Policy Narrative

- **定義**：row、variance、trait resolution、Proof search、ownership narrowing、normalization 等の方針を実装する、予約 Narrative から派生した Proof 付き trait。新たな trusted root ではない。
- **参照**：ホワイトペーパー §2.1.5、`policy-narrative.md` §3、§5、§6。
- **関連要件 ID**：POL-001、POL-002（G2）。

### Boundary

- **定義**：`return`、`yield`、Effect handler 等が値または制御を返す静的に識別された境界。
- **参照**：ホワイトペーパー §3.2、§11.5.4、付録 A。
- **関連要件 ID**：RET-001、RET-002、RET-003。

### Refinement

- **定義**：値が満たす命題の Proof を型に保持する機構。
  `Refined τ φ` は τ の値と φ の Proof の対であり、φ の Proof は実行時に検査されない。
- **参照**：ホワイトペーパー §4.6、proof-value.md §3.2、§3.4。
- **関連要件 ID**：RFN-001（G2）。

### Untrusted

- **定義**：外部由来で未検証の値を表す型。
  `Untrusted τ` の値は判定表に登録された validator を経由してのみ Refined になる。
- **参照**：ホワイトペーパー §6、proof-value.md §3.2、§4.2。
- **関連要件 ID**：RFN-001（G2）。

### 常在性 witness

- **定義**：制御フロー合流の全 non-Never branch に同じ型と可変性で存在した field について、その常在性を述べる命題 `Presence(label)` の Proof。
  merge 位置の局所文脈としてのみ使う。
- **参照**：ホワイトペーパー §6、proof-value.md §5.1、§5.2。
- **関連要件 ID**：RFN-002（G2）。

### discharge 互換

- **定義**：Proof obligation の反変判定において、上位型の明示記載に加えて大域候補文脈からの discharge による充足も認める互換判定。
- **参照**：ホワイトペーパー §6、proof-value.md §6.1、§6.3。
- **関連要件 ID**：RFN-003（G2）。

## 3. calculus 仕様の記法

以下は `core-calculus.md` が使う記法である。
ホワイトペーパー §11.5 の記法を基礎とし、G1 で追加した記法には参照節の代わりに `core-calculus.md` の節番号を書く。

### 未型付き縮小 Core

- **定義**：elaboration の入力となる、Narrative 情報を持たない項言語。Surface 構文から表面的な糖衣を除いた形に相当するが、Surface 構文との対応づけは Phase 1 で定める。
- **参照**：core-calculus.md §3.1。
- **関連要件 ID**：なし。

### Typed Core

- **定義**：elaboration の出力となる、型、Effect、origin の情報が確定した項言語。Redex model の簡約はこの言語の上で定義する。
- **参照**：ホワイトペーパー §11.5.1、§12、core-calculus.md §3.3。
- **関連要件 ID**：EFF-001。

### elaboration

- **定義**：未型付き縮小 Core の項を検査し、Typed Core の項へ変換する処理。型付けと変換を同時に行う。
- **参照**：ホワイトペーパー §11.5.1、core-calculus.md §4。
- **関連要件 ID**：RET-001、EFF-001。

### Γ（term bindings）

- **定義**：項変数から型への有限写像。ホワイトペーパーでは利用モードも保持するが、G1 では型だけを持つ。
- **参照**：ホワイトペーパー §11.5.1、core-calculus.md §2。
- **関連要件 ID**：なし。

### Δ（type / kind bindings）

- **定義**：型名から `TypeInfo<κ>` への有限写像。
- **参照**：ホワイトペーパー §11.5.1、§11.5.5、core-calculus.md §2。
- **関連要件 ID**：TYP-001。

### Π（proof / capability bindings）

- **定義**：Proof 名から命題と origin の組への有限写像。capability もこの形で保持する。
- **参照**：ホワイトペーパー §11.5.1、core-calculus.md §2。
- **関連要件 ID**：PRF-001。

### B（boundary stack）

- **定義**：現在 active な Narrative boundary の stack。`return` の送信先は elaboration 時にこの stack から静的に決まる。
- **参照**：ホワイトペーパー §3.2.3、§11.5.1、core-calculus.md §2。
- **関連要件 ID**：RET-001、RET-002、RET-003。

### Ω（place 状態）

- **定義**：place から利用状態への有限写像。状態は `Available`、`Moved`、`Dropped` の三値である。借用の状態は Ω へ入れず、静的な記録 Ψ が別に持つ（borrow.md §4）。
- **参照**：ホワイトペーパー §11.5.8、core-calculus.md §2、§5、borrow.md §4。
- **関連要件 ID**：OWN-001、OWN-002、OWN-003。

### Ξ（place typing）

- **定義**：place から型への有限写像。簡約途中の構成の well-formedness（⊢config）の検査で使う。
- **参照**：core-calculus.md §2、§5.1。
- **関連要件 ID**：なし。

### ε（Effect row）

- **定義**：式が発生させうる Effect の集合。`τ ! ε` の形で型に併記する。`Partial` や `Own` のように、発生する Effect ではなく簡約の性質を保守的に示す静的な marker ラベルも含む。
- **参照**：ホワイトペーパー §5.1、core-calculus.md §3.2。
- **関連要件 ID**：EFF-001。

### κ（kind）

- **定義**：TypeInfo の分類。`Type` と `κ -> κ` から構成する。
- **参照**：ホワイトペーパー §4.2、core-calculus.md §3.2。
- **関連要件 ID**：TYP-002。

### NFn

- **定義**：Narrative 関数を表す情報束。ホワイトペーパーの完全形は `NFn<P, R, εin, εout, Q, O>`（P は引数 telescope、R は返り値型、εin と εout は Effect 制約と変換、Q は Proof transformer、O は origin）。G1 では εin と εout を単一の潜在 row ε に縮約し、O を値成分へ移した `NFn<P, R, ε, Q>` を使う。
- **参照**：ホワイトペーパー §11.5.2、core-calculus.md §3.2。
- **関連要件 ID**：NAR-001、NAR-002、CUR-001。

### ComputationClass

- **定義**：計算の分類 `Finite`、`Productive`、`Unknown` の総称。
- **参照**：ホワイトペーパー §7.1、core-calculus.md §6。
- **関連要件 ID**：REC-001、REC-002。

### SearchResult

- **定義**：暗黙 Proof 探索の結果を表す meta-sort。
  `Resolved P`、`Absent`、`Ambiguous (P ...)` の三形を持ち、型 τ は拡張しない。
- **参照**：ホワイトペーパー §6.4、proof-search.md §2.1。
- **関連要件 ID**：PSR-001、PSR-002、PSR-003（G2b）。

### Goal descriptor

- **定義**：暗黙 Proof 探索が充足する命題と特殊化情報を保持する記述子。
  G2b では `(Goal φ ⊥ext)` とし、φ だけを充填する。
- **参照**：ホワイトペーパー §6.4、proof-search.md §3.1。
- **関連要件 ID**：PSR-001、PSR-002（G2b）。

### 候補文脈

- **定義**：暗黙充足に利用できる Proof 候補の有限写像。
  G2b の固定 Π0 から作る候補と、G2e/G2f の正典表から作る global 候補を決定的に合わせた Γ_pc⁰ を使う。
- **参照**：ホワイトペーパー §6.4、proof-search.md §3.2、trait.md §6.1。
- **関連要件 ID**：PSR-001、PSR-002、TRT-002、TRT-003（G2）。

### 候補同一性

- **定義**：二つの Proof 候補を同じ候補として畳めるかを決める関係。
  G2e/G2f では命題の正準鍵、origin、候補識別子、scope 識別子、priority 識別子、trait hook の組で判定する。
- **参照**：ホワイトペーパー §6.4、proof-search.md §3.3、trait.md §6.2。
- **関連要件 ID**：PSR-002、TRT-003（G2）。

### trait requirement template

- **定義**：trait が要求する field row の雛形。
  型位置に meta-level placeholder `Self` を持ち、実装対象の型で具体化した後にだけ通常の field row になる。
- **参照**：ホワイトペーパー §8.1、trait.md §4.1。
- **関連要件 ID**：TRT-001、TRT-002（G2）。

### trait hook

- **定義**：暗黙 trait 候補を、trait origin と `impl` または `derive` origin の組へ束縛する候補成分。
  候補同一性と well-formedness の両方で使う。
- **参照**：ホワイトペーパー §6.4、trait.md §6.1、§6.2。
- **関連要件 ID**：TRT-002、TRT-003（G2）。

### 合成 trait 候補

- **定義**：`Implements τ tn_out` の goal に対して、対応する intersect 行の左右成分候補の直積から作る候補。
  Γ_pc へ事前登録せず、`project-goal` の中で生成する。
- **参照**：`trait.md` §6.5、`proof-search.md` §4.1。
- **関連要件 ID**：TRT-004（G2）。

### Compose origin

- **定義**：合成 trait 候補の由来を表す `Derived(Reserved(iid), Compose(tn_out, O_A, O_B))`。
  `O_A` と `O_B` は intersect 行の左右成分候補から保持する。
- **参照**：`core-calculus.md` §3.4、`trait.md` §5.3、`proof-value.md` §7。
- **関連要件 ID**：TRT-004（G2）。

### Union 正規形

- **定義**：有限な Union を平坦化し、外部表現で整列し、型同値な要素を除き、右結合へ戻した型。
  一要素だけなら Union 構成子を残さない。
- **参照**：ホワイトペーパー §4.5.3、trait.md §3.2。
- **関連要件 ID**：CMP-001（G2）。

### FieldType witness

- **定義**：merge の特定 field が特定の branch 型を持っていたことを表す局所 Proof。
  `FieldType(label, τ)` と書き、merge 位置を越えて型や成果物へ保存しない。
- **参照**：ホワイトペーパー §4.5.3、trait.md §7.2。
- **関連要件 ID**：RFN-002、CMP-001（G2）。

### 採択可能性

- **定義**：計算クラス、SearchResult、一意性の証拠から、探索結果を暗黙充足に使えるかを判定する関係。
  `admissible?` と書く。
- **参照**：ホワイトペーパー §6.4、proof-search.md §5。
- **関連要件 ID**：PSR-002、PSR-003（G2b）。

### 分類 oracle

- **定義**：goal と候補文脈から探索計算の ComputationClass を返す型検査器側の信頼環境。
  χ と書き、検査対象の artifact からは供給しない。
- **参照**：proof-search.md §2.3。
- **関連要件 ID**：PSR-001、PSR-003（G2b）。

### 探索 oracle

- **定義**：Productive な探索の SearchResult と一意性 certificate を返す型検査器側の信頼環境。
  `Ω_search` と書き、地の文では Ωs と略記する。
- **参照**：proof-search.md §4.2。
- **関連要件 ID**：PSR-002（G2b）。

### 一意性 certificate

- **定義**：Productive な探索結果が同じ goal、候補文脈、Proof 候補に対して一意であることを示す信頼済み証拠。
- **参照**：ホワイトペーパー §6.4、proof-search.md §4.3。
- **関連要件 ID**：PSR-002（G2b）。

### ⇒ / ⇐（elaboration judgment）

- **定義**：`Γ; Δ; Π; B ⊢ e ⇒ τ ! ε ⟹ c` は項 e の型 τ と Effect row ε を合成（synthesize）し、Typed Core の c へ変換することを表す。`⇐` は期待型に対する検査（check）を表す。
- **参照**：ホワイトペーパー §11.5.1、core-calculus.md §4.1。
- **関連要件 ID**：なし。

### ⇓class（計算分類 judgment）

- **定義**：`c ⇓class Finite(p)` の形で、Typed Core の項 c の計算分類を静的解析で判定する judgment。p は判定根拠を表す。
- **参照**：ホワイトペーパー §11.5.6、core-calculus.md §6.2。
- **関連要件 ID**：REC-001、REC-002。

### 観測深度

- **定義**：Productive な計算に対して要求する観測の個数 n。観測関係 `c ⇓obs n ⟨u1, …, un⟩` は、c が有限ステップで n 個の観測値を順に生成することを表す。
- **参照**：core-calculus.md §6.1。
- **関連要件 ID**：REC-002。

### δ規則

- **定義**：整数の比較や乗算など、primitive 演算の簡約規則。初期環境の primitive にのみ与える。
- **参照**：core-calculus.md §3.5、§5.2。
- **関連要件 ID**：なし。

### bounded counterexample search

- **定義**：redex-check による反例探索を、試行数、項の深さ、評価 fuel、観測深度、discard 上限、乱数 seed を固定して行う検査。反例が出ないことは性質の証明ではなく、設定した探索範囲での反例未発見を意味する。
- **参照**：core-calculus.md §7、`model/redex/README.md`。
- **関連要件 ID**：なし。

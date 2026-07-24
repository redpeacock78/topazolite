# Topazolite 要件 ID レジストリ

**状態**：G2b 執筆版（codex 実装、claude レビュー前）
**参照**：`draft/topazolite_whitepaper_draft_0.4.md` §15（以下、ホワイトペーパー）
**関連文書**：`docs/specification/core-calculus.md`、`docs/specification/structural-row.md`、`docs/specification/proof-search.md`、`docs/specification/glossary.md`

## 1. 本レジストリの位置づけ

本ファイルは、Topazolite の要件 ID の唯一のレジストリである。
新しい要件 ID はこのファイルへの追記だけで起こし、個別の仕様書内では起こさない。

各仕様書の規則には `[REQ: <ID>]` の形の注釈を付け、Redex model のテスト名には ID を埋め込む。
一つの ID を複数の規則や複数のテストが参照してよい。
`tools/req-coverage.rkt` は本レジストリ、仕様書、テストを突き合わせ、未知 ID、重複定義、対象サイクルなのに規則かテストを欠く ID を見つけたら失敗する。

## 2. 記載形式

各要件は `### <ID>` の見出しで始まり、次の項目と本文を持つ。
状態と由来は必須、正典と検証は任意である。

- **状態**：その ID を扱うサイクルまたは Phase。値は次のいずれかとする。
  - `G1`：Phase 0 サイクル G1（用語集、Core calculus、Redex model 中核部）の対象。
  - `G2`：Phase 0 サイクル G2（構造 row、binding policy、Proof search、Policy Narrative）へ延期。
  - `G3`：Phase 0 サイクル G3（Portable Racket feature matrix）へ延期。
  - `G4`：Phase 0 サイクル G4（Diagnostic IR schema、canonical source span）へ延期。
  - `G5`：Phase 0 サイクル G5（borrow、region、unsafe boundary）へ延期。
  - `Phase 1 以降`：Phase 0 では扱わず、表面機能を実装する Phase で扱う。
  - `Phase 2 以降`：表面構文と backend を実装する Phase で扱う。
  - `Phase 3 以降`：FFI を実装する Phase で扱う。
- **由来**：`ホワイトペーパー §15` か、`新規（<起こした文書>）` のいずれか。
- **正典**：（任意）要件を担当する正典文書と節。
- **検証**：（任意）状態のサイクルで仕様と契約を定めるが、実行可能な検証が後の Phase の成果物に依存する場合、その Phase を書く。この項目を持つ ID は、状態のサイクルでは仕様書の規則注釈だけを要求し、テストは検証 Phase で要求する。

本文はホワイトペーパー §15 の文言をそのまま転記する。
新規 ID の本文は起こした時点の文言を正とする。

状態が `G1` の ID は、`core-calculus.md` の規則注釈と Redex model のテストの両方で参照されなければならない。
状態が `G2` で G2a の明示集合に含まれる ID は、`structural-row.md` の規則注釈と G2a テストの両方で参照されなければならない。
状態が `G2` で G2b の明示集合に含まれる ID は、`proof-search.md` の規則注釈と G2b テストの両方で参照されなければならない。
延期された ID は、担当サイクルまたは Phase の設計時に同じ規則で扱う。

## 3. 要件一覧

### NAR-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

予約 Narrative trait は makeNarrativeTrait 以外から生成できない。

### NAR-002

- **状態**：G1
- **由来**：ホワイトペーパー §15

派生 Narrative は origin chain を保持しなければならない。

### NAR-003

- **状態**：Phase 1 以降
- **由来**：ホワイトペーパー §15

ユーザー trait は予約 Narrative が継承した正規 trait constructor を経由し、ValidNarrativeTrait Proof を保持しなければならない。

### POL-001

- **状態**：G2
- **由来**：ホワイトペーパー §15

標準 Policy Narrative は LanguageNarrative / TypeNarrative から派生し、新たな trusted root を作ってはならない。

### POL-002

- **状態**：G2
- **由来**：ホワイトペーパー §15

Policy Narrative の返却値は kernel kind / Proof / Core invariant の検証を通過しなければならない。

### CUR-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

curry は返り値型、Effect、Proof obligation を正しく特殊化する。

### CUR-002

- **状態**：G1
- **由来**：ホワイトペーパー §15

curry は予約 origin を新規生成してはならない。

### TYP-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

型位置には正規の TypeInfo<κ> のみ置ける。

### TYP-002

- **状態**：G1
- **由来**：ホワイトペーパー §15

TypeInfo の kind application は飽和または明示的型関数でなければならない。

### TYP-003

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/structural-row.md` §3.3、§3.4

ユーザー record type は構造 row を公開するが、予約 Narrative と予約基本型の内部表現は structural matching の対象外である。

### ROW-001

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/structural-row.md` §3.2

`const x : T = e` では、T と互換な必須 row を除く残余 row は空でなければならない。

### ROW-002

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/structural-row.md` §3.1、§3.2

`let x : T = e` では、T と同名 field の型・可変性・ownership が互換である限り、残余 row を contextual type として保持できる。

### ROW-003

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/structural-row.md` §3.5

制御フロー合流時の row merge は、全経路で安全に利用可能であることを Proof できる field のみを無条件利用可能として残す。

### ROW-004

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/structural-row.md` §3.1、§3.3

mutable field は代入安全性を守るため既定で不変として扱う。

### TRT-001

- **状態**：G2
- **由来**：ホワイトペーパー §15

trait requirement の shape 一致だけでは Implements Proof を生成してはならない。

### TRT-002

- **状態**：G2
- **由来**：ホワイトペーパー §15

`impl` / `derive` は正規 origin を持つ Proof<Implements<T, Trait>> を返さなければならない。

### TRT-003

- **状態**：G2
- **由来**：ホワイトペーパー §15

暗黙 trait resolution は一意な候補を確定できなければならない。Ambiguous candidate はエラーとする。

### PSR-001

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/proof-search.md` §2.3

暗黙 Proof search は ComputationClass と SearchResult を独立に返さなければならない。

### PSR-002

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/proof-search.md` §4.3、§5.1

標準暗黙挿入は Finite<Resolved<Unique<P>>>、または有限時間で一意性が確定すると Proof された Productive search のみを採用する。

### PSR-003

- **状態**：G2
- **由来**：ホワイトペーパー §15
- **正典**：`docs/specification/proof-search.md` §5.2

Unknown search は暗黙に継続せず、明示 Proof、探索境界、または termination Proof を要求する。

### RET-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

return の boundary は elaboration 時に静的に解決される。

### RET-002

- **状態**：G1
- **由来**：ホワイトペーパー §15

式 Narrative の return は当該式の返り値型と unify する。

### RET-003

- **状態**：G1
- **由来**：ホワイトペーパー §15

文 Narrative は明示的に指定されない限りローカル return boundary を作らない。

### EFF-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

展開後 Core の Effect row は展開前に宣言された Effect の部分集合でなければならない。

### PRF-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

予約 Proof はユーザーコードから forge できない。

### PRF-002

- **状態**：G1
- **由来**：ホワイトペーパー §15

Unknown Proof は definitional equality の自動正規化に使用しない。

### PRF-003

- **状態**：G1
- **由来**：ホワイトペーパー §15

Proof term は既定で型同一性に対して irrelevant とし、provenance / capability identity は relevant とする。

### REC-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

Finite 判定は sound でなければならないが complete である必要はない。

### REC-002

- **状態**：G1
- **由来**：ホワイトペーパー §15

Productive 判定は各有限観測が有限計算で得られることを保証する。

### MAC-001

- **状態**：Phase 1 以降
- **由来**：ホワイトペーパー §15

ユーザーマクロの展開結果は再度 type/effect/proof/origin 検査を受ける。

### SCP-001

- **状態**：Phase 1 以降
- **由来**：ホワイトペーパー §15

`let` binding は既定で immutable とし、再代入には `mut` を要求する。

### SCP-002

- **状態**：Phase 1 以降
- **由来**：ホワイトペーパー §15

shadowing は新規 binding として扱い、同一 place の assignment と区別する。

### OWN-001

- **状態**：G1
- **由来**：ホワイトペーパー §15

`Owned<T>` は move 後に再利用できない。

### OWN-002

- **状態**：G1
- **由来**：ホワイトペーパー §15

scope exit は未消費の affine resource を高々一度 drop する。

### OWN-003

- **状態**：G1
- **由来**：ホワイトペーパー §15

非局所 return / Effect escape を含むすべての scope exit path が cleanup を実行する。

### OWN-004

- **状態**：Phase 1 以降
- **由来**：ホワイトペーパー §15

構造型 narrowing が余剰 Owned field を失う場合、borrowed view、明示 projection、または RemainderSafelyDropped Proof を要求する。

### BOR-001

- **状態**：G5
- **由来**：ホワイトペーパー §15

safe borrow は owner より長生きしてはならない。

### BOR-002

- **状態**：G5
- **由来**：ホワイトペーパー §15

mutable borrow の有効期間中、競合する alias を許可しない。

### BOR-003

- **状態**：G5
- **由来**：ホワイトペーパー §15

初期 lexical region 解析は将来の NLL region solver と置換可能な IR を持つ。

### PTR-001

- **状態**：G5
- **由来**：ホワイトペーパー §15

raw pointer の dereference は `Unsafe` Effect と必要 Proof obligation を要求する。

### PTR-002

- **状態**：G5
- **由来**：ホワイトペーパー §15

raw pointer から safe reference を構築するには lifetime、alignment、validity の Proof を要求する。

### BIT-001

- **状態**：Phase 2 以降
- **由来**：ホワイトペーパー §15

`.&.`、`.|.`、`.^.`、`.<<.`、`.>>.` は単一 token として parse される。

### BIT-002

- **状態**：G3
- **由来**：ホワイトペーパー §15
- **検証**：Phase 2 以降（fixed-width integer / bit conformance の実装）

固定幅整数の bit 演算結果は backend に依存せず同一でなければならない。

### BIT-003

- **状態**：Phase 2 以降
- **由来**：ホワイトペーパー §15

`|` と `&` は型位置では Union / Intersection として解決される。

### BAK-001

- **状態**：G3
- **由来**：ホワイトペーパー §15
- **検証**：Phase 2 以降（Portable Racket emitter と Racket runtime の実装）

Portable Racket lowering は Typed Core の型・Effect・評価順を保存する。

### BAK-002

- **状態**：G3
- **由来**：ホワイトペーパー §15
- **検証**：Phase 3 以降（RacketScript runtime と Portable Racket conformance suite の実装）

Racket CS と RacketScript runtime は共通 semantic conformance suite を通過する。

### BAK-003

- **状態**：G3
- **由来**：ホワイトペーパー §15
- **検証**：Phase 3 以降（backend 未対応機能の明示診断）

未対応 backend feature は silent fallback せず capability diagnostic を返す。

### FFI-001

- **状態**：Phase 3 以降
- **由来**：ホワイトペーパー §15

foreign binding は ABI、ownership、nullability、Effect を明示しなければならない。

### FFI-002

- **状態**：Phase 3 以降
- **由来**：ホワイトペーパー §15

C++ exception は C ABI boundary を越えてはならない。

### FFI-003

- **状態**：Phase 3 以降
- **由来**：ホワイトペーパー §15

外部 pointer を safe Topazolite value として公開する前に正規 Proof を要求する。

### DIA-001

- **状態**：G4
- **由来**：ホワイトペーパー §15

すべての compiler phase は文字列ではなく Diagnostic IR を生成する。

### DIA-002

- **状態**：G4
- **由来**：ホワイトペーパー §15

Diagnostic の primary span は利用可能な最小原因 span を指す。

### DIA-003

- **状態**：G4
- **由来**：ホワイトペーパー §15

Diagnostic は Surface origin と expanded/Core origin を追跡可能でなければならない。

### DIA-004

- **状態**：G4
- **由来**：ホワイトペーパー §15

terminal、LSP、JSON renderer は同一 Diagnostic IR を入力とする。

### DIA-005

- **状態**：G4
- **由来**：ホワイトペーパー §15

error code は安定識別子として versioning される。

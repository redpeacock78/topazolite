# Topazolite 暗黙 Proof 探索仕様（G2b）

**状態**：G2b 執筆版（codex 実装、claude レビュー前）
**基底仕様**：`docs/specification/core-calculus.md`（以下、G1 仕様）
**参照**：`draft/topazolite_whitepaper_draft_0.4.md`（以下、ホワイトペーパー）§6.3、§6.4、§7.1
**関連文書**：`docs/specification/structural-row.md`、`docs/specification/glossary.md`、`docs/specification/requirements.md`

## 1. 本仕様の位置づけ

本文書は、G1 仕様の Proof 値、Proof 型、Proof obligation、origin 検証、計算分類の上に、暗黙 Proof 探索の静的な義務充足を追加する差分仕様である。
本文書に定義がない型付け規則と elaboration 規則は G1 仕様に従う。
Redex model の G2b 実装は本文書を正とし、実装との乖離が見つかった場合は本文書を先に修正する。

G2b は探索結果の解決と採択だけを扱う。
Typed Core の構文、値、評価文脈、簡約関係は G2a から変更しない。

規則には `[REQ: <ID>]` の形で要件 ID を注釈する。
要件 ID の本文は `requirements.md` を正とする。

## 2. 探索結果と計算クラス

### 2.1 SearchResult

暗黙 Proof 探索の結果を表す meta-sort を追加する。

```text
P  ::= (ProofRep O φ)
SR ::= (Resolved P) | Absent | (Ambiguous (P ...))
```

**SearchResult** SR は型 τ の構成子ではなく、型検査時にだけ現れる meta オブジェクトである。
したがって `type-equiv?`、`type?`、実行時の値、簡約規則は SR の追加によって変わらない。

`Resolved P` は、解決対象の候補集合が一つの P に畳まれた結果を表す。
`Absent` は候補が存在しない結果を表す。
`Ambiguous` は一つに畳めない複数の候補を canonical order で保持する。

`Resolved P` は探索空間全体での一意性を単独では保証しない。
ホワイトペーパーの `Unique<P>` に対応する条件は、§4.3 の導出または certificate が別に保証する。

### 2.2 ComputationClass の再利用

探索計算の分類には G1 の `ComputationClass` を使う。

```text
ComputationClass ::= Finite | Productive | Unknown
```

G2b は新しい停止性モデルを導入しない。
実際の探索計算を組み立てて `⇓class` で分類する処理は後続層へ送り、G2b はその分類結果を信頼できる入力として受け取る。

### 2.3 分類 oracle と二軸の独立

**分類 oracle** χ は、goal と候補文脈から探索計算の `ComputationClass` を返す型検査器側の信頼環境である。

```text
χ(goal, Γ_pc) = class
```

χ は検査対象の artifact が供給せず、型検査器を parameterize する。
この配置により、手書きの artifact は `Unknown` を `Finite` と偽れない。

`ComputationClass` と `SearchResult` は独立した軸である。
class は χ から得て、SR は §4 の候補解決または探索 oracle から得る。

```text
proof-search(goal, Γ_pc, χ, Ω_search) = (class, SR)
```

したがって `Resolved` であることは `Finite` を含意せず、`Unknown` であることは `Absent` を含意しない。 [REQ: PSR-001]

## 3. Goal と候補文脈

### 3.1 Goal descriptor

探索対象を goal descriptor で表す。

```text
goal ::= (Goal φ ext)
ext  ::= ⊥ext
φ    ::= ValidNarrativeTrait | TypeNarrativeCap
```

**Goal descriptor** goal は、充足する命題 φ と特殊化情報 ext を持つ。
G2b は ext を空の `⊥ext` とし、型、Effect、lexical environment による特殊化は後続層へ送る。

### 3.2 初期候補文脈

**候補文脈** Γ_pc は、暗黙充足に利用できる Proof 候補の有限写像である。

```text
Γ_pc ::= ((name entry) ...)
entry ::= (φ O cid sid pid hook)
```

entry の φ は候補が充足できる命題を表し、O は候補 P の origin を表す。
cid は候補識別子、sid は scope 識別子、pid は priority 識別子である。
hook は trait origin と `impl` または `derive` Proof を後続層で加える位置であり、G2b では空とする。

G2b の初期候補文脈を次で定める。

```text
Γ_pc⁰ = candidateize(Π0)
```

`candidateize` は Π0 の各 name から一つの entry を作る。
cid は name、sid は `root`、pid は `default` から決定的に構成する。
実行ごとに変わる gensym や counter は使わない。

G2b の Core には局所 Proof 束縛がないため、候補文脈は項を降りても成長しない。
すべての義務位置は同じ Γ_pc⁰ を使う。

可視な候補環境は次の射影で得る。

```text
project(Γ_pc, sc-ctx) = Σ
Σ    ::= (cand ...)
cand ::= (Candidate P cid sid pid hook)
```

`project` は scope 文脈 `sc-ctx` から sid が可視な entry だけを Σ へ写す。
G2b の通常の探索位置では `root` が可視である。

### 3.3 候補同一性と well-formedness

**候補同一性**は、二つの候補を同じ候補として畳める条件である。
G2b は `(φ, O, cid, sid, pid)` の五つ組が一致するときに限って候補を同一視する。
trait 由来の同一性成分が空の間も provenance と cid を含めるため、判別できない候補を誤って一つに畳まない。

**wf-candidate** は候補が次の条件をすべて満たすことを表す。

- 候補 P が `(ProofRep O φ)` の形である。
- O が φ の正当な発行者であり、forge された origin でない。
- sid が探索位置から可視である。
- cid と pid が `candidateize` の決定規則に従う。
- hook が空である。

**wf-context** は、Γ_pc のすべての entry が候補単体の条件を満たすことを表す。
wf-context は特定の goal との命題一致を要求しない。

goal ごとの候補集合を次で定める。

```text
Σ_goal = project-goal(Γ_pc, sc-ctx, goal)
```

`project-goal` は scope から可視な候補のうち、命題が goal と一致する候補を漏れなく抽出する。

**wf-Σ** は、Σ_goal のすべての候補が wf-candidate を満たし、命題が goal と一致することを表す。
Finite な探索では、Σ_goal がその goal に対する可視候補を漏れなく含む完全な集合であることも要求する。
`project-goal` は Γ_pc から構成上 wf-Σ を満たす Σ_goal を返す。

## 4. 候補解決と一意性

### 4.1 Finite な候補解決

Finite な closed-world 探索の解決を次の全域メタ関数で定める。

```text
resolve-candidates(goal, Σ) = SR
```

`resolve-candidates` は goal の φ と一致する候補を集め、§3.3 の候補同一性で重複を除く。
残る候補が 0 個なら `Absent`、1 個なら `Resolved`、2 個以上なら `Ambiguous` を返す。
`Ambiguous` の候補は cid の順に並べる。
この集合演算と canonical order により、結果は Σ の記述順に依存しない。

### 4.2 計算クラスごとの探索結果

Finite と Productive は候補空間の性質が異なるため、SR の入手経路を分ける。

- **Finite**：χ が `Finite` を返し、`resolve-candidates(goal, project(Γ_pc, sc-ctx))` から SR を得る。
- **Productive**：χ が `Productive` を返し、SR と一意性 certificate を探索 oracle Ωs から得る。
- **Unknown**：χ が `Unknown` を返し、探索を起動せず却下する。

**探索 oracle** `Ω_search` は Productive な探索の SR と certificate を返す型検査器側の信頼環境である。
地の文では `Ω_search` を Ωs と略記する。
G2b は Productive な候補列を自ら枚挙しない。

### 4.3 一意性の証拠

Finite では、完全な wf-Σ に対して `resolve-candidates` が `Resolved P` を返す導出を一意性の証拠とする。

```text
Σ = project(Γ_pc, sc-ctx)
Σ は完全な wf-Σ
resolve-candidates(goal, Σ) = (Resolved P)
------------------------------------------------------------
unique(goal, Σ, P)
```

Productive では、有限前置きの一意性から候補列全体の一意性を導けない。
このため Ωs が、同じ goal、Γ_pc、P、`Productive` に束縛された**一意性 certificate**を返さなければならない。

```text
Ω_search(goal, Γ_pc) = ((Resolved P), cert)
cert = Cert(goal, Γ_pc, P, Productive)
```

certificate は検査対象の artifact が供給する裸の項ではない。
別の goal、候補文脈、P に対する certificate は流用できない。

## 5. 採択規則

### 5.1 採択可能性

**採択可能性** `admissible?` は、探索結果を暗黙充足に使えるかを判定する。

```text
admissible?(goal, Γ_pc, class, SR, ev) = #t | #f
```

ev は Finite では goal ごとに抽出した完全な Σ_goal から得た一意性の導出であり、Productive では Ωs が返す certificate である。
採択規則を次で定める。

- `(Finite, Resolved P)` は、`ev = Σ_goal` が wf-Σ を満たし、`unique(goal, ev, P)` を再検査できるときに採択する。
- `(Productive, Resolved P)` は、certificate が同じ goal、Γ_pc、P に対して有効なときに採択する。
- `Absent` と `Ambiguous` は計算クラスによらず採択しない。

標準の暗黙挿入は、Finite で一意性を導出できる候補か、Productive で一意性 certificate を検査できる候補だけを採択する。 [REQ: PSR-002]

### 5.2 Unknown の拒否

`(Unknown, SR)` は SR の形によらず採択しない。
Unknown な探索は暗黙に継続せず、明示 Proof、探索境界、termination Proof のいずれかを要求する。 [REQ: PSR-003]

探索境界と termination Proof は、探索計算を有限化して χ の分類を `Finite` へ移す後続機能である。
明示 Proof は暗黙探索を経ずに Proof 値を与える別経路である。
G2b はこれらの構築を扱わず、Unknown を却下する判定だけを持つ。

## 6. 型検査への接続

### 6.1 義務充足 judgment

Proof obligation の暗黙充足を次の judgment で表す。

```text
Γ_pc; χ; Ω_search ⊢discharge goal
```

この judgment は次の順に判定する。

1. `class = χ(goal, Γ_pc)` を得る。
2. class に応じて §4.2 の経路から SR と証拠 ev を得る。
3. `admissible?(goal, Γ_pc, class, SR, ev)` が真であれば充足に成功する。

`admissible?` が真になるのは `Resolved P` の枝だけなので、成功時に使う P は一意に定まる。

### 6.2 elaboration と `⊢core` の一致

NFn の Proof obligation 列 Q に含まれるすべての φ は、対応する `(Goal φ ⊥ext)` に対して `⊢discharge` を満たさなければならない。
一つでも充足できなければ、適用は型エラーになる。

elaboration と `⊢core` は、どちらも固定の Π0 から `candidateize` した Γ_pc⁰ と、同じ χ と Ωs を使う。
Γ_pc⁰ の識別子は決定的なので、両経路は同じ候補文脈を再構成する。
この共有により、elaboration が受理した義務は `⊢core` の再検査でも同じ結果になる。

充足の証拠は artifact に保存しない。
`⊢core` は各義務位置で `⊢discharge` を再導出する。
χ と Ωs は型検査器側の信頼環境であり、手書きの artifact は計算クラスや certificate を注入できない。

### 6.3 Proof の非実体化

G2b は義務を受理できるかだけを判定し、選択した P を Typed Core の項へ埋め込まない。
G2b の下流には候補の provenance や capability identity を利用する処理がないため、この範囲では P の搬送経路を要しない。

Proof term の provenance は PRF-003 により relevant である。
したがって、候補の provenance を下流で利用する処理を導入するときは、選択した P を artifact または項へ搬送する経路を別に定めなければならない。

## 7. 後続層との境界

G2b は暗黙 Proof 探索の静的な骨格に範囲を限る。
次の機能は後続層で定める。

- trait 型と `impl` または `derive` を使う暗黙 trait resolution。
- trait origin と `impl` または `derive` Proof を含む候補同一性。
- **異種命題の候補文脈**：カーネル命題の範囲は G2d が `proof-value.md` §6.3 として回収し、goal ごとの候補抽出と候補文脈全体の well-formedness を分けた。
  trait 由来の候補同一性は trait 層に残る。
- 局所 Proof 束縛による候補文脈の成長と scope ごとの統合性質。
- 実際の探索計算、その `⇓class` 導出、Productive の SR と certificate の構築。
- Unknown を有限化する探索境界と termination Proof。
- priority による候補の勝者選択。
- 選択した候補の provenance の実体化と下流利用。

これらを導入するまでは、複数の候補を保守的に `Ambiguous` とし、G2b の簡約関係と評価文脈を変更しない。

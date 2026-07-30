# Topazolite trait 層仕様

**状態**：G2e 執筆版（codex 実装、claude レビュー前）
**参照**：`draft/topazolite_whitepaper_draft_0.4.md` §4.5.3、§6.4、§8.1、§15（以下、ホワイトペーパー）
**関連文書**：`core-calculus.md`、`structural-row.md`、`proof-search.md`、`proof-value.md`、`requirements.md`、`glossary.md`

## 1. 本仕様の位置づけ

本文書は、G2 の型へ有限な Union と構造型の Intersection を加え、正典表から trait の型、Proof、暗黙候補を導く差分仕様である。
本文書に定義がない型付け規則、簡約規則、候補探索規則、成果物検証規則は、関連文書に従う。
Redex model の G2e 実装は本文書を正とし、実装との乖離が見つかった場合は本文書を先に修正する。

規則には `[REQ: <ID>]` の形で要件 ID を注釈する。
要件 ID の本文は `requirements.md` を正とする。

## 2. 範囲と前提

G2e は、次の対象を扱う。

- `Union` の有限な正規化と互換判定。
- record 行の合成で消去できる構造型の `Intersection`。
- trait、実装、二項合成を記録する三つの正典表。
- `impl` と `derive` の単相 kernel primitive、および表由来の Proof。
- trait origin と実装 origin を含む候補同一性。
- scope 識別子による coherence の近似。
- 制御フロー合流における `imm` field の Union join と局所 witness。

正典表と merge が受け取る型は、正規形であり、record の label が一意であることを前提とする。
表由来の型は読み込み時に検査し、型付け経路の型は成果物境界の正規性検査でこの前提を課す。
この前提を満たさない値を meta-level API へ直接渡した場合の結果は、本仕様の対象外である。

## 3. 型と命題

### 3.1 構文

G2 の型と命題へ次の構成子を加える。

```text
τ  ::= .... | (Union τ τ) | (Intersection τ τ)
tn ::= id
φ  ::= .... | (ValidNarrativeTrait tn)
            | (Implements τ tn)
            | (RequiresBoth tn tn)
            | (FieldType label τ)
```

`Union` と `Intersection` は二項構成子である。
三つ以上の Union 要素は、右結合の入れ子で表す。

UCore は `Union` と `Intersection` を型注釈に持てる。
UCore の命題注釈は `(ValidNarrativeTrait tn)`、`(Implements uτ tn)`、`(RequiresBoth tn tn)` を持てる。
`FieldType` は merge 位置だけで生成する局所命題であるため、UCore の注釈には書けない。

G1 の引数を取らない `ValidNarrativeTrait` と、G2e の `(ValidNarrativeTrait tn)` は別の命題である。
引数を取らない形は G1 が置いた予約席であり、発行者も暗黙候補も持たない。
引数を取る形は trait ごとに異なる命題であり、Γ0 では、§4 の trait 定数だけがその Proof を供給する。

### 3.2 Union の正規形

有限に正規化できる Union を、次の手順で一意の正規形へ写す。 [REQ: CMP-001]

1. 各構成要素を再帰的に正規化する。
2. 入れ子の Union を要素列へ平坦化する。
3. 型の外部表現を文字列として昇順に並べる。
4. 各要素を、それまでに保持したすべての要素と `type-equiv?` で比較し、同値な要素を捨てる。
5. 残った要素を右結合に戻し、一要素だけなら Union を作らない。

重複除去を整列より後に置くことで、同値類の代表は入力順に依存しない。
保持済みの全要素と比較することで、外部表現順で隣接しない同値要素も一つに畳める。

`compat?(sub, sup)` は、どちらかが Union なら両辺を要素列として扱う。
判定は、sub の各要素について sup のいずれかの要素が互換であることを要求する。
この単一規則は、両辺が Union の場合も同じ分岐を通すため、節順に意味を預けない。

型注釈、型付け結果、正典表の型、設定内の型は正規形でなければならない。
正規化に失敗する型と、消去されずに残った Intersection は、成果物の境界で拒否する。
作用列と Proof obligation 列は並べ替えず、列に埋め込まれた型だけを正規化する。

### 3.3 構造型の Intersection

構造型の Intersection は、両辺の record 行を `field-row-⊕` で合成して消去する。 [REQ: CMP-002]
合成後の record 行は label の昇順に並べる。
両辺に同じ label がある場合は、field 型が同じでも衝突として正規化を拒否する。
少なくとも一方が record でない Intersection も正規化を拒否する。

trait の Intersection は、この型構成子では表さない。
trait の二項合成は、§4.3 の `intersect-table` と `RequiresBoth` Proof で表す。

### 3.4 命題の正準鍵

`canonical-proposition-key` は、命題に埋め込まれた型を正規化し、型同値と一致する鍵を作る。
record 行は鍵の内部だけで label 順に並べ、プログラム中の record の field 順は書き換えない。
`RequiresBoth A B` の trait 名は symbol 順に並べるため、左右を入れ替えた命題は同じ鍵を持つ。

命題の一致、候補同一性、Proof 発行者の照合、関数型の obligation 包含は、同じ命題同値判定を使う。
正準鍵を作れない命題は、構文一致へ退化させる。
この退化により、鍵が作れない別命題を同一視せず、同じ命題に対する反射性も保つ。

## 4. trait の正典表

### 4.1 trait-table

`trait-table` の行は、次の四要素を持つ。

```text
(tid tn sid_trait template)
```

`tid` は trait origin、`tn` は trait 名、`sid_trait` は trait を生成した scope である。
`template` は requirement field の行であり、型位置に meta-level placeholder `Self` を持てる。
`Self` は型文法に属さず、実装対象の型 τ で `instantiate-requirements(template, τ)` を行った後にだけ通常の field row になる。

G2e の表は、次の四行を持つ。

```text
(o-trait-printable Printable root
  ((print (NFn (Self) String () ()) imm)))
(o-trait-sizable Sizable root
  ((size (NFn (Self) Int () ()) imm)))
(o-trait-printable-sizable PrintableSizable root
  ((print (NFn (Self) String () ()) imm)
   (size (NFn (Self) Int () ()) imm)))
(o-trait-taggable Taggable s-kernel
  ((tag (NFn (Self) String () ()) imm)))
```

`PrintableSizable` は、`Printable` と `Sizable` の requirement を衝突なく合わせた合成 trait である。

### 4.2 impl-table

`impl-table` の行は、次の六要素を持つ。

```text
(oid nm kind tn τ sid_target)
kind ::= impl | derive
```

`oid` は実装 Proof の origin、`nm` は kernel primitive 名、`kind` は宣言の由来である。
`tn` と τ は実装する trait と対象型を表し、`sid_target` は対象型を生成した scope を表す。
行は、`Record(instantiate-requirements(template-of(tn), τ))` の shape が検査済みである信頼された宣言である。
実装 record の値自体は表に保存しない。

G2e の表は、次の五行を持つ。

```text
(o-impl-printable-int impl-printable-int impl Printable Int root)
(o-derive-sizable-int derive-sizable-int derive Sizable Int root)
(o-impl-printable-str-a impl-printable-str-a impl Printable String root)
(o-impl-printable-str-b impl-printable-str-b impl Printable String root)
(o-impl-taggable-bool impl-taggable-bool impl Taggable Bool s-user)
```

一行目は一意解決、二行目は `derive` 経路、三行目と四行目は曖昧性、五行目は coherence の検査に使う。

### 4.3 intersect-table

`intersect-table` の行は、次の五要素を持つ。

```text
(oid nm tn_left tn_right tn_out)
```

`tn_left` と `tn_right` は symbol 順に並べる。
逆順の入力は命題の正準化で同じ対へ写す。
両辺の requirement template は衝突なく合成でき、その結果が `tn_out` の template と一致しなければならない。

G2e の表は、次の一行を持つ。

```text
(o-intersect-print-size intersect-printable-sizable
 Printable Sizable PrintableSizable)
```

### 4.4 読み込み時検査と環境の導出

表の読み込み時に、trait 名、origin 識別子、primitive 名の一意性を検査する。
各行が参照する trait の存在、template の label 一意性、`Self` の出現位置、具体化後の型の整形式性と正規性も検査する。
合成行については、trait 名の順序、row 合成の成功、出力 template との一致を検査する。
R0 と Γ0 へ追加した後に、既存 kernel 行との key 衝突も検査する。

各 trait 行から、次の Γ0 定数を導く。

```text
tn-trait : Proof<(ValidNarrativeTrait tn)>
```

各 impl 行から、次の Γ0 primitive を導く。

```text
nm : NFn<Record(instantiate-requirements(template-of(tn), τ)),
         Proof<Implements<τ, tn>>, (), ()>
```

各 intersect 行から、次の Γ0 primitive を導く。

```text
nm : NFn<Proof<ValidNarrativeTrait<tn_left>>,
         Proof<ValidNarrativeTrait<tn_right>>,
         Proof<RequiresBoth<tn_left, tn_right>>, (), ()>
```

R0 は、trait origin を `(trait tn)` へ、impl と intersect の origin を `(prim nm)` へ対応させる。
表由来の名前または引数個数が合わない δ 適用は `undefined` を返し、既存の R-Delta を不発火にする。

## 5. Proof の生成と検証

### 5.1 shape 一致と宣言 origin

requirement と同じ shape の record を持つことだけでは、`Implements τ tn` Proof を生成しない。 [REQ: TRT-001]
shape の検査は impl primitive の引数型を満たすために必要だが、Proof の権威にはならない。
Proof の発行には、`impl-table` の行へ結び付いた予約 origin が必要である。
この分離により、同じ field を持つ手書き record は実装宣言を偽造できない。

### 5.2 impl と derive

`kind` が `impl` と `derive` のどちらでも、対応する単項 primitive は同じ形の Proof を返す。 [REQ: TRT-002]

```text
impl-table に (oid, nm, kind, tn, τ, sid_target) がある
δ(nm, record)
  = ProofRep(Reserved(oid), Implements<τ, tn>)
```

δ 規則は `kind` を分岐条件に使わない。
`kind` は Proof の形ではなく、宣言を生成した経路の違いを記録する。
表層構文の `derive` が実装 record を自動生成する規則は、§9 へ送る。

### 5.3 発行者対応と出現許可

`ValidNarrativeTrait tn` は、対応する trait 行の `tid` だけが発行できる。
`Implements τ tn` は、対応する impl 行の `oid` だけが発行できる。
`RequiresBoth A B` は、対応する intersect 行の `oid` だけが発行できる。
発行者対応は R0 の登録内容も照合する。

これら三形の ProofRep は、発行者対応を満たす限り初期成果物と到達成果物に現れてよい。
正しい origin と命題を持つ ProofRep の再表明は、正典表にない事実を増やさないためである。

`FieldType f τ` は `Presence f` と同じく `o-merge` だけが発行できる。
両命題の ProofRep は merge の局所候補としてだけ使い、初期成果物と到達成果物への出現を拒否する。

## 6. 暗黙 trait resolution

### 6.1 初期候補と hook

初期候補文脈は、Π0 を `candidateize` した候補の後ろへ、`impl-table` の各行から作る global 候補を追加する。
trait 定数と intersect 行は global 候補へ追加しない。
したがって、`ValidNarrativeTrait tn` と `RequiresBoth A B` は暗黙には充足されない。

impl 行から作る entry は、次の形を持つ。

```text
(Implements τ tn, Reserved(oid), nm, root, default, (tid oid))
```

hook `(tid oid)` は、命題、trait 行、impl 行、entry の Proof origin を同じ二つの origin へ束縛する。
`wf-context?` と `wf-candidate?` は同じ `hook-ok?` を使う。
trait 以外の候補は、G2b までと同じ空 hook を持つ。

### 6.2 候補同一性と曖昧性

候補同一性は、命題の正準鍵、Proof origin、cid、sid、pid、hook の組で決める。 [REQ: TRT-003]
候補は、goal との一致で絞り、外部表現で整列し、候補同一性で重複を除き、候補同一性全体の順序で再び整列する。
重複除去より先に整列するため、同一候補の代表は候補文脈の記述順に依存しない。

同じ `(τ, tn)` に対する妥当な impl 行が二つある場合、origin、cid、hook が異なるため候補は一つに畳まれない。
`resolve-candidates` はこの場合に `Ambiguous` を返し、`admissible?` は採択を拒否する。
priority による勝者選択は行わない。

### 6.3 scope と coherence

entry の sid は global 可視性のため `root` とする。
これとは別に、`project-goal` は trait の `sid_trait` または対象型の `sid_target` が現在の `sc-ctx` から可視であることを要求する。
この条件は、ホワイトペーパー §8.1 の package または module の系譜を既存の scope 識別子で近似する。

`sc-ctx` は `project-goal`、`wf-candidate?`、`wf-Σ?`、`admissible?` へ同じ値を渡す。
production の `obligations-dischargeable?` は `root` を使うため、production で暗黙利用する表の行は trait または対象型の少なくとも一方が `root` に属さなければならない。
両方が non-root の行は、`sc-ctx` を明示する coherence 検査だけで使う。

### 6.4 計算分類

`Implements`、引数付き `ValidNarrativeTrait`、`RequiresBoth`、`FieldType` は、命題の形によって `Finite` に分類する。
Finite の証拠は、`project-goal` が抽出した goal 単位の完全な候補集合でなければならない。
候補がなければ `Absent`、一件なら `Resolved`、二件以上なら `Ambiguous` になる。

## 7. merge と join

### 7.1 field の合流規則

`merge-record-types` は、すべての non-Never branch に同じ label がある field だけを候補にする。
可変性が一致しない field は、合流 row から落とす。
全 branch の field 型が同値なら、その型と可変性を保つ。
field 型が異なり、可変性がすべて `imm` なら、branch 型の集合を §3.2 の Union 正規形へ join する。
field 型が異なり、可変性が `mut` なら、field を合流 row から落とす。

branch に現れる型は、正規化してから `type-equiv?` で重複を除く。
合流結果と witness の列は、branch の順序に依存しない。

### 7.2 局所 witness

型が同値なまま残る field には、`Presence f` だけを発行する。
異型の `imm` field には、`Presence f` と、相異なる各 branch 型に対する `FieldType f τ_i` を発行する。

候補の束縛名と cid は、次の形で決定する。

```text
Presence f      -> presence-f
FieldType f τ_i -> field-type-f-i
```

添字 `i` は正規化して整列した branch 型列の 0 から始まる位置である。
この名前により、同じ field に複数の型 witness があっても候補文脈の key は一意になる。

witness は、その merge が作った局所候補文脈だけで discharge する。
witness を型や成果物へ保存せず、別の merge の goal へ流用しない。
`infer-eliminate` は合流型だけを返し、局所候補文脈を捨てる。

## 8. 要件と規則の対応

| 要件 ID | 対応する規則、定義 |
|---|---|
| TRT-001 | §5.1 shape 一致と宣言 origin |
| TRT-002 | §4.2 impl-table、§4.4 環境の導出、§5.2 impl と derive |
| TRT-003 | §6.1 初期候補、§6.2 候補同一性、§6.3 coherence |
| CMP-001 | §3.2 Union の正規形、§7.1 `imm` field の join |
| CMP-002 | §3.3 構造型の Intersection |

## 9. 未回収の範囲

本節の項目は、G2e で回収済みではない。
範囲を狭めた理由は実装規模であり、ホワイトペーパーの意味を置き換えない。

- **合成 trait への所属の導出**：`intersect-table` と `RequiresBoth A B` Proof は導入するが、`Implements τ A`、`Implements τ B`、`RequiresBoth A B` から合成 trait の `Implements` を導く規則は導入しない。
  `RequiresBoth` の implicit discharge も行わない。
  ホワイトペーパー §8.1 の Proof-bearing trait composition は、この導出を含む正典として残る。
- **異型 mut field の Union 方針**：G2e の merge は、異なる型を持つ `mut` field を合流 row から落とす。
  これは ROW-004 の不変性を守るための実装上の狭めであり、ホワイトペーパー §4.5.3 の Union 方針を回収したことを意味しない。
  この未回収範囲では、ホワイトペーパー §4.5.3 の Union 方針を正典として残す。
- **Union の eliminator と型付き field 回復**：G2e は join 型と局所 `FieldType` witness を作るが、witness を使って Union から単一 branch の型を取り出す操作は導入しない。
  この操作には、merge の動的意味論と Preservation の値レベルでの改訂が要る。
- **recursive Union の opaque identity**：G2e は有限に正規化できる Union だけを扱う。
  正規化分類と opaque identity は Phase 1 以降へ送る。
- **表層構文の derive**：G2e は `impl-table` の `kind` として `derive` origin を区別するが、実装 record を自動生成する表層規則は導入しない。
- **型引数、継承、supertrait**：G2e の trait は単相の requirement template だけを持つ。
- **三項以上の trait 合成**：`intersect-table` は二項の合成だけを持つ。
- **package と module の coherence**：G2e は既存の scope 識別子で系譜を近似し、production の入口を `root` に固定する。
- **priority と provenance の下流利用**：候補の `pid` は既定値のままにし、選択した Proof を artifact へ搬送しない。

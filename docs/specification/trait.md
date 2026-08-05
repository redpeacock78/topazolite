# Topazolite trait 層仕様

**状態**：G2f 執筆版
**参照**：`draft/topazolite_whitepaper_draft_0.4.md` §4.5.3、§6.4、§8.1、§15（以下、ホワイトペーパー）
**関連文書**：`core-calculus.md`、`structural-row.md`、`proof-search.md`、`proof-value.md`、`policy-narrative.md`、`requirements.md`、`glossary.md`

## 1. 本仕様の位置づけ

本文書は、G2 の型へ有限な Union と構造型の Intersection を加え、正典表から trait の型、Proof、暗黙候補を導く差分仕様である。
本文書に定義がない型付け規則、簡約規則、候補探索規則、成果物検証規則は、関連文書に従う。
Redex model の G2f 実装は本文書を正とし、実装との乖離が見つかった場合は本文書を先に修正する。

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

G2f の正典表は、次の五行を持つ。

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
(o-trait-printable-taggable PrintableTaggable root
  ((print (NFn (Self) String () ()) imm)
   (tag (NFn (Self) String () ()) imm)))
```

`PrintableSizable` は、`Printable` と `Sizable` の requirement を衝突なく合わせた合成 trait である。
`PrintableTaggable` は、`Printable` と `Taggable` の requirement を衝突なく合わせた合成 trait である。

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

G2f の正典表は、次の七行を持つ。

```text
(o-impl-printable-int impl-printable-int impl Printable Int root)
(o-derive-sizable-int derive-sizable-int derive Sizable Int root)
(o-impl-printable-str-a impl-printable-str-a impl Printable String root)
(o-impl-printable-str-b impl-printable-str-b impl Printable String root)
(o-impl-taggable-bool impl-taggable-bool impl Taggable Bool s-user)
(o-derive-sizable-str derive-sizable-str derive Sizable String root)
(o-impl-taggable-int impl-taggable-int impl Taggable Int s-user)
```

一行目は一意解決、二行目は `derive` 経路、三行目と四行目は曖昧性、五行目は coherence の検査に使う。
六行目は `String` に対する `Sizable` を追加して合成候補の曖昧性を観測し、七行目は対象型 `Int` の非 root scope による可視性を観測する。
`Taggable` の trait scope は `s-kernel`、`Int` の target scope は `s-user` であるため、`(root)` からは見えず `(root s-user)` からは見える。
`Bool` を対象型にした `Taggable` の行は、`search-trait-integration-test.rkt` の `finite-absent-reject` が反転するため、この fixture では追加しない。

### 4.3 intersect-table

`intersect-table` の行は、次の五要素を持つ。

```text
(oid nm tn_left tn_right tn_out)
```

`tn_left` と `tn_right` は symbol 順に並べる。
逆順の入力は命題の正準化で同じ対へ写す。
命題側のこの正準化は、`Compose` の origin step が保持する成分の順序を変更しない。
両辺の requirement template は衝突なく合成でき、その結果が `tn_out` の template と一致しなければならない。

G2g の正典表は、次の四行を持つ。

```text
(o-intersect-print-size intersect-printable-sizable
 Printable Sizable PrintableSizable)
(o-intersect-print-tag intersect-printable-taggable
 Printable Taggable PrintableTaggable)
(o-intersect-size-tag intersect-sizable-taggable
 Sizable Taggable SizableTaggable)
(o-intersect-print-size-tag intersect-printable-sizable-taggable
 PrintableSizable Taggable PrintableSizableTaggable)
```

`tn_left` と `tn_right` は合成 trait でもよい。 [REQ: TRT-006]
成分が合成 trait である行の候補は、成分側の合成候補を成分として持ち、その origin は `Compose` の入れ子になる。

### 4.4 読み込み時検査と環境の導出

表の読み込み時に、trait 名、origin 識別子、primitive 名の一意性を検査する。
各行が参照する trait の存在、template の label 一意性、`Self` の出現位置、具体化後の型の整形式性と正規性も検査する。
合成行については、trait 名の順序、row 合成の成功、出力 template との一致を検査する。
intersect 行の trait 名は symbol 順でなければならず、`intersect-acyclic?` が trait 名の依存グラフの非巡回性を検査する。
`impl` 行と `derive` 行の対象 trait は、`intersect-table` のどの出力 trait でもあってはならない。 [REQ: TRT-007]
合成 trait への直接実装を許すと、同じ goal に表由来の直接候補と合成候補が並び、`Ambiguous` になるためである。
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
合成 `Implements τ tn_out` は、対応する intersect 行の `iid` を親に持つ `Compose` step と、成分二つの origin を含む origin だけが発行できる。
発行者対応は R0 の登録内容も照合する。

`Compose` の発行者検査は、intersect 行の出力 trait と primitive binding を照合し、命題から復元した左右の `Implements` を成分 origin へ再帰的に適用する。
この再帰は intersect-table の非巡回性に依存する。

これら三形の ProofRep は、発行者対応を満たす限り初期成果物と到達成果物に現れてよい。
正しい origin と命題を持つ ProofRep の再表明は、正典表にない事実を増やさないためである。

`FieldType f τ` は `Presence f` と同じく `o-merge` だけが発行できる。
両命題の ProofRep は merge の局所候補としてだけ使い、初期成果物と到達成果物への出現を拒否する。

## 6. 暗黙 trait resolution

### 6.1 初期候補と hook

初期候補文脈は、Π0 を `candidateize` した候補の後ろへ、`impl-table` の各行から作る global 候補を追加する。
intersect-table の各行から作る `RequiresBoth` 候補も、その後ろへ追加する。
trait 定数は global 候補へ追加しないため、`ValidNarrativeTrait tn` は引き続き Γ0 の定数からだけ供給する。

impl 行から作る entry は、次の形を持つ。

```text
(Implements τ tn, Reserved(oid), nm, root, default, (tid oid))
```

intersect 行から作る entry は、次の形を持つ。

```text
(RequiresBoth tn_left tn_right, Reserved(iid), nm, root, default, (iid))
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
可視性は scope の系譜で決める。 [REQ: COH-001]
`sc-ctx` に並ぶいずれかの scope から親を辿って到達できる scope を可視とする。
この系譜は、ホワイトペーパー §8.1 の package または module の入れ子を既存の scope 識別子で近似する。

`sc-ctx` は `project-goal`、`wf-candidate?`、`wf-Σ?`、`admissible?` へ同じ値を渡す。
production の `obligations-dischargeable?` は `root` を使うため、production で暗黙利用する表の行は trait または対象型の少なくとも一方が `root` に属さなければならない。
両方が non-root の行は、`sc-ctx` を明示する coherence 検査だけで使う。

合成候補は、出力 trait の生成 scope が可視であり、かつ左右の成分候補がともに coherent である場合だけ残す。
合成 trait は名前で呼べなければ立てる意味がないため、出力 trait の生成 scope を可視にする。
成分の所属が見えない場合は合成の所属も見えないため、左右の成分候補をともに coherent とする。
出力 trait の生成 scope が不可視なら、成分がともに coherent でも合成候補を立てない。 [REQ: COH-001]

### 6.4 計算分類

`Implements`、引数付き `ValidNarrativeTrait`、`RequiresBoth`、`FieldType` は、命題の形によって `Finite` に分類する。
Finite の証拠は、`project-goal` が抽出した goal 単位の完全な候補集合でなければならない。
候補がなければ `Absent`、一件なら `Resolved`、二件以上なら `Ambiguous` になる。

### 6.5 合成 trait への所属

`project-goal` は `(Implements τ tn_out)` の goal に対し、`tn_out` を出力する intersect 行ごとに左右の成分候補を抽出する。
左右の候補の直積を一件ずつ合成し、元の Γ_pc へは追加しない。

合成候補は次の形を持つ。

```text
(Candidate ProofRep(Derived(Reserved(iid), Compose(tn_out, O_A, O_B)),
                    Implements τ tn_out),
           (compose iid cid_A cid_B), root, default,
           (compose tid iid (O_A hook_A) (O_B hook_B)))
```

`O_A` は `intersect-left` の候補から、`O_B` は `intersect-right` の候補から作る。
この順序は origin の発行者検査が左右の成分を表の順序で照合するため固定される。
合成候補は成分二つが現在の系譜から coherent で、出力 trait の生成 scope も可視なときだけ残る。

性質検査は表の現在の三つの対象型 `Int`、`String`、`Bool` を使い、型を追加生成せずに `Resolved`、`Ambiguous`、`Absent` の三分岐を観測する。

[REQ: TRT-004]

### 6.6 `RequiresBoth` の暗黙充足

`intersect-table` に `(A, B, A&B)` の行があるとき、`trait-global-bindings` は `(RequiresBoth A B)` の候補を一件供給する。
命題の正準化は左右を symbol 順へ写すため、逆順の `RequiresBoth B A` も同じ候補で充足する。

正典表に対応する行がない命題には候補を作らない。
したがって `RequiresBoth` の暗黙充足は表の行の存在と同値であり、合成 trait の `Implements` 候補を Γ_pc へ事前登録することとは別の経路である。

[REQ: TRT-005]

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
| TRT-004 | §6.5 合成 trait への所属 |
| TRT-005 | §6.6 `RequiresBoth` の暗黙充足 |
| TRT-006 | §4.3 合成 trait を成分とする intersect 行、§4.4 非巡回性検査 |
| TRT-007 | §4.4 合成 trait への直接 impl の禁止 |
| COH-001 | §6.3 scope 系譜による可視性、合成候補の出力 scope 検査 |
| CMP-001 | §3.2 Union の正規形、§7.1 `imm` field の join |
| CMP-002 | §3.3 構造型の Intersection |

## 9. 未回収の範囲

本節の項目は、G2e/G2f で回収済みではない。
範囲を狭めた理由は実装規模であり、ホワイトペーパーの意味を置き換えない。
本節に項目を足したときは、`requirements.md` §4 の申し送り表へも 1 行追記する。

- **合成 Proof 値と primitive**：G2f は合成候補の静的な `ProofRep` を検証するが、それを生成して引数へ渡す primitive は導入しない。
  現在の Γ0 は閉じた単相型を持ち、合成 `Implements` の Proof 値を取る正典構文もないためである。
  これはホワイトペーパー §8.1 の Proof-bearing trait composition を値側まで回収したことを意味しない。
- **異型 mut field の Union 方針**：G2g の merge は、異なる型を持つ `mut` field を `imm` へ降格したうえで Union join する。
  降格の理由は代入安全性であり、join 型の field へ書き込める規則を与えられないためである。
  これはホワイトペーパー §4.5.3 が求める、可変性を保ったまま join する規則を回収したことを意味しない。
  この未回収範囲では、ホワイトペーパー §4.5.3 の Union 方針を正典として残す。
  可変性を保つ join は、借用と代入を同時に規定できる G5 へ送る。
- **Union の eliminator と型付き field 回復**：G2e は join 型と局所 `FieldType` witness を作るが、witness を使って Union から単一 branch の型を取り出す操作は導入しない。
  この操作は Phase 1 以降へ送る。
  witness は存在言明であり、どの branch から来た値かを実行時に判別する情報を持たない。
  Union 値に runtime tag が無い以上、eliminator を足すと Preservation が破れる。
  次の三案は採らなかった。
  branch 添字を持つ witness は、witness の意味を存在言明から位置情報へ変え、merge の局所検査を通らなくなる。
  `(Refined τ_union (FieldType label τ))` による絞り込みは、`Refined` のペイロードが validate 由来であるという RFN-001 の前提を崩す。
  `Eliminate` の分岐を Union へ拡張する案は、branch を判別する runtime tag を値側へ導入することと同じであり、Phase 0 の値集合を越える。
- **合成 Proof 値の入れ子と直接実装**：合成 trait を成分とする intersect 行と、合成 trait への直接 impl の禁止は、G2g が §4.3 と §4.4 として回収した。
  合成候補の `ProofRep` を値として生成する primitive は、上の「合成 Proof 値と primitive」のとおり未回収である。
- **recursive Union の opaque identity**：G2e は有限に正規化できる Union だけを扱う。
  正規化分類と opaque identity は Phase 1 以降へ送る。
- **表層構文の derive**：G2e は `impl-table` の `kind` として `derive` origin を区別するが、実装 record を自動生成する表層規則は導入しない。
- **型引数、継承、supertrait**：G2e の trait は単相の requirement template だけを持つ。
- **三項以上の trait 合成**：`intersect-table` は二項の合成だけを持つ。
- **package と module の coherence**：G2e は既存の scope 識別子で系譜を近似し、production の入口を `root` に固定する。
- **typing 経路の scope 文脈**：`obligations-dischargeable?` は `sc-ctx` を引数に取らず、`discharge?` の既定値 `(root)` を使う。
  typing と elaborate の判断は、いずれもこの経路を通る。
  したがって現在の模型では、`root` から不可視な scope を要する義務は、探索としては解けても typing としては解けない。
  G2g はこの差を埋めない。埋めるには typing 判断そのものが scope 文脈を運ぶ必要があり、`Γ` の形を変える改訂になるためである。
  これはホワイトペーパー §17.6 の「global implicit `impl` は trait または target type の少なくとも一方が現在の package / module 系譜で生成されていることを要求する」を、typing 側でも回収したことを意味しない。
  typing への scope 文脈の搬送は Phase 1 以降へ送る。
- **priority の下流利用**：候補の `pid` は既定値のままであり、勝者選択に使わない。
  選択した Proof の artifact への搬送は、G2g が `proof-value.md` §6.4 として回収した。
  搬送した Proof を消費する下流処理は、Phase 1 以降で扱う。

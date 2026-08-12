# CanonicalSpan と spanful 構文

この文書は、Surface と Typed Core の項へ source coordinate を付与し、実行意味論へ渡す直前に coordinate を取り除く規約を定める。
Diagnostic IR の schema、error code registry、phase ごとの Diagnostic 生成、origin chain、renderer はこの文書の対象外である。

## 1. CanonicalSpan

**CanonicalSpan** は、source file を識別する `sourceId` と UTF-8 byte offset の対からなる source coordinate である。

```text
rsid ::= #:synthetic
usid ::= variable-not-otherwise-mentioned
sid  ::= usid rsid
s    ::= (#:span sid natural natural)
```

`usid` は利用者が指定する source file の識別子である。
`rsid` は模型が生成した項に使う予約値であり、`#:synthetic` の 1 語だけからなる。
`#:synthetic` は Racket の keyword であり、`usid` が受け取る記号とは値の種類が異なる。

`sourceId` は source file を識別する記号であり、line と column を持たない。
`startByte` と `endByte` は非負の UTF-8 byte offset である。
`startByte <= endByte` を要求する。
`startByte = endByte` の空 span を許す。
空 span は、展開で生成した項を展開位置の幅ゼロの coordinate へ写すために使う。

line、column、UTF-16 code unit offset は `span` に持たせない。
line と column の再計算は renderer adapter と LSP adapter の責務である。
Phase 0 の模型はそのための相互変換 index を持たない。

span と semantic origin `O` は別のフィールドである。
origin は信頼済みの生成経路を表し、span は source coordinate を表す。
origin の検証契約は span の導入によって変わらない。

## 2. metadata の head を keyword に取る理由

metadata の head には Racket の keyword を使う。
span の構成子名を記号で追加すると、既存の識別子の受理集合が黙って狭まるためである。

Redex の `variable-not-otherwise-mentioned` は、その言語に literal として現れる記号を除外集合へ入れる。
keyword は記号ではないため、metadata を何語追加しても記号の除外集合は増えない。

`lang.rkt` の識別子非終端は `x`、`f`、`b`、`K`、`nm`、`id`、`cid`、`label` の 8 件である。
`elaborate.rkt` の `T` を加えると、UCore が扱う識別子非終端は 9 件になる。
G1 は 7 件、G2 は `label` を加えた 8 件、UCore は `T` を加えた 9 件として受理集合を検査する。

metadata の head は `#:span`、`#:bind`、`#:lbl`、`#:ty`、`#:ef`、`#:var`、`#:lit` の 7 語である。
予約 sourceId も `#:synthetic` という keyword である。
`Var`、`Lit`、`Bind`、`Lbl`、`Ty`、`Ef`、`span`、`%foo`、`%synthetic` は、既存言語と spanful 言語の両方で識別子として受理する。
この受理集合と annotate、erase の往復は `span-collision-test.rkt` が固定する。

記号の head と numeric tag は採らない。
記号の head は `%foo` のような既存の名前を落とし、numeric tag は項を読みにくくするためである。

## 3. span を持つ構文要素

span を持たせる単位は、項の全構成子、変数参照、literal、binder、field label、型注釈の出現位置の 6 つである。

UCore の `e ::= x` と G1 の `c ::= x` は構成子ではないため、変数参照を `(#:var x s)` で包む。
`l ::= integer unit string` も裸の token であるため、literal を `(#:lit l s)` で包む。
`Let`、`Fn`、`Recur`、分岐、handler が導入する名前は `(#:bind x s)` で包む。
項の `Rec` と `Proj` に現れる field label は `(#:lbl label s)` で包む。
型注釈の出現位置は §4.2 の表に従って `(#:ty ...)` または `(#:ef ...)` で包む。

型そのものは spanless のままにする。
record 型の row `r ::= ((label tau m) ...)` に現れる label も spanless のままにする。
型内部の label を指す診断は、その型注釈全体の span で代表する。

## 4. spanful 文法

spanful 言語は `define-extended-language` で定義する。
既存の spanless な UCore、G1、G2 は変更しない。

`Core+` は G2+ を指し、G1+ は G2+ の部分言語である。
`G1+` は G1 だけを使う fixture のための断片である。

G1+ は `c`、`v`、`ov`、`br`、`h` の production を spanful 版へ置き換える。
UCore+ は `e`、`ubr` の production を spanful 版へ置き換える。
G2+ は G1+ を継承し、G2 が追加する production を spanful 版で足す。

Redex の `define-extended-language` は、拡張側の production 列に `....` がある場合だけ基底の production を残す。
G1+ の `c`、`v`、`ov`、`br`、`h` と UCore+ の `e`、`ubr` では `....` を使わない。
これらの非終端に `....` を書くと spanless な production が残り、全構成子が span を持つ契約が崩れる。
G2+ の spanful な非終端では、G1+ の production を継承するために `....` を使う。
`tau`、`phi`、`r`、`ell`、`epsilon`、`Q` のように span を持たない非終端でも、継承のために `....` を使う。

span は構成子名の直後に置く。

```text
(Apply s c c ...)
(Rec s ((#:lbl label s_l) m c) ...)
(Proj s c (#:lbl label s_l))
```

構成子名を持たない `br`、`h`、`ubr` では span を先頭に置く。

| 非終端 | spanful 形 | erase 後 |
|---|---|---|
| `br` | `(s K (xs ...) -> c)` | `(K (x ...) -> c)` |
| `h` | `(s xs -> c)` | `(x -> c)` |
| `ubr` | `(s K (xs ...) -> e)` | `(K (x ...) -> e)` |
| `op` | `(Return b ts)` | `(Return b tau)` |

`xs` は `(#:bind x s)`、`ls` は `(#:lbl label s)` である。
`ts` は UCore+ では `(#:ty u_tau s)`、G1+ と G2+ では `(#:ty tau s)` である。
`es` は UCore+ の effect annotation を包む `(#:ef u_epsilon s)` である。
`vr` は `(#:var x s)`、`lt` は `(#:lit l s)` である。
`#:ty` と `#:ef` の中身は spanless であり、span を持つのは注釈の出現位置だけである。

`op` は effect label であり、`lang.rkt` では `ell` に属するため項構成子ではない。
そのため `Return` の境界名と label は spanless のままにし、内側の型注釈 `ts` だけが span を持つ。

境界名 `b`、ADT tag `K`、semantic origin `O`、境界 ID `cid`、primitive 名 `nm`、mutability `m`、`bmode`、型名 `T`、trait 名 `tn` は spanless である。
これらを指す診断は、それらを含む構成子の span で代表する。
これは §3 が定める 6 単位だけに span を持たせ、識別子一般には span を持たせないためである。
`span-collision-test.rkt` が境界名 `b` を 5 位置の一つとして検査するのは受理集合を検査するためであり、`b` に span を与えることを意味しない。

`O` が spanless であることは、`G1+` の `step` を置き直すことで保っている。
基底の `step` は `(Curry v)` であり、`G1+` が `v` を spanful へ置き換えると、`O` の内側まで span を要求してしまう。
内側の値を文法で spanless と書き下すには `G1` の `v` から `c` までを複製する必要があるため、`G1+` は `step` の `Curry` の内側を `any` で受ける。

このため `G1+` と `G2+` は spanful な `O` も受理する。
`O` を spanless に保つ責任は項を作る側にあり、`annotate-core` は `O` を包まない。
`origin-shape-valid?` は投影の上で origin の形を見るため、`O` の内側が spanful でも erase 後には spanless 版と一致し、`(forged c)` にならない。
erase 後に同じ項へ写る以上、この受理は実行意味論へ届く項を変えない。

### 4.1 変数参照と literal

UCore+、G1+、G2+ の変数参照はすべて `(#:var x s)` に包む。
UCore+、G1+、G2+ の literal はすべて `(#:lit l s)` に包む。
`Move w` の `w ::= x` も参照位置であるため `(#:var x s)` に包む。
`erase-core` と `erase-surface` はこれらをそれぞれ裸の変数と literal へ戻す。

spanful な項へ `substitute` を掛けない。
`substitute` は `(#:var x s)` の内側に置換値を差し込み、`(#:var (#:lit 7 s) s)` のような不正な項を生成することがある。
このため `substitute` は erase 後の G1 と G2 にだけ適用する。

`substitute` は束縛子を freshen するため、束縛子を含む置換結果を直の `check-equal?` で比較しない。
束縛子を含む結果は alpha 同値で比較し、束縛子を含まない結果は直の構造比較で固定する。

### 4.2 型注釈の出現位置

| 言語 | 構成子 | 注釈の位置 |
|---|---|---|
| UCore+ | `Fn` | 引数の各 `u_tau`、返り値 `u_tau`、effect `u_epsilon` |
| UCore+ | `Recur` | 引数の各 `u_tau`、返り値 `u_tau`、effect `u_epsilon` |
| UCore+ | `Let` の注釈あり形 | `u_tau` |
| UCore+ | `Let` の注釈なし形 | 無し |
| UCore+ | `Construct` の `(Types u_tau ...)` 形 | 各 `u_tau` |
| UCore+ | `Construct` の型引数なし形 | 無し |
| UCore+ | `TypeMake`、`LetType` | `spec` の出現 |
| G1+ | `Let` | `tau` |
| G1+ | `Construct` | `tau` |
| G1+ | `Return` の effect boundary | `tau` |
| G2+ | `Let` の `(x bmode tau)` 形 | `tau` |

`Lam`、`Recur`、`RecurVal` は Core で型注釈を持たない。
`TypeRep` と `ProofRep` は TypeMake と search が作る値であり、source に書かれた型注釈ではない。

### 4.3 束縛形

G1 が宣言する 6 形と G2 が宣言する 1 形を、G1+ と G2+ で再宣言する。
production 側は略記を使い、`#:binding-forms` 側では `(#:bind x s)` を展開して pattern variable を明示する。

| 元の束縛形 | spanful 形 |
|---|---|
| `Lam` | `(Lam s O cid ((#:bind x s_b) ...) c)` |
| `Let` | `(Let s ((#:bind x s_b) (#:ty tau s_t)) c_1 c_2)` |
| `br` | `(s K ((#:bind x s_b) ...) -> c)` |
| `h` | `(s (#:bind x s_b) -> c)` |
| `Recur` | `f` と各 `x` を `#:bind` で包んだ同形 |
| `RecurVal` | `f` と各 `x` を `#:bind` で包んだ同形 |
| G2 の `Let` | `(Let s ((#:bind x s_b) bmode (#:ty tau s_t)) c_1 c_2)` |

`#:refers-to` は `(#:bind x s)` の内側の `x` を binder として解決する。
UCore+ は UCore が束縛形を宣言していないため、束縛形を宣言しない。

### 4.4 実行意味論との境界

G1+ と G2+ は静的な項だけの言語である。
評価文脈 `F`、`E`、`G` は G1m と G2m に属し、spanful 版を定義しない。
実行意味論へ入るのは `erase-core` の出力だけであり、その出力は既存の G1 と G2 の項である。

## 5. 生成された項の span

展開や脱糖で新しく作った項は、元になった source 項の span または展開位置の空 span へ決定的に写す。
実行のたびに異なる span を作らない。
Phase 0 の模型には parser と macro 展開器がないため、fixture adapter が生成する span は `(#:span #:synthetic i i)` とする。
expansion trace は source span と別の情報であり、別の phase が扱う。

## 6. erase と投影

```text
erase-core    : G2+ -> G2
erase-surface : UCore+ -> UCore
```

両方の投影は spanful な項と既存の spanless な項を受ける。
spanless な入力では恒等写像になり、spanful な入力では metadata をすべて取り除く。

投影は次の 4 法則を満たす。

1. **全域性**：spanful な言語のすべての項に対して投影が定義される。
2. **冪等性**：`erase(erase(t)) = erase(t)` が成り立つ。
3. **span 違いの一致**：span だけが異なる 2 項の投影は一致する。
4. **span 残留なし**：投影結果に `#:span`、`#:bind`、`#:lbl`、`#:ty`、`#:ef`、`#:var`、`#:lit` は現れない。

投影は未知の metadata head を素通ししない。
span 機構へ新しい head を追加したときに、投影側の更新漏れを検出するためである。

## 7. phase 契約

| phase | 入力 | 出力 | span の扱い |
|---|---|---|---|
| elaboration | `UCore+` | `(core type row callables)` | core は G2+ |
| typing | `G2+` | `(tau, epsilon)` | 型と row は spanless |
| classify | `G2+` | 分類結果 | span を見ない |
| type-shape | `G2+` と型 | 判定 | 項を走査するが span を見ない |
| origins | `G2+` と `G2m` の `c` | `ok` または `(forged c)` | 項を走査し、`(forged c)` は入力の span を保つ |
| search | 型、`Gamma-pc`、Goal | `Resolved`、`Absent`、`Ambiguous` | `ProofRep` を生成する |
| compat、traits、type-equiv | 型と表 | 判定 | 項構成子を走査しない |
| policy-check | policy 表と `R0` | 判定 | 項を受け取らない |
| lowering | `G2+` | `PR` または capability diagnostic | 出力に span を残さない |
| machine、obs、pr-machine、pr-obs | `G2`、`PR` | 実行結果 | span を扱わない |

### 7.1 search が生成する ProofRep の span

search が生成する `ProofRep` には常に `(#:span #:synthetic 0 0)` を与える。
この span は goal と候補文脈に依存しない。
候補文脈は表から作られ、source coordinate を持つ項ではないためである。
goal の span を継承すると、同じ候補の同一性判定に span が混入する。
`Discharge` の位置を指す診断は項側の `Discharge` の span を読む。

`Γ0` の `ProofRep` は search が生成する項ではない。
参照した位置の span を持つ。
参照位置が `(#:span #:synthetic 0 0)` を持つ場合、search が生成した項と span の値が一致する。
由来の判別に span を使わない。

### 7.2 elab の返り値

elab の返り値の形は変えない。
成功時は `(core type row callables)` の 4 要素を返す。
失敗時は `(err reason)` の形を返す。
失敗時の `reason` は Diagnostic IR ではなく、Diagnostic IR への置換は後続の phase が扱う。

### 7.3 型を受け取る位置の fail-closed

型、命題、作用 label、trait 表の行を受け取る関数は、span 機構の包みを受理しない。
包みが渡ったら error を上げる。
黙って通すと、包みが型として `equal?` で比較され、型同一性と正規形の判定が偽の成立をする。

この規則を課す関数は `normalize-type`、`normalize-proposition`、`type-equiv?`、`effect-equiv?`、`type-shape-ok?`、`instantiate-requirements`、`compat?` である。

`compat?` は再帰の入口であり、入れ子の spanful な型もここで拒否する。
`type-equiv?` への委譲だけに頼らない。
`compat?/impl` の `Never` の枝は sup を見ずに真を返すためである。
`policy-wrap` の境界検査は実装が値を返したあとに走る。
そのため、fail-closed を境界検査の実装に依存させない。

`check-spanless!` は head だけを見る。
`type-equiv?` と `compat?/impl` は再帰の入口ごとにこの検査を呼ぶため、深い走査へ変えると比較のたびに項全体を歩き直す。
命題を受け取る入口は再帰の外にあり、呼ばれる回数が項の大きさに比例しない。
`make-goal` と `candidateize` はここへ深い検査を置き、`(Implements (#:ty Int s) Printable)` のように内側へ包みを持つ命題も拒否する。
どの層が拒否するかを、head の検査と深い検査の 2 段として定める。

項を受け取る関数は spanful な項と spanless な項の両方を受理する。
typing の `core-type-of` と `core-check-row` は、入口検査のために一度だけ投影し、走査は spanful な項のまま行う。
`core-types-normal?` と `classify` は、入口で投影した spanless な項を走査する。
lowering の `lower/with-matrix` と `lower-value` は、入口検査のために一度だけ投影し、走査は spanful な項のまま行う。
値と計算の振り分けだけが、節点ごとに局所の投影を使う。
`core-check` は `core-check-row` へ、`lower` は `lower/with-matrix` へ委譲するため、投影を重ねて置かない。
投影は文法照合より前に置く。
spanful な項は G2m の `c` に属さないため、後に置くと判定へ届く前に不受理へ落ちる。

`config-ok?` は投影しない。
`config` は G2m に属し、§4.4 の通り spanful 版を定義しないためである。

`erase-core` は閉世界検査を伴うため、未知の keyword head と項の位置に現れた span は入口で error になる。
`lower` の全域性は Core の形に対するものであり、span 機構の誤りはその外にある。
投影を診断の内側へ置くと、span 機構の誤りが `unknown-core-form` として現れ、Core の形の誤りと区別できなくなるためである。

semantic origin の形の検査も投影の上で行う。
`O` は spanless であり、`CurryVal` の origin へ埋まる値、`Δ0` の行、validator が見る payload はいずれも spanless であるため、spanful な項の側だけを投影して比べる。
判定結果は投影しない。
`verify-origins` が返す `(forged c)` の `c` は入力のままの項であり、span を保つ。

rows、schema、validators、policy は項構成子を走査しない leaf module であるため、span 基盤では変更しない。
`validators` に現れる `Yield` は effect label の pattern であり、項構成子ではない。

### 7.4 elab が core へ span を写す規則

elab は表層の span を core へ次の 3 通りで写す。

1. **そのまま渡す**：`#:var`、`#:lit`、`#:bind`、`#:lbl` の包みは表層と core で同じ形を持つため、開かずに core へ置く。
2. **組み直す**：`#:ty` の包みは解決前の注釈を包む。core へ置く `ts` は、解決後の型と注釈の span から組み直す。包みの span は第 3 要素にあり、節点の span（第 2 要素）とは位置が違う。
3. **生成した節点へ与える**：表層に対応を持たない core の節点は、その節点を生んだ表層の節点の span を持つ。

規則 3 が定める span は次のとおりである。

- `Fn` から生まれる `Handle`、`Scope`、handler の束縛、`op` の `ts` は `Fn` の span を持つ。
- `NarrativeExpr` から生まれる `Handle` と `Scope` も同じ形である。
- `Apply` の義務から生まれる `Discharge` は `Apply` の span を持つ。
- 表層の `Return` から生まれる `Perform` とその `op` の `ts` は `Return` の span を持つ。
- `Drop` の被演算子が owned な変数参照であるときに補う `Move` は `Drop` の span を持つ。
- 型注釈を持たない `Let` の `ts` は `Let` の span を持つ。
- `Construct` の `ts` は `Construct` の span を持つ。`Types` の有無で分かれない。`ts` は構成子の結果型を包む位置であり、個々の型引数の注釈とは対応しない。

`Γ0` の値は表の項であり span を持たない。
参照した位置の span を与えて core へ置く。
表の項は source coordinate を持たないため、参照位置が唯一の決定的な選択である。

`UCore` と `UCore+` は `ucore.rkt` に置く。
`UCore+` を span.rkt へ置くと、span.rkt が elaborate.rkt を require するため、elab が自分の入力の文法を参照できない。
`UCore` は `lang.rkt` の `G1` だけを基底に取り、`UCore+` は `UCore` だけを基底に取るため、2 つを `lang.rkt` の上の 1 つの module へ置ける。
`span-core.rkt` の `G1+` と `G2+` も同じ形である。

elab は入力を `UCore+` と `UCore` の両方へ照合する。
`UCore+` の `e` は全 production を spanful へ置き換えており、literal も包みを持つため、2 つの文法は交わらない。
`UCore+` に属する項はそのまま使い、`UCore` に属する項は `annotate-surface` で `UCore+` へ正規化する。
どちらにも属さない項は `invalid-syntax` で拒否する。
span を一部だけ持つ項はここで落ちる。

入力の判定に投影を使わない。
`erase-surface` は列の要素として現れた span を落とす。
節点の span を落とす機構がこれであるため、項の位置に紛れた span も静かに消え、投影の出力は `UCore` に属してしまう。
文法へ直接照合すれば、この縮退を経ずに拒否できる。

文法への照合だけでは §3 を満たさない。
`s ::= (#:span sid natural natural)` は `startByte <= endByte` を書けないため、`(#:span #:synthetic 10 0)` も `UCore+` に属する。
`UCore+` に属した項は、続けて全 span を再帰的に走査し、`span-ok?` を満たさない span が 1 つでもあれば `invalid-syntax` で拒否する。
`annotate-surface` の出力は常に `span-ok?` を満たすため、`UCore` の枝ではこの走査を行わない。

この文書は G4b の span 契約だけを定め、要件 ID や申し送り表の行を追加しない。

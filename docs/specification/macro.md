# マクロ展開

本文書は、ユーザーマクロの置換の契約から、展開器、呼出しの形、診断、再検査の接続までを定める。
節番号の §2 と §3 は予約であり、表層構文を導入する段でマクロの位置づけと展開の全体像を置く。

## 1. spanful な置換

Core の項は `span-core.rkt` の `G2+` に属する。
`G2+` の変数参照は `(#:var x s)` という包みであり、変数名 `x` と出現位置の span `s` を持つ。

Redex の `substitute` はこの層では使えない。
`substitute` は変数名の位置、すなわち `(#:var x s)` の第 2 要素へ像を差し込むため、`(#:var (#:lit 7 s_2) s_0)` のような `G2+` に属さない項を作る。

そこで置換の単位を `(#:var x s)` の節点全体に取り直した写像を `span-subst.rkt` に置く。
この写像は `(span-subst t σ)` という形で、`σ` は変数名と像の対の並びである。

### 1.1 契約

- **置換の単位**：`(#:var x s)` の節点全体を像で置き換える。変数名の位置へは差し込まない。
- **span の帰属**：像は出現位置の span を捨て、像自身が持つ span のまま項へ入る。引数はユーザーが書いた項であり、その位置情報は引数自身が持つ。
- **同時性**：`σ` のすべての鍵を同時に置き換える。1 つずつ順に置き換える形は採らない。順に行うと、先に入れた像の中に含まれる自由変数へ後続の置換が届く。引数は template の pattern 変数とは無関係の名前空間に属するため、この到達は誤りである。
- **捕捉回避**：束縛子の名前が、その範囲へ入る像の自由変数と衝突するとき、束縛子を新しい名前へ改名する。改名しても束縛子の span と、範囲内の出現位置の span は動かない。
- **shadowing**：束縛子が `σ` の鍵と同じ名前のとき、その範囲では当該の鍵を落とす。
- **結果の所属**：入力が `G2+` の `c` に属し、像も `G2+` の `c` に属するなら、結果も `G2+` の `c` に属する。

### 1.2 束縛形

捕捉回避が働く束縛形は、`span-core.rkt` が `#:binding-forms` で宣言する 7 つである。

- `Lam`：仮引数の並びが本体を束縛する。
- `Let`（型注釈だけの形）：束縛変数が第 2 の本体だけを束縛する。第 1 の本体は束縛の外である。
- `Let`（`bmode` 付きの形）：同じ。
- 分岐（`(s K (xs ...) -> c)`）：構成子の引数の並びが本体を束縛する。
- ハンドラ（`(s xs -> c)`）：継続変数が本体を束縛する。
- `Recur`：再帰名が 2 つの本体の双方を、仮引数の並びが第 1 の本体だけを束縛する。
- `RecurVal`：再帰名と仮引数の並びが本体を束縛する。

`span-subst` はこの 7 つを個別の節として持ち、それ以外の節点は子を一様に辿る。

### 1.3 自由変数

`span-free-vars` は項の中で自由に現れる変数を、最初の出現順で重複なく返す。
束縛形の範囲は 1.2 のとおりに扱う。
`origin` の内側も走査は通る。
ただし `origin` は spanless であり（`span.md` §4）、その内側の変数参照は `(#:var x s)` の包みを持たない裸の名前である。
`span-free-vars` が拾うのは包みを持つ参照だけなので、`origin` の内側からは何も拾わない。
`span-subst` も `origin` を書き換えない。

走査が `origin` の内側へ入ること自体には意味がある。
`G1+` の `step` は `(Curry any)` という形で値を受けるため、内側には spanless な束縛形が現れうる。
分岐とハンドラの spanless な形は spanful な形と同じ要素数を持つので、束縛形の節は `(#:bind x s)` の包みを確かめてから適用する。

## 4. マクロ環境

### 4.1 環境は引数である

マクロ定義の集まりを **マクロ環境**（`macro-env`）と呼ぶ。
`macro-env` は展開器の引数であり、モジュール定数ではない。

P2h1 では trait の行も `trait-env` として `lower-surface` の引数にし、宣言から追加する。
その環境は固定のモジュール表ではなく、`compile-source` が宣言ごとに trait 台帳へまとめる。
したがって `macro-env` と `trait-env` はそれぞれ展開器と lowering の呼出し側が与える環境であり、モジュール定数へ閉じない。
環境を引数にすれば、呼出し側が各展開・コンパイルの内容を組み立てられる。

### 4.2 マクロ定義の形

マクロ定義は次の4つ組である。

- **name**：マクロの名前。origin の `step` が取る `nm` と同じ名前空間に属する。
- **span**：定義そのものの位置。定義に対する Diagnostic の primary span になる。
- **pattern**：仮引数となる変数の並び。`G2+` の `x` の並びである。
- **template**：本体。`G2+` の `c` である。

### 4.3 定義の妥当性

`macro-env` を組み立てる時点で、各定義に次の3条件を課す。

- pattern の変数に重複が無い。
- template の自由変数が pattern の変数の部分集合である。
- template の中の `Lam` と `MacroCall` の origin が、すべて `User` である。

2番目は hygiene の片側を閉じる。
template の自由変数を pattern へ限れば、展開先の束縛が template の自由変数を捕捉する経路が存在しない。
自由変数の算出は spanful な自由変数関数を使う。

3番目は §8 の origin の座を空けるための条件である。
展開はこの2形の `User` を展開由来の origin へ書き換えるため、定義の時点で別の値が入っていると、書き換えが元の値を黙って捨てる。
検査は template 全体を再帰的に走査し、深い位置の `Lam` と `MacroCall` も見る。
primary span は違反した節点自身の span であり、定義の span は `related` の要素として添える。

`ov` の残り4形（`PrimVal`、`CurryVal`、`TypeRep`、`ProofRep`）と `RVal` を template へ直接置くことは許す。
これらの origin は展開が触らない。
禁じると、型表現や証明表現を本体に含む template が書けなくなり、マクロの用途が痩せる。

ホワイトペーパー §10.1 の「reserved origin を新規生成できない」へ、定義時の走査は当てない。
`(Reserved id)` を名乗る節点は、展開後の origin 再検査が `R0` と突き合わせて落とす。
`verify-origins/proc` が項全体を走査するため、深い位置の偽の `(Reserved id)` も届く。
定義時に同じ走査を重ねると、同一の禁止を二箇所で管理することになる。
再検査が担うと決めることは、MAC-001 の「展開結果は再度 origin 検査を受ける」をそのまま使う形でもある。

`macro-env` の名前の重複は拒否する。
`assoc` の先勝ちにすると、後から足した定義が黙って無視され、呼出し側からは展開結果だけが食い違って見える。
重複の diagnostic は、後に現れた定義の span を primary span とし、先に現れた定義の span を `related` の要素として添える。

診断は定義の現れた順に並べ、1つの定義の中では本節の3条件を挙げた順に並べる。

## 5. MacroCall

### 5.1 呼出しの形

`G2+` の `c` は、展開前のマクロ呼出しを `(MacroCall s O nm (c ...))` として表す。

`s` は呼出し節点の span、`O` は呼出しの provenance、`nm` は macro の名前、最後の list は実引数である。

`MacroCall` は束縛を持たないため、`span-core.rkt` の `#:binding-forms` へは加えない。

展開器の出力には `MacroCall` を残さない。

### 5.2 O 欄の2段の不変条件

公開の root 入口へ渡す項では、すべての `MacroCall` の `O` が `User` でなければならない。

`Derived` も `Reserved` も root 入口では拒む。

違反は `E-MAC-004` であり、primary span は違反した `MacroCall` の span である。

`MacroCall` の `O` は `origin-bearing-heads` の投影では検査しない。
`MacroCall` は展開器が消費する前段の節点であり、origin の検査は展開器の `E-MAC-004` が担う。

内部の再帰入口は展開器の module 内だけから呼ぶ。
外側の展開が template 中の `MacroCall` の `O` を `(Derived O_call (Expand nm))` へ書き換えるため、再帰の入口では `Derived` を受け入れる。

### 5.3 合成 span を付ける範囲

template 由来の節点すべてへ新しい合成 span を割り当てる。

対象は `c`、`v`、`ov` を問わず、`s` の欄を持つ節点すべてである。

実引数由来の部分項は自身の span を保つ。

合成 span は `(#:span #:synthetic k k)` の形であり、1 回の展開器起動を通じて `k` を単調に増やす。

連番の起点は、入力の項に現れる `#:synthetic` の `k` の最大値へ 1 を足した値である。

これにより展開器が割り当てた span は入力のどの span とも重ならない。

同じ展開の中でも節点ごとに異なる番号を配る。

引数由来の span は展開表の鍵にならない。

置換で消える `#:var` の span と、再帰で置き換わる入れ子の `MacroCall` の span も鍵に残らない。

## 6. 展開と hygiene

### 6.1 spanful な捕捉回避置換

展開は template の pattern 変数を対応する実引数項で置き換える。

置換には `span-subst` を使い、Redex の `substitute` は使わない。

`span-subst` は `(#:var x s)` の節点全体を実引数へ置き換え、実引数自身の span を保つ。

束縛子の改名では `#:bind` の span と範囲内の変数参照の span を保つ。

pattern の変数は同時に置換し、1 つずつ順に置換しない。

template の自由変数は §4.3 の検査で pattern の変数に限る。

### 6.2 束縛形は7つである

置換と自由変数の算出は、`G1+` と `G2+` が宣言する7つの束縛形を個別に扱う。

- `Lam`
- `Let`（型注釈だけを持つ形）
- `Let`（`bmode` を持つ形）
- 分岐
- ハンドラ
- `Recur`
- `RecurVal`

各束縛形について、引数由来の自由変数による α 改名、実引数の span の保存、結果が `G2+` の `c` に属することを回帰で固定する。

### 6.3 template の束縛子

template は束縛子を持ってよい。

`span-subst` が α 改名を行うため、生成した束縛子へ別の hygiene 注釈を持たせる必要はない。

### 6.4 入れ子の展開と段数の上限

展開結果がさらに `MacroCall` を含む場合、展開を繰り返す。

上限は **32 段** とする。

数えるのは一つの `MacroCall` を起点とする再帰の深さであり、展開全体に現れた呼出しの総数ではない。

起点の `MacroCall` を展開した時点が深さ1である。

深さ32は成功し、深さ33に達した時点で `E-MAC-002` を出す。

兄弟の `MacroCall` は互いに深さを足さない。

循環は別の検出機構を置かず、深さ超過として拒否する。

深さ超過の primary span は最も外側の呼出しの span であり、`expansion-trace` は32要素である。

## 7. 再検査

### 7.1 展開器の返り値

展開器は 3 つの値を返す。
展開後の項、展開表、診断の並びである。
診断は list であり、空であれば棄却は無い。
診断が空でないとき、展開後の項と展開表は使わない。

### 7.2 展開済みを要求する3つの入口

型、効果、証明、origin の 4 検査は、展開後の項の上で行う。 [REQ: MAC-001]
入口は次の3箇所である。

- `type-of/raw` の内部の投影
- `core-check-row` の投影
- `verify-origins/proc` の入口

いずれの入口も、走査を始める手前で、項のどこにも `MacroCall` が無いことを要求する。
型の2つは `erase-core` の投影の直前、origin は `c` の照合の直後である。

`G2+` の照合だけに頼らない理由は、その照合が `MacroCall` を含む項を `c` として受けてしまう点にある。
`MacroCall` は `G2+` の `c` であるから、照合は通る。
型と効果の経路がこの網を素通りするのを防ぐため、3箇所すべてへ明示の検査を置く。

origin の入口を節点ごとの述語ではなく走査の入口に置く理由は、その述語が origin を持つ頭にしか呼ばれない点にある。
`MacroCall` は origin を持つ頭の並びに無いため、`MacroCall` だけを子に持つ項では述語が一度も呼ばれない。

Δ0 の origin 検査はこの要求の対象外である。
Δ0 は展開を経ない層であり、展開前の項を受け取る。

### 7.3 expansion-trace を決める順序

`diagnostic-of` は `expansion-trace` の欄を次の順序で決める。

1. `#:expansion-trace` が `#f` でなければ、その値を使う。
2. そうでなければ primary span を鍵として展開表を引き、当たればその値を使う。
3. どちらでもなければ空とする。

展開器自身が組む診断は 1 を使う。
4 検査が組む診断は 2 を使う。
展開を経ていない診断は 3 になる。

### 7.4 展開表の寿命

展開表の寿命は、展開から 4 検査の終了までである。
展開器の外へ表を持ち出さない。

診断を返す adapter のうち、展開表を受け取るのは 2 つである。
Δ0 の `verify-initial-origins/diagnostic` は展開を経ないため、既定の空の表を使う。
`core-check-row` は boolean を返す入口であり診断を組まないため、展開表を取らない。

## 8. origin

### 8.1 Expand の座

展開が作った `Lam` の origin は `(Derived O_call (Expand nm))` である。

`O_call` は `MacroCall` の `O` 欄の値であり、`nm` は展開したマクロの名前である。

`Expand` は既存の origin step であり、`valid-origin?` はその親が妥当であることを検査する。

`MacroCall` の `O` は展開前の呼出しの由来を保持するために置く。

### 8.2 展開由来の Lam

展開器が template 由来の `Lam` を生成するとき、その origin は `(Derived O_call (Expand nm))` である。

`O_call` は現在の `MacroCall` の origin であり、`nm` はその名前である。

`Expand` 以外の step を持つ origin は展開由来の `Lam` として受理しない。

`Derived` の親は `valid-origin?` を満たさなければならない。

### 8.3 入れ子の連鎖

入れ子の展開では origin が連鎖する。

外側の展開は template 中の `MacroCall` の `O` を `(Derived O_call (Expand nm_outer))` へ書き換える。

内側の展開がその呼出しを展開すると、内側の `Lam` の origin は `(Derived (Derived O_call (Expand nm_outer)) (Expand nm_inner))` になる。

引数由来の節点の origin は変えない。

ユーザーが書いた項の由来は、展開を経ても呼出し側の由来へ置き換わらない。

## 9. Diagnostic

マクロ展開の失敗は `expand` 相の Diagnostic へ変換する。

| code | key | 展開器が検査する事象 |
| --- | --- | --- |
| `E-MAC-001` | `macro-arity-mismatch` | 実引数の個数が pattern の個数と一致しない |
| `E-MAC-002` | `macro-depth-exceeded` | 展開段数が上限を超える |
| `E-MAC-003` | `macro-name-duplicate` | macro-env に同じ名前の定義が複数ある |
| `E-MAC-004` | `macro-origin-invalid` | Lam または MacroCall の origin が User でない |
| `E-MAC-005` | `macro-pattern-duplicate` | pattern の変数が重複している |
| `E-MAC-006` | `macro-template-free-var` | template の自由変数が pattern の外にある |
| `E-MAC-007` | `macro-unknown-name` | 呼出しの名前が macro-env に無い |

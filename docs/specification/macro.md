# マクロ展開

本文書は、ユーザーマクロの展開とその後の再検査について定める。
本節はそのうち置換の契約だけを定める。
展開器、呼出しの形、診断、再検査の接続は後続の節で足す。

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

固定の定数にしない理由は、`model/redex/traits.rkt:54` の `trait-table` が固定定数であるために「ユーザーが trait を定義する経路が無い」という縮約を今も残している点にある。
同じ形をマクロで繰り返すと、「ユーザーマクロ」という要件の語が実体を持たないまま閉じてしまう。
環境を引数にすれば、表層構文が無くても呼出し側が定義を組み立てられる。

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

## 8. origin

### 8.2 展開由来の Lam

展開器が template 由来の `Lam` を生成するとき、その origin は `(Derived O_call (Expand nm))` である。

`O_call` は現在の `MacroCall` の origin であり、`nm` はその名前である。

`Expand` 以外の step を持つ origin は展開由来の `Lam` として受理しない。

`Derived` の親は `valid-origin?` を満たさなければならない。

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

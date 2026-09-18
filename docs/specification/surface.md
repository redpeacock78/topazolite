# Topazolite Surface 構文

**状態**：P2c 版
**参照**：`draft/topazolite_whitepaper_draft_0.4.md` §15（以下、ホワイトペーパー）
**関連文書**：`docs/specification/core-calculus.md`、`docs/specification/structural-row.md`、`docs/specification/span.md`、`docs/specification/diagnostic.md`、`docs/specification/requirements.md`

## 1. 範囲

本書は Surface 構文の正典である。
lexer と parser は canonical source span を保持し、Surface 構文から未型付き縮小 Core への lowering はその span を引き継ぐ。 [REQ: SUR-001]

この版が扱う構文は、整数、文字列、真偽値のリテラル、変数、無名関数、関数宣言、関数適用、`const`、`let`、`let mut` の束縛、record リテラル、射影、`type` による型別名の宣言、および block である。

この版は、ジェネリクスと ADT（`ADT-001`）、パターン照合（`PAT-001`）、`?=`、pipe、interpolation（`SUR-002`）、Effect 注釈（`SUR-003`）、borrow 表記（`SUR-004`）、bit 演算子（`BIT-001`）、モジュール（`MOD-001`）を受理しない。
余剰 `Owned` field の明示 projection は `SUR-006` が担う。

Surface の型注釈と署名から Typed Core への elaboration は `SUR-007` が担う。
`#:expansion-context` を Surface の入口へ接続する作業は、この版では行わない。

## 2. 字句

空白はスペースと水平タブであり、区切りとしてのみ働く。
空白はトークンにならない。

改行は有意である。
連続する改行は 1 個の `nl` へ畳み、その間の空白と行コメントも run に含める。
`nl` の span は、その run 全体を覆う。

行コメントは `//` から改行の手前までである。
改行そのものは `nl` として残る。

識別子は `[A-Za-z_][A-Za-z0-9_]*` である。
予約語は `const`、`let`、`mut`、`fn`、`type`、`true`、`false` の 7 語である。
予約語は識別子の規則に合っていても、`ident` として扱わない。

整数リテラルは `[0-9]+` である。
符号は付かない。

文字列リテラルは `"` で囲む。
エスケープは `\"`、`\\`、`\n`、`\t` の 4 種だけを許す。

記号は `{`、`}`、`(`、`)`、`,`、`:`、`=`、`.` の 8 種である。

トークンの種別は `int`、`str`、`ident`、`kw`、`punct`、`nl`、`eof` の 7 種である。
`int` の値は符号なしの整数である。
`str` の値はエスケープを展開した文字列であり、囲みの `"` は含まない。
`ident` と `kw` の値は symbol である。
どの種別でも span は入力中の token 全体を覆い、文字列では囲みの `"` も含む。

不正 byte の検査は字句走査より前に入力全体へ 1 度だけ行う。
コメント中と文字列リテラル中も同じ規則で検査する。
この検査は他のどの字句の誤りよりも優先する。
走査順で最初の 1 件を返す規則は、不正 byte の検査を通った入力に対してだけ適用する。

## 3. 文法

この節の文法が、この版で受理する構文の全てである。
ホワイトペーパーの Surface 構文はここより広く、受理しない構文は診断で拒否する。

```text
program  ::= NL* pitem* expr NL*
pitem    ::= typedecl | fndecl | binding NL+
typedecl ::= "type" ident "=" ty NL+
fndecl   ::= "fn" ident "(" params ")" ty block NL+
expr     ::= postfix
postfix  ::= primary suffix*
suffix   ::= "(" args ")" | "." ident
primary  ::= int | string | "true" | "false" | "(" ")"
           | ident | anonfn | record | block | "(" expr ")"
anonfn   ::= "fn" "(" params ")" ty block
params   ::= ε | param ("," param)*
param    ::= ident ":" ty
args     ::= ε | expr ("," expr)*
block    ::= "{" NL* (binding NL+)* expr NL* "}"
binding  ::= bmode ident (":" ty)? "=" expr
bmode    ::= "const" | "let" | "let" "mut"
record   ::= "{" NL* "}"
           | "{" NL* field (fsep field)* fsep? NL* "}"
field    ::= ident ":" expr
fsep     ::= "," NL* | NL+
ty       ::= ident
           | "{" NL* "}"
           | "{" NL* tyfield (fsep tyfield)* fsep? NL* "}"
           | "fn" "(" tys ")" ty
tyfield  ::= ident ":" ty
tys      ::= ε | ty ("," ty)*
```

トップレベルにも束縛を置ける。
トップレベルの束縛は block の中の束縛と同じ規則で扱う。

関数の戻り型は省略できない。
戻り型の推論は `SUR-007` の範囲に属するため、この版では行わない。

program の末尾は式でなければならない。
空の入力と、宣言だけで式の無い入力は、どちらも `E-SUR-006` で拒否する。
縮小 Core の項は式であり、式を持たない program には落とし先が無いためである。

### 3.1 受理しない構文

字句に無い記号は lexer が `E-SUR-002` を返す。
`-`、`+`、`*`、`/`、`%`、`<`、`>`、`?`、`|`、`!`、`&`、`[`、`]`、`;` は字句にならない。
`List<Int>`、`fn f() -> Int`、算術演算子を含む式、`?=`、pipe は、最初の未対応記号の位置で `E-SUR-002` になる。

字句にはなるが構文に無い `if`、`for`、`while`、`return`、`match` は予約語ではなく `ident` になる。
`if cond { }` のように後ろへ式が続く形は、2 つ目の primary の位置で `E-SUR-005` になる。
単独の `return` は変数式として受理し、未束縛変数の診断は後段に委ねる。

この版では予約語の集合をこれ以上増やさない。
後続の構文が実際に必要とする語は、それぞれの要件で定める。

### 3.2 `let mut` の字句と構文

`let mut` は `kw` token 2 個（`let` と `mut`）からなる。
lexer は `let mut` を 1 個の token へ畳まない。

parser は `let` の直後を覗き、次が `kw` の `mut` ならそれを消費して `bmode` を `mut` とする。
次が `mut` でなければ消費せず、`bmode` を `let` とする。
AST の `bmode` は `const`、`let`、`mut` のいずれか 1 個の symbol であり、`let mut` という 2 語の並びは AST に残らない。

`let` と `mut` の間に改行を置くことは許さない。
`nl` が 2 語の間にある場合、`mut` は次の束縛の先頭として扱われ、構文エラー `E-SUR-005` になる。

### 3.3 `{` の曖昧性

`{` は record リテラルと block の両方を始める。
`{` の後の空白、改行、行コメントを読み飛ばした 2 token の lookahead で区別する。

- `}` が来れば空の record リテラルである。
- `ident` の後に `:` が来れば record リテラルである。
- それ以外は block である。

この規則では空の block を書けない。
block は末尾の式を必ず持つためである。

### 3.4 意味のある改行

式の途中の改行は受けない。
改行は block の束縛どうし、item どうし、record の field どうしを区切るためにだけ使う。

record の field は読点または改行で区切る。
block の束縛と item は改行で区切る。
`fsep` は `, NL*` または `NL+` である。

## 4. span

span は `(#:span sid lo hi)` の 4 要素である。
`lo` と `hi` は UTF-8 byte 位置であり、半開区間 `[lo, hi)` を表す。

Surface の節点はすべて `(Ctor span ...)` の形であり、span は必ず第 2 欄に置く。
`span-of` は Surface の節点と縮小 Core の節点の両方から span を取る。

節点の span は、その子孫のすべての span を包含する。
包含の検査は、親と子が同じ source id を持ち、親の開始位置が子以下で、親の終了位置が子以上であることを確かめる。

括弧で括った式は括弧の span を持たない。
括弧そのものが節点を作らないため、括弧内の式の span をそのまま使う。
ただし `()` は単位値の節点を作るため、その節点は 2 個の括弧を含む span を持つ。

節点の span は最初の token の左端から最後の token の右端までである。
区切りの `nl` は節点の span に含めない。
`SBlock` の span は開き `{` から閉じ `}` までを含む。
`SProgram` の span は前後の `NL*` を含まず、最初の item（item が無ければ式）から末尾の式までを覆う。

## 5. 型別名

型別名は Surface だけの糖衣である。
UCore+ には型別名を置く欄が無いため、`STypeDecl` は節点を生成せず、lowering の別名環境へ消費する。

別名環境は 2 度の走査で作る。
1 度目は program の `spitem` を原文順に読み、型別名の名前と未展開の `sty` を登録する。
2 度目は各 `sty` の中の `TName` を環境の定義へ置き換え、展開結果に現れる `TName` も同じ規則で解決する。

1 度目の走査で名前をすべて登録してから 2 度目の走査を行うため、宣言より前の位置から後の宣言を参照できる。
宣言順に 1 度で読む方式は採らない。

展開関数は展開後の型だけを返す。
使用位置の span は呼び出し側が入力の `sty` から `(span-of ty)` で取るため、展開後の型と span を 2 値で返す必要はない。

### 5.1 拒否する型別名

型別名の展開は次の 4 件を拒否する。

- 環境に無く、基本型でもない名前は `E-SUR-008` とする。
- 同じ名前の 2 度目の宣言は `E-SUR-009` とし、2 度目の `SName` の span を primary span にする。
- 展開経路上で循環する参照は `E-SUR-010` とし、循環を閉じた `TName` の span を primary span にする。
- 基本型と同じ名前の宣言は `E-SUR-011` とする。

基本型は `Int`、`Bool`、`Unit`、`String` の 4 つである。
これらは `ucore.rkt` の `A` の先頭 4 つと同じ綴りを使う。

循環は、いま展開している別名の名前を積んだ stack で判定する。
`TName` を展開するとき、同じ名前が stack にあれば循環とし、定義を展開し終えた名前は stack から外す。
一度でも展開した名前を記録する集合では判定しない。

```text
type B = Int
type A = { a: B, b: B }
```

上の `A` は `B` を 2 度参照するが、参照経路が同時に stack へ載らないため受理する。

```text
type A = { x: B }
type B = { y: A }
```

上の `A` は展開経路の中で `A` を再び参照するため `E-SUR-010` になる。

`TRec` の中で同じ label を 2 度書いた場合も拒否する。
式の record と型の record は同じ誤りを表すため、どちらも `E-SUR-007` を使い、2 度目の `TField` の `slabel` の span を primary span にする。

### 5.2 診断の順序

診断は最初の 1 件だけ返す。
1 度目の走査では、宣言を原文順に読み、基本型名かどうかを先に検査して `E-SUR-011` とし、次に既出かどうかを検査して `E-SUR-009` とする。
名前の誤りがあれば 2 度目の走査へ進まない。

2 度目の走査では、型名の解決を先に検査して `E-SUR-008` とし、解決後に循環を検査して `E-SUR-010` とする。
record と record 型の field は左から右へ走査し、最初に見つかった 2 度目の label で `E-SUR-007` を返す。
3 件以上の重複があっても、最初の 1 件だけを返す。

## 6. UCore+ への lowering

lowering の入口は `(lower-surface sprog)` である。
返り値は UCore+ の項か Diagnostic 1 件のいずれかである。
引数が Diagnostic のときは、それをそのまま返す。
この節は parser が diagnostic を返した経路を呼び側の分岐漏れで失わないために置く。

別名環境を §5 の規則で先に構築し、`sty` を `uτ` へ落とす際に使う。
宣言の並びは右から畳み、`Let` と `Recur` を積む。

### 6.1 対応表

Surface の span は、下表で `s` と書いた欄へそのまま渡す。
型注釈の span は入力の `sty` 節点から `(span-of ty)` で取る。
別名展開後も、型注釈の包みが持つ span は使用位置の `TName` の span とする。

- `(SInt s n)` は `(#:lit n s)` へ落とす。
- `(SStr s str)` は `(#:lit str s)` へ落とす。
- `(SUnit s)` は `(#:lit unit s)` へ落とす。
- `(SBool s true)` と `(SBool s false)` は、それぞれ `(Construct s true)` と `(Construct s false)` へ落とす。
- `(SVar s x)` は `(#:var x s)` へ落とす。
- `(SApply s f (a ...))` は `(Apply s f' a' ...)` へ落とす。
- `(SProj s e (SLabel s_l l))` は `(Proj s e' (#:lbl l s_l))` へ落とす。
- `(SRec s ((SField s_f (SLabel s_l l) e) ...))` は `(Rec s (((#:lbl l s_l) imm e') ...))` へ落とす。
- `(SFn s ((SParam s_p (SName s_x x) ty) ...) ty_r body)` は、span を持つ binder、型注釈、空の effect row を持つ `(Fn ...)` へ落とす。
- `(SBlock s (bind ...) e)` は、束縛を右から畳んだ `Let` の入れ子へ落とす。
- `(SBind s bmode (SName s_x x) ty e)` は、注釈があれば型注釈付き `Let` へ、無ければ mode-only `Let` へ落とす。
- `(SFnDecl s (SName s_f f) ... )` は、関数本体と後続の項を持つ `Recur` へ落とす。
- `(STypeDecl s (SName s_n T) ty)` は別名環境へ入れるだけで、節点を生成しない。

`TName` のうち `Int`、`Bool`、`Unit`、`String` は同綴りの `uτ` へ写す。
それ以外は §5 の別名環境から解決し、未登録なら `E-SUR-008` とする。
`TRec` は field mode を `imm` とする `(Record ((l uτ imm) ...))` へ写す。
`TFn` は effect row と obligation を空にした `(NFn (uτ ...) uτ_r () ())` へ写す。
Surface に field の可変性と effect 注釈が無いためである。

### 6.2 宣言の畳み込み

`rest'` は、その束縛より後ろの残りを lowering した結果である。
末尾の式を先に lowering して種にし、束縛を後ろから 1 つずつ被せる。

```text
lower [b1 b2 b3] e = L(b1, L(b2, L(b3, lower e)))
```

右から畳むことで、先の束縛の名前が後続の束縛と末尾式から見える関係が `Let` の本体として表れる。
別名の登録と重複宣言の検査は、畳み込みとは独立に原文順で行う。

`Let` と `Recur` の span は、宣言の先頭から後続の項の末尾までを覆う尾部 span である。
block の i 番目の束縛は `[startByte(b_i), endByte(block の末尾式))`、トップレベルの束縛または関数宣言は `[startByte(宣言 i), endByte(program の末尾式))` を持つ。
この span は元の `SBind` や `SFnDecl` の span とは一致しない。

尾部 span を使うと、`Let` と `Recur` の親 span が後続の項を包含する。
生成した span は入力の token 位置から決まり、`#:synthetic` は使わない。

### 6.3 span の対応単位

`SUR-001` の span 引き継ぎは、UCore+ の節点または包みを 1 個生成する構成子を単位とする。
`SName`、`SLabel`、`TName`、`TRec`、`TFn` の span は、それぞれ binder、label、型注釈の欄へ渡す。

`SProgram`、`SBlock`、`STypeDecl`、`SParam`、`SField`、`TField` は、対応する UCore+ の節点または欄が無いため、その構成子自身の span を渡さない。
`uτ` に span を足す改修はこの版の範囲外である。

## 7. 診断

Surface の相は registry の版 15 に `surface` として登録する。
字句、構文、型別名、lowering を 1 つの相にまとめ、区別は code で付ける。

- `E-SUR-001` `surface-invalid-byte`：UTF-8 として解釈できない byte 列
- `E-SUR-002` `surface-unknown-character`：字句にならない文字。`\r` を含む
- `E-SUR-003` `surface-unterminated-string`：閉じない文字列リテラル
- `E-SUR-004` `surface-invalid-escape`：許さないエスケープ
- `E-SUR-005` `surface-unexpected-token`：構文が合わないトークン
- `E-SUR-006` `surface-unexpected-eof`：入力が構文の途中で終わる
- `E-SUR-007` `surface-duplicate-field`：record または record 型の同じフィールドを 2 度書いた
- `E-SUR-008` `surface-unknown-type-name`：宣言の無い型の名前
- `E-SUR-009` `surface-duplicate-type-alias`：同じ型別名を 2 度宣言した
- `E-SUR-010` `surface-recursive-type-alias`：型別名の参照に循環がある
- `E-SUR-011` `surface-reserved-type-name`：基本型の名前を型別名として宣言した

診断の primary span は、原則として誤りを起こした token または節点の span とする。
lexer が token を生成できない E-SUR-001、E-SUR-003、E-SUR-004 はこの原則の例外である。
`E-SUR-001` の primary span は、不正な byte 1 個を指す `(#:span source-id i (add1 i))` である。
`E-SUR-003` の primary span は、開き引用符から停止位置までを指す。
`E-SUR-004` の primary span は、逆斜線から許されない escape 文字までを指す。

E-SUR-001 から E-SUR-011 は P2c1 で registry に登録し、fixture v15 をその時点で 1 度だけ凍結した。
P2c2 は producer を追加するだけで registry を変更しない。
surface の producer 突合は producer のある code だけを対象とするため、未実装の producer をこの文書の契約へ先取りしない。

## 8. F* と parity

F* 側では、Redex の有限例では示せない Surface の全域性と span の性質を並行して検査する。
この版で書く命題は 4 つである。

1. **lexer の全域性**：任意の byte 列に対し、`lex` は token 列または診断を返して停止する。
2. **span の健全性**：`lex` が返す token と診断の primary span が、入力の byte 長の範囲に入る。
3. **span の包含**：`wf_node` を満たす節点について、その span が子の span をすべて包含する。
4. **lowering の span 保存**：`SInt`、`SStr`、`SUnit`、`SBool`、`SVar`、`SApply`、`SProj`、`SRec`、`SFn` の 9 構成子について、`lower_expr` が生成する節点の span が元の span と等しい。

命題 3 は `wf_node` を前提とする条件付き補題である。
parser の出力が `wf_node` を満たすことは F* 側からは示さない。
命題 4 は尾部 span を持つ `SBlock`、`SBind`、`SFnDecl` と、節点を生成しない `STypeDecl`、`SProgram`、型構成子を量化対象から外す。

parity の対応表には、1 対 1、多対 1、対応なし、対象外の 4 種類の行を置く。
parity 検査は、ツール内の構成子リストと対応表の自己整合性だけを保証する。
ツールは `.fst` と `surface.rkt` のソースを読まない。

F* 側の構成子の増減は F* の網羅性検査で、Racket 側の構成子の増減は `fstar-parity-test.rkt` の回帰で、両者の対応は parity 検査で捕まえる。

### 8.1 Surface AST の対応

- `SInt`、`SStr`、`SUnit`、`SBool`、`SVar`、`SFn`、`SApply`、`SProj`、`SRec`、`SBlock` は、同名の F* 構成子と 1 対 1 で対応する。
- `TName`、`TRec`、`TFn` は、同名の F* 構成子と 1 対 1 で対応する。
- `SBind` と `SFnDecl` は、F* 側の `SDecl` へ多対 1 で対応する。
- `STypeDecl` と `SProgram` は、型別名の環境と宣言の並びへ消費されるため、対応する F* 構成子を持たない。
- `SName`、`SParam`、`SField`、`SLabel`、`TField` は、親の構成子の欄へ展開するため、独立した F* 構成子を持たない。

Racket 側の Surface 構成子リストは 22 個、F* 側の `sexpr`、`sty`、`sdecl` の構成子リストは 14 個である。

### 8.2 UCore+ の対応

UCore+ では `#:lit`、`#:var`、`Apply`、`Proj`、`Rec`、`Fn`、`Construct`、`Let`、`Recur` の 9 構成子だけを parity の対象とする。
F* 側では、これらに対応する `CLit`、`CVar`、`CApply`、`CProj`、`CRec`、`CFn`、`CConstruct`、`CLet`、`CRecur` を置く。
`CRecur` は parity の対象を揃えるための構成子であり、この版の lowering は生成しない。
UCore+ の対象構成子リストは 9 個、F* 側の `core` の構成子リストも 9 個であり、F* 側の全対象構成子は 23 個（`sexpr` 10 個、`sty` 3 個、`sdecl` 1 個、`core` 9 個）である。

`Suspend`、`Move`、`TypeMake`、`LetType`、`MacroCall` など、lowering が生成しない UCore+ 構成子は対象外とする。

### 8.3 parity 対象外の型

`Topazolite.Surface` は parity 対象の型のほかにも補助型を置く。
これらは Surface 構文の構成子集合ではないため、parity の対象に含めない。

- `sid`、`span`、`diag`：span と診断の層を写す型であり、Racket 側では `span-core.rkt` と `diagnostic.rkt` が持つ。
- `stok`：`kind` 欄で 7 種の token を表す 1 構成子の record であり、構成子名の集合を成さない。
- `lex_result`、`string_scan`：走査結果を表す和であり、Racket 側では返り値の場合分けとして書かれる。
- `dkind`：束縛の種別を表す欄の型であり、構成子集合の対象ではない。
  `SBind` と `SFnDecl` が F* 側の `SDecl` 1 つへ対応する多対 1 の行は、この型の畳み込みとは別に表す。
- `node`：`sexpr`、`sty`、`sdecl` を命題 3 でまとめて量化するための包みである。
- `bytes_split`、`pos_split`：証明の中だけで使う補助型である。

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

# Topazolite Surface 構文

**状態**：P2h1 版
**参照**：`draft/topazolite_whitepaper_draft_0.4.md` §15（以下、ホワイトペーパー）
**関連文書**：`docs/specification/core-calculus.md`、`docs/specification/structural-row.md`、`docs/specification/span.md`、`docs/specification/diagnostic.md`、`docs/specification/requirements.md`

## 1. 範囲

本書は Surface 構文の正典である。
lexer と parser は canonical source span を保持し、Surface 構文から未型付き縮小 Core への lowering はその span を引き継ぐ。 [REQ: SUR-001]

この版が扱う構文は、整数、文字列、真偽値のリテラル、変数、`=>` の式本体を含む無名関数、Effect row 注釈、関数宣言、関数適用、`const`、`let`、`let mut` の束縛、record リテラル、射影、`type` による型別名と data 型宣言、`trait` と `impl` の宣言、および block である。

この版は、`?=`、pipe、interpolation（`SUR-002`）、borrow 表記（`SUR-004`）、bit 演算子（`BIT-001`）、モジュール（`MOD-001`）を受理しない。
data 型の宣言とその型仮引数、型の位置での data 型の参照は受理する。
constructor の式は受理する。
record 型の欄の `label?: τ` は受理する（`ADT-001`）。
パターン照合（`PAT-001`）は受理しない。
関数と型別名の宣言は型仮引数を持てない。
型位置では `List<Int>` のような型構成子への型適用を受理する（`SUR-016`）。
余剰 `Owned` field の明示 projection は `SUR-006` が担う。

Surface の型注釈と署名から Typed Core への elaboration の入口と返り値は §9 が定める。
`#:expansion-context` は `compile-source` の任意入力として `elab` へ渡す。
Surface の経路は展開表を生成しない。

## 2. 字句

空白はスペースと水平タブであり、区切りとしてのみ働く。
空白はトークンにならない。

改行は有意である。
連続する改行は 1 個の `nl` へ畳み、その間の空白と行コメントも run に含める。
`nl` の span は、その run 全体を覆う。

行コメントは `//` から改行の手前までである。
改行そのものは `nl` として残る。

識別子は `[A-Za-z_][A-Za-z0-9_]*` である。
予約語は `const`、`let`、`mut`、`fn`、`type`、`true`、`false`、`trait`、`impl`、`for`、`derive`、`return`、`match` の 13 語である。
予約語は識別子の規則に合っていても、`ident` として扱わない。

整数リテラルは `[0-9]+` である。
符号は付かない。

文字列リテラルは `"` で囲む。
エスケープは `\"`、`\\`、`\n`、`\t` の 4 種だけを許す。

記号は `{`、`}`、`(`、`)`、`,`、`:`、`=`、`.`、`->`、`=>`、`|`、`&`、`!`、`<`、`>`、`?` の 16 種である。
`->` は `-` と `>` の 2 byte からなる 1 個の `punct` token である。
`=>` は `=` と `>` の 2 byte からなる 1 個の `punct` token である。
`!`、`<`、`>`、`?` はそれぞれ 1 byte の `punct` token である。

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
pitem    ::= typedecl | traitdecl | impldecl | derivedecl | fndecl | binding NL+
typedecl ::= "type" ident "=" ty NL+
           | "type" ident tparams? "=" NL* "|" variant (NL* "|" variant)* NL+
tparams  ::= "<" ident ("," ident)* ">"
variant  ::= ident ("<" ty ("," ty)* ">")?
traitdecl ::= "trait" ident tyrec NL+
impldecl ::= "impl" ident "for" ty record NL+
derivedecl ::= "derive" ident "for" ty NL+
fndecl   ::= "fn" ident "(" params ")" ["->" ty] ["!" row] block NL+
expr     ::= "return" expr | lambda | postfix
lambda   ::= ident "=>" expr
           | "fn" "(" lparams ")" ["!" row] "=>" expr
postfix  ::= primary suffix*
suffix   ::= "(" args ")" | "." ident | "." "{" labels "}"
labels   ::= NL* ident (sep ident)* sep? NL*
sep      ::= ("," | NL) NL*
primary  ::= int | string | "true" | "false" | "(" ")"
           | ident | anonfn | record | block | "(" expr ")" | match
match    ::= "match" expr "{" NL* arm (NL* arm)* NL* "}"
arm      ::= "|" ctor ["(" binders ")"] "=>" expr
ctor     ::= ident | "true" | "false"
binders  ::= ε | ident ("," ident)*
anonfn   ::= "fn" "(" lparams ")" ["->" ty] ["!" row] block
params   ::= ε | param ("," param)*
param    ::= ident ":" ty
lparams  ::= ε | lparam ("," lparam)*
lparam   ::= ident [":" ty]
args     ::= ε | expr ("," expr)*
block    ::= "{" NL* (binding NL+)* expr NL* "}"
binding  ::= bmode ident (":" ty)? "=" expr
bmode    ::= "const" | "let" | "let" "mut"
record   ::= "{" NL* "}"
           | "{" NL* field (fsep field)* fsep? NL* "}"
field    ::= ident ":" expr
fsep     ::= "," NL* | NL+
ty       ::= tyand ("|" tyand)*                         [REQ: BIT-003]
tyand    ::= tyatom ("&" tyatom)*
tyatom   ::= ident ["<" ty ("," ty)* ">"] | tyrec | "fn" "(" tys ")" "->" ty ["!" row] | "(" ty ")"  [REQ: SUR-016]
tyrec    ::= "{" NL* "}"
           | "{" NL* tyfield (fsep tyfield)* fsep? NL* "}"
tyfield  ::= ident "?"? ":" ty
tys      ::= ε | ty ("," ty)*
row      ::= label | "{" [label ("," label)*] "}"          [REQ: SUR-003]
label    ::= ident ["<" ty ">"]
```

`&` は `|` より強く結合し、どちらも左結合である。
`?` を付けた欄は optional であり、`?` と `:` の間に空白を置いてよい。
`match` の各枝は `|` で始まり、枝の間は空白または改行で区切る。
枝の本体は次の `|` または閉じ波括弧の手前で終わる。
`K` と `K()` は同じ束縛子の列を表す。
`true` と `false` は Bool の constructor 名として枝の頭に書ける。
`match` の後ろには呼び出しや射影の suffix を続けられる。
型の括弧は結合順を変えるために使い、括弧自体は AST の節点を作らない。
型の位置の `()` は `E-SUR-005` で拒否する。

トップレベルにも束縛を置ける。
トップレベルの束縛は block の中の束縛と同じ規則で扱う。

関数型の戻り型は `->` で区切り、省略できない。 [REQ: SUR-011]
関数宣言、無名関数、関数型には、任意の Effect row を戻り型または仮引数リストの後ろに書ける。 [REQ: SUR-003]
row は単独の label または波括弧で囲んだ label 列であり、空の列も許す。
型引数を持つ label は `Yield<T>` だけであり、`Return` は宣言 row に限る。
関数型の row は直前の戻り型を持つ最も内側の `fn` 型に結び付く。
`fn(Int) -> Int | Bool ! Partial` は `Int | Bool` を返す `Partial` の関数型である。
`fn(Int) -> Int ! Partial | Bool` は row 付き関数型と `Bool` の Union である。
`fn(Int) -> fn(Int) -> Int ! Partial` の row は内側の関数型に結び付き、外側へ付けるには戻り型を括弧で囲む。
row 内の label は読点だけで区切り、改行は許さない。

Surface が受理する Effect label は次の 7 個である。

| label | 書ける形 | UCore label |
|---|---|---|
| `Partial` | 引数なし | `Partial` |
| `Suspend` | 引数なし | `Suspend` |
| `Compile` | 引数なし | `Compile` |
| `Own` | 引数なし | `Own` |
| `Mutation` | 引数なし | `Mutation` |
| `Yield<T>` | 型引数を 1 個 | `(Yield uτ)` |
| `Return` | 引数なし、宣言 row だけ | `Return` |

row の label は lowering が左から検査し、未知の label、引数の形の不一致、関数型の row に書かれた `Return` は `E-SUR-024` になる。
診断の primary span は最初に不正となった label の span であり、`Yield<T>` の型引数中にある未知の型名は既存の `E-SUR-008` になる。
重複 label は lowering ではそのまま保ち、宣言 row と `resolve-type-row` を通る row の正規化で除く。

宣言 row の `Return` は、row を書いた関数を囲む最も近い境界の `Return<b, T>` を指す。
Surface の関数宣言の宣言 row は、その宣言の外側の境界へ解決されるため、最上位では `E-RET-001` になる。
関数宣言の本体の `return` は、その関数宣言が作る境界へ解決される。
合成位置で戻り型を省略した無名関数の中にある無名関数の宣言 row の `Return` は、戻り型の候補があれば外側の無名関数の推論した戻り型へ解決され、候補が無ければ `E-TYP-024` になる。
候補が無いときに `E-TYP-024` になるのは、本体の elaboration が `return` に先に到達した場合に限る。
その前に別の拒否が起きた場合は、その診断 code が出る。

Surface の式が直接起こさない `Suspend`、`Compile`、`Own`、`Mutation`、`Yield<T>` も宣言 row に書ける。
これらは関数本体の effect row を広げるだけであり、elaboration は本体の row が宣言 row に含まれることを検査する。
`IO`、`Async`、`State<S>`、`Throw<E>`、`Foreign`、`Allocation`、`Volatile`、`Atomic` は対応する Core label が無いため `E-SUR-024` で拒否する。
`Unsafe` は Core にあるが UCore の row に無く、Surface に unsafe 境界が無い段階で宣言だけを許すと境界を偽るため受理しない。
label 名を parser の固定集合で検査する案は採らない。
引数の無い未知 label と型引数を持つ未知 label を parser で別の段・code に分けず、lowering がどちらも `E-SUR-024` として診断する。
elaborate の `E-EFF-001` は防御的な分岐として残るが、UCore の row 文法が閉じているため未知 label は公開入力から到達しない。

関数宣言と無名関数の戻り型は省略でき、省略した戻り型は elaboration が推論する（core-calculus.md §4.3、§4.6）。 [REQ: SUR-008]
無名関数の仮引数型は省略でき、省略した仮引数型は期待型から推論する（core-calculus.md §4.3）。 [REQ: SUR-012]
仮引数型の省略は `=>` の式本体と block 本体の両方で許す。
`fndecl` の仮引数型は省略できない。
本体が自身を参照する関数宣言は、戻り型を省略できない（`E-TYP-024`）。

`=>` の本体は `expr` であり、`,`、`)`、`}`、改行の手前まで読む。
`x => x(1)` は適用を含む本体となり、無名関数をその場で適用するときは `(x => x)(1)` のように括弧で囲む。
`x => y => x` は右結合である。
`fn(x) -> T => e` は block が始まる位置で `E-SUR-005` になる。

program の末尾は式でなければならない。
空の入力と、宣言だけで式の無い入力は、どちらも `E-SUR-006` で拒否する。
縮小 Core の項は式であり、式を持たない program には落とし先が無いためである。

`typedecl` の 2 つ目の形は data 型宣言であり、`=` の後の改行を読み飛ばした次の token が `|` の場合に選ぶ。
型仮引数を持つ宣言の右辺が `|` で始まらない場合は、`E-SUR-005` で拒否する。
型仮引数を持たない型別名の文法は従来どおりである。
`<>` と constructor を持たない宣言も `E-SUR-005` で拒否する。
`true` と `false` は予約語なので constructor 名にならず、構文解析で `E-SUR-005` になる。
識別子として書ける組み込み constructor（`nil`、`cons`、`none`、`some`、`ok`、`ng`）との重なりは、名前検査で `E-SUR-029` になる。

型別名と data 型の名前は、trait 名と共有する型の名前空間で解決する。
型別名と data 型の名前をすべて先に集めるため、型別名の右辺と欄の型は後方の data 型も参照でき、data 型どうしの相互参照も書ける。
trait 宣言はすべて impl 宣言より先に環境へ登録するため、impl は対応する trait より前に書ける。

### 3.1 受理しない構文

字句に無い記号は lexer が `E-SUR-002` を返す。
単独の `-`、`+`、`*`、`/`、`%`、`[`、`]`、`;` は字句にならない。
算術演算子を含む式、`?=`、pipe は、最初の未対応記号または構文に合わない token の位置で拒否する。
`x |> f` は `E-SUR-005` になる。`List<>` は `>` の位置で `E-SUR-005` になる。
`|` は型位置と match の枝の先頭で受理し、`&` は型位置だけで受理する。
式の位置の `x | y` と `x & y` は `E-SUR-005` になる。
`x |> f` は、式位置の `|` で `E-SUR-005` になる。

字句にはなるが構文に無い `if` と `while` は予約語ではなく `ident` になる。
`if cond { }` のように後ろへ式が続く形は、2 つ目の primary の位置で `E-SUR-005` になる。
`return expr` は最も弱く結合する前置式で、`expr` 全体を戻り値とする。
予約語 `for` は式の先頭には置けず、その位置で `E-SUR-005` になる。

P2h1 では `trait`、`impl`、`for` を予約語へ加え、P2h2 では `derive` を、P2k1 では `return` を、P2m1 では `match` を加えた。

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

### 3.5 多 field 射影の label 列

`r.{a, b}` は、`r` から複数の field を一度に取り出す後置である。 [REQ: SUR-006]
label 列は非空であり、同じ label を 2 度書けない。
どちらに反しても `E-SUR-012` を返し、primary span は `{` から `}` までとする。

label 列の区切りは読点と改行のどちらでもよく、末尾の読点を許す。
record literal の field の区切りと同じ規則である。

この検査は parser が行う。
`SProjRec` の第 1 欄の span は `r.{a, b}` の全体を覆うものであり、`{` から `}` までだけを囲む span は構文解析の時点にしか無いからである。

波括弧の中に書けるのは `ident` だけである。
`r.{a: 1}` や `r.{1}` は `E-SUR-005` になる。

drop する側を書く構文は置かない。
残す label を列挙すれば残余は一意に決まるため、2 通りの綴りを持つ必要が無い。

## 4. span

span は `(#:span sid lo hi)` の 4 要素である。
`lo` と `hi` は UTF-8 byte 位置であり、半開区間 `[lo, hi)` を表す。

Surface の節点はすべて `(Ctor span ...)` の形であり、span は必ず第 2 欄に置く。
`span-of` は Surface の節点と縮小 Core の節点の両方から span を取る。

節点の span は、その子孫のすべての span を包含する。
包含の検査は、親と子が同じ source id を持ち、親の開始位置が子以下で、親の終了位置が子以上であることを確かめる。

型演算子の節点は `(TUnion s left right)` と `(TInter s left right)` である。
節点の span は左右 operand の span の hull とし、型の括弧は AST を作らず span も広げない。

括弧で括った式は括弧の span を持たない。
括弧そのものが節点を作らないため、括弧内の式の span をそのまま使う。
ただし `()` は単位値の節点を作るため、その節点は 2 個の括弧を含む span を持つ。

節点の span は最初の token の左端から最後の token の右端までである。
区切りの `nl` は節点の span に含めない。
`SBlock` の span は開き `{` から閉じ `}` までを含む。
`SProgram` の span は前後の `NL*` を含まず、最初の item（item が無ければ式）から末尾の式までを覆う。
`SEffRow` の span は `!` から、波括弧形なら `}` まで、単独 label ならその末尾までを含む。
`SEffLabel` の span は名前の先頭から、型引数があれば `>` までを含む。

## 5. 型別名と data 型

型別名は Surface だけの糖衣である。
UCore+ には型別名を置く欄が無いため、`STypeDecl` は節点を生成せず、lowering の別名環境へ消費する。
型別名は `TypeNarrative` による `TypeInfo` 生成を経ず、静的な型 `τ` へ直接展開する。
型宣言と型位置の演算子から `TypeNarrative` を使って `TypeInfo` を生成する経路は、requirements.md §4 の申し送り表に記録する。
`SDataDecl` も UCore+ の節点を生成せず、宣言表として台帳へ渡す。

別名環境は 2 度の走査で作る。
1 度目は program の `spitem` を原文順に読み、型別名の名前と未展開の `sty`、および data 型の名前を登録する。
2 度目は型別名の各 `sty` の中の `TName` を環境の定義へ置き換え、展開結果に現れる `TName` も同じ規則で解決する。

1 度目の走査で名前をすべて登録してから 2 度目の走査を行うため、宣言より前の位置から後の宣言を参照できる。
宣言順に 1 度で読む方式は採らない。

展開関数は展開後の型だけを返す。
使用位置の span は呼び出し側が入力の `sty` から `(span-of ty)` で取るため、展開後の型と span を 2 値で返す必要はない。

### 5.1 拒否する型別名

型別名、data 型、trait 名は一つの名前空間を共有する。
型別名の展開は次の誤りを拒否する。

- 環境に無く、基本型でもない名前は `E-SUR-008` とする。
- trait 名を型の位置で使った `TName` は `E-SUR-021` とする。
- 同じ名前の 2 度目の宣言は `E-SUR-009` とし、2 度目の `SName` の span を primary span にする。
- 展開経路上で循環する参照は `E-SUR-010` とし、循環を閉じた `TName` の span を primary span にする。
- 基本型と同じ名前の宣言は `E-SUR-011` とする。
- 型の名前が基底の trait または原文中の trait と衝突するときは `E-SUR-023` とする。primary span は型の `SName` であり、原文中の trait との衝突ではその `SName` を `trait-declaration` の related にする。
- 基本型名を trait 名として宣言したときも `E-SUR-023` とし、primary span は trait の `SName` とする。

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
1 度目の走査では、宣言を原文順に読み、型宣言では `Self`、基本型名、既出名、trait 名との衝突の順に検査して、それぞれ `E-SUR-008`、`E-SUR-011`、`E-SUR-009`、`E-SUR-023` とする。
trait 宣言では基本型名との衝突を `E-SUR-023` とする。
trait 名との衝突は基底環境の全 trait 名と原文中の全 trait 宣言名を比較するため、宣言の順序に依存しない。
名前の誤りがあれば 2 度目の走査へ進まない。

2 度目の走査では、型名を左から右へ検査する。
展開中の stack にある名前は `E-SUR-010` とし、環境の trait 名へ解決される名前は `E-SUR-021` とする。
型別名、data 型、基本型、trait 名、または型構成子のいずれでもない名前は `E-SUR-008` とする。
型構成子を引数なしで使う場合は `E-SUR-025` とする。
record と record 型の field は左から右へ走査し、最初に見つかった 2 度目の label で `E-SUR-007` を返す。
3 件以上の重複があっても、最初の 1 件だけを返す。

合成宣言の候補分類は診断を返さず、最大不動点で決める（§5.3）。
名前の検査と通常の型別名の検査を通った後、合成宣言を原文順、各右辺を後行順に解決する。
解決中の合成宣言名を再び辿った葉は `E-SUR-010` とし、同じ構造鍵の左右または衝突する要求 label は、その `TInter` 全体を primary span とする `E-SUR-022` とする。

### 5.3 trait の合成

合成 trait の表層宣言は、二項の `intersect` の入れ子へ lowering されなければならない。 [REQ: SUR-009]

`type N = rhs` の右辺が `TInter` を根とし、`TInter` だけを辿った葉がすべて `TName` であるとき、その宣言を合成宣言の候補とする。
候補から、葉のどれかが既知の trait 名でも候補の宣言名でもないものを除き、除くものがなくなるまで繰り返す。
残った候補が合成宣言であり、分類は最大不動点を使う。
このため合成宣言どうしの循環は候補に残り、解決時に `E-SUR-010` となる。

trait 名は基底環境の trait 名と原文の trait 宣言名である。
型別名と trait 名は一つの宣言名前空間を共有する。
型宣言と trait 宣言の名前が衝突すれば `E-SUR-023` とし、基本型名 `Int`、`Bool`、`Unit`、`String` の trait 宣言も同じ診断にする。
型位置にある trait 名は `E-SUR-021` とする。

合成宣言右辺の各葉と `TInter` に、括弧の形を保つ構造鍵を与える。
通常の trait 名の鍵はその名前、既存の合成 trait 名の鍵はその intersect 行から再帰的に得る鍵とする。
合成宣言名の鍵はその宣言の右辺の根の鍵であり、`TInter` の鍵は左右の鍵を全順序で並べた組である。
葉は組より小さく、葉どうしは `symbol<?`、組どうしは左の成分を再帰的に比べ、等しければ右の成分を比べる。
左右をこの順序で揃えるため、`A & B` と `B & A` は同じ鍵を持つ。
括弧の形は平坦化しないため、`(A & B) & C` と `A & (B & C)` は異なる鍵になる。

鍵ごとの出力は、基底環境の合成 trait、原文順で最初にその鍵を根に持つ合成宣言名、隠れた名前 `%compose-<n>` の順で決める。
同じ鍵を持つ後続の宣言は最初の出力への Surface 別名になり、行を追加しない。
たとえば `type RW = Readable & Writable` の後の `type WR = Writable & Readable` は `RW` への別名である。
kernel の `Printable & Sizable` と `Printable & Sizable & Taggable` は、それぞれ `PrintableSizable` と `PrintableSizableTaggable` への別名になる。

無括弧の三項合成 `A & B & C` は左結合である。
最初の鍵に名前付き出力がなければ内側に `%compose-1` を作り、外側の行はその名前を成分として持つ。
合成宣言の鍵をすべて先に求めてから出力名を決めるため、`type X = (A & B) & C` が `type AB = A & B` より先にあっても、内側の出力は後続する `AB` になる。

trait 名は合成宣言右辺の `TInter` の葉と、`impl` または `derive` の trait 名としてだけ使える。
通常の型別名、`let` 注釈、関数型、record 型の欄、trait template の欄、impl と derive の対象型では型名として解決し、trait または合成宣言名なら `E-SUR-021` とする。
型位置の `TName` は、`Self`、型仮引数、基本型、型構成子の単独使用、展開中の型別名、環境中の型別名・data 型・trait、未知名の順で解決する。
`TApp` の頭は、型仮引数、`Self`、展開中の型別名、trait、型構成子でない既知の型、組み込み型構成子と data 型、未知名の順で解決する。
型式は左から右へ検査する。

### 5.4 data 型宣言の名前と診断

data 型の名前は、型別名と trait の名前と共有する型の名前空間に属する。
原文の data 型の名前は欄の型を解決する前にすべて集めるため、data 型の前方参照と相互参照ができる。
基底の data 型も名前表へ含め、同じ名前空間に属する原文の名前との衝突を検査する。

data 型の宣言名は、次の順で検査する。
`Self` は型別名と同じく `E-SUR-008`、組み込み型の名前は `E-SUR-028`、既出の data 型名は `E-SUR-027`、型別名との重なりは `E-SUR-031`、trait 名との重なりは `E-SUR-023` とする。
組み込み型の名前には基本型のほか、`Never`、`Res`、`List`、`Option`、`Result`、`Owned`、`Borrowed`、`BorrowedMut`、`RawPtr`、`NFn`、`TypeInfo`、`Proof`、`Record`、`Untrusted`、`Refined`、`Union`、`Intersection`、`ForallRegion`、`Data` を含む。
原文の宣言どうしが重なる場合は後の宣言名を primary、先の宣言名を related とする。
基底の宣言との重なりは原文の名前を primary とし、基底に span が無いため related を付けない。
基底の data 型名と原文の constructor 名、および基底の constructor 名と原文の data 型名は別の名前空間に属するため衝突しない。

constructor 名は全ての data 型で一意とし、組み込み constructor の名前とも重ねない。
識別子として書ける組み込み constructor `nil`、`cons`、`none`、`some`、`ok`、`ng` との重なりは `E-SUR-029` とする。
`true` と `false` は予約語であり、constructor 名として書くと構文段階で `E-SUR-005` になる。
原文の constructor 名どうしの重なりは、後の名前を primary、先の名前を related とする。
組み込みまたは基底の constructor との重なりでは related を付けない。
constructor 名を top-level 関数、基底環境、または kernel の `Γ0` の名前と重ねることは `E-SUR-032` とする。
top-level 関数の名前を組み込みの constructor 名（`nil`、`cons`、`none`、`some`、`ok`、`ng`）と重ねることも `E-SUR-032` とし、関数の名前を primary として related を付けない。
原文の関数と重なる場合は後に現れた名前を primary、先の名前を related とする。
原文の関数名と基底の constructor 名が重なる場合は、原文の関数名を primary とし、related を付けない。
基底環境または kernel の `Γ0` の名前と重なる場合は constructor 名を primary とし、related を付けない。
Surface の式構文は `SVar` と `SApply` を保ち、parse 後の名前解決が constructor を内部 AST の `SConstruct` へ置き換える。
`let` の右辺は外側の有効範囲で調べ、継続は束縛子を加えた有効範囲で調べる。
関数の仮引数と `=>` の仮引数は、その本体だけで同名の constructor を隠す。
この pass は局所束縛子に無い constructor 名だけを置き換え、その他の未束縛名は変数として残す。

型仮引数はその data 型の欄の型だけで有効であり、型別名、data 型、組み込み型より先に解決する。
同じ宣言で型仮引数名を重ねた場合は `E-SUR-030` とし、後の名前を primary、先の名前を related とする。
欄の型の未知名は `E-SUR-008`、型適用の個数不一致は `E-SUR-025` とする。

data 宣言に複数の誤りがある場合は、型名、constructor 名、型仮引数、欄の型、regularity、positivity の順で最初の 1 件を返す。
同じ段では原文の順で最初に見つかった誤りを返す。
regularity の違反は `E-SUR-033`、positivity の違反は `E-SUR-034` とする。
どちらも違反する出現を含む欄の型を primary、欄を持つ data 型宣言の名前を related とする。

## 6. UCore+ への lowering

lowering の入口は `(lower-surface sprog trait-env)` である。
返り値は Diagnostic 1 件か `(struct lowered (term trait-rows impl-rows intersect-rows data-decls spans))` のいずれかである。
`term` は UCore+ の項、`trait-rows`、`impl-rows`、`intersect-rows` は宣言から作った行、`data-decls` は data 型宣言の並び、`spans` は宣言由来の鍵から原文 span への対応表である。
各 data 型宣言は `(T (X ...) ((K (σ ...)) ...))` の形であり、`T` は型名、`X ...` は型仮引数、各 `K` は constructor 名、各 `σ ...` はその欄の型である。
合成 trait 行は `trait-rows` に、合成で作った intersect 行は `intersect-rows` に含める。
呼び側はこれらの行を基底の `trait-env` へ重ね、`data-decls` を基底の data 宣言と合わせて台帳を作る。
引数が Diagnostic のときは、それをそのまま返す。
この節は parser が diagnostic を返した経路を呼び側の分岐漏れで失わないために置く。

別名環境を §5 の規則で先に構築・検査し、`sty` を `uτ` へ落とす際に使う。
この前処理では合成宣言の候補も分類するが、合成の鍵と出力はまだ確定しない。
data 型宣言は先行収集した名前の下で欄の型を解決し、`data-decls` へ写す。
欄の型の解決までに名前、constructor、型仮引数を検査し、型適用の不一致や未知名を Surface 診断として返す。
欄の型を解決した後、基底と原文の data 宣言から台帳用の索引を作り、原文に data 宣言がある場合は regularity と positivity を検証する。
この検証は trait、impl、intersect の宣言を lowering する前に行い、違反はそれぞれ `E-SUR-033` と `E-SUR-034` にする。
primary は違反する出現を含む欄の型、related はその data 型宣言の名前である。
台帳の `#:fail` に kind `data` の失敗が届くことはない。
lowering が regularity と positivity を先に検証するためであり、届いた場合は内部の誤りとして扱う。
この検証済みの索引は、trait と impl の要求型を検査する残りの lowering でも使う。
続いて全 trait 宣言を原文順に読み、既存または原文中の同名 trait を `E-SUR-013` とする。
生成した origin id や primitive 名が基底環境または kernel の `R0`・`Γ0` の鍵と衝突すれば `E-SUR-016` とする。
次に全合成宣言の鍵と template を解決し、鍵ごとの出力を決めて合成 trait 行と intersect 行を作る。
基底環境へ trait 行、合成 trait 行、intersect 行を重ねた後、`impl` と `derive` の宣言を原文順に 1 件ずつ検査する。
この段で原文に書かれた合成宣言名を出力 trait 名へ写してから参照先を調べるため、合成 trait への直接実装は `E-SUR-018` になる。
どちらも参照先の trait が無ければ `E-SUR-015`、合成 trait なら `E-SUR-018` とする。
impl では本体の label 集合が要求と異なれば `E-SUR-017` とする。
対象型を lowering して正規化し、未知の型名は `E-SUR-008` とする。
impl では対象型への `Self` 置換後に要求型を正規化し、失敗すれば対象型の span を primary、trait 名の span を `trait-requirement` の related とする `E-SUR-020` を返す。
derive では trait の origin に対応する生成規則を先に引き、規則が無ければ `E-SUR-019` とする。
規則がある場合は impl と同じ要求型の検査を行い、正規化に失敗すれば `E-SUR-020` とする。
同じ trait と型同値な対象型の impl 行または derive 行がすでにあれば、どちらの宣言でも `E-SUR-014` とする。
このため impl の検査順は `E-SUR-015`、`E-SUR-018`、`E-SUR-017`、対象型の lowering、`E-SUR-020`、`E-SUR-014` である。
derive の検査順は `E-SUR-015`、`E-SUR-018`、対象型の lowering、`E-SUR-019`、`E-SUR-020`、`E-SUR-014` である。
生成した origin id または primitive 名が既存の鍵と衝突すれば `E-SUR-016` とする。
各行は検査を通ってから環境へ加えるため、後続の impl と derive の重複も検出する。
この前処理の後、項の宣言を右から畳み、`Let` と `Recur` を積む。

### 6.1 対応表

Surface の span は、下表で `s` と書いた欄へそのまま渡す。
型注釈の span は入力の `sty` 節点から `(span-of ty)` で取る。
別名展開後も、型注釈の包みが持つ span は使用位置の `TName` の span とする。

- `(SInt s n)` は `(#:lit n s)` へ落とす。
- `(SStr s str)` は `(#:lit str s)` へ落とす。
- `(SUnit s)` は `(#:lit unit s)` へ落とす。
- `(SBool s true)` と `(SBool s false)` は、それぞれ `(Construct s true (Types))` と `(Construct s false (Types))` へ落とす。
  `Bool` は型引数を持たないので、空の `(Types)` が core-calculus.md §4 の E-Construct-Synth の型引数注釈を与え、合成位置でも型が定まる。 [REQ: SUR-007]
- `(SVar s x)` は `(#:var x s)` へ落とす。
- `(SApply s f (a ...))` は `(Apply s f' a' ...)` へ落とす。
- `(SConstruct s (SName s_K K) (e ...))` は constructor `K` の所有 data 型の型仮引数の個数に応じて lowering する。
  型仮引数が無い場合は `(Construct s K (Types) e' ...)` とし、期待型が無い位置でも合成できる。
  型仮引数がある場合は `(Construct s K e' ...)` とし、検査位置の期待型から型引数を決める。
  constructor の単独使用は 0 欄の適用として扱う。
  型仮引数の無い constructor の欄数不一致は常に `E-ARI-001` とする。
  型仮引数のある constructor は、期待型が所属 data 型なら欄数不一致を `E-ARI-001`、期待型が無ければ `E-TYP-003`、他の型なら `E-DAT-002` とする。
- `(SProj s e (SLabel s_l l))` は `(Proj s e' (#:lbl l s_l))` へ落とす。
- `(SProjRec s e ((SLabel s_l l) ...))` は、受け側を 1 度だけ束縛する `Let` と、label ごとの `Proj` を並べた `Rec` へ落とす。 [REQ: SUR-006]
- `(SRec s ((SField s_f (SLabel s_l l) e) ...))` は `(Rec s (((#:lbl l s_l) imm e') ...))` へ落とす。
- `(SFn s ((SParam s_p (SName s_x x) sty-or-none) ...) return-sty-or-none row-or-none body)` は、span を持つ binder、戻り型、Effect row を持つ `(Fn ...)` へ落とす。row が明示されていれば、その label を lower-row した row と row 節の span `s_row` を `(#:ef labels s_row)` として置く。
  row が省略されていれば `(#:ef #:infer s)` を置き、`s` は関数全体の span である。
  `=>` と block の両形の無名関数でこの印を使う。
  検査位置では期待型から `Owned` を 1 層剥がして `NFn` を得た場合に、その出口 row を継承し、合成位置または `NFn` でない期待型では空 row になる（core-calculus.md §4.2、§4.3）。
  row が明示されていれば、空の row も期待型から継承せず、宣言 row と期待 row の照合は既存の検査規則で行う。
  仮引数型が `#:none` なら型欄は `(#:infer s_x)` となり、`s_x` は binder の span である。
  戻り型が `#:none` なら戻り型欄は `(#:infer s)` となる。
- `(SBlock s (bind ...) e)` は、束縛を右から畳んだ `Let` の入れ子へ落とす。
- `(SBind s bmode (SName s_x x) ty e)` は、注釈があれば型注釈付き `Let` へ、無ければ mode-only `Let` へ落とす。
  右辺が仮引数型または Effect row を省略した `Fn`、または型引数欄の無い `Construct` なら宣言型で検査する。
  それ以外は右辺を合成し、その結果へ binding mode の policy を適用する（core-calculus.md §4.2、structural-row.md §4）。
- `(SFnDecl s (SName s_f f) ... return-sty-or-none row-or-none body)` は、関数本体と後続の項を持つ `Recur` へ落とす。明示 row は lower-row の結果を row 節の span `s_row` とともに置く。
  row が省略されていれば Recur の row は空であり、その row 欄の span は関数宣言全体の span `s` である。
  戻り型が `#:none` なら `Recur` の戻り型欄は `(#:infer s)` となり、`s` は関数宣言全体の span である。
- `(STypeDecl s (SName s_n T) ty)` は別名環境へ入れるだけで、節点を生成しない。
- `(SDataDecl s (SName s_T T) ((SName s_X X) ...) ((SName s_K K) (sty ...)) ...)` は data 宣言表へ入り、節点を生成しない。
  `lowered-data-decls` の各要素は `(T (X ...) ((K (σ ...)) ...))` である。
  欄の型を解決して `σ` へ写す。
  `spans` には `(data . (T K i #f))` を欄の型の span として記録し、`i` は 0 始まりの欄の位置である。
  `(data-name . T)` には宣言名の span を記録する。
- `(STraitDecl s (SName s_n tn) (tyfield ...))` は trait 環境へ行を追加するだけで、UCore+ 節点を生成しない。
- trait 宣言の template の型位置では `Self` を実装対象型の placeholder として扱う。欄名の `Self` は通常の label である。
- `Self` は字句上の予約語ではないが、trait template 以外の型位置と型別名の宣言名では `E-SUR-008` とする。
- `(SImplDecl s (SName s_n tn) ty (SRec s_b (field ...)))` は生成 primitive の適用を後続の項へ束縛する `Let` と `Apply` へ落とす（§6.2）。
- `(SDeriveDecl s (SName s_n Tr) ty)` は、`trait.md` §4.6 の生成規則が作る `rec_core` を derive primitive へ適用し、その結果を後続の項へ束縛する `Let` と `Apply` へ落とす。

```text
(SDeriveDecl s (SName s_n Tr) ty)
  ⟶ (Let s_tail ((#:bind %derive-Tr-n s) const)
          (Apply s (#:var derive-user-Tr-n s) rec_core) rest)
```

この版で定義する `rec_core` の形と生成規則は `trait.md` §4.6 に従う。

多 field 射影の落とし先は次の形である。

```text
(SProjRec s r ((SLabel s_a a) (SLabel s_b b)))
  ⟶ (Let s ((#:bind %projrec s_r) const) r_core
          (Rec s (((#:lbl a s_a) imm (Proj s_a (#:var %projrec s_r) (#:lbl a s_a)))
                  ((#:lbl b s_b) imm (Proj s_b (#:var %projrec s_r) (#:lbl b s_b))))))
```

受け側の束縛の mode は `const` であり、結果の欄はすべて `imm` である。
元の field が `mut` でも結果は `imm` になる。
`Owned` の欄を残す射影は、`Rec` が `Owned` の欄を持てないため `T-Rec` が拒否する（`structural-row.md` §3.1）。
F* 側の `SProjRec` は Surface 欄に label の綴りと span を持つが、`proj_fields` は綴りを Core へ渡さず、各 field の label span を `Rec` と `Proj` に保持する。
受け側の綴り `%projrec` は、`lexer.rkt` の `ident-start?` が `%` を受理しないため入力の識別子と衝突しない。

`TName` のうち `Int`、`Bool`、`Unit`、`String` は同綴りの `uτ` へ写す。
それ以外は §5 の別名環境から解決し、未登録なら `E-SUR-008` とする。
`TRec` は field mode を `imm` とする `(Record ((l uτ imm) ...))` へ写す。
`?` を付けた欄は `(l uτ imm opt)` へ写す。
省略の受理と `ProjOpt` への写しは elaborate が行う（`structural-row.md` §3）。
`TFn` は `(NFn (uτ ...) uτ_r ε ())` へ写す。
`ε` は明示された型 Effect row を lower-row した結果であり、省略時は空である。
型 Effect row の `Return` は拒否する。
obligation は Surface から表せないため空であり、record 型の field mode は Surface に可変性の構文が無いため `imm` とする。
`(TUnion s left right)` は `(Union left' right')` へ、`(TInter s left right)` は `(Intersection left' right')` へ写す。
`TInter` は operand を lowering した後、`Self` を含まなければ `lift-template-type` と `normalize-type` で検査し、失敗時はその `TInter` の span で `E-SUR-020` を返す。
ここでいう `Self` は型の位置に限り、Record の field label は数えない。
`Self` を含む Intersection の検査は対象型の具体化まで遅らせる。

trait template はまず Record 全体を正規化する。
それが失敗した場合は field label 順に並べ、各 field 型を個別に正規化し、失敗した型は未正規化の形で残す。
impl または derive の対象型で `Self` を置換した後、`instantiate-requirements` は各要求 field の型を正規化する。
具体化後も正規化できない要求があれば、対象型の span を primary、宣言中の trait 名の span を `trait-requirement` の related として `E-SUR-020` を返す。
lowering の検査を通った `Self` を含まない型は、正規化に成功する。

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
`SDataDecl` は項へ畳まず、`data-decls` に宣言を残す。

impl 宣言の lowering は次の形であり、`Apply` は impl 宣言全体の span、`Let` は尾部 span を持つ。

```text
(SImplDecl s (SName s_n T) ty (SRec s_b fields))
  ⟶ (Let s_tail ((#:bind %impl-T-n s) const)
          (Apply s (#:var impl-user-T-n s) body_core) rest)
```

`%impl-T-n` は局所の束縛名であり、`impl-user-T-n` は台帳から得る impl primitive 名である。
impl の実装 record はこの primitive へ渡す。

尾部 span を使うと、`Let` と `Recur` の親 span が後続の項を包含する。
生成した span は入力の token 位置から決まり、`#:synthetic` は使わない。

### 6.3 span の対応単位

`SUR-001` の span 引き継ぎは、UCore+ の節点または包みを 1 個生成する構成子を単位とする。
`SName`、`SLabel`、`TName`、`TRec`、`TFn` の span は、それぞれ binder、label、型注釈の欄へ渡す。

`SProgram`、`SBlock`、`STypeDecl`、`SDataDecl`、`STraitDecl`、`SParam`、`SField`、`TField` は、対応する UCore+ の節点または欄が無いため、その構成子自身の span を項へ渡さない。
`SDataDecl` の宣言名と欄の型の span は、data 検証の診断用に `spans` へ記録する。
`SImplDecl` の span は生成する `Apply` へ渡し、`Let` には宣言から後続の項までの尾部 span を使う。
`uτ` に span を足す改修はこの版の範囲外である。

### 6.4 Sizable の Union

Surface の `Sizable` derive recipe は、正規化後の Union の各異なる成分について葉の数を求め、その和を `size` とする。
Union の重複成分は正規化で除かれる。
Intersection は正規化後の Record として扱い、Record に対する葉の数の規則（`trait.md` §4.6）を適用する。

## 7. 診断

`surface` 相は registry v15 で登録した。
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
- `E-SUR-012` `surface-projection-labels`：多 field 射影の label 列が空か重複している
- `E-SUR-013` `surface-duplicate-trait-decl`：同じ名前の trait を 2 度宣言した
- `E-SUR-014` `surface-duplicate-impl-decl`：同じ trait と型同値な対象型の組へ impl または derive を 2 度宣言した
- `E-SUR-015` `surface-unknown-trait-name`：宣言の無い trait の名前を impl または derive が参照した
- `E-SUR-016` `surface-trait-name-collision`：宣言から作る鍵が基底の trait 環境または kernel の `R0`・`Γ0` と衝突した
- `E-SUR-017` `surface-impl-requirement-mismatch`：impl 本体のラベル集合が trait の要求と合わない
- `E-SUR-018` `surface-impl-composite-trait`：合成 trait へ impl または derive を宣言した
- `E-SUR-019` `surface-derive-no-recipe`：kernel の生成規則を持たない trait と対象型の組へ derive を宣言した
- `E-SUR-020` `surface-type-not-normalizable`：型位置の &、または trait の要求型の Self を対象型で置き換えた結果が正規化できない
- `E-SUR-021` `surface-trait-in-type-position`：trait 名または合成宣言の名前を型の位置で使った
- `E-SUR-022` `surface-invalid-trait-composition`：同じ鍵の trait、または label が衝突する trait を `&` で並べた
- `E-SUR-023` `surface-type-trait-name-collision`：型の名前が trait の名前と衝突した。基本型の名前の trait を含む
- `E-SUR-024` `surface-invalid-effect-label`：Surface で書けない Effect label、または引数の形が合わない Effect label
- `E-SUR-025` `surface-type-application-mismatch`：型構成子でない名前への型適用、型引数の個数が合わない型適用、または型引数の無い型構成子
- `E-SUR-026` `surface-reserved-type-constructor-name`：型構成子の名前（List、Option、Result、Owned）を型別名として宣言した
- `E-SUR-027` `surface-duplicate-data-type`：同じ名前の data 型を 2 度宣言した、または基底の data 型と同じ名前の data 型を宣言した
- `E-SUR-028` `surface-reserved-data-type-name`：組み込み型の名前を data 型の名前として宣言した
- `E-SUR-029` `surface-duplicate-constructor`：constructor の名前が組み込み、基底、または他の宣言の constructor と重なった
- `E-SUR-030` `surface-duplicate-type-parameter`：data 型の宣言で同じ型仮引数を 2 度書いた
- `E-SUR-031` `surface-type-data-name-collision`：data 型の名前と型別名の名前が重なった
- `E-SUR-032` `surface-constructor-value-name-collision`：constructor の名前が top-level の関数、基底の constructor、または kernel の `Γ0` の名前と重なった。組み込み constructor と top-level 関数の重なりも含む
- `E-SUR-033` `surface-irregular-data-recursion`：data 型の再帰的な出現の型引数が宣言の型仮引数の並びと一致しない
- `E-SUR-034` `surface-non-positive-data-recursion`：data 型の再帰的な出現が関数型の引数の側にある

`E-SUR-022` の primary span は、失敗した `TInter` 全体を指す。
related は `composition-left` と `composition-right` の 2 件で、原文に書かれた左右の operand の span と表示名を持つ。
`E-SUR-023` の related は、原文の trait 宣言と衝突した場合の `trait-declaration` である。
`E-SUR-033` と `E-SUR-034` は `lower-surface` が段 5 と段 6 の data 宣言の検証で返す。
primary は違反する出現を含む欄の型、related は欄を持つ data 型宣言の名前である。
これらは trait、impl、intersect の宣言を lowering する前に検査される。
台帳の `#:fail` に kind `data` の失敗が届くことはなく、届いた場合は内部の誤りである。

診断の primary span は、原則として誤りを起こした token または節点の span とする。
lexer が token を生成できない E-SUR-001、E-SUR-003、E-SUR-004 はこの原則の例外である。
`E-SUR-001` の primary span は、不正な byte 1 個を指す `(#:span source-id i (add1 i))` である。
`E-SUR-003` の primary span は、開き引用符から停止位置までを指す。
`E-SUR-004` の primary span は、逆斜線から許されない escape 文字までを指す。

E-SUR-001 から E-SUR-011 は P2c1 で registry に登録し、fixture v15 をその時点で 1 度だけ凍結した。
E-SUR-012 は registry v17、E-SUR-013 から E-SUR-018 は P2h1 の registry v19 で追加した。
E-SUR-019 は P2h2 の registry v20 で追加した。
E-SUR-020 は P2h3a の registry v21 で追加した。
E-SUR-021 から E-SUR-023 は P2h3b の registry v22 で追加した。
E-SUR-024 は P2j の registry v26 で追加した。
E-SUR-025 と E-SUR-026 は P2l2a の registry v28 で追加した。
E-SUR-027 から E-SUR-034 は P2l2b1 の registry v29 で追加した。
surface の producer 突合は producer のある code だけを対象とするため、未実装の producer をこの文書の契約へ先取りしない。

## 8. F* と parity

F* 側では、Redex の有限例では示せない Surface の全域性と span の性質を並行して検査する。
この版で書く命題は 7 つである。

1. **lexer の全域性**：任意の byte 列に対し、`lex` は token 列または診断を返して停止する。
2. **span の健全性**：`lex` が返す token と診断の primary span が、入力の byte 長の範囲に入る。
3. **span の包含**：`wf_node` を満たす節点について、その span が子の span をすべて包含する。
4. **lowering の span 保存**：`SInt`、`SStr`、`SUnit`、`SBool`、`SVar`、`SReturn`、`SApply`、`SConstruct`、`SProj`、`SRec`、`SFn` の 11 構成子について、`lower_expr` が生成する節点の span が元の span と等しい。
5. **予約語**：Racket の `lexer.rkt` が予約する 13 語のそれぞれについて、`keyword_word` がその byte 列に `TkKw` を返す。
6. **block の根の span**：空でない宣言の列について、`span_of_core (lower_block (d :: ds) tail)` は `hull (span_of_decl d) (span_of_core (lower_block ds tail))` に等しい。
7. **欄の保存**：`lower_expr` と `lower_block` が作る節点は、元の名前と label の span、Effect row を保持する。

命題 3 は `wf_node` を前提とする条件付き補題である。
parser の出力が `wf_node` を満たすことは F* 側からは示さない。
命題 4 は尾部 span を持つ `SBlock`、`SBind`、`SFnDecl` と、1 つの節点を複数の節点へ増やす `SProjRec`、節点を生成しない `STypeDecl`、`SProgram`、型構成子を量化対象から外す。
`SProjRec` の lowering の根の span は入力の span を保存するが、複数の節点へ展開するため命題 4 の対象外である。
命題 6 は、空の block の元の span を保存するとは主張しない。
空の block の lowering は末尾式の lowering そのものであり、`SBlock` の span を持たない。
命題 7 は、`SFn` の仮引数名の span と row、`SProj` の label の span、`SRec` の label の span の列、`SProjRec` の受け側の span と各 field の label の span、`SBind` の束縛名の span、`SFnDecl` の関数名と仮引数名の span と row を扱う。
`SFn` の省略した row は省略のまま保ち、`SFnDecl` の省略した row は宣言全体の span の空の row とする。
これは Racket の `surface-lower` が `SFn` の省略を推論へ回し、`SFnDecl` の省略を空の row へ写すことに合わせる。
名前と label の span が親の span に含まれることは、`wf_expr` と `wf_decl` の定義が直接検査する。
これらの span は子の節点ではないので、命題 3 の結論には入らない。

F* の `core` は span と項の形の模型であり、型を検査しない。
型注釈、戻り型、束縛の種別は `core` へ写さないので、命題 7 は型注釈の span の保存を主張しない。

parity の対応表には、1 対 1、多対 1、対応なし、対象外の 4 種類の行を置く。
parity 検査は、ツール内の構成子リストと対応表の自己整合性だけを保証する。
ツールは `.fst` と `surface.rkt` のソースを読まない。

F* 側の構成子の増減は F* の網羅性検査で、Racket 側の構成子の増減は `fstar-parity-test.rkt` の回帰で、両者の対応は parity 検査で捕まえる。

### 8.1 Surface AST の対応

- `SInt`、`SStr`、`SUnit`、`SBool`、`SVar`、`SFn`、`SApply`、`SConstruct`、`SProj`、`SProjRec`、`SRec`、`SBlock` は、同名の F* 構成子と 1 対 1 で対応する。
- `SReturn` は、同名の F* 構成子と 1 対 1 で対応する。 [REQ: SUR-015]
- `TName`、`TRec`、`TFn`、`TApp` は、同名の F* 構成子と 1 対 1 で対応する。
- `SBind` と `SFnDecl` は、F* 側の `SDecl` へ多対 1 で対応する。
- `TUnion` と `TInter` は、同名の F* 構成子と 1 対 1 で対応する。
- `SEffRow` と `SEffLabel` は、同名の F* 構成子と 1 対 1 で対応する。
- `STypeDecl` と `SProgram` は、型別名の環境と宣言の並びへ消費されるため、対応する F* 構成子を持たない。
- `STraitDecl`、`SImplDecl`、`SDeriveDecl` は trait 環境、impl 行、derive 行へそれぞれ消費されるため、対応する F* 構成子を持たない。
- `SName`、`SParam`、`SField`、`SLabel`、`TField` は、親の構成子の欄へ展開するため、独立した F* 構成子を持たない。
  `SFn` の `SParam` は、F* 側では仮引数名の span と `option sty` の組として表す。
  `SFnDecl` の `SParam` は仮引数名の span と `sty` の組、`SName` は `SDecl` の束縛名の span、`SField` と `SLabel` は label の span と式または label 名の組として、F* の欄に残る。
  `SParam` と `SField` のそれ自体の span と `TField` は Core へ届かないので、F* には残らない。
  `TField` の末尾の `opt` も F* には残らない。
  F* の `TRec` は欄の label を持たないので、presence も持たない。
  `TApp` の頭の名前は、F* 側で頭の span と名前の組として欄に残る。
  Racket の `Construct` に付く `(Types)` の有無は、F* の `CConstruct` へ写すと保持されない。

Racket 側の Surface 構成子リストは 34 個、F* 側の `sexpr`、`sty`、`sdecl`、Effect row の構成子リストは 22 個（`sexpr` は 13 個、`sty` は 6 個）である。
P2h1 で加えた `STraitDecl` と `SImplDecl`、P2h2 で加えた `SDeriveDecl`、P2l2b1 で加えた `SDataDecl` は Racket 側だけにあり、parity 表で「対応なし」とする。
P2i2 は `SFn` の仮引数欄を拡張するが、新しい Surface 構成子を加えないため、構成子の一覧と件数は変わらない。
P2k1 は `SReturn` と F* の `CReturn` を加える。
F* の lexer の `keyword_word` は、Racket の `lexer.rkt` と同じ 13 語を予約する。
`tools/fstar-parity.rkt` の `fstar-keywords` は F* が予約する語を手で書いた一覧であり、`fstar-parity-test.rkt` がこれを `lexer.rkt` の `keywords` と照合する。
F* の補題 `keyword_word_reserved` と `fstar-keywords` の対応は手で保ち、CI はこの対応の食い違いを検出しない。

### 8.2 UCore+ の対応

UCore+ では `#:lit`、`#:var`、`Apply`、`Proj`、`Rec`、`Fn`、`Construct`、`Let`、`Recur`、`Return`、`FnDecl` の 11 構成子を parity の対象とする。
F* 側では `Return` に対応する `CReturn` を置き、ほかの構成子には `CRecur` などの対応を置く。
`FnDecl` と `Recur` から `CRecur` への行は多対 1 の対応であり、F* の lowering は関数宣言を `CLet` で包まず直接 `CRecur` へ写す。
UCore+ の対象構成子リストは 11 個、F* 側の `core` の構成子リストは 10 個であり、F* 側の全対象構成子は 32 個（`sexpr` 13 個、`sty` 6 個、`sdecl` 1 個、Effect row 2 個、`core` 10 個）である。

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

## 9. Typed Core への接続

`lex` から `elab` までを 1 つの入口へつなぐ。 [REQ: SUR-007]
入口は `model/redex/driver.rkt` の `compile-source` と `compile-source/string` である。

経路は 4 段である。
`lex` が byte 列を token 列へ、`parse` が token 列を Surface の構文木へ、`lower-surface` が構文木を UCore+ へ、`elab` が UCore+ を Typed Core へ移す。
span はこの 4 段のいずれでも落とさない。
`erase-core` は成果物を受けた側が必要に応じて掛ける。
経路の途中で span を落とすと、診断の primary span が指す位置を呼び手が復元できない。

成功の成果物は `(struct compiled (core type row callables ledger))` である。
先頭 4 欄は `elab` の返り値と同じ順で並び、`ledger` はその compilation で使った trait 台帳である。
成果物を実行するときは、`compiled-ledger` を `call-with-trait-ledger` へ渡して台帳を揃える。

失敗の返り値は Diagnostic 1 件である。
最初に落ちた段の診断をそのまま返し、phase を書き換えない。
lexer と parser と lowering の診断は `surface`、`elab` の診断は `elaborate` である。
`elab` が返す `` `(err ...) `` の包みは入口が剥がすため、呼び手は `diagnostic?` だけで成否を判別する。

`compile-source` は任意入力 `#:expansion-context` を取り、`elab` へそのまま渡す。
既定は空の hash である。
Surface の経路は展開表を生成しないため、入口は空の hash を作らずに受けた値を素通しする。

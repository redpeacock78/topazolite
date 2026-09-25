# Topazolite Surface 構文

**状態**：P2h1 版
**参照**：`draft/topazolite_whitepaper_draft_0.4.md` §15（以下、ホワイトペーパー）
**関連文書**：`docs/specification/core-calculus.md`、`docs/specification/structural-row.md`、`docs/specification/span.md`、`docs/specification/diagnostic.md`、`docs/specification/requirements.md`

## 1. 範囲

本書は Surface 構文の正典である。
lexer と parser は canonical source span を保持し、Surface 構文から未型付き縮小 Core への lowering はその span を引き継ぐ。 [REQ: SUR-001]

この版が扱う構文は、整数、文字列、真偽値のリテラル、変数、無名関数、関数宣言、関数適用、`const`、`let`、`let mut` の束縛、record リテラル、射影、`type` による型別名、`trait` と `impl` の宣言、および block である。

この版は、ジェネリクスと ADT（`ADT-001`）、パターン照合（`PAT-001`）、`?=`、pipe、interpolation（`SUR-002`）、Effect 注釈（`SUR-003`）、borrow 表記（`SUR-004`）、bit 演算子（`BIT-001`）、モジュール（`MOD-001`）を受理しない。
余剰 `Owned` field の明示 projection は `SUR-006` が担う。
戻り型の省略（`SUR-008`）も受理しない。

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
予約語は `const`、`let`、`mut`、`fn`、`type`、`true`、`false`、`trait`、`impl`、`for`、`derive` の 11 語である。
予約語は識別子の規則に合っていても、`ident` として扱わない。

整数リテラルは `[0-9]+` である。
符号は付かない。

文字列リテラルは `"` で囲む。
エスケープは `\"`、`\\`、`\n`、`\t` の 4 種だけを許す。

記号は `{`、`}`、`(`、`)`、`,`、`:`、`=`、`.`、`->`、`|`、`&` の 11 種である。
`->` は `-` と `>` の 2 byte からなる 1 個の `punct` token である。

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
traitdecl ::= "trait" ident tyrec NL+
impldecl ::= "impl" ident "for" ty record NL+
derivedecl ::= "derive" ident "for" ty NL+
fndecl   ::= "fn" ident "(" params ")" "->" ty block NL+
expr     ::= postfix
postfix  ::= primary suffix*
suffix   ::= "(" args ")" | "." ident | "." "{" labels "}"
labels   ::= NL* ident (sep ident)* sep? NL*
sep      ::= ("," | NL) NL*
primary  ::= int | string | "true" | "false" | "(" ")"
           | ident | anonfn | record | block | "(" expr ")"
anonfn   ::= "fn" "(" params ")" "->" ty block
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
ty       ::= tyand ("|" tyand)*                         [REQ: BIT-003]
tyand    ::= tyatom ("&" tyatom)*
tyatom   ::= ident | tyrec | "fn" "(" tys ")" "->" ty | "(" ty ")"
tyrec    ::= "{" NL* "}"
           | "{" NL* tyfield (fsep tyfield)* fsep? NL* "}"
tyfield  ::= ident ":" ty
tys      ::= ε | ty ("," ty)*
```

`&` は `|` より強く結合し、どちらも左結合である。
型の括弧は結合順を変えるために使い、括弧自体は AST の節点を作らない。
型の位置の `()` は `E-SUR-005` で拒否する。

トップレベルにも束縛を置ける。
トップレベルの束縛は block の中の束縛と同じ規則で扱う。

関数の戻り型は `->` で区切り、省略できない。 [REQ: SUR-011]
戻り型の推論は `SUR-008` が担うため、この版では行わない。

program の末尾は式でなければならない。
空の入力と、宣言だけで式の無い入力は、どちらも `E-SUR-006` で拒否する。
縮小 Core の項は式であり、式を持たない program には落とし先が無いためである。

型別名は全宣言から作った環境で解決する。
trait 宣言はすべて impl 宣言より先に環境へ登録するため、impl は対応する trait より前に書ける。

### 3.1 受理しない構文

字句に無い記号は lexer が `E-SUR-002` を返す。
単独の `-` と `>`、`+`、`*`、`/`、`%`、`<`、`?`、`!`、`[`、`]`、`;` は字句にならない。
`List<Int>`、算術演算子を含む式、`?=`、pipe は、最初の未対応記号の位置で `E-SUR-002` になる。
`|` と `&` は型位置だけで受理する。
式の位置の `x | y` と `x & y` は `E-SUR-005` になる。
`x |> f` は `|` の次に字句にならない `>` が現れるため、`>` の位置で `E-SUR-002` になる。

字句にはなるが構文に無い `if`、`while`、`return`、`match` は予約語ではなく `ident` になる。
`if cond { }` のように後ろへ式が続く形は、2 つ目の primary の位置で `E-SUR-005` になる。
単独の `return` は変数式として受理し、未束縛変数の診断は後段に委ねる。
予約語 `for` は式の先頭には置けず、その位置で `E-SUR-005` になる。

P2h1 では `trait`、`impl`、`for` を予約語へ加え、P2h2 では `derive` を加えた。

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

## 5. 型別名

型別名は Surface だけの糖衣である。
UCore+ には型別名を置く欄が無いため、`STypeDecl` は節点を生成せず、lowering の別名環境へ消費する。
型別名は `TypeNarrative` による `TypeInfo` 生成を経ず、静的な型 `τ` へ直接展開する。
型宣言と型位置の演算子から `TypeNarrative` を使って `TypeInfo` を生成する経路は、requirements.md §4 の申し送り表に記録する。

別名環境は 2 度の走査で作る。
1 度目は program の `spitem` を原文順に読み、型別名の名前と未展開の `sty` を登録する。
2 度目は各 `sty` の中の `TName` を環境の定義へ置き換え、展開結果に現れる `TName` も同じ規則で解決する。

1 度目の走査で名前をすべて登録してから 2 度目の走査を行うため、宣言より前の位置から後の宣言を参照できる。
宣言順に 1 度で読む方式は採らない。

展開関数は展開後の型だけを返す。
使用位置の span は呼び出し側が入力の `sty` から `(span-of ty)` で取るため、展開後の型と span を 2 値で返す必要はない。

### 5.1 拒否する型別名

型別名と trait 名は一つの名前空間を共有する。
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
型別名でも基本型でも trait 名でもない名前は `E-SUR-008` とする。
record と record 型の field は左から右へ走査し、最初に見つかった 2 度目の label で `E-SUR-007` を返す。
3 件以上の重複があっても、最初の 1 件だけを返す。

## 6. UCore+ への lowering

lowering の入口は `(lower-surface sprog trait-env)` である。
返り値は Diagnostic 1 件か `(struct lowered (term trait-rows impl-rows spans))` のいずれかである。
`term` は UCore+ の項、`trait-rows` と `impl-rows` は宣言から作った行、`spans` は宣言由来の鍵から原文 span への対応表である。
呼び側はこの行を `trait-env` へ重ねて台帳を作る。
引数が Diagnostic のときは、それをそのまま返す。
この節は parser が diagnostic を返した経路を呼び側の分岐漏れで失わないために置く。

別名環境を §5 の規則で先に構築・検査し、`sty` を `uτ` へ落とす際に使う。
続いて全 trait 宣言を原文順に読み、既存または原文中の同名 trait を `E-SUR-013` とする。
生成した origin id や primitive 名が基底環境または kernel の `R0`・`Γ0` の鍵と衝突すれば `E-SUR-016` とする。
その行を基底の環境へ重ねた後、impl と derive の宣言を同じ前処理で原文順に 1 件ずつ検査する。
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
- `(SBool s true)` と `(SBool s false)` は、それぞれ `(Construct s true)` と `(Construct s false)` へ落とす。
- `(SVar s x)` は `(#:var x s)` へ落とす。
- `(SApply s f (a ...))` は `(Apply s f' a' ...)` へ落とす。
- `(SProj s e (SLabel s_l l))` は `(Proj s e' (#:lbl l s_l))` へ落とす。
- `(SProjRec s e ((SLabel s_l l) ...))` は、受け側を 1 度だけ束縛する `Let` と、label ごとの `Proj` を並べた `Rec` へ落とす。 [REQ: SUR-006]
- `(SRec s ((SField s_f (SLabel s_l l) e) ...))` は `(Rec s (((#:lbl l s_l) imm e') ...))` へ落とす。
- `(SFn s ((SParam s_p (SName s_x x) ty) ...) ty_r body)` は、span を持つ binder、型注釈、空の effect row を持つ `(Fn ...)` へ落とす。
- `(SBlock s (bind ...) e)` は、束縛を右から畳んだ `Let` の入れ子へ落とす。
- `(SBind s bmode (SName s_x x) ty e)` は、注釈があれば型注釈付き `Let` へ、無ければ mode-only `Let` へ落とす。
- `(SFnDecl s (SName s_f f) ... )` は、関数本体と後続の項を持つ `Recur` へ落とす。
- `(STypeDecl s (SName s_n T) ty)` は別名環境へ入れるだけで、節点を生成しない。
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
F* 側の `SProjRec` は label の綴りを保持せず、`proj_fields` は欄の個数だけを写す。
受け側の綴り `%projrec` は、`lexer.rkt` の `ident-start?` が `%` を受理しないため入力の識別子と衝突しない。

`TName` のうち `Int`、`Bool`、`Unit`、`String` は同綴りの `uτ` へ写す。
それ以外は §5 の別名環境から解決し、未登録なら `E-SUR-008` とする。
`TRec` は field mode を `imm` とする `(Record ((l uτ imm) ...))` へ写す。
`TFn` は effect row と obligation を空にした `(NFn (uτ ...) uτ_r () ())` へ写す。
Surface に field の可変性と effect 注釈が無いためである。
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

`SProgram`、`SBlock`、`STypeDecl`、`STraitDecl`、`SParam`、`SField`、`TField` は、対応する UCore+ の節点または欄が無いため、その構成子自身の span を渡さない。
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
命題 4 は尾部 span を持つ `SBlock`、`SBind`、`SFnDecl` と、1 つの節点を複数の節点へ増やす `SProjRec`、節点を生成しない `STypeDecl`、`SProgram`、型構成子を量化対象から外す。
`SProjRec` の lowering の根の span は入力の span を保存するが、複数の節点へ展開するため命題 4 の対象外である。

parity の対応表には、1 対 1、多対 1、対応なし、対象外の 4 種類の行を置く。
parity 検査は、ツール内の構成子リストと対応表の自己整合性だけを保証する。
ツールは `.fst` と `surface.rkt` のソースを読まない。

F* 側の構成子の増減は F* の網羅性検査で、Racket 側の構成子の増減は `fstar-parity-test.rkt` の回帰で、両者の対応は parity 検査で捕まえる。

### 8.1 Surface AST の対応

- `SInt`、`SStr`、`SUnit`、`SBool`、`SVar`、`SFn`、`SApply`、`SProj`、`SProjRec`、`SRec`、`SBlock` は、同名の F* 構成子と 1 対 1 で対応する。
- `TName`、`TRec`、`TFn` は、同名の F* 構成子と 1 対 1 で対応する。
- `SBind` と `SFnDecl` は、F* 側の `SDecl` へ多対 1 で対応する。
- `TUnion` と `TInter` は、同名の F* 構成子と 1 対 1 で対応する。
- `STypeDecl` と `SProgram` は、型別名の環境と宣言の並びへ消費されるため、対応する F* 構成子を持たない。
- `STraitDecl`、`SImplDecl`、`SDeriveDecl` は trait 環境、impl 行、derive 行へそれぞれ消費されるため、対応する F* 構成子を持たない。
- `SName`、`SParam`、`SField`、`SLabel`、`TField` は、親の構成子の欄へ展開するため、独立した F* 構成子を持たない。

Racket 側の Surface 構成子リストは 28 個、F* 側の `sexpr`、`sty`、`sdecl` の構成子リストは 17 個（`sty` は 5 個）である。
P2h1 で加えた `STraitDecl` と `SImplDecl`、P2h2 で加えた `SDeriveDecl` は Racket 側だけにあり、parity 表で「対応なし」とする。

### 8.2 UCore+ の対応

UCore+ では `#:lit`、`#:var`、`Apply`、`Proj`、`Rec`、`Fn`、`Construct`、`Let`、`Recur` の 9 構成子だけを parity の対象とする。
F* 側では、これらに対応する `CLit`、`CVar`、`CApply`、`CProj`、`CRec`、`CFn`、`CConstruct`、`CLet`、`CRecur` を置く。
`CRecur` は parity の対象を揃えるための構成子であり、この版の lowering は生成しない。
UCore+ の対象構成子リストは 9 個、F* 側の `core` の構成子リストも 9 個であり、F* 側の全対象構成子は 26 個（`sexpr` 11 個、`sty` 5 個、`sdecl` 1 個、`core` 9 個）である。

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

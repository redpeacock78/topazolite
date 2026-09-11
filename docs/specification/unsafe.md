# raw pointer と unsafe boundary

本文書は raw pointer の型、pointer 操作、Proof obligation、unsafe boundary を定める。
借用の型と permission は `docs/specification/borrow.md` が定め、region IR と Core API は `docs/specification/region.md` が定める。
raw pointer は safe borrow とは別の構成子であり、借用の台帳へ暗黙に登録しない。

## 1 raw pointer の型

### 1.1 文法

[REQ: PTR-001]

`RawPtr` は、ポインタの形状を次の 6 つの型成分で表す。

```text
(RawPtr τ ptrmut nul align as prov)
```

`ptrmut` は可変性、`nul` は nullability、`align` は alignment、`as` は address space、`prov` は provenance を表す。

各成分の文法は次のとおりである。

```text
(ptrmut ::= Const Mut)
(nul    ::= NonNull Nullable)
(align  ::= (Align natural))
(as     ::= (AddrSpace id))
(prov   ::= (Prov id))
```

`ptrmut` と `nul` は二つの literal を直接列挙する。
`as` と `prov` は識別子を受けるが、受理する識別子は validator の許可集合で閉じる。
address space の許可集合は `native`、`wasm-linear`、`js-buffer`、`ffi` である。
provenance の許可集合は `foreign`、`owned`、`unknown` である。

文法上の `align` は自然数を受けるが、受理する alignment は 1 以上に限る。
`(Align 0)` は alignment として意味を持たないため、`align-ok?` が拒否する。
alignment を 2 の冪に限る制約は本サイクルへ入れない。
`Aligned` の Proof が実際の alignment を担うためである。

非終端名を `mut` ではなく `ptrmut` とする。
既存の `m` は record row の可変性を表す `(m ::= imm mut)` を持つ。
Redex は非終端名と同じ綴りの記号を非終端参照として解決するため、pointer の非終端を `mut` と名付けると既存の literal `mut` が照合できなくなる。
record の可変性と pointer の可変性は別の概念なので、pointer 側を `ptrmut` として分離する。

`nul` の `NonNull` と Proof obligation の `NonNull` は同じ綴りを使う。
前者は型の成分であり、後者は命題の識別子であるため、現れる位置が異なる。

### 1.2 address space の暗黙 cast を認めない

address space は `RawPtr` の型成分である。
したがって、次の二つの型は型同値ではない。

```text
(RawPtr τ ptrmut nul align (AddrSpace native) prov)
(RawPtr τ ptrmut nul align (AddrSpace js-buffer) prov)
```

異なる address space 間の暗黙の cast は型検査で拒否する。
明示的な cast の演算は本サイクルでは導入しない。

### 1.3 safe borrow と同一視しない

`RawPtr` は `Borrowed` と `BorrowedMut` とは別の構成子であり、region 引数 `ρ` を持たない。
借用検査が追跡する capability は place、field path、region で表される。
`RawPtr` はその capability ではないため、safe borrow の台帳と同一視しない。

### 1.4 `Owned` の直下に置かない

`Owned` の直下に `RawPtr` を置く型は拒否する。

```text
(Owned (RawPtr τ ptrmut nul align as prov))
```

`Owned` の境界を越えた値は heap 値の再検査で所有の木へ組み直される。
`PtrVal` は place と field path を持つが所有の木の節点ではないため、`Owned` の直下を許すと再検査へ pointer 専用の節を追加しなければならない。

一方、`Owned` を経由しない record の欄へ置くことは許す。

```text
(Record ((ptr (RawPtr τ ptrmut nul align as prov) imm)))
```

禁じるのは直接の `Owned` だけであり、所有値を含む構造の借用まで再帰的に禁じるものではない。

## 2 pointer 操作と Unsafe Effect

### 2.1 Effect label

Effect label に `Unsafe` を加える。

```text
(ℓ ::= .... Unsafe)
```

`Unsafe` は `Perform` される operation ではなく、`Own`、`Partial`、`Compile` と同じ静的な marker である。

ホワイトペーパーの署名には `Foreign` も現れるが、本サイクルでは追加しない。
`Foreign` の意味、および backend へ課す契約は未確定であり、別の申し送りとして扱う。

### 2.2 操作の型付け

Core へ次の操作を加える。

```text
(c ::= .... (AddressOf c) (PtrOffset c c) (RawLoad c)
          (RawStore c c) (Unsafe c))
```

型付けの署名は次のとおりである。

```text
AddressOf : (BorrowedMut τ ρ) ->
            (RawPtr τ Mut NonNull (Align 1) (AddrSpace native) (Prov owned)) ! ()
PtrOffset : (RawPtr τ ptrmut nul align as prov) × Int ->
            (RawPtr τ ptrmut Nullable align as prov) ! (Unsafe)
RawLoad   : (RawPtr τ ptrmut nul align as prov) -> τ ! (Unsafe)
RawStore  : (RawPtr τ Mut nul align as prov) × τ -> Unit ! (Unsafe Mutation)
```

raw 操作のうち `H` を書き換えるのは `RawStore` だけである。
`FromRawPtr` の二つの署名は §3.3 に示す。
`AddressOf` は `Unsafe` Effect を付けない。
addressOf は借用から pointer を作るだけであり、ホワイトペーパーの署名もこの操作の Effect を空にしている。

`AddressOf` の返り値の 5 つの成分は固定する。
可変借用から作る pointer は `Mut`、`NonNull`、`(Align 1)`、`(AddrSpace native)`、`(Prov owned)` になる。
生成源が `H` の place であるため、外部 provenance や別の address space をここから作らせない。
より強い alignment は型ではなく `Aligned` の Proof で述べる。

`PtrOffset` は返り値の nullability を `Nullable` へ落とす。
offset の結果が非 null である保証は無く、`NonNull` を保つには Proof が要る。

`RawStore` は第一引数が `Mut` の pointer である場合だけ型付けする。
`Const` の pointer へ書き込む操作は型検査で拒否する。

### 2.3 実行時の値と簡約

実行時の pointer 値は、place、field path、可変性、provenance を持つ。

```text
(v ::= .... (PtrVal p fp ptrmut prov))
```

`BorrowRef p fp ρ` と同じく、`p` と `fp` が指す場所を表す。
`RawPtr` が region の代わりに provenance を持つのに対応して、`PtrVal` も `prov` を持つ。
さらに `ptrmut` を値へ持たせ、機械規則で `Const` と `Mut` を区別する。

機械規則は型検査済みの config だけでなく、手組みの config にも適用できる。
性質 9 の生成器も config を直接組むため、実行時の値に可変性を残して `RawStore` の側で閉じる。

pointer 操作の簡約規則は次の 6 本である。

- `R-AddressOf` は可変借用から `Mut` の `PtrVal` を作る。
- `R-PtrOffset` は field path の末尾の自然数 segment を動かし、入力の `ptrmut` を保つ。
- `R-RawLoad` は `Const` と `Mut` の両方で発火し、`H` の該当欄を読む。
- `R-RawStore` は `Mut` の場合だけ発火し、`H` の該当欄を書き換える。
- `R-FromRawPtrConst` は `BorrowRef` を作る。
- `R-FromRawPtrMut` は `BorrowMutRef` を作る。

`R-UnsafeExit` は pointer 操作ではなく boundary の規則として §4.2 で定める。

`Ω` の place が `Available` であることを要求する規則は、`R-RawLoad`、`R-RawStore`、`R-FromRawPtrConst`、`R-FromRawPtrMut` の 4 本に限る。
`R-AddressOf` と `R-PtrOffset` は `Ω` を読まない。
`PtrVal` は capability ではなく、`Ω` を確認する必要があるのは pointer を使用する規則だからである。
性質 9 の oracle も使用側の規則を条件としているため、この非対称は意図したものである。

`RawLoad` と `RawStore` は指す先が存在しない場合に発火しない。
`RawStore` が書ける先は `Rec` の欄に限る。
`value-set-path` が `Rec` の欄だけを差し替える一方、`heap-walk-path` は `Construct` の欄も読めるためである。

`Available` でない place や存在しない field path に対する raw 操作も発火しない。
この失敗を `Error(p)` へ変換しないのは、`Error(p)` が OwnershipError を表し、raw pointer の実行時 Proof 失敗とは別の終端だからである。
`Unsafe` の内側で未解決の Proof を許す結果、このような構成は stuck として残る。

`PtrOffset` が動かすのは field path の末尾の自然数 segment であり、これは `Construct` の欄の index に対応する。
`Construct` の欄へ `RawStore` を実行する経路が無いため、`PtrOffset` の後へ `RawStore` を置いても発火しない。
性質 9 の生成域が `PtrOffset` を `RawLoad` とだけ組み合わせるのは、この非対称と整合する。
`Construct` の欄への `RawStore` を追加するときは、書き換えの型検査と生成域を同時に広げる必要がある。

## 3 Proof obligation

### 3.1 命題

Proof obligation は次の形で表す。

```text
(ptr-prop-id ::= id NonNull)
(φ ::= .... (PtrProp ptr-prop-id τ))
```

`NonNull` は `nul` の literal と同じ綴りであるため、`PtrProp` の識別子を単なる `id` にしない。
`ptr-prop-id` へ `NonNull` を明示的に加え、文法と許可集合の両方でこの綴りを受理する。

許可する識別子は次の 10 個である。

- `NonNull`
- `Aligned`
- `InBounds`
- `Initialized`
- `AliveAllocation`
- `Readable`
- `Writable`
- `AbiMatched`
- `LifetimeValid`
- `OwnershipTransferred`

Proof search は `(PtrProp ptr-prop-id τ)` に対して 1 本の分岐を持ち、識別子を許可集合と比較する。
命題ごとに規則を 10 本作ると、命題の追加が search の規則数へそのまま波及するためである。

`PtrProp` は validator の表に無い構成子であり、`Γ-pc0` から暗黙に充足したことにはしない。
許可集合に無い識別子は命題の形で拒否し、許可された命題は proof search の結果を要求する。

### 3.2 各操作が要求する obligation

各操作は次の `Q` を要求する。

- `RawLoad`：`AliveAllocation`、`NonNull`、`Aligned`、`Initialized`、`Readable`、`InBounds`
- `RawStore`：`AliveAllocation`、`NonNull`、`Aligned`、`Writable`、`InBounds`
- `PtrOffset`：`AliveAllocation`、`InBounds`

`RawStore` が `Initialized` を要求しないのは、未初期化の領域を store によって初期化できるためである。
`RawLoad` が `Writable` を要求しないのは、読み出しに書き込み権限が要らないためである。

### 3.3 raw pointer から safe reference を構築する

[REQ: PTR-002]

raw pointer から safe reference を作る `FromRawPtr` は、lifetime、alignment、validity の Proof を要求する。

```text
(c ::= .... (FromRawPtr c ρ))
```

```text
FromRawPtr : (RawPtr τ Const nul align (AddrSpace native) (Prov owned)) × ρ
           -> (Borrowed τ ρ) ! (Unsafe)
FromRawPtr : (RawPtr τ Mut nul align (AddrSpace native) (Prov owned)) × ρ
           -> (BorrowedMut τ ρ) ! (Unsafe)
```

`Const` は `Borrowed` を、`Mut` は `BorrowedMut` を返す。
入力の `nul` は場合分けしない。
`Nullable` の pointer からも構築を試みてよく、非 null であることは `NonNull` の Proof が述べる。
型で `NonNull` に限ると、`PtrOffset` を通った pointer を Proof によって safe reference へ戻せなくなるためである。

両方の署名は `Q` に `LifetimeValid`、`Aligned`、`Initialized`、`AliveAllocation`、`NonNull` を要求する。
`LifetimeValid` は lifetime に、`Aligned` は alignment に、残りの 3 つは validity に対応する。

入力の provenance は `(Prov owned)` に、address space は `(AddrSpace native)` に限る。
`foreign` と `unknown` の provenance は `H` の place を指すとは限らず、借用検査が追跡する対象を持たない。
native 以外の address space も、現在の借用台帳が扱う対象へ結び付ける経路を持たない。
この二つの経路は未回収として別に記録する。

`ρ` は任意の値ではなく、elaboration の時点で束縛されている region に限る。
`(RParam rp)` を書くときは、その `rp` を束縛する `RegionLam` の内側にいなければならない。
この検査は既存の region の well-formedness と同じ層で行い、`FromRawPtr` 固有の規則を足さない。

所有者との整合は Proof ではなく借用検査が担う。
実行時には `R-FromRawPtrConst` が `(BorrowRef p fp ρ)` を、`R-FromRawPtrMut` が `(BorrowMutRef p fp ρ)` を作る。
place と field path をそのまま引き継ぐため、生成された借用は `borrow.md` の借用台帳へ通常の借用と同じ形で載る。

## 4 unsafe boundary

### 4.1 型付け

`Unsafe` を別の Core 構成子として置く。
複数の obligation と `Unsafe` Effect を別々の呼び出し側が局所的に許可すると、境界の外へ未解決の obligation や Effect が漏れるためである。

`c` の型が `τ`、Effect row が `ε` であるとき、`(Unsafe c)` の型は `τ`、Effect row は `ε` から `Unsafe` だけを除いたものになる。

```text
(Unsafe c) : τ ! (ε \ Unsafe)
```

本体の検査中に未解決の `PtrProp` が残ったときは、`Unsafe` の内側だけ許可する。
この許可は `unsafe-permitted` parameter で表し、`(Unsafe c)` の本体をその parameter が有効な環境で検査する。
`ownleaf-permitted` が `Owned` の検査に同じ形を使うため、境界を parameterize で表す。
境界の外へ `unsafe-permitted` を持ち出さないので、外側の項へ未解決の Proof は残らない。

### 4.2 評価文脈と簡約

`Unsafe` は静的 marker だが、機械がその内側の `Perform` と owned な `Let` を評価できる必要がある。
そのため `G2m` の 3 つの評価文脈へ枠を加える。

```text
(F ::= .... (Unsafe F))
(E ::= .... (Unsafe E))
(G ::= .... (Unsafe G))
```

`E` だけへ枠を加えると、`Unsafe` の内側にある `Perform` が評価文脈の外へ出られず停止する。
`F` を使うのは `R-ScopePerform` と handler 群（`R-HandleValue`、`R-HandleReturn`、`R-HandleSkip`、`R-HandleError`）である。
`G` を使うのは `Scope` の直下にある owned な `Let` を拾う `R-LetOwned` である。

handler 群と `R-ScopePerform` は `F_inner` を右辺へ持たないため、そこで `Unsafe` の枠は捨てられる。
これは通常の `Let` が評価文脈を右辺へ持たないことと同じ扱いである。
一方、`R-LetOwned` は `G_inner` を右辺へ持つため、owned な束縛の簡約後も `Unsafe` の枠が保たれる。

既存の G2m の評価文脈も `F`、`E`、`G` の 3 つへ同じ形を加える構成であり、`Unsafe` もこの配置に揃える。

境界が値まで評価されたときは、次の規則で枠を外す。

```text
E[Unsafe(v)] -> E[v]
```

この規則を `R-UnsafeExit` と呼ぶ。
`R-UnsafeExit` は追加の側条件を持たない。
値へ落ちた後に raw pointer が外へ出ないことは、次節の型検査と bounded oracle が検査する。

raw 操作の `Available` や field path の側条件が満たされない場合、`Unsafe` はその失敗を OwnershipError へ変換しない。
この動的な Proof 失敗は stuck として扱い、progress の判定では通常の値や OwnershipError とは別に扱う。

### 4.3 外部漏出

unsafe boundary の外へ raw pointer を返さない。
型検査では `leaks-rawptr? : τ -> boolean` を使い、次の 3 群を fail-closed に列挙する。

- 漏出なしの基底型：`Int`、`Bool`、`Unit`、`String`、`Never`、`Res`、`(TypeInfo κ)`、`(Proof φ)`。
- 漏出ありの基底型：`(RawPtr τ ptrmut nul align as prov)`。
- 内側を走査する構成子：`List`、`Option`、`Result`、`Owned`、`Borrowed`、`BorrowedMut`、`Untrusted`、`Refined`、`Union`、`Intersection`、`ForallRegion`、`Record`、`NFn`。

内側を走査する構成子では、`Record` の各 field 型、`NFn` の引数型と返り値型、`NFn` の Effect row のうち `(Return b τ)` と `(Yield τ)` が運ぶ型を調べる。
`NFn` の `φ` と `Q` へは降りない。
これらは命題の対象であり、pointer 値そのものを運ばないためである。
`Proof` の値も `ProofRep` であり、pointer を含まない。

列挙にない型構成子は漏出ありとして扱う。
G2m の型文法には再帰型構成子が無いため、走査は停止する。
この fail-closed の形により、型構成子を追加したときに判定だけが黙って通ることを防ぐ。

本体の型だけでなく、本体の Effect row にも `effect-leaks-rawptr? : ε -> boolean` による同じ走査を適用する。
`Yield` は観測値の型を `(Yield τ)` として row へ運ぶため、本体の型が `Unit` でも row に `RawPtr` が残りうる。
その項を評価すると `R-Yield` が観測値を event trace へ記録し、`R-UnsafeExit` とは別の口から `PtrVal` が境界の外へ出る。

型検査と oracle は同じ外部漏出を二重に検査する。
型検査は静的な型と Effect row を調べ、oracle は `R-UnsafeExit` の結果値と `R-Yield` の観測値を調べる。
両者が食い違う場合は、型付けと簡約のどちらかに欠陥がある。

`AddressOf` と `PtrOffset` の結果型を型検査の返り値から観測する経路は無い。
raw pointer を boundary の外へ出せない設計だからであり、これらの成分は pointer の型付けと `FromRawPtr` の回帰で検査する。

### 4.4 型走査の fail-closed 規約

`owned-free?` も型構造を走査する判定である。
`owned-free?` と `leaks-rawptr?` は、どちらも match の最後へ catch-all を置き、未知の型構成子を安全側へ倒す。
`owned-free?` は `[_ #f]`、`leaks-rawptr?` は `[_ #t]` を返す。
節を足し忘れても例外にはならず、安全側の値が黙って返るため、追加漏れは受理の欠落として現れる。

`ForallRegion` は明示的に本体を走査する。
`Borrowed` 系のように `#t` を返して打ち切ると、束縛の内側に隠した `Owned` を見落とす。
実際、fail-open だった時期に `ForallRegion` が列挙に無く、`(Untrusted (ForallRegion (rp) (Owned Res)))` が両方の検査を通っていた。

`Borrowed`、`BorrowedMut`、`RawPtr` は明示の節で `#t` を返し、payload へ降りない。
所有値を含む構造の借用は意図された用法であり、借用の payload を再帰的に `owned-free?` へ渡すと既存の受理を失うためである。

型構成子を追加する実装者は、`owned-free?` に対応する節を追加する。
この規約は fail-open による affine 制約の隠蔽を防ぎ、追加漏れを安全側の失敗として検出できる形を保つ。

## 5. 性質 9 の bounded 検査

### 5.1 性質の主張

性質 9（unsafe containment）は次を主張する。
型検査を通った項の到達可能なすべての実行について、raw 操作は `Unsafe` の内側でだけ発火し、その操作が要求する `PtrProp` の集合は静的側が求めた obligation と一致し、`Unsafe` の境界を越えて `PtrVal` が外へ出ない。

「越えて外へ出ない」の意味は 2 つの経路で定める。
1 つは `R-UnsafeExit` が返す値であり、もう 1 つは `Unsafe` の内側の `Yield` が event trace へ足す観測値である。
前者は静的側の `leaks-rawptr?`（§3.4）と対応し、後者は静的側に対応物を持たない。
`Yield` の観測値は型ではなく trace へ流れるため、型検査だけでは閉じない。

### 5.2 静的側の記録

`model/redex/ptr-static.rkt` の `ptr-sidecar` は、型検査が受理した項について raw 操作の出現ごとに 1 件の `ptr-request` を持つ。
各件は操作の種類、節点の位置、obligation の集合、囲む `Unsafe` の有無を記録する。

記録する操作は `RawLoad`、`RawStore`、`PtrOffset`、`FromRawPtr` の 4 つである。
いずれも §3.2 と §3.3 の obligation を `check-raw-obligations!` で要求し、Effect 行へ `Unsafe` を足す。
`AddressOf` は §2.2 のとおりどちらも行わないため、記録しない。

囲む `Unsafe` の有無は `unsafe-permitted` パラメタから読む。
`infer-unsafe` が本体を `(parameterize ([unsafe-permitted #t]) ...)` の内側で走らせるため、深さを別に数える必要はない。

この欄は型検査の言い換えではない。
`check-raw-obligations!` は、obligation が `Γ-pc0` で解けるとき境界の外の raw 操作も通す。
したがって受理された項に `unsafe?` が偽の出現が現れうる。
検査は、生成域の範囲でそのような出現が実際には現れないことを確かめる。

### 5.3 oracle の 5 条件

`model/redex/unsafe-oracle.rkt` は、`raw-steps-g2/named` が返す規則名と遷移の前後の config だけを見て次の 5 つを判定する。
`typing.rkt` の判定関数を呼ばない。
静的側の言い換えに退化させないための分業である。

- 発火した規則が `R-RawLoad`、`R-RawStore`、`R-PtrOffset`、`R-FromRawPtrConst`、`R-FromRawPtrMut` のいずれかであるとき、簡約前の config の評価文脈に `Unsafe` の枠が少なくとも 1 つある。
- 同じ遷移について、その操作が §3.2 と §3.3 で要求する `PtrProp` の集合が、静的側が求めた obligation の集合と一致する。
- 発火した規則が `R-UnsafeExit` であるとき、簡約後の制御項が `PtrVal` を leaf に持たない。
- 発火した規則が `R-Yield` であり、簡約前の config の評価文脈に `Unsafe` の枠があるとき、event trace へ足す観測値が `PtrVal` を leaf に持たない。
- どの規則も発火せず、かつ制御項が終端の形でもないとき、その config の redex が `RawLoad`、`RawStore`、`PtrOffset`、`FromRawPtr` のいずれかであって `Unsafe` の内側にある。

1 番目と 5 番目は評価文脈の一意分解を使う。
`(in-hole E_1 (Unsafe (in-hole E_2 (RawLoad any))))` に照合できることは、次の redex が `Unsafe` の内側の `RawLoad` であることと同値である。
制御の経路を別に辿る必要はない。

2 番目は操作の種類で照合する。
実行時の redex は `(RawLoad (PtrVal ...))` の形であり、静的側が記録した `(RawLoad x)` とは決して等しくならない。
出現ごとに対応づけるには G5c6b の provenance 機構が要る。
obligation の集合は操作の種類ごとに定数であるため、種類で引くことで足りる。
oracle は §3.2 と §3.3 の表を `typing.rkt` から import せず独立に転記する。
import すると条件が恒真になる。

5 番目の条件が終端の構成を除くのは、値や `Error(p)` や `Perform` に達した config も「どの規則も発火しない」に該当するためである。
除かないと正常な停止がすべて反例になる。

### 5.4 生成域

生成器 `model/redex/unsafe-gen.rkt` は G2 core を直に作る。
elaboration も surface 構文も通さない。

- `AddressOf` で得た pointer に対する `RawLoad` と `RawStore`。
- `PtrOffset` を挟んだ `RawLoad`。
- `Unsafe` の内側と外側の両方に raw 操作を置いた項。
- `Unsafe` が `PtrVal` を返す項と、返さない項。`FromRawPtr` で借用へ戻した項。
- `Unsafe` の内側に `Yield` を置き、pointer でない値を観測する項。

`Unsafe` の外側に raw 操作を置いた項は型検査で落ちる。
性質 9 は型付けを前件に置くため、落ちた項は検査対象から外す。
外した項が実際に生成されていることは、生成器の単体テストで別に確かめる。
確かめないと、生成器が境界の外の形を 1 つも作らないまま 1 番目の条件が空回りする。

### 5.5 発火しない規則

生成域は `PtrOffset` を含み、bounded 検査はその発火回数を数える。
可変借用の `Eliminate` が fp の末尾へ自然数の segment を積み、その束縛子へ `AddressOf` を適用すると、`R-PtrOffset` が要求する `PtrVal` が作れるためである。

`R-FromRawPtrConst` は発火しない。
`AddressOf` が作る `PtrVal` は `Mut` であり、`R-PtrOffset` は `ptrmut` をそのまま保つため、`Const` の `PtrVal` を作る経路が無い。
この規則は、手で組んだ `PtrVal` を初期構成に置く単体テストでだけ動く。

2 章の末尾は、`Construct` の欄へ `RawStore` を実行する経路が無いため、`PtrOffset` の後へ `RawStore` を置いても発火しないと述べた。
その事実は変わらない。
`R-PtrOffset` が発火するようになっても、その結果の pointer へ書き込む経路は別に要る。

回収の条件は 6 章に置く。

### 5.6 探索の上限

探索の attempts、項の深さ、fuel、discard の上限は `model/redex/README.md` が定める値を正とする。
性質 8 の探索と同じ設定を使う。
反例が見つからないことは証明ではなく、設定した範囲での反例未発見を意味する。

## 6. 未回収

本章は G5c7 が扱わず後段へ送る事項を挙げる。
`requirements.md` の申し送り表がこの章を参照する。

### 6.1 backend profile

raw 操作がどの backend でどう降りるかは Phase 2 以降で定める。
Redex model は `H` の上の path lookup として扱い、機械語の load と store へは対応づけない。

### 6.2 address space

`AddrSpace` は `native` の 1 値だけを認める（§3.1）。
複数の address space をまたぐ pointer の変換と比較は Phase 1 以降で定める。

### 6.3 外部の allocation

`Prov` は `owned` の 1 値だけを認める（§3.1）。
`H` の外の allocation を指す pointer と、そこからの safe な reference の構築は Phase 3 以降で定める。
PTR-002 の `FromRawPtr` は `H` の中の place を指す pointer だけを対象とする縮約である。

### 6.4 pointee の生存

pointee が `H` の外にある場合の生存の判定は本章の外にある。
§4.3 の実行時側条件は `Ω` の `Available` と path の存在で閉じており、外部の allocation には届かない。

### 6.5 Effect label

`Foreign` の Effect label は `core-calculus.md` §3.2 の row に無い。
FFI の境界設計が未着手であり、label だけ先に置いても検査の対象が無い。
境界の設計と同時に定める。

### 6.6 構文の欄

`Construct` の field へ `RawStore` を置く形と、`Const` の raw pointer を作る式は G5c7 の構文に無い。
どちらも Phase 1 以降で定める。

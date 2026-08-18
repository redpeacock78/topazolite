# Topazolite Region IR 仕様

## 1. 位置づけ

本文書は、lexical region 解析と将来の NLL region solver が共通に使う IR と問い合わせ界面を定める。
BOR-003 の置換可能性は、本文書の region IR、core API、well-formedness によって判定する。
borrow の許可条件、borrow の型、Ω の状態拡張、raw pointer、Proof は本文書の対象外である。

## 2. Region IR の成分

region IR は次の 3 成分を持つ。

- `regions`：region の集合。
- `outlives`：`(ρ_long, ρ_short)` の対の集合。
  対は、`ρ_long` の寿命が `ρ_short` の寿命を含むことを表す。
  推移閉包ではなく、直接の制約だけを置く。
- `owners`：region から、その region が管理する place 列 π への有限写像。

region 識別子は不透明である。
利用側が読むのは識別子の同一性と問い合わせ結果だけであり、採番、走査順、内部の鍵の形は契約に含まれない。

root region は Scope に対応せず、プログラム全体の寿命を表す。
root region の `owners` の値は空の π である。

## 3. Point

point は Core の根から目的の節点までの意味的な子の添字の列である。
意味的な子は c の位置に来る部分項だけである。
span、束縛子、型注釈、label、`op`、`O`、`cid`、π、構築子名 `K` は子に数えない。
子の並びは項の書き順に従う。

主要な形の子の並びを次に定める。

- `(Apply c_f c_a ...)`：`c_f` に続けて `c_a ...`。
- `(Let (x τ) c_1 c_2)` と `(Let (x bmode τ) c_1 c_2)`：`c_1`、`c_2`。
- `(Construct τ K c ...)`：`c ...`。
- `(Construct τ K v ...)`：`v ...`。
- `(Eliminate c (br ...))`：`c` に続けて各 `br` の本体を分岐順に並べる。
- `(Perform op c)`：`c`。
- `(Handle op h c)`：`h` の本体に続けて `c`。
- `(Scope π c)`：`c`。
- `(Recur cid f (x ...) c_1 c_2)`：`c_1`、`c_2`。
- `(Yield c_1 c_2)`：`c_1`、`c_2`。
- `(Suspend c)`：`c`。
- `(Drop c)`：`c`。
- `(Curry c_1 c_2)`：`c_1`、`c_2`。
- `(Rec ((label m c) ...))`：`c ...`。
- `(Rec ((label m v) ...))`：`v ...`。
- `(Proj c label)`：`c`。
- `(Discharge (ProofRep O φ) c)`：`c`。
- `(Lam O cid (x ...) c)` と `(RecurVal cid f (x ...) c)`：`c`。
- `(UVal v)` と `(RVal (ProofRep O φ) v)`：`v`。
- `(CurryVal O v_1 v_2)`：`v_1`、`v_2`。
- `(Reborrow c)`：`c`。
- `(ReborrowAt ρ c)`：`c`。
- `(Borrow w)`、`(BorrowMut w)`、`(BorrowAt ρ w)`、`(BorrowMutAt ρ w)`：子を持たない。
  `w` は designator であり `c` の位置の部分項ではない。
- `(BorrowRef p ρ)`、`(BorrowMutRef p ρ)`：子を持たない。
- `l`、`x`、`(Move w)`、`(PrimVal O nm)`、`(TypeRep O t κ)`、`(ProofRep O φ)`、`(resource n)`：子を持たない。

値の内側も歩く。
`Lam` の本体が `Scope` を含む場合、その `Scope` も point の対象になる。

この定義の対象は elaboration が返す `G2` の Core である。
`(Error p)` は実行時の形であり、elaboration の Core には現れないため対象外である。
`(BorrowAt ρ w)`、`(BorrowMutAt ρ w)`、`(ReborrowAt ρ c)`、`(BorrowRef p ρ)`、`(BorrowMutRef p ρ)` も注釈後および実行時の形であり、elaboration の Core には現れない。
未知の形に出会ったときは、子を持たないものとして扱わず `error` を出す。

point は `erase-core` の像の上で数える。
spanful な Core と spanless な Core は、`erase-core` を通した後に同じ point を持つ。

## 4. 問い合わせ契約

### 4.1 Core API

次の 6 つは、すべての region solver が実装する。

- `region-at ir point`：point で有効な最も内側の region を返す。
  Scope に包まれない節点では root region を返す。
- `region-outlives? ir ρ_long ρ_short`：`ρ_long` の寿命が `ρ_short` の寿命を含むかを返す。
  反射的かつ推移的である。
- `regions-overlap? ir ρ_1 ρ_2`：2 つの region が同時に生きる瞬間を持つかを返す。
  対称である。
- `regions-exiting-at ir point`：point が指す節点の評価完了時に退場する region の集合を返す。
- `region-owning ir p`：`p` を `owners` に持つ region を返す。
  その region が一意に定まるときだけ値を返す。
  所有者が無い、または 2 つ以上ある IR は不正であり `error` にする。
  root region の `owners` は空の π であるため、root が返ることは無い。
- `region-solve ir constraints`：下限制約と上限制約の並びを受け、
  `(ok σ)` または `(error broken)` の判別可能な 2 択を返す。
  `σ` は寿命変数から region への immutable hash であり、決定的かつ極小である。
  極小解が一意であることは要求しない。
  `broken` は満たせなかった制約を入力の並び順で返す。

`region-at` と `regions-exiting-at` の定義域は、Core の節点を指す point に限る。
定義域外の point は `#f` や空集合へ置き換えず `error` にする。
`regions-exiting-at` は root region を返さない。

### 4.2 Inspection API

次の 3 つは lexical adapter の検査で使う。
将来の solver の利用側はこれらを読まない。

- `region-parent ir ρ`：`ρ` の親 region を返す。
  root region では `#f` を返す。
- `region-contains? ir ρ_outer ρ_inner`：`ρ_outer` が `ρ_inner` を構造として包むかを返す。
  反射的かつ推移的である。
- `region-ir-regions ir`：region の集合を返す。

### 4.3 Materialize API

- `materialize-regions ir core table σ`
  α 表と σ から、借用の項の注釈欄を解いた寿命へ置き換えた core を返す。
  対象は `BorrowAt` と `BorrowMutAt` と `ReborrowAt` の注釈欄である。
  point の数え方は §3 に従う。

`check-region-annotation` は materialize の前だけで走る。
materialize 後の注釈欄は起点ではなく寿命なので、後で掛け直すと必ず
`E-BOR-002` になる。

## 5. Well-formedness

`region-ir-ok? ir core` は次の 8 条件をすべて検査する。

1. `regions` は region の集合である。
2. `outlives` は 2 要素の対の集合であり、各要素は region である。
3. `owners` は region から π の列への有限写像である。
4. `regions` は空でない。
5. `outlives` に現れる region はすべて `regions` に含まれる。
6. `owners` の定義域は `regions` と一致する。
7. `regions-exiting-at` は Core の全 point で `regions` の部分集合を返す。
8. `region-at` は Core の全 point で `regions` の元を返す。

`outlives` の循環は許す。
同じ寿命を持つ region 間の制約を禁止しないためである。

`lexical-region-ir-ok? ir` は次の 2 条件を加えて検査する。

1. `parents` の定義域と値域が `regions` に含まれる。
2. 親を持たない region がちょうど 1 つあり、親の連鎖に循環がない。

この 2 条件は lexical adapter 固有であり、region IR の共通契約ではない。
いずれかの検査が偽になる IR は adapter または solver の実装誤りであり、入力診断ではない。

## 6. Lexical adapter

lexical adapter は Core を `erase-core` へ通し、その像を 1 回走査して IR を作る。
root region を走査の開始時に作り、Scope 1 つへ region 1 つを割り当てる。
Scope へ入るとき、現在の region を親として新しい region を作り、`outlives` へ親から子への直接の対を加える。
Scope の π を新しい region の `owners` の値にする。
Scope から出るとき、現在の region を親へ戻す。

`region-at` は、point の接頭辞のうち Scope を指す最も長いものの region を返す。
`region-outlives?` は直接制約の到達可能性で答える。
`region-contains?` は親の連鎖で答える。
`regions-overlap?` は一方が他方を構造として包むときに真である。
`regions-exiting-at` は Scope 自身の point でその Scope の region 1 件を返し、それ以外では空集合を返す。

lexical adapter は次の性質を満たす。

- **C1**：`region-contains?` が真なら `region-outlives?` も真である。
- **C2**：兄弟の region は互いを包まず、同時に生きない。
- **C3**：Core の Scope の個数と root 以外の region の個数が一致する。
- **C4**：`regions-exiting-at` は Scope の point でちょうど 1 件を返し、それ以外の point で空集合を返す。
  root region はどの point でも返さない。
- **C5**：core-calculus.md §8 の golden program `findPositive` と `map` について、Scope の入れ子から読み取れる親子関係、outlives、退場を問い合わせだけで再構成できる。
- **C6**：spanful な Core と `erase-core` 済みの Core から作った IR は、point ごとの `region-at`、退場、`region-outlives?`、`regions-overlap?` が一致する外延的同型を持つ。

C5 の検査は IR の内部表を直接読まず、Core の Scope の木から独立に期待値を作る。
C6 は region 識別子の採番や内部鍵の一致を要求しない。

## 7. NLL solver への置換条件

[REQ: BOR-003] lexical adapter を NLL solver へ置換するには、次の 6 条件を満たす。

1. 新しい solver は 3 成分を埋め、`region-ir-ok?` の 8 条件を満たす IR を返す。
2. 新しい solver は Core API の 6 つを実装する。`region-owning` と `region-solve` を含む。
3. 新しい solver は per-IR bridge の `region->rho ir ρ` と `rho->region ir n` を実装する。
   両者は `gen:region-solver` の method であり、1 つの IR の中で互いの逆写像である。
   その IR に属さない region や `ρ` に対しては `error` にする。
4. 新しい solver は region 識別子を、その solver のすべての実行を通じて fresh に採番する。
   採番の順序、大小、連番は契約に含めない。
5. 利用側は region 識別子の同一性と Core API の結果だけを見る。
6. 同じ制約集合について、lexical solver が受理した形は NLL solver も受理する。
   上限制約の `region-outlives?` は、lexical で真だった対について NLL でも真である。
   借用どうしの衝突 `regions-overlap?` は、lexical で偽だった対について NLL でも偽である。
   これらは解の region 識別子ではなく判定の結果を比較する。
   最後の条件には置換の余地があり、lexical で真だった衝突が NLL で偽になることは許す。

6 条件を満たす限り、利用側の書き換えは要らない。
新しい solver は Inspection API、`lexical-region-ir-ok?`、C1 から C4 を実装または満たす必要はない。
C6 は point の定義に関する性質であり、solver の種類を問わず成り立つ。

条件 4 の保証は `build-region-ir` と solver が返す IR についてのみ主張する。
手組みの IR は実装誤りを示す fixture のため、この保証を迂回する。

## 8. 位置

region IR が扱う位置の単位と source-map の規則は、`docs/specification/span.md` §8 に従う。
point の意味的な子の定義と source span の byte offset は別の概念である。

この文書は G5a の region IR の契約だけを定め、要件 ID や申し送り表の行を追加しない。

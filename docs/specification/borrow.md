# Topazolite 借用の型と permission 仕様

## 1. 位置づけ

本文書は borrow の型、許可条件、走査の状態を定める。
region IR と Core API は `docs/specification/region.md` が定める。
raw pointer と Proof は本文書の対象外である。

## 2. 借用の型

型 τ へ次の 2 つを足す。

- `(Borrowed τ ρ)`：共有借用。
- `(BorrowedMut τ ρ)`：可変借用。

payload を `Owned` で包まない。
`(Borrowed (Owned τ) ρ)` と `(BorrowedMut (Owned τ) ρ)` は型として禁じる。
禁じるのは直接の `Owned` だけである。
所有値を含む構造の借用は意図された用法であり、再帰的には禁じない。

`Borrowed` から `BorrowedMut` への暗黙の強化と、その逆の弱化をどちらも認めない。
弱化が要るときは `Reborrow` を書かせる。

## 3. 走査の状態

**Λ**（region 文脈）は木を下る向きにだけ流れる。
`ir`、`point`、`owners`、`tokens` の 4 欄を持つ。
`tokens` は借用の値を束縛した変数から、その借用が指す designator の集合への写像である。
集合にするのは `Eliminate` の分岐合流が 2 つ以上の所有者を返しうるためである。

束縛子は、借用を束縛したかどうかにかかわらず必ず `tokens` へ登録する。
借用でない束縛には空集合を張る。
外側の同名の変数が持つ designator を、内側の別物の変数で引かないためである。

designator の集合を引く手続きは、`tokens` に加えて走査中の局所束縛も見る。
`(Reborrow (Let (y let (BorrowedMut τ ρ)) (BorrowMut x) y))` のように
`Reborrow` の operand 自身が束縛子を含む形では、`y` の束縛はまだ `tokens` に無い。
局所束縛は走査の途中でその場で集め、`tokens` より先に引く。
この順序が、内側の束縛子が外側の同名を遮蔽するという規則を表す。

designator が局所束縛にも `tokens` にも無いときは、その designator 自身を親 capability とみなす。
構築子の欄へ格納された借用を分岐の束縛子で受けた形がこれに当たり、真の所有者は構造からは辿れない。
これは近似である。
G5b でこの近似が健全なのは次の 3 点による。

1. 真の所有者は外側の region が続くあいだ `mut` に残り続ける。
   `Move`、`Drop`、再度の借用はその項目で引き続き禁じられる。
2. 許可の判定は designator の名前で引くため、束縛子を停止すれば束縛子経由の使用は塞がる。
3. G5b には借用を経由した書込み操作が無い。
   真の所有者を停止しないことによる観測可能な差が生じない。

書込み操作を導入する段では、provenance を厳密に辿る形へ改める。
このとき、分岐の束縛子が受けた借用の所有者を型か注釈で持ち運ぶ必要がある。

**Ψ**（permission 状態）は評価順に流れる。
`shared`、`mut`、`suspended` の 3 欄を持つ。

Λ を下る向きだけの文脈にし、Ψ を評価順に流すのは `Let` のためである。
`(Let (y τ) c_1 c_2)` の `c_2` は `c_1` の子ではなく兄弟であり、
`c_1` で取った借用が `c_2` へ届かなければ競合を判定できない。

所有値の束縛だけが `owners` へ入る。
`Lam`、`Recur`、`RecurVal` の仮引数は入らない。
仮引数の owner region は呼出し側にあり、本サイクルの情報だけでは定まらない。

## 4. 借用の許可条件

[REQ: BOR-001] 借用は owner より長生きしてはならない。

`(Borrow w)` と `(BorrowMut w)` の判定は 3 段である。

1. owner の region `ρ_owner` を引く。
2. 借用の region `ρ_borrow` を `region-at ir point` で引く。
3. `region-outlives? ir ρ_owner ρ_borrow` を要求する。

`ρ_borrow` を最も内側の Scope にするのは lexical な近似である。
NLL solver へ置き換われば `ρ_borrow` は短くなり、通るプログラムが増える。
判定の式は変わらない。

`w` の型は所有でなければならない。
結果の型は `(Borrowed τ ρ_borrow)` または `(BorrowedMut τ ρ_borrow)` であり、`Owned` は剥がす。

[REQ: BOR-002] mutable borrow の有効期間中、競合する alias を許可しない。

Ψ に対する規則は 3 つである。

1. 共有借用どうしは許す。
2. 可変借用は排他である。同じ `w` について重なる region の借用を許さない。
3. 可変借用を取るとき、同じ `w` の共有借用と region が重なるなら取れない。

`Move w` と `Drop w` は、`w` について生きている借用が 1 つも無いときだけ許す。
借用の項目が Ψ から消えるのは Scope の退場だけである。
所有者の状態を自動で戻すことはしない。
所有権の状態は機械の Ω が持つ別の概念であり、Ψ は静的な借用の生存だけを表す。

## 5. 診断

本文書が定める条件の診断は `E-BOR` 分類である。
key と番号は `docs/specification/diagnostic.md` の registry に従う。

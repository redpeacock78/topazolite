# Topazolite 借用の型と permission 仕様

## 1. 位置づけ

本文書は borrow の型、許可条件、走査の状態を定める。
region IR と Core API は `docs/specification/region.md` が定める。
raw pointer と Proof は本文書の対象外である。

### 1.1 借用を含む Core の型付け

借用を含む Core は region IR を作り、span を保った Core に region 注釈を付けて、region context の下で一度型付けする。
`core-type-of/regions` は型、row、region IR、解決表、寿命解 `σ` などをまとめた結果を返し、失敗時は元の Core 節点を使って診断を作る。
実行用 Core は同じ型付け結果から `region-execution-core` で materialize し、別の型検査は行わない。

宣言型と推論型の借用 region を対応づけるとき、`Record` の欄は名前で照合し、同じ欄の推論 region だけを宣言型へ採る。
`UnionInject` では tag が指定する member の payload を対象に、同名の欄を対応づける。
宣言 member にだけある欄は宣言型のまま残して後段の型照合へ渡すため、payload に必要な欄が無い形は `E-RCD-008` で拒否する。
payload にだけある欄は region の採用対象にしない。

Surface driver は `borrow-bearing-core?` で借用の式または型を含む Core を判定し、該当する項にこの経路を使う。
elaborate が生成する adapter も借用を含む場合は同じ経路で検査する。
借用を含まない Core は従来の `execution-core` と `core-type-of/diagnostic` を使う。
これらの従来入口は空の region context で型付けするため、借用を含む Core の型付けには使わない。

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
[REQ: SCP-002] `tokens` は借用の値を束縛した束縛出現の識別子から、その借用が指す designator の集合への写像である。
鍵は名前ではなく、elaboration が焼き込んだ一意な記号である。
集合にするのは `Eliminate` の分岐合流が 2 つ以上の所有者を返しうるためである。

束縛子は、借用を束縛したかどうかにかかわらず必ず `tokens` へ登録する。
借用でない束縛には空集合を張る。
束縛出現の識別子が一意であるため、同名の束縛が入れ子になっても別の鍵になり、
外側の束縛が持つ designator を内側の別物の束縛で引くことはない。

designator の集合を引く手続きは、`tokens` に加えて走査中の局所束縛も見る。
`(Reborrow (Let (y let (BorrowedMut τ ρ)) (BorrowMut x) y))` のように
`Reborrow` の operand 自身が束縛子を含む形では、`y` の束縛はまだ `tokens` に無い。
局所束縛は走査の途中でその場で集め、`tokens` より先に引く。
この順序は、局所束縛の designator を `tokens` の写像より先に解決する規則を表す。

G5b では、局所束縛にも `tokens` にも無い designator をそれ自身の親 capability とみなす近似を使っていた。
この近似は外され、現在は所有者を辿れない designator を `E-BOR-020` で落とす（§10）。

**Ψ**（借用の記録）は評価順に流れる。
`shared`、`mut`、`suspended` の 3 欄を持つ。
記録は単調であり、Scope の退場で項目を落とす操作は無い。
借用が生きている範囲は寿命変数の解 σ が決める。

Λ を下る向きだけの文脈にし、Ψ を評価順に流すのは `Let` のためである。
`(Let (y τ) c_1 c_2)` の `c_2` は `c_1` の子ではなく兄弟であり、
`c_1` で取った借用が `c_2` へ届かなければ競合を判定できない。

所有値の束縛だけが `owners` へ入る。
`Lam`、`Recur`、`RecurVal` の仮引数は入らない。
仮引数の owner region は呼出し側にあり、本サイクルの情報だけでは定まらない。

## 4. 借用の許可条件

[REQ: BOR-001] 借用は owner より長生きしてはならない。

`(Borrow w)` と `(BorrowMut w)` の判定は次の 3 手順で行う。

1. owner の region `ρ_owner` を引く。
2. 借用の region `ρ_borrow` を `region-at ir point` で引く。
3. `region-outlives? ir ρ_owner ρ_borrow` を要求する。

`ρ_borrow` を最も内側の Scope にするのは lexical な近似である。
NLL solver へ置き換われば `ρ_borrow` は短くなり、通るプログラムが増える。
判定の式は変わらない。
この判定は段 3 で、解決済みの σ を用いて行う。

`w` の型は所有でなければならない。
結果の型は `(Borrowed τ ρ_borrow)` または `(BorrowedMut τ ρ_borrow)` であり、`Owned` は剥がす。

[REQ: BOR-002] mutable borrow の有効期間中、競合する alias を許可しない。

Ψ に対する規則は 3 つである。

1. 共有借用どうしは許す。
2. 可変借用は排他である。同じ `w` について重なる region の借用を許さない。
3. 可変借用を取るとき、同じ `w` の共有借用と region が重なるなら取れない。

この判定は段 3 で、解決済みの σ と Ψ を用いて行う。

可変借用の値の複製は新しい借用ではない。
`R-Let` の置換、同じ欄の二度の取り出し、変数の別名によって一つの可変借用が複数の位置に現れても、同じ借用を指す。
規則 2 は別々に取得した可変借用の重なりを `E-BOR-003`（`borrow-conflicting-alias`）で拒否する。
子の借用が生きている間に親の借用またはその複製を使う形は、§13 の capability の衝突として `E-BOR-025` で検査する。
性質 8 の oracle は同じ正規化借用の複数の出現を一つと数え、生存中の可変借用の再取得を `R-BorrowMut` の step で拒否する。
射影で作った借用も oracle の派生関係に親子として記録し、その祖先と子孫を独立した可変借用の重なりとして数えない。
可変の派生子が生きている間に親の借用値を消費する簡約段は、`reborrow-parent-live` で拒否する。
射影の子を親とする `Reborrow` では、親の値が後続に現れるだけでは停止違反とせず、親を消費する段を派生関係に基づいて判定する。
直接の `Reborrow` は従来どおり親の出現で判定する。

`Move w` と `Drop w` は、`w` について生きている借用が 1 つも無いときだけ許す。
Ψ から項目が消えることは無い。
借用が生きている範囲は σ が決めるため、記録を落とさなくても範囲の外の使用は通る。
所有権の状態は機械の Ω が持つ別の概念であり、Ψ は静的な借用の生存だけを表す。

## 5. Reborrow

`(Reborrow c)` は、可変借用をより短い region の共有借用へ落とす。
`c` の型は `(BorrowedMut τ ρ_parent)` でなければならない。
子の region `ρ_child` は `Reborrow` の節点で有効な region である。
`ρ_parent` が `ρ_child` を包むことを要求する。
結果の型は `(Borrowed τ ρ_child)` である。
親子の寿命と停止窓の判定は段 3 で、解決済みの σ を用いて行う。

親の借用が指す designator の集合は、operand の形から遡って求める。
`Let` で束縛した名前を経由する場合は、束縛時に記録した対応を引く。
その名前が `Reborrow` の operand の内側で束縛されている場合も、走査中に集めた局所束縛から引く。
対応が記録されていない designator は `E-BOR-020` で落とす。

この集合は 2 つ以上になりうる。
`Eliminate` の分岐がそれぞれ別の所有者を借用して合流する場合である。
このとき `Reborrow` は集合の全要素を停止する。
実行時に走るのは 1 つの分岐だけなので、全要素の停止はそのとき本当に停止すべき項目を必ず含む。
`ρ_child` の退場では、停止した項目だけが可変借用へ戻る。
そのため、走らなかった分岐の所有者を停止したままにする状態は残らない。

集合が空になるのは、designator から対応を辿れない入力である。
この場合は `E-BOR-020` で落ちるため、走査の後段へ届かない。

この数え上げは、借用を運ぶ構文を足したときに崩れる。
新しい構文が内側の項の型をそのまま返すなら、上の走査へその形の規則を同時に足す必要がある。

親の可変借用は `ρ_child` の間だけ停止する。
停止が始まるのは `Reborrow` の節点であり、それより前に作られた借用は停止窓に入らない。
region は lexical であって節点の前後を区別しないため、窓の開始は region ではなく走査順で定める。
停止した項目は退避され、`ρ_child` が退場するとき可変借用へ戻る。
停止中の値は `Move` も `Drop` もできない。
親自身の region が同じ退場に含まれる場合は戻さない。

可変借用から値位置の field 射影を作る場合も、子の寿命の間、親を射影先の field path 上で停止する。
停止する capability は親の capability の path に field label を足したものであり、重ならない別の field path は停止しない。
子が `BorrowedMut` なら可変の項目と判定要求を、子が `Borrowed` なら共有の項目と判定要求を登録する。
place 位置の field 射影は子を作らず、停止もしない（§13）。

停止の起点を判定するときは、停止関係を推移閉包でたどる。
親、子、孫の順に停止が連なる場合、孫を起点とする使用も祖先の停止を迂回しない。

退避するのは、その designator が可変借用の項目として実際に記録されている場合だけである。
親が共有借用である `Reborrow` では `mut` に項目が無く、規則そのものは変わらない。
この場合は子 region の共有借用だけを張る。
共有借用は `Move`、`Drop`、可変借用を子 region のあいだ塞ぐため、必要な制約はこれで足りる。
退避しないのは、記録に無い項目を退場時に作り出さないためである。
作り出すと、子 region が終わったあとも `Move` と `Drop` が恒久に塞がれる。

借用の region が Scope の退場時に抜ける場合、その Scope の内側で作られた loan は、退場後に現れる借用と使用に重ならない。
この判定は Ψ から項目を削除せず、σ が示す loan の生存範囲だけを用いる。
point の順序を使うのは、二つの point が線形な評価順にある場合に限る。
`Handle` の handler と body、`Recur` の本体と継続をまたぐ比較では point 順の除外を使わず、σ による判定を保つ。

### 関数本体から実体化する再借用の停止窓

関数本体で記録した遅延再借用を呼出し位置へ実体化するとき、停止と子の共有 loan に窓を付ける場合がある。
窓の Scope は、関数本体内で `Reborrow` を包む最も内側の Scope である。

窓を付けるのは、関数に仮引数があり、戻り型が借用を含まないスカラーで、latent row に借用を含む payload が無く、窓の Scope の本体が次の形だけで構成される場合である。

- 入れ子の Scope。
- スカラー値の `const` または `let` 束縛。
- 既知のスカラー借用を親とする `Reborrow` または `ReborrowAt` の `const` または `let` 束縛。
- スカラー値またはスカラー借用の読み出し。
- 借用を指す place へのスカラーリテラルの `Assign`。
- スカラーリテラル。

ここでスカラー型は `Int`、`Bool`、`Unit`、`String` である。
再借用の親は走査中に記録され、その payload は子の借用と同じスカラー型でなければならない。
窓の Scope が無い場合、または本体にこれ以外の形がある場合は窓を付けず、σ で判定する。

遅延要求を実体化するときは、本体相対の窓の point を呼出し位置の下へ写し、停止の組と子の共有借用の要求に保持する。
親の使用は `Reborrow` の開始点より後で、かつ窓の Scope 内にある場合に限って停止する。
子の loan は生成点を含み、窓の Scope 内にある要求との重なりを判定する。
窓の外にある使用と借用は、その停止と子の loan によって拒否されない。
窓を付けない再借用は、従来どおり σ の region で判定する。

関数本体で仮引数の可変借用から値位置の field 射影を作る場合、本体では実引数の owner と path が定まらないため、子の借用要求と親子の region 制約を延期する。
呼出し時に要求を実引数の capability へ写し、親の可変項目を確保したうえで、field label を足した path に対する停止を実体化する。
同じ仮引数からの place 位置の射影は子を作らず、通常の使用要求だけを既存の関数境界の経路で呼出し時へ写す。

## 6. 分岐の合流

分岐が同じ欄へ異なる region の `Borrowed` 値を返すとき、record merge の失敗条件は広げない。
合流した借用の寿命を新しい寿命変数へ束ね、その寿命が両分岐の寿命に収まることを制約で検査する。
分岐の借用が所有者を超える形は `borrow-escapes-owner` で報告する。

現行の伝播ではこの制約の左辺が必ず寿命変数であり、σ を右辺まで広げてから検査するため、制約は恒に満たされる。
よって合流に固有の診断 key は置かない。
opaque な region 引数が入り、伝播で左辺を広げられなくなる段で必要になれば、その段で足す。

失敗条件を借用の region 差へ広げる案は採らない。
両分岐が同じ所有者を同じ長さだけ借りていながら、走査上の region 識別子だけが違う形を弾くためである。

## 7. 診断

本文書が定める条件の診断は `E-BOR` 分類である。
key と番号は `docs/specification/diagnostic.md` の registry に従う。

`E-BOR-027` `borrow-hidden-by-narrowing` は、borrow-hiding-kind が拒否を返す narrowing、または RSD の義務があるのに有効な `Discharge` が無い Core を拒否する。
`RegionLam` が自由変数として捕捉する可視環境項目の型に、bound set で束縛されない借用 region が含まれる場合も同じ診断で拒否する。
その bound set は当該 `RegionLam` の alpha-renamed binder と、捕捉する環境項目自身の `ForallRegion` binder だけから作り、外側の region binder は引き継がない。
現在の Surface の lowering と narrowing 経路では `E-BOR-027` に到達しない。
この診断は owner と借用 region の outlives 関係違反を報告する `E-BOR-004` とは異なり、borrowed value を narrowing で view から隠す根拠が無いことを示す。

## 8. 関数境界の受け渡し

[REQ: BOR-007] 関数の仮引数の型、結果型、捕捉に `Borrowed` と `BorrowedMut` を置ける。
置けるのは region 欄が、その関数を囲む `RegionLam` が束縛した `(RParam rp)` である場合に限る。
region 欄が具体的な region か、束縛されていない `rp` であれば違反とする。
具体的な region を関数の内側から名指す形を許すと、呼出し側の region を関数の定義が決めることになり、呼出しごとに異なる region で同じ定義を使えない。
結果型だけを開くと仮引数と捕捉が判定を持たないため、3 つを同じ判定で扱う。
対象は `Lam`、`Recur`、`RecurVal`、`Curry`、`Apply` である。

関数と再帰関数は `Owned<τ>` の仮引数を宣言できる。
呼出し側から渡された値は、呼出された側の `Scope` が管理する place へ載る。 [REQ: OWN-006]

`Lam` は外側の `Owned<τ>` を捕捉できる。
捕捉した値は `Curry` の固定引数として `Move` で渡し、closure の型を `Owned<NFn …>` とする。 [REQ: OWN-007]
捕捉の仮引数は本体の内側で元の名前へ開く。
この開き方は `Owned` の仮引数の符号化と同じである。

`Owned` の関数を関数の位置へ置くときは、根が `Move` または `CurryVal` である形だけを許す。
surface の closure は elaborate が `Let` と `Move` を挿入するため、この制限に適合する。
Core を直接書く場合に制限へ違反した形は、型検査で拒否する。

`Curry` は `Owned<τ>` の固定引数を `Move` 経由で受け取る。
固定引数を持つ `CurryVal` の結果型は `Owned<NFn 残余>` になる。 [REQ: OWN-008]
一回性は型による `Move` の要求、実行時の `R-MoveError`、性質 7 の bounded 検査で確認する。

`CurryVal` の内部に入った `Owned` 値の drop 責務は、`Construct` の欄と `Yield` の payload に入った `Owned` 値と同じ機構で扱う。
producer の位置で `OwnLeaf` を通して token を割り当て、`OwnedLeaf` として値の内部へ残す。

判定は型木を再帰的に走査する。
直下の形だけを見る判定では、`(Union (Borrowed τ ρ) τ')` や仮引数列の 2 番目だけが借用の `NFn` がそのまま通ってしまう。
走査は `Union`、`Intersection`、`Record`、`List`、`Option`、`Result`、`Refined`、`Untrusted`、`NFn` の τ 欄すべてに入る。
`NFn` は仮引数列、結果型、`Q` の 3 欄を走査する。
`Q` の欄の違反は結果型の違反として報告する。
`ε` は効果ラベルの列であり、型の欄を持たないため走査しない。

`Curry` は残余の `NFn` も検査する。
第 1 引数の型だけを見ると、2 引数目が借用の関数を部分適用したときに残余が境界を越える。
残余の仮引数列の違反は仮引数の診断、残余の結果型の違反は結果型の診断として報告する。

型環境として外から与えられた関数の署名は、定義位置の検査を通らない。
そのため、変数として持ち出した関数は使用位置、すなわち `Apply` と `Curry` でも検査する。
入口の妥当性検査でこれを掛けてはならない。
入口の検査は型付けより先に走るため、仮引数と結果型の 2 つの診断が入口の診断に覆い隠される。

仮引数の型が借用である場合と、仮引数そのものを借用しようとした場合は別の条件である。
後者は仮引数が owner の表に入らないことによる。

束縛された `rp` の集合は、`RegionLam` の型付けが本体へ入るときに与える。
集合が空である文脈、つまり region 引数を持たない関数では、あらゆる借用型が違反になる。

署名そのものが `ForallRegion` である再帰関数では、束縛された `rp` の集合を `ForallRegion` の束縛から与える。
関数境界の検査は、その集合を置いた状態で走らせる。
本体の中では関数の名前が 1 段剥がした `NFn` を指し、本体の外では `ForallRegion` のままである。

要約を持つ callable の呼出し側の検査は、宣言の `(RParam rp)` の束縛性を直接見ず、
実引数がその借用の所有者を運ぶ capability を持っているかを見る。
要約を持たない具体の region の `NFn` は region 多相以前からの禁止であり、従来どおりの判定を保つ。 [REQ: BOR-007]

借用の仮引数は呼出し側の借用の別名である。
本体の再借用と使用は定義位置では要求にならず、仮引数の位置ごとの鍵を持つ雛形として残る。
`Apply` が実引数の capability と起点で鍵を置き換え、`RegionApp` が受けた region 項で
`(RParam rp)` を置き換えてから、初めて要求になる。
再借用の遅延制約も、親の capability に含まれる各 formal key に対応づけて残す。
`Apply` は各 key を対応する実引数の capability へ展開する。

再帰呼出しの借用の実引数は、対応する仮引数の鍵を根とする capability に限る。
根が別の鍵である場合、capability の集合が空である場合、別名を経て根が定まらない場合は `E-BOR-020` で落とす。
この制限があるため、再帰呼出しの位置では雛形を実体化しない。
本体の検査が収束したあと、確定した要約を継続の側の呼出しが使う。

結果型に借用の leaf があるときは、各 leaf を結果型の path `π` で特定し、その宣言 region を `ρπ` とする。
仮引数 `i` の型にある path `π'` の leaf が `ρπ` と同じ宣言 region を持つとき、`(i, π')` をその結果 leaf の候補とする。
この組を formal key とし、`i` は 0 起点の仮引数位置、`π'` はその仮引数を根とする入力型の path である。
path は型の構造をたどり、record 欄、構成子の欄位置、Union member を区別する。
候補は関数の宣言型に書かれた region の等値で決め、`RegionApp` を適用した後の具体 region から数え直さない。

各結果 leaf の候補は独立に扱う。
結果と仮引数の最上位が借用型である場合は `π` と `π'` がともに空であり、従来の候補位置の規則になる。
欄の内側にある借用も、同じ宣言 region を持つ仮引数の欄を候補にできる。

本体の出現の要約を持たない concrete な `NFn` では、各結果 leaf の候補が一つに定まり、その実引数が対応する `π'` の欄に capability を持たなければならない。
候補が無いか複数ある場合、または唯一の候補の欄が capability を持たない場合は `E-BOR-020` で落とす。
要約を持つ署名では、各結果 leaf の候補が空の場合、または候補となる実引数のいずれかが対応する欄に capability を持たない場合に `E-BOR-020` で落とす。
結果の capability 表は、各結果 leaf について候補となる実引数の対応欄の capability を合わせて作る。
結果値そのものは、実際に返った `BorrowRef` または `BorrowMutRef` の root と path を保つ。

### 呼出しを Scope で包む借用の実引数

Core の `Apply` に専用の呼出し region は無い。
`Borrow` または `BorrowMut` で新たに作る実引数の loan は、その式を包む最も内側の Scope の region に入り、その Scope の退場まで生きる。
`Apply` 自体は loan を短くしないため、直接の借用式を渡す裸の `Apply` では、loan は呼出しを含む外側の Scope の残りの範囲にも重なる。

次の条件をすべて満たす Core では、呼出しのために新たに作った実引数の loan は、`Apply` を含む Scope の退場で終わる。

1. 借用を作るすべての実引数を同じ一つの Scope の中で作り、その Scope の中に `Apply` を置く。
   実引数ごとに別の Scope へ分けると、同じ呼出しへ渡す借用どうしの重なりを判定できない。
2. `RegionApp` に渡す region は借用した owner の region とする。
   Scope 内の point に対応する region を渡す形は `E-TYP-023` で拒否される。
3. 呼出しの結果型は再帰的に借用を含まない。
4. latent row の `Return` operation の payload は再帰的に借用を含まない。
   `Option` で包まれた payload も同じである。
5. 借用済みの値を包んでも、その値の loan は短くならない。
   呼出しの間だけ有効にするには、Scope の中で `Reborrow` してから渡す。

```text
(Scope ()
  (Let (t ...) (BorrowMut x)
    (Apply sink t)))
```

上の 3 または 4 を満たさず、Scope 内で新たに作った借用が呼出し結果または `Return` payload として Scope の外へ届く形は、loan を Scope の退場で短縮せず、`E-BOR-020` で拒否する。
結果型に借用を含む呼出しと、借用を含む `Return` payload を持つ呼出しを、それぞれこの形で型検査すると `E-BOR-020` になる。

部分適用は借用が現れる署名を運べない。
置き換えは呼出しの出現に結び付いており、部分適用が作る関数値には出現の情報が残らない。
借用が現れる署名を `Curry` と `CurryVal` へ渡すと落とす。
落とす鍵は署名の素性で分かれる。
本体の出現の要約を持つ署名は、写す先の出現が無いため `E-BOR-020` で落とす。
要約を持たない具体の region の署名は、region 多相以前からの禁止であり、
仮引数なら `E-BOR-012`、結果型と証明義務なら `E-BOR-013` で落とす。

段 A が扱うのは、`RegionLam` と `RegionApp` を持つ関数と、その呼出しで借用を受け渡す形である。
`RecurVal` と `Recur` は署名の `ForallRegion` を 1 段剥がし、本体では `rp` を置いた `NFn` を関数の名前へ束縛する。
本体の外では関数の名前は `ForallRegion` のままであり、呼出しは `RegionApp` で包みを剥がしてから行う。
machine では `RecurVal` に対するこの剥がしを **`R-RegionAppRecur`** が行う。
署名が素の `NFn` である再帰関数は、囲む `RegionLam` が束縛した `rp` のうち署名が言及するものを本体へ引き継ぐ。

## 9. capability

借用が指す先を **capability** と呼ぶ。
capability は根の place `w` と field path `fp` の組である。

path の形そのものを `path-wf?` が検査する。
path segment は record の `label` または positional な `natural` である。
借用と field 射影の入口は `record-path?` を使い、label だけを許す。
所有値の内部を走査する入口は `owner-path?` を使い、label と natural の双方を許す。
`owner-path?` と `path-wf?` は同じ segment alphabet を共有するが、用途ごとの
record 境界を混ぜない。b3a の leaf path は `Rec` の label だけからなり、natural
segment は b3b の positional producer 用に予約する。segment の種類と対象値の形が
合わない操作、欠落 field、非 list path は fail-closed に拒否する。

`fp` の空の列は place そのものを指す。
`(Rec ((a ...) (b ...)))` を束縛した place `1` に対し、`(1 ())` は record 全体を、`(1 (a))` は field `a` を、`(1 (a x))` は field `a` の中の field `x` を指す。

型検査が使う capability 表は、`Rec` の各 field を `(record-field . label)` の鍵で保持する。
field に借用が無い場合も空の capability を記録し、record 全体の集合は全 field の集合の合併とする。
`Proj` は表があるとき対象 field の組だけを返し、鍵が無ければ空の組を返す。
表自体が無い式に限り、従来どおり式全体の集合を使う。
`ProjOpt` は対象 field の組を `Option` の `some` 欄 `(some . 0)` の下に包むため、`Eliminate` が payload の capability を分岐束縛子へ渡せる。
`RecRewrite` と `RecRewriteOpen` も出力 field ごとの表を保持し、書き換えた field は書換え後の値から、通過する field は入力表の同じ label から capability を得る。
RSD の `Discharge` は、欄表がある値では expected に残る欄だけを再帰的に残し、record 全体の capability 集合を残った欄の集合から作り直す。
欄表が無い値は除去された欄と capability の対応を復元できないため、従来の集合をそのまま透過する。

`Apply` の結果の表は、結果型の各借用 leaf について §8 の候補 `(i, π')` を調べ、実引数 `i` の `π'` にある capability を合わせて作る。
実引数が欄表を持たない場合は、要求された欄の代わりに実引数全体の capability 集合を用いる。
この集合には入れ子の leaf の capability も含まれるため、欄の区別は粗くなるが capability を取り落とさない。
結果全体の capability 集合は、すべての結果 leaf の集合の和である。

欄表の鍵は、record の `(record-field . label)`、構成子 `K` の第 `i` 欄の `(K . i)`、正規化した Union member 型である。
呼出しに適用した region 引数で Union member 型を置換し、正規化して鍵にする。
置換後に複数の member が同じ鍵へ潰れた場合は、対応する欄の capability を合わせる。
Union 自体が一つの型へ潰れた場合は member の segment を path から除き、潰れた欄の capability を Union があった位置に置く。

値位置の `ProjBorrow` は、親の各 capability path に射影した record 欄の label を足す。
`Read` は operand の各 `(root, path)` capability に対し、その root の token が持つ欄表から `path` の欄を選び、得られた entry を合わせて結果の集合と表を作る。
この lookup は record 欄、data の構成子と欄位置、Union の `Payload` をたどる。
したがって、空でない path を持つ `ProjBorrow` の `Read` も、Union payload を読む `Read` も同じ規則で扱う。

`UVal`、`RVal`、`OwnLeaf`、`OwnedLeaf`、`OwnedTransit` は内側の値の capability 集合と表をそのまま保つ。
`Unsafe` も本体の集合と表を透過する。
`Recur` は継続の集合と表を結果にする。
`Suspend` は内側の capability 集合を保つが、欄表を落とす。

値の内部に入った所有資源は `(OwnedLeaf tk v)` として leaf token `tk` を持つ。
同じ token の複製を許さず、`Available`/`Moved` の token は live value に一度だけ現れ、
`Dropped` の token は live value に現れないことを構成検査で確認する。 [REQ: OWN-009]
scope 終了では leaf を走査して `Dropped` にし、`finLeaf(w, fp)` を root の `fin(w)` より先に記録する。
明示 `Drop` は同じ leaf 走査で token だけを消費し、観測イベントを追加しない。 [REQ: OWN-010]

2 つの capability `(w1 fp1)` と `(w2 fp2)` が **重なる** のは、`w1` と `w2` が同じ place であり、かつ `fp1` と `fp2` の一方が他方の接頭辞であるときに限る。 [REQ: BOR-006]
`(1 (a))` と `(1 (a x))` は重なる。
`(1 (a))` と `(1 (b))` は重ならない。
兄弟の field を同時に可変で借りられるのは、この規則による。

借用の値は `(BorrowRef w fp ρ)` と `(BorrowMutRef w fp ρ)` の 2 つの形を持つ。
3 節の Ψ の 3 欄の鍵は place ではなく capability である。

## 10. 所有者の注釈

直接の借用を作る `BorrowAt` と `BorrowMutAt` は、その借用の所有者を **`own` の欄** として運ぶ。 [REQ: BOR-006]
`own` の形は `(Own w fp)` であり、9 節の capability と同じ組である。
再借用と field 射影は own 欄を持たず、入力の借用値から root と path を受け継ぐ。

`own` は region の注釈と同じ経路で `BorrowAt` と `BorrowMutAt` に入る。
注釈を入れる走査が 3 節の `owners` から所有者を決め、項の欄へ書き込む。
書き込んだ直後と、実体化の前後で、欄の値と走査が決めた designator が一致することを検査する。
一致しなければ `E-BOR-023` で落とす。
この照合は直接の借用の欄に限る。

G5b の `borrow-token-key` は、所有者を辿れない designator を自分自身とみなす近似を持っていた。
書き込み操作が入ると、この近似は真の所有者への可変借用を停止させない経路を作る。
近似を消し、所有者を辿れない designator は `E-BOR-020` で落とす。

簡約の側は `BorrowAt` と `BorrowMutAt` の `own` だけを読み、規則の側条件 `own-agrees?` で照合する。
再借用と射影の結果は入力の実行時借用値から作るので、型検査を通った項が own の不一致を理由に stuck になることはない。

## 11. field 射影

`(ProjBorrow c label)` は、借用 `c` が指す record の field `label` への借用を作る。 [REQ: BOR-005]
`(ProjBorrowAt ρ c label)` は寿命を明示する形である。

親の借用の capability が `(w fp)` なら、子の capability は `(w (fp ... label))` である。

mode は親の mode と field の可変性から決まる。

| 親の mode | field の可変性 | 子の mode |
|---|---|---|
| `Borrowed` | `imm` | `Borrowed` |
| `Borrowed` | `mut` | `Borrowed` |
| `BorrowedMut` | `imm` | `Borrowed` |
| `BorrowedMut` | `mut` | `BorrowedMut` |

親が共有なら子も共有である。
親が可変でも field が `imm` なら、その位置への書き込みは record の不変性を破るため、子は共有になる。

親が共有の射影は親の α を共有し、子の借用を新たに登録しない。
親が可変で値位置に射影する場合、子は新しい α を持つ。
分解の枝内では `region-at/branch` が返す枝またはその内側の region を下限とし、それ以外では射影の point を包む最も内側の `Scope` または owner-body を下限とする。
親の可変借用は子の capability、すなわち親の capability に field label を足した path の上で停止する。
子の mode に応じて、可変の子は `mut`、共有の子は `shared` の項目と判定要求を登録する。
親が関数の可変仮引数である場合、親子関係と要求は呼出し側で owner と path を確定するまで延期する。
place 位置の射影は §13 のとおりであり、可変の親からでも親の α を共有し、子の項目と停止を作らない。
`R-ProjBorrowMut` は `ProjBorrowAt` の注釈 region を実行時の借用値へ置く。
値位置ではこの注釈が子の寿命であり、place 位置では一時 view の消費後に config を再型付けするとき Core の place 位置の印を用いる。
`R-ProjBorrow` は共有の親の region を結果へ保つ。

operand が record の借用でなければ `E-BOR-016`、label が row に無ければ `E-BOR-017` で落とす。

`Eliminate` は scrutinee の capability 表から、構築子の label と欄位置に対応する capability を分岐の束縛子へ配る。
表を作れない scrutinee は `E-BOR-020` で落とす。

借用した data 値は分解して欄を借用のまま読み出せる。
`Eliminate` の scrutinee の型が `(Borrowed τ ρ)` であるとき、`τ` の構成子の欄の型 `τ_i` は分岐の束縛子へ `(Borrowed τ_i ρ)` として渡る。
束縛子が指す capability は、scrutinee の capability の path の末尾へ 0 起点の欄の位置を積んだものである。
この採番は core-calculus.md §5.1 が leaf の path について定めた採番と同じである。
構成子名は segment に入れない。
実行時に選ばれる分岐は 1 つだけであり、位置だけで欄が定まるためである。

`(BorrowedMut τ ρ)` も同じ規約で分解する。
構成子の欄には `Rec` の欄と違って mode が無いため、欄の可変性で mode を切り替える余地が無い。
親が可変であれば子もすべて可変になる。
`Rec` の field 射影が §11 の表で mode を落とすのと違い、data 値の分解では落ちる場所が無いためである。

複数の構成子を持つ data 型の可変借用を分解するとき、欄の位置は variant に依存する segment として記録する。
この印は、子の path が親の現在の構成子に依存することを表す。
構成子が一つの data 型の欄の位置と record の欄名には、この印を付けない。
Union の可変借用を分解するときは、payload の `(Payload)` segment に同じ印を付ける。

関数の可変仮引数以外の可変借用を親とする `Eliminate` と `UnionEliminate` では、各枝の各可変 binder に独立した寿命変数 α を与える。
親の capability 表に欄ごとの項目があるときは、data では選択された構成子と欄番号、Union では選択された member の payload に対応する項目だけを binder の親とする。
欄ごとの項目が無い場合は、親の全 token を親の項目とする。
各親の寿命変数は binder の α を含み、binder の下限はその枝の region である。
binder の可変要求と親の停止は、親の path に data の欄番号または Union の `Payload` を足した path に限る。
したがって、分解した親の別の欄は枝の中でもこの停止の対象にならない。
共有借用を親とする binder は従来どおり親の region を共有し、寿命変数を新設しない。
関数の可変仮引数を親とする binder も寿命変数を新設せず、呼出し時に親と path を確定する扱いを保つ。

## 12. 読み出しと書き込み

`(Read c)` は capability が指す先の値を複製する。 [REQ: BOR-004]
共有借用と可変借用のどちらからも読める。
operand が借用でなければ `E-BOR-018` で落とす。

読み出せる型は `Read` の型検査が決める。
`Owned` を含む型は読み出せず、`E-BOR-014` で落とす。
payload に含まれる借用は、すべての lifetime から所有者の region を引けなければならない。
payload のどこかに `BorrowedMut` があれば、同じ可変 loan を指す参照を複製するため `E-BOR-014` で落とす。
共有の `Borrowed` を欄に持つ payload は読み出せる。
所有者を引けない借用は `E-BOR-006`、view の region を超える借用は `E-BOR-004` で落とす。
その結果の capability 集合と欄表は、borrowed operand が指す place の token の欄表から、operand の capability path をたどって得る。
これにより共有参照の capability を保持するが、新しい loan として再束縛することはない。
借用の payload 自身がさらに借用を含む形は、内側の参照を再束縛する規則が無いため `E-BOR-014` で落とす。
借用の所有者は lifetime と region の上限制約から引き当てるため、値の側へ新しい token の台帳を置かない。

`(Assign c v)` は capability が指す先へ値を書き込む。 [REQ: BOR-004]
対象は可変借用でなければならない。
共有借用は `E-BOR-015`、借用でない値は `E-BOR-019` で落とす。
対象の型が所有値を含むときは `E-BOR-021` で落とす。
書き換えの前の値を捨てる仕組みが要るためであり、`OwnershipPolicy` の段へ送る。
`Let` の宣言型が `Owned` のとき、`bound` が計算した値をそのまま place へ載せる。 [REQ: OWN-005]
`resource` と `Move` 以外の項が計算した値も載せられるため、`Eliminate` で計算した `Record` を名前から借用し、`ProjBorrow` と `Assign` へ続ける合成経路を書ける。
載せる値の型に借用が入る形は `E-OWN-022` で落とす。
place へ載せた後は借用の所有者を追う手立てが無く、所有者より長生きする借用を作れるためである。

右辺の型 `τ_v` は、書き込み先の payload の型 `τ_t` と `tag-compat?` で両立しなければならない。
両立しない右辺は `E-BOR-022` で落とす。

Union の slot の値は tag で成分を表すので、`τ_t` が Union なら、tag を持つ Union の値をそのまま格納してよい。
tag を持たない値は `tag-compat?` を満たさないため、Union の slot へは書き込めない。
書き込みには `UnionInject` で tag を付けた値を渡す必要がある。
Surface に代入構文はなく、elaboration は `Assign` を生成しない。
Core の合流は tag の無い欄の型から Union を作らないので、`{ f : mut (Union τ_1 τ_2) }` の欄の値は実行時にも Union の値であり、成分ごとの record に分かれていない。
したがって、書き込む値を Union の各成分と照合する必要は無い。

`Assign` の結果は `Unit` である。
Ω も θ も動かない。

`Assign` と `Reassign` は異なる更新である。 [REQ: SCP-001]
`Assign` は借用した designator が指す field を書き換えるが、`Reassign` は借用を経由せず、`mut` binding が指す slot 自体を差し替える。
右辺が正常に完了する `Reassign` の結果は `Unit` であり、`H` の slot とその現在の view を原子的に更新して `Ω` と `θ` は動かさない。
右辺が `Never` なら `Reassign` も `Never` となり、slot、view、`Ω`、`θ` を更新せず、Mutation row も加えない。
そのため `Reassign` は借用の capability や Ψ の借用記録を新たに作らない。
`mut` binding は `Owned` と借用を型に持てない。`MutSlot` は読み出しと `Reassign` の target にだけ現れ、Borrow、BorrowMut、Move、pointer 生成の被演算子にはならない。

## 13. 使用の判定

使用の要求は、根の place `w`、field path `fp`、操作の種類、起点の集合 `source` の 4 つを持つ。 [REQ: BOR-004]
操作の種類は `read`、`assign`、`move` の 3 つである。

`source` は、その使用が経由した capability の α の集合である。
借用を経由しない使用、つまり `Move`、`Drop`、place への直接の読み書きでは空集合である。

`source` は借用の型から求める。
`(Borrowed τ ρ)` と `(BorrowedMut τ ρ)` の `ρ` を起点にし、合流した α をその合流が受け取った分岐の ρ へ置き換える。
置き換えは葉まで再帰する。
合流した α は「この α は分岐のどれかである」を表すため、自分自身を残さず分岐の側へ置き換える。

射影結果の α は親の mode と射影の位置で決まる。
共有の親からの射影は親の α を共有する。
可変の親から値位置に作る射影は新しい α を採り、子の寿命は射影の節点を包む最も内側の `Scope` の region である。
その子の capability は親の capability に field label を足したものであり、子の mode に応じた判定要求と、親を同じ path で停止する項目を登録する（§5、§11）。
`R-ProjBorrowMut` は `ProjBorrowAt` の注釈にある region を結果へ置く。
可変の親からの値位置の射影では、この注釈が結果の寿命を定める。

`Read` の operand と `Assign` の target にある place 位置の射影は例外であり、可変の親からでも親の α を共有する。
この形は射影先の path への使用要求だけを出し、子の借用や停止を作らない。
したがって、射影の直後に消費する place view は親と α を共有しても alias を残さない。
place 位置とは、`Read` の operand または `Assign` の target にある `ProjBorrow` と、その operand をたどった `ProjBorrow` chain の全節点を指す。
`Span` は剥がして判定し、chain は `ProjBorrow` 以外の節点で終わる。
`Eliminate` の scrutinee など、それ以外の位置は値位置である。

`source` が空集合の使用は、重なる借用が生きているだけで拒む。

`source` が空でない使用は、まず起点の借用が停止していないかを見る。
停止した借用を経由した使用は、その借用が再開するまで許さない。

停止していなければ、次のすべてを満たす借用があるときに拒む。

1. その借用の capability が使用の capability と重なる。
2. その借用の α が `source` に入っていない。
3. その借用の α を親とする停止した項目が `source` の中に無い。
4. 操作が `read` なら借用の mode が `mut` であり、`assign` と `move` なら mode を問わない。

この 4 条件とは別に、variant に依存する view を保護する。
Assign の capability `(w fp)` に対し、現在の lexical scope にある束縛またはその欄ごとの capability 表が、同じ根 `w` の capability `(w fp')` を運び、`fp` が `fp'` の厳密な接頭辞で、`fp'` の残りに variant に依存する segment が含まれるなら、その Assign は `E-BOR-025` で拒否する。
この保護は view を運ぶ束縛の lexical scope が終わるまで続き、view の最後の使用では終わらない。

値位置の `ProjBorrow` は、親の α と射影先の path に対する読み出し要求を出し、子の借用と停止を登録する。
同じ節点が出した読み出し要求は、同じ point にある借用との重なりに数えず、その point では停止中の親の使用判定にも含めない。
place 位置の `ProjBorrow` はこの読み出し要求だけを出し、借用の項目と停止は登録しない。
共有の親からの射影では子も親の α を使うが、可変の親から値位置に作る射影では新しい α を使う。
このため、停止中の親を経由する読み書きは通常の起点停止判定で拒否され、子の使用はその子の capability と停止関係に基づいて判定される。

枝内で作る借用の下限は `region-at/branch` が返す region である。
対象は `Borrow`、`BorrowMut`、`Reborrow`、値位置の `ProjBorrow` と §11 の可変 binder であり、内側の `Scope`、owner-body、入れ子の分解またはその枝の region があれば、その region が下限になる。
関数の可変仮引数を親とする分解 binder は新しい寿命変数を持たず、その親子関係と要求は既存の延期処理に従う。

出口制約の追跡対象は、callable 本体の境界を越えない枝の部分木で生成した直接の借用の α、可変 binder の α、およびそこから派生する α である。
派生には `Reborrow` と値位置の `ProjBorrow` による子、ならびにそれらを合流元に持つ寿命変数を含む。
合流元は寿命変数の合流関係を推移的に展開して求める。
追跡対象かどうかは下限 region の同一性ではなく、借用を生成した point の枝への所属で決める。

ここで分解 E の外へ値が出るとは、値を作った式の point に E が含まれ、値の行き先が E の部分木に含まれないことをいう。
値を作った式を含み、その行き先が部分木に含まれない各 E に対して、値の型に現れる追跡対象の α に `(contains α ρ_outer)` を課す。
`ρ_outer` は、分解 E の region の親である。
入れ子の分解では、間に `Scope` または owner-body が無い限り、外側の分解の region がこの親になる。
追跡対象でない α は、この制約の対象にせず、従来の下限に従う。

`Eliminate` と `UnionEliminate` 自身の結果型にある追跡対象の α は、当該分解の region の親を下限とする。
`Perform (Return ...)` の payload は、型検査が保持する handler stack のうち操作が一致する最初の `Handle` の point を行き先とし、一致する handler が無ければ関数の境界を行き先とする。
`Leave` の adapter も `Return` として扱う。
`Yield` の観測値は行き先を定めず、分解の部分木から出る値として扱う。
`Reassign` の右辺は、target の名前が束縛される本体を行き先とする。
その束縛 point を特定できない場合は、行き先を定めず分解の部分木から出る値として扱う。
`Assign` の右辺は、place の根を一意に特定でき、その束縛型が借用型でなければその束縛子を行き先とする。
根または束縛型を特定できない場合と、束縛型が借用型である場合は、行き先を定めず分解の部分木から出る値として扱う。
`Curry` の借用引数と `Lam`、`RecurVal` が捕捉する借用は、行き先を定めず分解の部分木から出る値として扱う。
`Apply` の実引数も行き先を定めず分解の部分木から出る値として扱う。
`Apply`、`RegionApp`、`Recur` の latent row にある `Return` は前述の handler または関数境界を行き先とし、`Yield` は分解の部分木から出る値として扱う。
これらの呼出し式の結果型には独立の出口制約を出さず、結果を外へ渡す経路で判定する。
`AddressOf` の operand は raw pointer に借用の α が現れないため、行き先を定めず分解の部分木から出る値として扱う。
`Handle` は独立した出口制約を出さず、捕捉する `Return` の行き先を定める。

`Lam` と `RecurVal` の借用捕捉は `E-BOR-011`、`Curry` の借用引数は `E-BOR-020` で出口制約より前に拒否される。
`Reassign` の借用型 `mut` 束縛は `E-VAR-009` で、`Owned` place への借用格納は `E-OWN-022` で、借用型を根に持つ place への `Assign` は `E-BOR-006` で、それぞれ出口制約より前に拒否される。

分解の region は分解節点の評価が完了すると退場し、分解の部分木内の使用はその退場前にある。
分解後の point が部分木の外にあり、point の順序を比較でき、分解節点がその point より前にある場合に限り、その使用を退場後として扱う。
`Handle` や `Recur` の制御順序の境界を越えて比較できない場合は、退場後とは扱わない。

## 14. 未回収

1. 閉包と部分適用が運ぶ region と借用の provenance。
捕捉した借用を返す関数、`Curry` と `CurryVal` が借用の現れる署名を受けること、
外側の仮引数の借用を捕捉する入れ子の `Lam`、
`RegionApp` の実引数が `RParam` で、束縛する `RegionLam` と適用位置のあいだに
`Lam` の境界が挟まる形の 4 つを本サイクルでは認めない。
いずれも所有者と起点を呼出しの出現から運ぶ手立てが無いためである。
前の 3 つは既存の関数境界の診断で落とし、最後の 1 つは `E-REG-003` で落とす。
Phase 4 以降で扱う。
本サイクルでは、narrowing で借用を含む残余欄が record または関数の境界を越える経路を、RSD による物理除去か拒否で閉じる。
`RegionLam` が自身の binder に束縛されない借用を含む環境項目を捕捉する経路も `E-BOR-027` で拒否する。
この二つは、上に列挙した closure と部分適用が運ぶ借用 provenance の未回収を解決しない。
2. 借用規則の backend 写し先。Phase 2 以降で扱う（`BAK-010`）。

3. 性質 8 の bounded 検査が覆わない範囲。
関数境界を含む項（BOR-007）と variance と subtyping を含む項（VAR-004）を本サイクルの生成器は作らない。
どちらも生成域を広げる作業であり、要件そのものの規定は G5 で終えている。
ただし `Recur` は生成域を広げるだけでは足りない。
R-RecurUnfold が本体の借用値を複製するため、oracle が複製された出現を承認済みの形へ照合できる必要がある。
Phase 4 以降で扱う。
BOR-003 も性質 8 の検査の外にあるが、未回収ではない。
oracle は region の解に対する置換可能性を判定しないので、生成域を広げても覆えない。
置換可能性は `region-test.rkt` と `solver-parity-test.rkt` が担う。
4. 整数リテラルを含む項が性質 8 の検査域から外れること。
oracle は所有値の place を裸の自然数として見るため、同じ値の整数リテラルと区別が付かない。
区別を付けるには sidecar が place を運ぶか型検査を参照する必要があり、後者は oracle が静的側の判定を呼ばない方針と衝突する。
本サイクルの生成器は整数リテラルを 1000 以上に限って衝突を避けるので、小さい整数を含む項は検査を通らない。
余分な対応は provenance を上位集合にするだけであり、oracle の fail-closed な消費のもとでは偽の合格を生まない。
Phase 未定である。
5. variant に依存する view の保護を最後の使用で終える精度。
現行の保護は束縛の lexical scope の終わりまで続く。
その精度を上げるには使用区間の解析が要る。
これは §4 の借用 region を最も内側の Scope にする lexical な近似とは別の近似である。
回収時期は、BOR-003 の置換先として想定する control-flow と last-use による region 推論を導入する段階と同じとする。
分解 binder 由来の借用も、binder の最後の使用後を含めて枝 region 全体で親の対応する欄を停止する lexical な近似である。
最後の使用で停止を終える精度は control-flow と last-use による region 推論を導入する段階で回収する。
停止は binder の path に限るため、親の別の欄はこの近似の対象にならない。
6. 共有の子が生きている間に親を通して `Read` する形を拒む過剰な制約。
可変の親からの射影や共有 `Reborrow` の子が生きている間、現行の停止判定は子の mode によらず親を通す `Read` を拒む。
子の mode と使用の種類を考慮して停止中の親の使用を判定する段階で、許可条件を精密化する。
分解 binder の停止も親の対応する欄を通す `Read` を拒むため、この過剰な制約は分解 binder にも及ぶ。
7. 一時式の `Reborrow` を同じ `Scope` 内で直ちに使い切っても、`Scope` の退場まで生存させる過剰な制約。
暗黙の短い再借用を扱い、first-class な借用値の region を実際の使用範囲に合わせて定める段階で回収する。
8. 仮引数を親とする分解 binder の寿命変数と、実引数・仮引数の escape 精度。
callable summary が分解 binder の親、相対 path、寿命および escape 条件を呼出し側へ運び、仮引数を親とする binder を実体化する必要がある（BOR-001、BOR-002、BOR-007）。
`RegionLam` 本体で局所 owner を region 仮引数で借り、その分解 binder を `Reborrow` して読み切る形では、局所射影の借用と region 仮引数の借用が deferred summary を経て最終の `check-borrows` で衝突し、`E-BOR-003` になる。
この形も callable summary で親、相対 path、寿命および escape 条件を呼出し側へ運ぶ段階で回収する。
9. `E-BOR-006` のうち、仮引数の入れ子の path が呼出し時に確定する形。
所有者と path を呼出し側で確定できるようにする必要がある（BOR-006、BOR-007）。
10. `E-OWN-022`：借用を含む計算値を `Owned` の slot へ格納する形。
回収には、計算値の place 化を定める OWN-005 の範囲を借用を含む値へ明示的に広げる必要がある（OWN-005、BOR-001、BOR-006）。
11. `E-VAR-009`：借用型を持つ `mut` 束縛への再代入。
回収には、旧借用の終了と再代入後の新しい所有者の寿命を扱う必要がある（SCP-001、BOR-002）。

所有資源が leaf に対して token の台帳を持つのに対し、借用と region には同じ機構を置かない。
token は所有権の移動と回収を一度だけに保つための同一性であり、回収の主体が値の側にあるときに必要になる。
借用は回収の主体を持たず、region の順序制約が生存期間を決めるので、同一性を別に持たせても新しい不変条件を得られない。
借用の重複と escape は BOR-001 と同じ形の region の上限制約で拒否でき、この制約は所有者を追う走査と region の順序だけで閉じている。

本節に項目を足したときは、`requirements.md` §4 の申し送り表へも 1 行追記する。

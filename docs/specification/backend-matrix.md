# Portable Racket backend matrix

Typed Core を Portable Racket へ写す規約と、backend ごとの feature 対応を定める。

## 1. 位置づけと不変条件

Portable Racket は意味論を決定しない。
Typed Core verifier を通過した意味論を実行形式へ写像するだけである。

この不変条件から 2 つが従う。
目標項は型を担がない。
型に依存する規則の選択は、写像の時点で静的に解く。

## 2. Portable Racket profile

ホワイトペーパー §13.3.1 の項目のうち、Phase 0 で採用するものと除外するものを分ける。

| profile 項目 | `PR` の形 |
|---|---|
| lambda / application | `PLam`、`PClosure`、`PApp` |
| let / letrec | `PLet`、`PLetOwned`、`PLetrec` |
| immutable record | `PRec`、`PProj` |
| explicit tagged ADT | `PTagged`、`PMatch` |
| primitive arithmetic and comparison | `PPrim` |
| explicit closure environment | `PClosure` の `penv` |
| explicit Effect dispatcher | `PEffect`、`PInstall`、`pop` |
| explicit recur / suspend / yield runtime calls | `PRuntime` |
| explicit scope-exit / finalizer runtime calls | `PScopeExit`、`PRuntime drop`、`PRuntime move` |
| fixed-width integer / bit-operation runtime shims | `PPrim` の shim 名（§10） |

除外する項目は 3 つである。

| 除外項目 | 理由 |
|---|---|
| immutable vector | Phase 0 の Typed Core に vector 型が無い |
| module import / export | Phase 0 の Typed Core は単一の項であり module 境界を持たない |
| source-map metadata | 全構成子に metadata を付けると構文が倍の大きさになる。保存の言明にも要らない |

3 つとも Phase 0 で狭めた範囲であり、§12 に記録する。

資源獲得 `tz:acquire` は `PPrim` の側に置く。
源の `δ` が `(resource n)` を純関数として返し、資源表も状態表も触らないためである。
profile の行に対応が無いのは、ホワイトペーパー §13.3.1 が資源獲得を runtime 呼び出しとして挙げていないからである。

`PRuntime` を `PPrim` から分けるのは、意味論の性質が違うためである。
`PPrim` は `δpr` で値を返すだけで、機械の状態を触らない。
`PRuntime` は継続と資源表を触る。
両者を同じ構成子にすると、§6 の Effect 保存で runtime 呼び出しの集合を構文から取り出せなくなる。

## 3. 目標言語 PR の構文

目標言語 `PR` は `G2m` の拡張ではなく独立した言語として定義する。
`extend-language` で延ばすと `τ` と `ε` と `Q` が目標言語へ漏れて入り、§1 の不変条件が言語定義の時点で崩れる。
代償として `pl` と値の literal の定義が源と重複する。

```
px   ::= 変数
pnm  ::= shim / Effect 境界の名前
prt  ::= move | drop | yield | suspend | curry
ptycode ::= 型に由来する dispatch tag
pp   ::= 場所（自然数）        pn ::= 資源識別子（整数）
pl   ::= 整数 | unit | 文字列

pop  ::= (return pnm ptycode)

penv ::= ((px pv) ...)
pv   ::= pl
       | (PClosure penv (px ...) pc)
       | (PTagged K pv ...)
       | (PRec ((label pv) ...))
       | (PResource pn)
       | (PPlace pp)

pbr  ::= (K (px ...) -> pc)
pc   ::= pv | px
       | (PLam (px ...) pc)
       | (PApp pc pc ...)
       | (PLet px pc pc)
       | (PLetOwned px pc pc)
       | (PLetrec px pc pc)
       | (PTagged K pc ...)
       | (PRec ((label pc) ...))
       | (PProj pc label)
       | (PMatch pc (pbr ...))
       | (PPrim pnm pc ...)
       | (PEffect pop pc)
       | (PInstall pop pc pc)
       | (PRuntime prt pc ...)
       | (PScopeExit (pp ...) pc)
       | (PError pp)
```

`pc` の形の数は源の `c` より少ない。
`Perform` と `Handle` が `PEffect` と `PInstall` へ、`Yield` と `Suspend` と `Move` と `Drop` と `Curry` が `PRuntime` へ潰れる。

`ptycode` は `pop` の中にだけ現れる。
型そのものではなく型から作った記号であり、目標側は等号でしか使わない。
`PInstall` の handler 選択が `pop` 全体の等号で決まるので、境界名だけでは足りない。

評価文脈は `PF`、`PG`、`PE` の 3 つを別々に展開する。
`PF` の句を貼ったうえで `PInstall` の句だけを足す書き方では、`PE` が `PInstall` の本体の内側へ届かない。
`PRuntime` の評価位置は源の評価文脈 `F` と同じ 4 本に限る。
総称の `(PRuntime prt pv ... PF pc ...)` を置くと `yield` の継続と `suspend` の本体まで掘れてしまい、後続が 2 つ残って §4 の決定性が壊れる。

## 4. 目標機械と観測

config は源と同じ 5 つ組である。

```
pconfig ::= (pcfg pc PH PΩ θ)
PH ::= ((pp pv) ...)      PΩ ::= ((pp pstate) ...)
pstate ::= Available | Moved | Dropped
θ ::= (event ...)         event ::= (obs pv) | (fin pp)
```

`event` の形を源の `G1m` と揃えるのは、観測抽出を同型に書けるようにするためである。
`obs-eval-pr` は源の `obs-eval/using` と同じ構造を持ち、観測列と終端種別の対を返す。
終端種別は `value`、`ownership-error`、`perform`、`stuck`、`observed`、`timeout` の 6 つである。

`-->pr` は決定的である。
観測に基づく評価器は、重複除去後に 2 つ以上の後続 config が残ると error を投げる。
非決定な遷移を残すと、保存の言明を確かめる装置そのものが使えない。

規則は 20 本である。
源の `-->g2` の 25 本を基準に、`R-CurryVal` と `R-ApplyCurry`、`R-RecurBind` と `R-RecurUnfold`、`R-Let` と `R-LetB`、`R-LetOwned` と `R-LetOwnedB` をそれぞれ 1 本へ畳んで 4 本減り、`R-Discharge` が目標側に規則を持たないので 1 本減る。

| 源の規則 | 目標の規則 | 差分 |
|---|---|---|
| `R-Delta` | `R-PR-Prim` | 源の名前ではなく shim 名で `δpr` を引く（§10） |
| `R-Beta` | `R-PR-App` | `penv` の束縛も代入する。arity 不一致は stuck |
| `R-CurryVal`、`R-ApplyCurry` | `R-PR-Curry` | 2 本が 1 本になる。中間値を作らず `penv` を延ばす |
| `R-Let`、`R-LetB` | `R-PR-Let` | 型の判定が消える。束縛様相も落ちる |
| `R-LetOwned`、`R-LetOwnedB` | `R-PR-LetOwned` | 型ではなく構成子で選ぶ |
| `R-Eliminate` | `R-PR-Match` | なし |
| `R-Proj` | `R-PR-Proj` | 可変性が落ちているので label の一意性の側条件だけが残る |
| `R-Discharge` | なし | Proof は実行時に意味を持たない |
| `R-RecurBind`、`R-RecurUnfold` | `R-PR-Letrec` | 2 本が 1 本になる。展開は `R-PR-App` との合成になり、呼び出しごとに 1 段増える |
| `R-Move` | `R-PR-Move` | なし |
| `R-MoveError` | `R-PR-MoveError` | なし |
| `R-Drop` | `R-PR-Drop` | なし。状態表は触らない |
| `R-Yield` | `R-PR-Yield` | なし |
| `R-Suspend` | `R-PR-Suspend` | なし |
| `R-ScopeValue` | `R-PR-ScopeValue` | なし |
| `R-ScopeAbort` | `R-PR-ScopeAbort` | なし |
| `R-ScopeError` | `R-PR-ScopeError` | なし |
| `R-HandleValue` | `R-PR-InstallValue` | なし |
| `R-HandleReturn` | `R-PR-InstallEffect` | `pop` 全体の等号で選ぶ |
| `R-HandleSkip` | `R-PR-InstallSkip` | 同上 |
| `R-HandleError` | `R-PR-InstallError` | なし |

`finalize-pr` は源の `finalize` と同じ働きをする。
管理下の場所を `Dropped` にし、`(fin pp)` を trace へ足す。
足す順序も源と揃える。
§6 の観測一致が順序まで比べるためである。

`PLam` を単独で還元する規則は置かない。
`PLam` は `PLetrec` の右辺と `PInstall` の handler にしか現れず、どちらもその位置で規則が消費する。

この対応表は `model/redex/tests/rule-crosscheck-test.rkt` が機械照合する。
源の規則名の集合は `machine.rkt` の `-->g1/rules` と `-->g2/rules` から取り、対応表がその集合をちょうど覆うことを検査する。
対応表の値の側が `pr-machine.rkt` の `-->pr/rules` と一致することは `model/redex/tests/pr-machine-test.rkt` が検査する。

## 5. lowering 関係と表現規約

lowering は Racket 関数として書く。 [REQ: BAK-001]

```
(lower c backend) → (values 'ok pc) | (values 'capability diag)
```

metafunction では失敗を `undefined` 以上に表せず、診断値を返せない。

公開する `lower` は正典表を引数に取らない。
表を任意に差し替えられる形を production の入口に置くと、「表が唯一の定義元」という原則が崩れる。
診断機構の検査には非対応を含む profile が要るので、表の注入は `lower/with-matrix` という別の入口に分ける。

型に依存する規則の選択は写す時点で解く。
源には `R-Let` と `R-LetOwned` が所有型かどうかで分かれる組が 1 つある。
目標言語は型を持たないので、この判定は実行時に解けない。
lowering が型を見て `PLet` と `PLetOwned` のどちらへ写すかを決め、目標項にはその結果だけが残る。
これがホワイトペーパー §11 の「Portable Racket は意味論を決定しない」の具体形である。
型に依存する選択が目標言語に残っていれば、目標言語が意味論を決めていることになる。
判定が漏れていないことは、目標項に型が現れないことで確かめる。

源の記号はそのまま写さない。
源と目標では literal の除外集合が違うため、素通しにすると `lower` が全域でなくなる。
種類ごとに接頭辞を付けて写す。

| 源の記号 | 接頭辞 | 例 |
|---|---|---|
| 変数 | `v:` | `x` → `v:x` |
| ADT tag | `k:` | `Some` → `k:Some` |
| record の field 名 | `f:` | `a` → `f:a` |
| Effect 境界名 | `b:` | `b` → `b:b` |
| 型符号 | `ty:` | `Int` → `ty:Int` |
| shim 名 | `tz:` | `add` → `tz:add` |

像は最初の `:` で一意に分かれ、目標側の literal に `:` を含むものは無いので、写しは単射である。
型符号は型同値で正規化しない。
源の handler 選択が Effect ラベル全体を構文の等号で比べるので、正規化すると源が別物として扱う 2 つのラベルを目標側が同一視する。

**表現規約** `repr` は型から目標値の形への写像である。

| 型 | `repr` |
|---|---|
| `Int` | 整数リテラル |
| `Bool` | `(PTagged k:true)` と `(PTagged k:false)` |
| `Unit` | `unit` リテラル |
| `String` | 文字列リテラル |
| `Never` | 値を持たない |
| `Res` | `(PResource pn)` |
| `(List τ)`、`(Option τ)`、`(Result τ τ)` | `PTagged` |
| `(Owned τ)` | `repr(τ)` と同じ |
| 関数型 | `PClosure` |
| 型情報 | `(PTagged typerep)` |
| 証明 | `(PTagged proof)` |
| record 型 | `PRec` |
| 非信頼型 | `(PTagged uval repr(τ))` |
| 篩型 | `(PTagged rval repr(τ))` |
| 合併型 | 成分のいずれかの `repr` |
| 交叉型 | 成分すべての `repr` |

所有を `repr(τ)` と同じにするのは、所有が静的な区別であり実行時表現に現れないためである。
型情報と証明を消去するのは、両者が実行時に意味を持たないためである。
非信頼型と篩型の tag を残すのは、源の `δ` が両者を実行時に区別しているためである。
篩型の tag は残すが、証明の値そのものは消去する。

合併型と交叉型の行は、成分の行を分配して定める。
Phase 0 の Typed Core が両者を持つので、`repr` を全域にするために必要である。

## 6. 保存の言明

BAK-001 は「Typed Core の型と Effect と評価順を保存する」と定める。 [REQ: BAK-001]
型を持たない目標言語の上でこれを言い直し、3 本に分ける。

**型の保存**を表現規約への適合として述べる。

```
⊢ c : τ かつ (lower c) が成功したとき
目標項の評価結果が値であれば、その値は repr(τ) に属する。
```

**Effect の保存**をラベル種別の一致として述べる。

源の Effect ラベルは型を含むが、型を持たない目標項から型そのものは復元できない。
一方で `(Return b τ)` は `(return b:b ty:τ)` として目標側に残るので、この 1 種のラベルについては型成分の情報が保たれる。
種別への写像は次のとおりである。

| 源のラベル | 種別 |
|---|---|
| `(Return b τ)` | `(return b:b ty:τ)` |
| `(Yield τ)` | `yield` |
| `Suspend` | `suspend` |
| `Partial` | `partial` |
| `Compile` | `compile` |
| `Own` | `own` |

`return` の種別をラベル全体にするのは、源の handler 型付けがラベル全体を差し引くためである。
境界名だけで差し引くと、同じ境界名で型が違う handler が源側では残す Effect を消してしまう。
目標側の `R-PR-InstallSkip` もラベル全体を比べるので、3 者が揃う。

`(Yield τ)` の型成分だけは落ちる。
写し先の `PRuntime yield` が型符号を担がないためである。
これは Phase 0 で狭めた範囲であり、§12 に記録する。

目標項に残る Effect の種別は、構文から抽出する。
値の形と `PLam` の寄与は空である。
関数の本体の Effect は潜在行に属し、現在行には立たない。
本体を和に含めると、関数を作っただけで Effect が立つ。
適用の形では、適用先が構文上の関数値のときにその本体の種別を現在行へ足す。

言明は 2 段になる。

```
⊢ c : τ / ε かつ (lower c) が成功したとき

(1) 目標の残差 ⊆ kinds(ε)                       ; 全域
(2) 目標側で潜在 Effect が構文から取れ、かつ源側の宣言潜在行が
    本体の実効果と等しいとき、両者は一致する
```

`ε` は Typed Core の型付け判定が返す行であり、表層構文から Typed Core への elaboration が返す行ではない。
elaboration は型宣言の形にコンパイル時の Effect を足すが、Typed Core の型付け規則はそれを立てない。
上の種別の表の各行の根拠を Typed Core の規則に置いているので、比べる相手も Typed Core の行でなければ食い違う。

(1) は「目標が型に無い Effect を作らない」である。
`ε` は実際に起きる Effect の上界なので、この向きの包含が全域で言える。

(2) に条件が要るのは 2 つの理由による。
目標側では、適用先が変数のとき潜在 Effect が構文から取れない。
源側では、宣言した潜在行が本体の実効果より広い関数が合法である。
潜在行を目標項に持たせればこの差は消えるが、目標項が型情報を担ぐことになりホワイトペーパー §11 に反する。

**評価順の保存**を観測 trace の一致として述べる。

```
⊢ c : τ / ε かつ (lower c) が成功したとき
源と目標を同じ観測深度で評価して、観測列と終端種別が対応する。
観測列の対応は、源の観測値を lowering の値写像で写した列が目標の観測列に等しいことである。
```

`ε` に制限を置かない。
観測評価器は未処理の Effect に当たったとき終端種別 `perform` を返すので、Effect が残る項でも観測列を比べられる。

目標側の fuel は源と同じ値から始め、終端種別が `timeout` である限り倍にする。
`Recur` を含む項は目標側の展開に静的な上界を持たないため、固定比では源が観測に達し目標が `timeout` になる項を偽の失敗として数えてしまう。
上限回数に達しても `timeout` なら、その項について言明を確かめずに捨てる。
捨てた項の数は検査の出力に載せ、捨てた項が比べた項の半分を超えないことを確かめる。

## 7. feature 対応表と support の 3 値

feature ごとに、2 つの backend での実現方法を `native`、`shim`、`unsupported` の 3 値で宣言する。
表は `model/redex/backend-matrix.rkt` が唯一の定義元であり、検査規則は表の行から生成する。

（conformance suite の義務との対応は G3d で足す。）

## 8. capability diagnostic

非対応 feature に当たったとき、写像は近似的な結果を出さず capability diagnostic を返す。 [REQ: BAK-003]

診断は feature-id、backend、理由の 3 つを持つ。
診断を返した入力について、写像は目標項を返さない。
部分的な出力と診断を同時に返すことを禁じる。

診断 ID には feature に対応するものと、対応しないものがある。
後者は対応表に無い形に当たったときの fallback と、型符号を作れない入力に当たったときの fallback の 2 件であり、backend の能力の話ではないので support 値を持たない。

## 9. conformance suite の義務

（G3d で埋める。）

## 10. bit 意味論と算術 shim

算術と比較の primitive は、写し先で Host の演算を直接指してはならない。 [REQ: BIT-002]
写し先は Topazolite が定めた shim 関数の呼び出しである。
backend を差し替えても結果が変わらないことの根拠は、この一点にある。

模型が shim の意味論をどう実装するかは、これとは別の話である。
`Int` は任意精度整数なので、`tz:add` の意味論は Racket の `+` そのものである。
固定幅の切り詰めが意味論に入るのは Phase 2 以降の型追加後であり、そのとき shim の実装も変わる。

### 10.1 shim の意味論

目標機械の shim を、源の primitive と 1 対 1 で定める。
値の形と引数個数まで固定する。

| shim | 引数 | 結果 | 源の primitive |
|---|---|---|---|
| `tz:add` | 整数 2 | 整数の和 | `add` |
| `tz:sub` | 整数 2 | 整数の差 | `sub` |
| `tz:mul` | 整数 2 | 整数の積 | `mul` |
| `tz:lt` | 整数 2 | `(PTagged k:true)` または `(PTagged k:false)` | `lt` |
| `tz:le` | 整数 2 | 同上 | `le` |
| `tz:eq` | 整数 2 | 同上 | `eq` |
| `tz:acquire` | 整数 1 | `(PResource n)` | `acquire` |
| 上記以外の名前、引数個数の不一致、非整数の引数 | | 未定義 | |

`Bool` の結果が 2 つの tag になるのは、源の真偽値を写像が tag の符号化を通して写すためである。
目標機械が源の符号化に依存するのはこの 2 つの tag だけであり、両者が一致することをテストで固定する。
どちらかの tag を選ばざるを得ず、選んだ tag が写像の像と食い違えば分岐が選べない。

意味論が未定義の呼び出しでは規則が発火せず、項は stuck する。
源の primitive が同じ入力で不発火になるのと同じ扱いである。
引数個数の合わない適用は適用の側でも stuck するので、η 展開を経た正しい個数の呼び出しだけが shim へ届く。

### 10.2 feature の分割

7 件の shim に、名前ごとの feature-id を 1 つずつ与える。
表の `shim` 列は名前を 1 つだけ持ち、リストを置かない。
名前ごとに feature を分けるのはこの形を守るためであり、1 件を `unsupported` と宣言したときに他の名前まで閉じないためでもある。

| feature-id | shim | 表の要求 |
|---|---|---|
| `primitive-add` | `tz:add` | 両 backend が `shim`。`native` を許さない |
| `primitive-sub` | `tz:sub` | 同上 |
| `primitive-mul` | `tz:mul` | 同上 |
| `primitive-lt` | `tz:lt` | 同上 |
| `primitive-le` | `tz:le` | 同上 |
| `primitive-eq` | `tz:eq` | 同上 |
| `primitive-acquire` | `tz:acquire` | 両 backend が `shim`（`native` を禁じる検査の対象外） |

`native` を禁じる検査の対象は上の 6 件である。
資源取得を外すのは、BIT-002 が算術と比較の結果の同一性を言う要件だからである。
`tz:acquire` も `shim` だが、それは Host の資源表現を目標項へ持ち込まないためであり、別の理由による。

形の対応表は `PrimVal` の頭シンボルに `primitive-value` を割り当てる。
これは η 展開した closure を作る層であり、両 backend で `native` である。
名前ごとの feature は写像の内側でもう一度引く。
頭に算術の feature を割り当てると、算術を `unsupported` と宣言したときに、kernel primitive と trait primitive と資源取得の診断まで巻き込んで閉じてしまう。
`primitive-value` を閉じた対応表では 7 件すべての写しが診断になるが、粗い側へ倒れるだけであり、部分的な出力は返らない（§8）。

### 10.3 予約する feature

固定幅整数と `Bits<N>` は feature-id として表に予約する。
`semantic-test` 列は Phase 2 以降への延期とする。
Typed Core に対応する型が無いので、形の対応表の値域には現れない。

両 backend の support を `shim` と宣言する。
Racket の整数は任意精度であり、RacketScript の数値は倍精度浮動小数点数なので、固定幅の切り詰めをどちらの backend も native には持たない。
`native` を宣言すると BIT-002 と矛盾する。

予約した shim の名前は Phase 0 の shim 意味論に無い。
実装済みに見えると、対応する型が無いまま意味論を書いたことになるので、名前が未定義であることをテストで固定する。

### 10.4 Phase 0 で検査できる範囲

2 つである。
写し先が shim 名を指すことと、表が両 backend に `shim` を要求することである。

shim の意味論そのものが backend 間で一致するかは、ここでは確かめられない。
目標機械が 1 つしか無いためである。
一致は §9 の conformance suite が確かめる。

## 11. 要件対応表

（G3d で埋める。）

## 12. 未回収の範囲

（G3d で埋める。）

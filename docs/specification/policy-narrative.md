# Topazolite Policy Narrative 層仕様

**状態**：G2f 執筆版

**参照**：`draft/topazolite_whitepaper_draft_0.4.md` §2.1.5、§8.1、§15（以下、ホワイトペーパー）

**関連文書**：`core-calculus.md`、`trait.md`、`proof-search.md`、`proof-value.md`、`requirements.md`、`glossary.md`

## 1. 位置づけ

Policy はカーネルへ追加する新しい primitive ではない。
型検査、elaboration、Proof 探索などの方針を実装する標準 Narrative trait であり、二つの予約 Narrative から派生する。

G2f は、既存の方針実装を `policy-wrap` で包み、方針の origin と返却値を検査する。
方針の規則そのものは変更しない。

## 2. policy 行

**policy 行**は、名前、origin、親の集合、宣言操作、所有モジュールを持つ。

```text
(name origin parents (operation ...) owner)
```

G2f の `policy-table` は次の五行を持つ。

- `RowPolicy` は `merge-record-types` を `typing.rkt` へ登録する。
- `VariancePolicy` は `compat?` を `compat.rkt` へ登録する。
- `TraitResolution` は `project-goal` と `resolve-candidates` を `search.rkt` へ登録する。
- `ProofSearch` は `discharge?` を `search.rkt` へ登録する。
- `Normalization` は `normalize-type` を `type-equiv.rkt` へ登録する。

`BindingPolicy` と `OwnershipPolicy` の行は置かない。
これらの方針を実装するサイクルで行を追加する。

## 3. 二つの予約 Narrative

Policy の origin は次の形を取る。

```text
(Derived (Reserved o-language-narrative) (Policy name))
```

origin の `Derived` は親を一つだけ持つため、origin 上の親は `o-language-narrative` に固定する。
これは `o-type-narrative` を派生関係から外すことを意味しない。
policy 行の `parents` 欄は `(o-language-narrative o-type-narrative)` を保持し、二つの予約 Narrative からの派生を表す。

`policy-origin-ok?` は、origin の形、policy 名、二つの親の集合、および R0 の実値を検査する。
R0 では `o-language-narrative` が `languageNarrative` に、`o-type-narrative` が `typeNarrative` に束縛されていなければならない。

[REQ: POL-001]

## 4. trusted root を増やさない構成

Policy 層が R0 へ追加する予約 origin は `(o-language-narrative languageNarrative)` の一件だけである。
`o-type-narrative` は既存の R0 entry である。

Policy に固有の R0 id を与えると、それは `Reserved(id)` として proof issuer の照合対象になり、新しい trusted root になる。
各 `proof-issuer-ok?` 節が R0 の実値を引くため、Policy origin は予約 Narrative を親に持つ `Derived` として表現し、固有 id を持たない。

この構成上の制約に加えて、テストは予約 Narrative の実値を別の値へ束縛した R0 を拒否する。
id の綴りだけが一致していても、R0 の値が一致しなければ Policy origin は正当にならない。

## 5. `policy-wrap` の契約

各所有モジュールは素の実装を `/impl` という非公開 binding に置き、公開名を `policy-wrap` の返却値へ束縛する。

`policy-wrap` は登録時に、policy 名が宣言されていること、操作名がその policy 行に含まれること、policy 行の形が正しいことを検査する。
呼び出し時には `call-with-values` で実装の返却値をリストへ集め、所有モジュールの検査述語へ渡す。
検査が偽なら error を送出する。
偽を返却値として返すと、操作が返した失敗値と検査失敗を区別できないためである。

検査述語は所有モジュール側に置く。
`policy.rkt` は型、row、探索を知らず、所有モジュールから `policy.rkt` への依存だけを持つ。
包み忘れ検査は五つの所有モジュールを静的に読む `policy-check.rkt` に置く。

## 6. 返却値の検査

各操作の検査述語は、操作の返却値が満たす不変条件を確認する。
操作が規則上の fail-closed 値を返す場合、その値は成功した検査として扱う。

### 6.1 Normalization

`Normalization.normalize-type` は、`#f` を正規化できない型の fail-closed 返却として受理する。
`#f` 以外の返却値には、正規化をもう一度適用しても同じ値になる冪等性を要求する。

### 6.2 VariancePolicy

`VariancePolicy.compat?` は常に boolean を返す。
二つの型が `type-equiv?` で同値なら、互換の結果は必ず真でなければならない。
同値でない二型の結果には、この Policy 層は制約を課さない。

G2f の VariancePolicy は判定規則そのものを差し替えない。
推移律を Policy 層の検査へ移す機構も持たない。

### 6.3 RowPolicy

`RowPolicy.merge-record-types` の成功返却は、label が一意で昇順の `Record` と、well-formed な witness 列である。
`(Record ())` は共通 field が存在しない合流の成功返却であり、検査を素通りさせない。

`#f` と空 witness 列の組だけを、正規化失敗に対する fail-closed 返却として受理する。
現状の well-formed な入力では、merged row の型が正規形で label が一意なため、この返却経路は到達しない。

### 6.4 TraitResolution

`TraitResolution.project-goal` の返却候補は、goal と一致し、well-formed で coherent でなければならない。
空リストは候補が存在しない fail-closed 返却として受理する。

`TraitResolution.resolve-candidates` は、`Resolved` の Proof が候補集合に実際に含まれ、`Ambiguous` の Proof 列が二件以上で重複しないことを検査する。
`Absent` は候補がない fail-closed 返却として受理する。

### 6.5 ProofSearch

`ProofSearch.discharge?` が真を返すとき、計算クラスは `Finite` または `Productive` で、探索結果は `Resolved` でなければならない。
偽の返却は fail-closed な探索結果として受理する。

[REQ: POL-002]

## 7. 包み忘れの検出

`policy-check.rkt` は、policy-table が宣言する `(policy . operation)` の集合と、各所有モジュールが `policy-wrap` で登録した集合を比較する。
二つの集合が一致しなければ、モジュールの読み込み時に失敗する。

宣言されていない操作が登録される場合も同じ検査で失敗する。
これにより、宣言側だけを増やした包み忘れと、登録側だけを増やした未宣言操作を区別せず拒否できる。

## 8. G2f で狭めた範囲

G2f は Policy の差し替え API を導入しない。
`BindingPolicy` と `OwnershipPolicy` の行も置かない。
これは実装上の範囲であり、ホワイトペーパー §2.1.5 の Policy Narrative の意味を置き換えない。

G2f の VariancePolicy は同値な二型の互換だけを検査する。
ホワイトペーパーの変性規則全体を回収済みとは記録しない。

RowPolicy の `merge-fields` が field 単位の `#f` に脱落と正規化失敗の二役を負わせていた状態は、G2g の ROW-005 が解消した。
脱落は `'absent`、正規化と join の失敗は `#f` であり、後者は合流全体を `(values #f '())` へ落とす。
可変性の不一致も脱落ではなくなり、`imm` へ降格したうえで Union join する。

`merge-record-types` が `(values #f '())` を返す経路は、正規化できない field 型を持つ入力で到達する。
`check-merge-return` の `#f` 節は、その経路が返す空の witness 列を検査する。
label が重複する入力では witness 名の重複検査が失敗するため、RowPolicy の検査は実際に働く。

合成 Proof を値として生成する primitive は G2f に含めない。
現在のΓ0は閉じた単相型を持ち、合成 Implements の Proof 値を引数に取る正典構文もないため、値を作っても呼び手がない。
これはホワイトペーパー §8.1 の Proof-bearing trait composition を値側まで回収したことを意味しない。

## 9. 正典文書の境界

本仕様が定めるのは、Policy の origin、返却値検査、および既存の方針を包むモジュール境界である。
合成 trait の候補、`RequiresBoth` の暗黙充足、`Compose` origin の検証は `trait.md` が定める。
合成 origin の成分が別の合成 trait である入れ子は、非巡回な正典表にその行がないため fixture では踏まない。

後続層で合成 Proof 値を導入する場合は、単相 Γ0 を多相化し、値を生成する primitive とその発行者検証を同時に定義する。

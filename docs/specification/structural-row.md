# Topazolite 構造 row 仕様（G2a / G2c）

**状態**：G2c 執筆版（codex 実装、claude レビュー前）
**基底仕様**：`docs/specification/core-calculus.md`（以下、G1 仕様）
**参照**：`draft/topazolite_whitepaper_draft_0.4.md`（以下、ホワイトペーパー）§4.5、§17.4
**関連文書**：`docs/specification/trait.md`、`docs/specification/glossary.md`、`docs/specification/requirements.md`

## 1. 本仕様の位置づけ

本文書は、G1 仕様へ record 型、field row、binding policy、構造互換性、制御フロー合流、record の簡約意味論を追加する差分仕様である。
本文書に定義がない構文、型付け規則、簡約規則、Effect row は G1 仕様に従う。
Redex model の G2a 実装は本文書を正とし、実装との乖離が見つかった場合は本文書を先に修正する。
G1 仕様へ統合せず差分文書に分けることで、G1 の規則と G2a の coverage 対象を混同しない。
G2c は本文書へ §6 の関数 variance を追加する差分であり、それ以外の節の規則を変えない（§3.3 と §3.4 の `NFn` と checking への言及だけを §6 へ付け替える）。

G2a はユーザー record を構造で照合する最小コアだけを扱う。
trait 層は、この構造 row を基礎として G2e の `trait.md` が定める。

規則には `[REQ: <ID>]` の形で要件 ID を注釈する。
要件 ID の本文は `requirements.md` を正とする。

## 2. 型と Core 構文

### 2.1 record 型と field row

型 τ へ record 型を追加する。

```text
τ ::= ... | (Record r)
r ::= ((label1 τ1 m1) ... (labeln τn mn))
m ::= imm | mut
```

**field row** r は、field ラベル、field 型、可変性の三つ組からなる有限集合である。
`imm` は immutable field を表し、`mut` は mutable field を表す。
省略時の可変性は `imm` とする。

field row r は Effect row ε と異なる sort である。
Effect row の `row-∪`、`row-⊆`、`row-∈`、`row-\` は field row に適用しない。
field row はラベルを鍵に型と可変性も照合するため、§2.2 の専用演算を使う。

`(Record r)` は closed と open の区別を型成分に持たない。
closed と open の違いは §3.2 の binding policy が決める。
この分離により、簡約前後で保存すべき型は一種類の `(Record r)` だけになる。

G2a の field はすべて required である。
optional field は §7 の後続層で導入する。

### 2.2 field row の well-formedness と演算

well-formed な field row は、同じラベルを二度以上含まない。
field row の同値、参照、差分はラベルを鍵とし、記述順に依存しない。

field row 専用の演算を次のように定める。

- **結合 `r ⊕ ρ`**：ラベル集合が互いに素な二つの field row を結合する。
  ラベルが重複するときは未定義である。
- **参照 `lookup(r, label)`**：指定ラベルの field 型と可変性を返す。
  指定ラベルが存在しないときは未定義である。
- **残余 `residual(r_b, r_T)`**：`r_b` のうち、ラベルが `r_T` に存在しない field だけを返す。
- **同値 `row-equiv?(r_1, r_2)`**：ラベル集合が一致し、各ラベルの型が `type-equiv?` で一致し、可変性も一致するときに真を返す。
- **交差 `r_1 ⋂ r_2`**：両方に存在し、型が `type-equiv?` で一致し、可変性も一致する field だけを返す。

`residual(r_b, r_T)` のラベルは定義上 `r_T` に存在しないため、`r_T ⊕ residual(r_b, r_T)` は常に結合の前提を満たす。

### 2.3 未型付き縮小 Core

G1 の未型付き縮小 Core へ record 型注釈、record 構築、射影、binding mode 付き束縛を追加する。

```text
uτ    ::= ... | (Record ur)
ur    ::= ((label1 uτ1 m1) ... (labeln uτn mn))
bmode ::= const | let

e ::= ...
    | (Rec ((label1 m1 e1) ... (labeln mn en)))
    | (Proj e label)
    | (Let (x bmode uτ) e1 e2)
```

この構文は Surface 構文ではない。
Surface の record リテラル、`const`、`let`、`let mut` から未型付き縮小 Core への変換は Phase 1 で定める。

### 2.4 Typed Core

G1 の Typed Core へ次の項と値を追加する。

```text
bmode ::= const | let

c ::= ...
    | (Rec ((label1 m1 c1) ... (labeln mn cn)))
    | (Proj c label)
    | (Let (x bmode τ) c1 c2)

v ::= ...
    | (Rec ((label1 m1 v1) ... (labeln mn vn)))
```

`Rec` は record の各 field と可変性を保持する。
`Proj` は record の field をラベルで射影する。
binding mode 付き `Let` は `const` と `let` の静的な row policy を区別する。

G1 の binding mode を持たない `Let(x : τ, c1, c2)` は存置する。
この旧形式は意味論上 `const` と同じ policy を持つが、G1 の項を新形式へ書き換えない。

## 3. 型付け

### 3.1 record の構築と射影

`Rec` は各 field を synthesis して record 型を構築する。

**(T-Rec)** [REQ: ROW-004]

```text
Γ; Δ; Π; Ξ; Φ ⊢core ci : τi ! εi        (i = 1 ... n)
label1, ..., labeln は互いに相異なる
どの τi も Owned<τ> の形でない
------------------------------------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core
  (Rec ((labeli mi ci) ...))
  : (Record ((labeli τi mi) ...)) ! ⋃i εi
```

`Rec` が可変性を値に保持するため、`mut` field を持つ record 型にも well-typed な値が存在する。
record 値の field に `Owned` を許すと affine 検査を record 内部へ迂回できるため、G2a は先頭型が `Owned` の field を拒否する。
この制限は G1 が constructor field、関数引数、closure capture から `Owned` を除外する方針を保つ。

`Proj` は scrutinee を synthesis し、field row から結果型を得る。

**(T-Proj)**

```text
Γ; Δ; Π; Ξ; Φ ⊢core c : (Record r) ! ε
lookup(r, label) = (τ, m)
------------------------------------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core (Proj c label) : τ ! ε
```

指定ラベルが r に存在しなければ型エラーである。
`let` が保持する残余 field も束縛変数の平坦な field row に含まれるため、合流前の現在の flow では射影できる。
必須 field と残余 field を型の中で二層に分ける表現は採らない。
G2a では平坦な field row だけで安全に射影でき、二層表現は Proof witness を導入する後続層まで必要ないためである。

### 3.2 binding policy

**binding policy** は、注釈型が要求する field と bound が持つ余剰 field の扱いを決める静的規則である。
binding mode 付き `Let` は record 型以外にも使える。

注釈型 T が record 型でない場合、`const` と `let` はどちらも bound を T で checking し、x を T で束縛する。
非 record 型には残余 row がないため、この場合の二つの mode に型付け上の差はない。

注釈型が `(Record r_T)` の場合、bound を synthesis して得た `(Record r_b)` と §3.3 の `compat?` を照合する。
このときの**残余 row**は `ρ = residual(r_b, r_T)` である。

**(T-LetConstRecord)** [REQ: ROW-001]

```text
Γ; Δ; Π; Ξ; Φ ⊢core cb : (Record r_b) ! εb
compat?((Record r_b), (Record r_T))
ρ = residual(r_b, r_T) = ∅
Γ, x : (Record r_T); Δ; Π; Ξ; Φ ⊢core cbody : τ ! εbody
------------------------------------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core
  (Let (x const (Record r_T)) cb cbody) : τ ! εb ∪ εbody
```

`const` は残余 row が空であることを要求する closed binding である。
残余があれば型エラーとする。

**(T-LetOpenRecord)** [REQ: ROW-002]

```text
Γ; Δ; Π; Ξ; Φ ⊢core cb : (Record r_b) ! εb
compat?((Record r_b), (Record r_T))
ρ = residual(r_b, r_T)
Γ, x : (Record (r_T ⊕ ρ)); Δ; Π; Ξ; Φ ⊢core cbody : τ ! εbody
------------------------------------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core
  (Let (x let (Record r_T)) cb cbody) : τ ! εb ∪ εbody
```

`let` は必須 field を注釈型へ narrow し、互換な残余 row を contextual type として保持する open binding である。
束縛変数の型は必須 field と残余を合わせた平坦な `(Record (r_T ⊕ ρ))` になる。

bound の型が `Never` の場合は、record 型を要求せず任意の注釈型に対して受理する。
この場合は body へ到達しないため、残余を空として x を注釈型で束縛しても射影の安全性と矛盾しない。

G2a の `let` は immutable binding であり、再代入を意味しない。
再代入を持つ `let mut` は §7 の対象である。

### 3.3 構造互換性

**構造互換性** `compat?(sub, sup)` は、sub が sup の要求を満たすかを判定する方向付きの関係である。
この関係は対称ではない。

`compat?` を型の形に対する全域判定として次のように定める。

```text
compat?(Never, sup) = true

compat?((Record r_sub), (Record r_sup)) =
  r_sup の各 (label : τ_sup @ m_sup) について、次をすべて満たす
    lookup(r_sub, label) = (τ_sub, m_sub) が存在する
    m_sub ∈ {imm, mut}
    m_sup = imm なら compat?(τ_sub, τ_sup)
    m_sup = mut なら m_sub = mut かつ type-equiv?(τ_sub, τ_sup)

compat?(Owned<τ_sub>, Owned<τ_sup>) = type-equiv?(τ_sub, τ_sup)
compat?(NFn_sub, NFn_sup) = §6.1 の関数互換性
compat?(sub, sup) = type-equiv?(sub, sup)       上記以外
```

record の sub は、sup が要求する field をすべて満たす限り余剰 field を持てる。
この width subsumption によって型同値でない二つの record 型が互換になりうる。

`imm` field は共変に再帰照合する。
`mut` field は読みと書きの双方に使われるため、`mut` を要求する位置では field 型が `type-equiv?` で一致する場合だけ互換とする。
`imm` を要求する位置には `mut` field を渡せる。 [REQ: ROW-005]
書き込み能力を捨てる方向であり、その位置からは読み出しだけが可能なため、§3.5 の降格した field を構成できる。
一方だけが `Owned` である field 型は互換でなく、双方が `Owned` の場合も内部型を不変に照合する。
`NFn` field の照合は §6.3 が定める（`imm` は関数 variance、`mut` は不変一致）。

予約基本型と予約 Narrative は record の分岐へ入らず、最後の `type-equiv?` 分岐だけで照合する。 [REQ: TYP-003]
したがってユーザー record の構造公開は、予約型の内部表現に structural matching を適用する権限を与えない。

checking 位置の `check-as` は、実際の型と期待型の形にかかわらず `compat?(actual, expected)` を使う（§6.4）。
この接続により、record を関数引数や branch の期待型へ渡す位置でも width subsumption が働く。
`Eliminate` が交差型へ型付けされた後に、field の多い実 record 値へ簡約しても、その値は期待する交差型と互換なので Preservation を保つ。

### 3.4 型同値との分離

`type-equiv?` は definitional equality であり、`compat?` は方向付きの subsumption である。
この二つは別の判定として実装する。

record 型の `type-equiv?` は `row-equiv?` に帰着する。
したがって両 record 型のラベル集合、各 field の型、可変性がすべて一致するときだけ型同値である。

`compat?` が余剰 field を許すことを理由に `type-equiv?` まで width subtyping へ変えてはならない。
型同値は G1 の型正規化と opaque identity の規則を引き続き担うためである。

### 3.5 制御フロー合流

`Eliminate` の非 `Never` 枝がすべて record 型を返す場合、結果型を field row の構造的交差で求める。

**(T-EliminateRecordMerge)** [REQ: ROW-003]

```text
各枝 ci の型を τi とする
Never の枝を merge 入力から除外する
残る型が (Record r1), ..., (Record rn) なら
  r = r1 ⋂ ... ⋂ rn
------------------------------------------------------------
Eliminate(c0, branches) : (Record r)
```

交差に残す field は全枝に存在する field だけである。 [REQ: ROW-005]
型が `type-equiv?` で一致しない field は、可変性を保ったまま Union join する。 [REQ: ROW-005]
可変性が枝の間で食い違う field だけを `imm` へ降格する。
`compat?` は方向付きであり、どの枝の field 型を結果へ残すかを一意に決めないため、merge には使わない。

非 `Never` 枝が一つもなければ結果型は `Never` である。
非 `Never` 枝に record 型と非 record 型が混在すれば型エラーである。
非 `Never` 枝がすべて非 record 型なら、G1 の `Eliminate` 規則を使う。

この構造的交差は、全経路に存在する field だけを残す decidable な近似である。
型が異なる field の Union join は、G2e が `trait.md` §7 として導入した。
G2g は join の対象を `imm` field から全 field へ広げた。 [REQ: ROW-005]
G2g の時点では、異型の `mut` field を `imm` へ降格して join していた。
降格の理由は代入安全性である。
join 型の field へ書き込めるとすると、ある枝が期待する狭い型の位置に別の枝の値を格納できてしまう。
G5c2 は降格をやめ、可変性を保ったまま join する規則へ置き換えた。
代入安全性は書き込みの側が受け持ち、`borrow.md` の `Assign` は Union の全成分と両立しない値を拒む。
合流型を作った枝の再照合は、`Eliminate` の導入点だけ専用の規則へ切り替える。
`mut` field の expected Union に対し、枝が単一型ならいずれかの成分と、枝が部分 Union なら全成分と `type-equiv?` で一致することを求める。
通常の `compat?` と `Assign` の全成分検査は緩めない。
合流を到達不能なまま未回収へ送る案は、ホワイトペーパー §4.5.3 の回収主張を実装で空にするため採らない。
Proof witness による型付き field 回復は未回収であり、§7 の後続層へ送る。

## 4. elaboration

G2a の elaboration は未型付き縮小 Core の record 構文を §2.4 の Typed Core へ変換する。

```text
Γ; Δ; Π; B ⊢ (Rec ((labeli mi ei) ...)) ⇒ (Record r) ! ε ⟹ (Rec ((labeli mi ci) ...))
Γ; Δ; Π; B ⊢ (Proj e label) ⇒ τ ! ε ⟹ (Proj c label)
Γ; Δ; Π; B ⊢ (Let (x bmode uτ) e1 e2) ⇒ τ ! ε ⟹ (Let (x bmode T) c1 c2)
```

`Rec` は各 field を synthesis し、ラベル一意性と `Owned` field の禁止を検査して、field 型と Effect row を合成する。
`Proj` は scrutinee を synthesis し、field row の参照から結果型を得る。
binding mode 付き `Let` は注釈を T へ解決し、bound を synthesis して §3.2 の policy を適用する。

Typed Core の binding mode 付き `Let` が保持する注釈は宣言型 T である。
`let` の残余 row は body を型付けする Γ の x にだけ保持し、Typed Core の注釈へ書き戻さない。
Typed Core を独立に型付けするときは bound を再び synthesis して残余 row を復元する。

binding mode を明示しない G1 由来の `let x = e1 in e2` は default const として検査する。
この形式は bound の完全な合成型を x の型にするため、その型自身に対する残余は空である。
elaboration の出力は G1 の `Let(x : τ, c1, c2)` のまま保ち、binding mode 付きの新形式へ正規化しない。

`Rec` と `Proj` は synthesis によって field から型を復元できる。
したがって `Construct(D, K, ...)` の D に相当する record 型をノードへ埋め込まない。
`Construct` は constructor 名と field だけでは具体化されたデータ型 D を復元できないが、`Rec` は各 field の型を直接 synthesis できるためである。

## 5. 動的意味論

### 5.1 G2m と評価文脈

G2a の machine 言語 G2m は G1m を拡張し、§2 の型、項、値を加える。
評価文脈 E、F、G のすべてへ `Rec`、`Proj`、binding mode 付き `Let` の文脈を加える。

```text
E ::= ... | (Rec ((label m v) ... (label m E) (label m c) ...)) | (Proj E label) | (Let (x bmode τ) E c)
F ::= ... | (Rec ((label m v) ... (label m F) (label m c) ...)) | (Proj F label) | (Let (x bmode τ) F c)
G ::= ... | (Rec ((label m v) ... (label m G) (label m c) ...)) | (Proj G label) | (Let (x bmode τ) G c)
```

`Rec` の field は記述順に左から右へ評価する。
binding mode 付き `Let` は bound を body より先に評価する。

E は `Scope` と `Handle` を含む一般の簡約文脈である。
F は `Scope` と `Handle` をまたがない未捕捉文脈である。
G は `Handle` を含められるが `Scope` をまたがない文脈である。
三つすべてを拡張することで、record field 内の `Perform` と `Error` を正しい境界が処理し、field 内の Owned binding を最寄りの `Scope` が管理する。

binding mode 付き `Let` は body だけで x を束縛する。
G2m の binding form は次の形であり、bound の c1 では x を束縛しない。

```text
(Let (x bmode τ) c1 c2)    x refers to c2
```

### 5.2 射影

record 値から指定ラベルの値を取り出す。

**(R-Proj)**

```text
labels は重複しない
proj-lookup(⟨labeli = vi⟩, labelk) = vk
------------------------------------------------------------
E[(Proj (Rec ((labeli mi vi) ...)) labelk)] → E[vk]
```

`proj-lookup` は先頭から走査し、一致する値を返す全域の metafunction である。
指定ラベルが存在しなければ `#f` を返し、R-Proj は発火しない。
ラベルが重複する record に対しても R-Proj は発火しない。
この二つの不正項は例外を起こさず stuck に留まるが、well-typed な項ではラベル一意性と field の存在が保証される。

### 5.3 binding mode 付き Let

binding mode は実行時の代入規則を変えない。
`const` と `let` の差は §3.2 の静的 policy だけであり、G2a は再代入を持たないためである。

**(R-LetB)**

```text
τ は Owned<τ'> の形でない
------------------------------------------------------------
E[(Let (x bmode τ) v c)] → E[c[x := v]]
```

**(R-LetOwnedB)**

```text
τ = Owned<τ'>
pnew は H と Ω の domain にない
------------------------------------------------------------
E[Scope(π, G[(Let (x bmode τ) v c)])], H, Ω, θ
  → E[Scope(π · pnew, G[c[x := pnew]])],
    H[pnew ↦ v], Ω[pnew ↦ Available], θ
```

`owned-type?` の正負で R-LetB と R-LetOwnedB を排他的にする。
この分岐は record 型と非 record 型に共通である。

### 5.4 Effect row

G2a が追加する項の Effect row は G1 の `row-∪` で合成する。

- `Rec` の Effect row は、各 field の Effect row を評価順に結合した row である。
- `Proj` の Effect row は、scrutinee の Effect row である。
- binding mode 付き `Let` の Effect row は、bound と body の Effect row の和である。

field row の演算はこの Effect 合成に使わない。

### 5.5 簡約関係の拡張

規則本体 `-->g2/rules` は、G1 の内部規則関係 `-->g1/rules` を G2m 上へ拡張し、R-Proj、R-LetB、R-LetOwnedB を加える。
公開する `-->g2` は G1 と同じく binder 一意性を検査してから内部規則を適用する R-Step ラッパーである。
公開 `-->g1` 自体を拡張元にしないのは、その関係が R-Step 一規則だけを公開し、β簡約などの規則本体を含まないためである。

G1 の `δ`、`substitute*`、`select-branch` は G1m を domain とするため、G2m 用に `δ/g2`、`substitute*/g2`、`select-branch/g2` へ拡張する。
R-Delta、R-Beta、R-RecurUnfold、R-Eliminate は `-->g2/rules` で同名規則を差し替え、G2m domain の metafunction を呼ぶ。
`select-branch/g2` は branch body の置換に `substitute*/g2` を使い、再帰呼び出しも `select-branch/g2` 自身へ向ける。

R-Let、R-LetOwned、R-RecurBind、R-HandleReturn と G2a の二つの Let 規則は、拡張言語の binding form を解釈する組み込み substitution を使う。
これらの規則には独自の domain 拡張を加えない。

G1 の `inject`、`run`、bounded trace、観測関係は存置する。
G2a は G2m と `-->g2` を使う G2 版の各ドライバを追加し、G1 の項と `-->g1` の挙動を変えない。

## 6. 関数型の variance

### 6.1 関数互換性の規則

`compat?` の `NFn` 分岐を、型同値への委譲から次の規則へ置き換える。 [REQ: VAR-001]

```text
compat?((NFn (A_sub_1 ... A_sub_n) R_sub E_sub Q_sub),
        (NFn (A_sup_1 ... A_sup_m) R_sup E_sup Q_sup)) =
  n = m
  各 i について compat?(A_sup_i, A_sub_i)     （引数は反変）
  compat?(R_sub, R_sup)                       （返り値は共変）
  E_sub ⊆ E_sup                               （§6.2）
  Q_sub ⊆ Q_sup                               （§6.2）
```

引数が反変であるのは、期待側が渡すどの引数も実際側が受け取れなければならないためである。
返り値が共変であるのは、実際側が返すどの値も期待側の文脈で使えなければならないためである。
引数個数は一致を要求する。
可変長引数や省略可能引数は G2c の型に存在しないためである。

引数と返り値の照合は `compat?` へ再帰する。
record 型を引数や返り値に持つ関数型では、この再帰によって §3.3 の width subsumption と関数 variance が相互に入れ子になる。
引数位置の引数位置のように、再帰のたびに極性は反転する。

### 6.2 latent Effect と Proof obligation の包含

`NFn` の Effect row E と Proof obligation 集合 Q は、集合包含で照合する。 [REQ: VAR-002]

E は共変である。
実際側が起こしうる作用は、期待側が宣言した作用の範囲に収まらなければならないためである。
E の要素の同一性は、型同値の Effect row 照合と同じ `effect-equiv?` を使う。
これにより、`Yield` や `Return` の payload 型の field 順序だけが違うラベルを別の作用と数えない。

Q は E と向きが逆の包含である（`Q_sub ⊆ Q_sup`）。
Q は呼び出し側が discharge すべき前提の宣言であり、期待側が引き受けると宣言した obligation の範囲内でだけ、実際側は discharge を要求できるためである。
G2c の Q の要素 φ は exact 一致で照合する。
G2e は型を内包する trait 命題を導入したため、`trait.md` §3.4 の命題同値を使う。
G2c までの命題では正準鍵が構文と同じになるため、既存の判定結果は変わらない。

### 6.3 field の可変性との交差

record field の照合（§3.3）が field 型として関数型に到達したときの規則を定める。 [REQ: VAR-003]

- `imm` field の関数型は、§3.3 の `imm` 再帰がそのまま §6.1 の関数 variance で照合する。
- `mut` field の関数型は、`type-equiv?` の不変一致に留まる。

`mut` field が不変に留まるのは、ROW-004 の代入安全性と同じ理由である。
読み手はより広い関数を期待でき、書き手はより狭い関数を格納しうるため、双方向の利用に安全な照合は同値だけになる。

### 6.4 checking 位置の統一

checking 位置の `check-as` は、実際の型と期待型の形にかかわらず `compat?(actual, expected)` を使う。 [REQ: VAR-001]
elaboration と ⊢core が同じ判定を共有しない場合、elaboration が受理した項の簡約途中に現れる互換非同値の関数値を ⊢core が拒否し、Preservation が破れるためである。
`Never` の bottom 受理は `compat?` の `Never` 分岐が引き続き担う。
`type-equiv?` の判定はこの統一で変わらない（§3.4 の分離を維持する）。

### 6.5 借用の region の variance

`Borrowed` と `BorrowedMut` は payload と region 欄を持つ。 [REQ: VAR-004]
`compat?` はこの 2 つの構成子のあいだの変換をどちらの向きも認めない。
共有借用を可変借用の位置へ渡すと書き込み能力が増える。
可変借用を共有借用の位置へ渡すと、元の可変借用が生き続ける抜けができる。

`(Borrowed τ_sub ρ_sub)` が `(Borrowed τ_sup ρ_sup)` と互換であるのは、payload が互換であり、かつ `ρ_sub` が `ρ_sup` を含むときである。
長く生きる借用は短く生きる借用の位置へ渡せる。
region どうしの包含の判定は `region.md` の関係へ預け、`compat?` はその関数を受け取るだけである。
payload の判定へも同じ関数を渡す。
渡さないと最上位でだけ共変になり、1 段下で region 欄の一致へ戻る。

`(BorrowedMut τ_sub ρ_sub)` は region 欄の一致と payload の型同値を要求する。
可変借用は書き込みの経路である。
region を共変にすると、書き込んだ値の region が宣言より短くなりうる。
payload を広げると、書き込んだ値が元の場所の型に合わなくなる。

この規則は record の field へ再帰的に適用する。
`imm` の field は payload の判定へ同じ関数を渡すため、field の型の中の共有借用も共変になる。
`mut` の field は §6.3 のとおり型同値を保ち、region も不変である。

`type-equiv?` の借用の判定は region 欄の一致を保つ。
同値と互換を同じ関係にすると、`policy-narrative.md` §6.2 が述べる「同値な二型は互換である」という契約が意味を持たなくなる。
緩めるのは同値でない側だけである。
VariancePolicy が列挙する readonly / mutable field、関数入出力、borrow の region variance は、それぞれ VAR-003、VAR-001、VAR-004 で回収済みである。

## 7. 範囲外の規則

G2a は次の規則を導入しない。
送り先は、その規則が必要とする意味論に合わせて定める。
本節に項目を足したときは、`requirements.md` §4 の申し送り表へも 1 行追記する。

- **optional field**：G2a の field はすべて required とする。
  optional と required の不一致検査は、optional を Core semantics として導入する G2 の後続層で扱う。
- **Union と Intersection**：有限な Union の正規形と構造型の Intersection 消去は、G2e が `trait.md` §3 として導入した。
  trait の Intersection は型構成子ではなく、同仕様 §4.3 の正典表と `RequiresBoth` Proof で表す。
- **Refinement と Untrusted**：値が満たす命題の Proof を保持するため、Proof 層で扱う。
  G2d が `proof-value.md` §3 と §4 として導入した。
- **join 型と Proof 付き merge**：型が異なる branch field の上位型と field 常在性の witness を要するため、Proof 層で扱う。
  field 常在性の witness は G2d が `proof-value.md` §5 として導入した。
  branch で型が異なる `imm` field の Union join と `FieldType` witness は、G2e が `trait.md` §7 として導入した。
  witness による型付き field 回復は未回収であり、同仕様 §9 へ送る。
  異型 `mut` field の join は G2g が §3.5 として導入した。 [REQ: ROW-005]
  G2g の降格は代入安全性のための狭めであり、G5c2 が可変性を保つ規則へ置き換えて、ホワイトペーパー §4.5.3 の要求を回収した。
- **mut field への代入と借用**：G5c2 が `ProjBorrow` と `Assign` と alias safety を同時に導入し、record field の借用と書き換えを回収した。
- **borrow mode の互換性**：G5c2 が record field の射影について `Borrowed` と `BorrowedMut` の mode 規則を定め、暗黙の強化と弱化を認めない範囲を回収した。
- **Surface 構文**：record リテラルと binding の Surface から未型付き縮小 Core への変換は Phase 1 で扱う。
- **region 引数どうしの関係の宣言**：異なる 2 つの region 引数のあいだには反射律だけを認める。
  region の束縛へ包含の宣言を書く構文は置かない。
  Phase 1 以降で扱う。
- **`ForallRegion` を `NFn` 以外の位置へ置くこと**：region 多相は関数の署名の位置に限る。
  record の field や Union の成分へ置く形は、消去子が束縛を持ち出す経路を増やすため扱わない。
  Phase 1 以降で扱う。
- **`NFn` の `εin` と `εout` を単一の row へまとめること**：入口と出口の effect row を 1 つにまとめる形は、部分適用の途中の状態を表せない。
  Phase 1 以降で扱う。

G2a で範囲外とした関数 field の variance は、G2c が §6 として導入した。

必須 field と残余 field を二層に分けた record 型は採らない。
G2a の現在の flow では平坦な field row から安全に射影でき、合流後の field 回復は Proof witness 側で表現できるためである。

closed と open を record 型の mode として保持する表現も採らない。
二つの違いは束縛時の残余処理だけであり、型へ mode を埋め込むと Preservation が不要な型の分岐を持つためである。

## 8. 要件と規則の対応

| 要件 ID | 対応する規則、定義 |
|---|---|
| TYP-003 | §3.3 の `compat?` 全域 dispatch、§3.4 の型同値との分離 |
| ROW-001 | §3.2 T-LetConstRecord |
| ROW-002 | §3.1 T-Proj、§3.2 T-LetOpenRecord |
| ROW-003 | §3.5 T-EliminateRecordMerge |
| ROW-004 | §3.1 T-Rec、§3.3 の `mut` field 不変性 |
| ROW-005 | §3.5 の可変性を保つ Union join、§3.3 の `imm` 要求を満たす `mut` field |
| VAR-001 | §6.1 関数互換性の規則、§6.4 checking 位置の統一 |
| VAR-002 | §6.2 latent Effect と Proof obligation の包含 |
| VAR-003 | §6.3 field の可変性との交差、§3.3 の `NFn` field 照合 |
| VAR-004 | §6.5 借用の region の variance |

# Topazolite Core calculus 仕様（G1）

**状態**：G1 執筆版（codex レビュー前）
**参照**：`draft/topazolite_whitepaper_draft_0.4.md`（以下、ホワイトペーパー）§3.2、§4.9、§5、§7、§11.5
**関連文書**：`docs/specification/glossary.md`、`docs/specification/requirements.md`

## 1. 本仕様の位置づけ

本文書は、ホワイトペーパー §11.5 の概略 judgment を、PLT Redex で実行可能モデルを実装できる精度へ拡張した Core calculus 仕様である。
Redex model（`model/redex/`）はこの文書を正として実装し、乖離が見つかった場合は本文書を先に修正する。

G1 の範囲は次のとおりである。

- **対象**：未型付き縮小 Core から Typed Core への elaboration、Typed Core の簡約意味論、origin model、return boundary model、Finite / Productive / Unknown の仕様、affine な move / drop と scope exit finalization。
- **G5 へ延期**：borrow、region、unsafe boundary の judgment と、メタ理論性質 8（borrow safety）、9（unsafe containment）。概略は §9 に置く。
- **Phase 1 へ延期**：Surface 構文から未型付き縮小 Core への対応づけ、user trait constructor、マクロ展開。

規則には `[REQ: <ID>]` の形で要件 ID を注釈する。
ID の本文は `requirements.md` を正とする。
規則と ID の対応の一覧は §10 に置く。

## 2. 環境

calculus は次の環境を使う。

- **Γ（term bindings）**：項変数から型への有限写像。`Γ, x : τ` で拡張する。
- **Δ（type / kind bindings）**：型名から TypeInfo 値（§3.4）への有限写像。
- **Π（proof / capability bindings）**：Proof 名から命題と origin の組への有限写像。
- **B（boundary stack）**：boundary frame の stack。frame は `FunctionBoundary(b, τ)` または `ExpressionBoundary(b, τ)` であり、b は elaboration が発行する一意な境界 ID である。
- **R0（予約 origin レジストリ）**：予約 origin ID から、その ID が正当化する値の種類（§3.4 の sort）への有限写像。初期環境だけが定め、elaboration と簡約の間で不変である。

簡約意味論（§5）はさらに次を使う。

- **Ω（place 状態）**：place p から状態への有限写像。G1 の状態は `Available`、`Moved`、`Dropped` の三値とする。
- **H（place 格納）**：place p から値への有限写像。
- **Ξ（place typing）**：place p から型への有限写像。構成の well-formedness（§5.1）で使う。
- **Λtok（leaf token 状態）**：値の内部の `OwnedLeaf` が持つ token から状態への有限写像。状態は `Available`、`Moved`、`Dropped` の三値とし、`Dropped` の entry は再利用防止の tombstone として残す。
- **θ（観測 trace）**：観測イベントの列。イベントは `obs(v)`（yield による観測値）、`fin(p)`（root の finalization による drop）、`finLeaf(p, fp)`（値内 leaf の finalization による drop）である。`fin(p)` は空 path の `finLeaf(p, ())` に相当する短縮形だが、leaf の path は常に非空である。

boundary stack の操作は次の二つである。

```text
push(B, frame)      frame を先頭に積んだ stack を返す
nearestReturn(B)    先頭の frame を返す。空なら未定義
```

`nearestReturn` は FunctionBoundary と ExpressionBoundary を区別しない。
どちらも `return` の送信先になれる。

## 3. 構文

### 3.1 未型付き縮小 Core

**未型付き縮小 Core** は elaboration の入力言語である。
Surface 構文から糖衣を除いた形に相当するが、Surface 構文との対応づけは Phase 1 で定める。

```text
e ::= l                                          リテラル
    | x                                          変数
    | fn(x1 : τ1, …, xk : τk) -> τ ! ε  e        関数抽象（注釈付き）
    | e0(e1, …, ek)                              適用
    | let x = e1 in e2                           束縛
    | construct K<τ̄>(e1, …, ek)                  constructor 適用（型引数は省略可）
    | eliminate e0 { K1(x̄1) => e1; …; Kn(x̄n) => en }   場合分け
    | return e                                   返却
    | narrativeExpr(e)                           式 Narrative 境界
    | recur f(x1 : τ1, …, xk : τk) -> τ ! ε = e1 in e2   再帰定義
    | yield e1; e2                               観測値の生成
    | suspend e                                  評価の区切り
    | move x                                     affine 資源の消費
    | drop e                                     明示 drop
    | curry(e1, e2)                              部分適用の派生
    | typeMake(spec)                             TypeInfo 生成
    | letType T = e1 in e2                       型名束縛

l ::= n | unit | s                               整数、unit、文字列
spec ::= T | spec<spec1, …, spek>                型式（型名とその適用）
```

`Bool` の値はリテラルではなく、constructor 表 C0（§3.5）の `true()` と `false()` で表す。
`eliminate` による場合分けを Bool にもそのまま使うためである。

`recur` はユーザーへ `fix` を露出しない内部 marker であり、Surface の loop 構文はここへ lowering される（ホワイトペーパー §7.2）。
`fn` と `recur` の注釈にある Effect row ε の中では、境界 ID を持たないラベル `Return` を書ける。
このラベルは elaboration が最寄りの境界へ静的に解決する（§4.5）。

### 3.2 型、Effect row、kind

```text
τ ::= Int | Bool | Unit | String | Never | Res   基本型
    | List<τ> | Option<τ> | Result<τ1, τ2>       組み込みデータ型
    | Owned<τ>                                   affine 所有
    | NFn<(τ1, …, τk), τ, ε, Q>                  Narrative 関数型
    | TypeInfo<κ>                                型情報値の型
    | Proof<φ>                                   Proof 値の型

κ ::= Type | κ1 -> κ2                            kind

ε ⊆ { Return<b, τ>, Yield<τ>, Suspend, Partial, Compile, Own }   Effect row
     （宣言注釈の中の ε に限り、境界 ID を持たない Return ラベルを許す。§3.1、§4.5）

Q ::= ⟨φ1, …, φn⟩                                Proof obligation の列

φ ::= ValidNarrativeTrait | TypeNarrativeCap     G1 で使う命題（最小）

t ::= τ | List | Option | Result                 型式（monotype と未適用 constructor）
```

`Own` は、Move / Drop（§4.7）の出現を示すラベルであり、ホワイトペーパーの row にない G1 の追加である。
`Partial` と同じく Perform される op ではなく、静的な marker として働く。
OwnershipError の源は R-Move / R-Drop に限られるため（§5.5）、row の `Own` は「その項の簡約が OwnershipError で終端しうる」ことの保守的な上界を与える。
C-Guarded の guard 部品条件（§6.2）がこの上界を使う。

`NFn<P, R, ε, Q>` はホワイトペーパー §11.5.2 の `NFn<P, R, εin, εout, Q, O>` の G1 簡約形である。
G1 では εin と εout を単一の潜在 Effect row ε に縮約し、適用時の `combine(εa, εi, εo)` を和集合で定義する（§4.3）。
また、origin O は型成分ではなく値成分として扱う（§3.4）。
この二点はホワイトペーパーからの意図的な単純化であり、εin / εout の分離と origin の型レベル追跡が必要になった時点（G2 以降）で拡張する。

`Res` は affine 資源の基本型であり、G1 の `Owned<τ>` の中身は `Res` に限る（§3.5）。
`t` は TypeRep（§3.3）が保持する型式である。
型式の kind は metafunction **kindOf** で定める。

```text
kindOf(List)   = Type -> Type
kindOf(Option) = Type -> Type
kindOf(Result) = Type -> Type -> Type
kindOf(τ)      = Type                            （monotype）
```

kind が `Type` の TypeRep は monotype τ を持ち、kind が矢印の TypeRep は未適用の組み込み constructor を持つ。
未適用 constructor が現れるのは TypeRep の中だけであり、項や注釈の型位置には置けない。
注釈の中の型名（`letType` で束縛した T を含む）は、elaboration が Δ を引いて monotype へ展開してから τ として扱う。

### 3.3 Typed Core

**Typed Core** は elaboration の出力言語であり、簡約意味論はこの言語の上で定義する。

```text
c ::= v                                          値
    | x                                          変数
    | Apply(c0, c1, …, ck)                       適用
    | Let(x : τ, c1, c2)                         束縛（型注釈付き）
    | Construct(D, K, c1, …, ck)                 constructor 適用（D は具体化されたデータ型）
    | Eliminate(c0, (K1(x̄1) -> c1), …, (Kn(x̄n) -> cn))   場合分け
    | Perform(op, c)                             Effect の発生
    | Handle(op, x -> ch, c)                     abortive handler
    | Scope(π, c)                                finalization 境界
    | Recur(r, f, (x1, …, xk), c1, c2)           再帰定義（r は callable ID）
    | Yield(c1, c2)                              観測値の生成
    | Suspend(c)                                 生産性の区切り
    | Move(w)                                    affine 資源の消費（w は変数または place）
    | Drop(c)                                    明示 drop
    | Curry(c1, c2)                              部分適用
    | Error(p)                                   ownership error の伝播（簡約が生成、§5.5）

op ::= Return<b, τ>                              G1 の handler 対象 Effect

v ::= l                                          リテラル
    | Lam(O, ℓ, (x1, …, xk), c)                  関数値（origin と callable ID 付き）
    | PrimVal(O, name)                           primitive 値（origin 付き）
    | CurryVal(O, vf, va)                        部分適用値（origin 付き）
    | RecurVal(r, f, (x1, …, xk), c)             再帰関数値
    | Construct(D, K, v1, …, vk)                 構成済みデータ
    | resource(n)                                affine 資源値（acquire が生成、§3.5）
    | TypeRep(O, t, κ)                           型情報値（origin 付き）
    | ProofRep(O, φ)                             Proof 値（origin 付き）
```

G1 の `Handle` は継続を再開しない **abortive handler** に限る。
継続を再開する一般の algebraic effect handler は、多相との干渉に対する設計選択（ホワイトペーパー §5.2）を要するため G1 では扱わず、G2 以降のサイクルで導入する。
G1 の handler 対象 Effect は `Return<b, τ>` だけである。
`Yield` と `Suspend` は Perform ではなく専用ノードで表し、観測関係（§6.1）で意味を与える。
`Error(p)` は elaboration の出力には現れず、簡約（§5.5 R-MoveError）だけが生成する。
`resource(n)` は G1 で唯一の `Owned` 型の値であり、primitive `acquire`（§3.5）だけが導入する。

`Recur(r, f, (x1, …, xk), c1, c2)` は f の再帰関数シグネチャ `NFn<(τ1, …, τk), τ, ε, Q>` を項から消去する（`RecurVal` も同様）。
この消去は `Lam` にも及ぶ。`Curry`/`Apply` の呼び出し先位置に置かれた `Lam(O, ℓ, (x̄), c)` は、その位置の期待型（curry 後の返り値型や apply の結果型）だけからは元の全パラメータ列を復元できない。
たとえば `curry(fn(xs: List<Int>, y: Bool) -> Int ! {} { … }, nil<Int>())` は `Curry(Lam(User, ℓ, (xs, y), c), Construct(List<Int>, nil))` へ elaboration されるが、curry 適用後の期待型は `NFn<(Bool), Int, {}, ⟨⟩>` であり、固定した第一引数の型 `List<Int>` を含まない。
この情報は elaboration の E-Lambda（§4.3）・E-Recur（§4.6）がそれぞれ `NFn` シグネチャを組み立てる際にしか現れず、Typed Core の項単独からは回復できない。

f は表層名にすぎず、同じ表層名を持つ複数の `recur` が同一の CoreArtifact 内に現れうる（E-Recur は f を内部的に改名しない。例：`recur f(x: Int) -> Int ! {} = 0 in 0` と `recur f(x: Bool) -> Int ! {} = 0 in 0` が同じ scope 中の兄弟式として現れる場合）。
そのためシグネチャを f の表層名で indexしても一意には取り出せない。origin で代用することもできない。`verify-origins`（§3.4）は `Lam` に対し常に `O = User` を要求しており、origin は個体識別に使えない。

この不足を補うため、elaboration は `Lam`・`Recur`・`RecurVal` の各インスタンスへ **CallableId** と呼ぶ新規のフィールドを割り当てる。
CallableId はプログラム中の束縛子（変数名、f の表層名）から独立した、elaboration が生成する不透明な識別子であり、origin（§3.4）とは無関係である。
`ℓ` は `Lam` インスタンスの、`r` は `Recur`/`RecurVal` インスタンスの CallableId を指す慣用の記法であり、両者は同じ名前空間を共有する。

**(GUN: Global Uniqueness of Names)**：一つの CoreArtifact に含まれるすべての CallableId は相異なる。
これは「表層上の名前が一意である」という条件ではなく、CoreArtifact 内の CallableId が変数束縛子とは独立にグローバルに一意であるという条件である。
表層で同じ名前の `recur f(...)` が複数 scope に現れても、対応する各 `Recur` ノードは相異なる r を持つため、Φ の一意性は表層名の改名に頼らずに保たれる。
同様に、パラメータ列が空、または互いに等しい複数の `Lam` が同一の CoreArtifact 中に現れても、それぞれ相異なる ℓ を持つ。

`Construct` は D をノード自身のフィールドとして保持するため、この CallableId のような側路の識別子を必要としない。
`NFn` シグネチャは呼び出し先位置の期待型だけからは元のパラメータ列を復元できない場合があった（上記の curry の例）のに対し、`Construct(D, K, c1, …, ck)` の D は constructor 適用が elaboration される時点（E-Construct-Check の検査位置、または E-Construct-Synth の明示型引数注釈）で必ず単一の具体化されたデータ型として確定しており、部分適用のような多段の呼び出しを経由しない。
そのため D は Φ のような別表を介さず、ノード自身のフィールドとしてそのまま保持できる。

elaboration の出力を c 単体ではなく組 **CoreArtifact** で表す。

```text
Φ : CallableId ⇀ NFnSignature
CoreArtifact ::= ⟨Φ, c⟩
```

Φ は、e0 の elaboration 導出中に現れるすべての E-Lambda・E-Recur 適用が組み立てる `(ι, NFn<(τ1, …, τk), τ, ε', Q>)` を集めた有限写像である（E-Lambda は ι = ℓ かつ Q = ⟨⟩ を、E-Recur は ι = r かつ Q = ⟨⟩ を組み立てる。§4.3、§4.6）。
GUN により Φ は関数である。すなわち同じ CallableId に二つの異なるシグネチャが対応することはない。
Φ は Ξ（place typing、§5.1）と同じ立場の補助環境であり、特定の elaboration アルゴリズムに依存せず、Typed Core の項に外部から付随するデータとして扱う。
手書きの Typed Core を検査する場合も、対応する Φ を項と揃えて与える必要があり、項中のすべての ℓ/r が Φ の定義域に属し、かつ GUN を満たすことが前提となる。
Ξ とは異なり、Φ は簡約が始まる前の初期構成（Γ = ∅ の時点）から既に必要になりうる。elaboration の出力自体が `Lam`/`Recur` を含みうるためである。

### 3.4 origin model

**origin** は、値がどの信頼済み生成経路から派生したかを示す情報である。

```text
O ::= Reserved(id)                               予約 origin。id ∈ dom(R0) のみ正規
    | Derived(O, step)                           派生 origin
    | User                                       ユーザー由来

step ::= Curry(v) | Make(t) | Expand(name) | Policy(name) | Compose(name, O, O)

sort ::= prim(name) | type(N) | typeNarrative    R0 が予約 origin ID へ与える種別
```

`Curry(v)` は部分適用（§5.3 R-CurryVal）の派生を表す。
`Make(t)` は TypeInfo 生成（§4.8 E-TypeMake）の派生を表し、生成された TypeRep が保持する型式 t を記録する。
`Expand` は Sugar 展開の派生を表す step であり、G1 では使わない（Phase 1 のマクロ展開で使う）。
sort の `N` は基本型名または組み込み constructor 名である。
R0 は予約 origin ID から sort への写像であり、どの ID がどの種類の値を正当化するかを定める（§3.5）。

origin の正規性は次で定める。

**(valid-origin)** [REQ: NAR-001] [REQ: NAR-002]

```text
valid-origin(R0, User)

id ∈ dom(R0)
--------------------------
valid-origin(R0, Reserved(id))

valid-origin(R0, O)
--------------------------
valid-origin(R0, Derived(O, step))
```

`Reserved(id)` は id が R0 に登録されている場合に限り正規である。
R0 は初期環境だけが定め、elaboration にも簡約にも R0 を拡張する規則はない。
これが NAR-001（予約 Narrative trait は makeNarrativeTrait 以外から生成できない）の calculus 上の表現である。
`Derived` は元の origin をそのまま保持するため、派生の履歴（origin chain）は失われない（NAR-002）。

値の origin を取り出す metafunction **origin(v)** を次で定める。

```text
origin(Lam(O, ℓ, (x̄), c))     = O
origin(PrimVal(O, name))      = O
origin(CurryVal(O, vf, va))   = O
origin(TypeRep(O, t, κ))      = O
origin(ProofRep(O, φ))        = O
origin(RecurVal(r, f, (x̄), c)) = User
```

`RecurVal` は origin 成分を持たない。
`recur` はユーザー構文なので、その関数値の origin は `User` とする。
curry の対象が RecurVal である場合、R-CurryVal（§5.3）はこの clause を経由して `Derived(User, Curry(va))` を作る。

`Lam`/`Recur`/`RecurVal` が持つ CallableId（ℓ/r、§3.3）は origin とは独立な成分であり、`origin` metafunction にも `valid-origin`/`verify-origins` にも現れない。
`Lam` の origin は個体によらず常に `User`（次項）であるのに対し、ℓ は個体ごとに相異なる（GUN、§3.3）。両者は別の目的を持つ独立した情報である。

Typed Core の項 c に対する **origin 検証** `verify-origins(R0, c)` を、次の二つがともに成り立つこととして定義する。

- c に出現するすべての origin 注釈が valid-origin を満たす。
- origin 付きの値について、値の形と origin の sort が次のとおり整合する。
  - `PrimVal(O, name)`：O = Reserved(id) かつ R0(id) = prim(name)。
  - `Lam(O, ℓ, (x̄), c')`：O = User（ℓ には制約を課さない。CallableId は origin の管轄外である、§3.4）。
  - `CurryVal(O, vf, va)`：O = Derived(origin(vf), Curry(va))。
  - `TypeRep(O, t, κ)`：κ = kindOf(t)（§3.2）であり、かつ次のいずれかが成り立つ。O = Reserved(id) であって、ある型名 T について Δ0(T) = TypeRep(Reserved(id), t, κ)（初期環境の triple と完全一致、§3.5）。または O = Derived(Reserved(o-type-narrative), Make(t))（step が記録する型式と本体の型式が一致）。
  - `ProofRep(O, φ)`：O = Reserved(o-type-narrative) かつ φ = TypeNarrativeCap（G1 の ProofRep はこの一形に限る）。

elaboration の出力は常にこれを満たす（§7 性質 3）。
偽造された `Reserved(id)`（id ∉ dom(R0)）を含む手書きの Typed Core も、値の形と sort が合わない origin（整数 primitive の origin を付けた Lam など）も、この検証で拒否される。
TypeRep の検査を型式の先頭名の比較にとどめると、`TypeRep(Reserved(o-list), List, Type)` のように kind を偽った値が通り、TYP-002 を迂回できる。
このため Reserved は初期環境の triple との完全一致まで、Derived は Make が記録する型式と本体の一致まで検査し、どちらの場合も kindOf による kind の整合を要求する。
Redex model の負例テストはこの拒否を確認する。

G2d は origin 検証を初期成果物の層と到達成果物の層に分け、validator 正典表に基づく Refined 値の検査を足した。
規則は `proof-value.md` §7 に置く（本節では二重に定義しない）。

ホワイトペーパー §11.5.2 は適用規則の前提に `valid-origin(O)` を置くが、G1 では origin を型成分から外したため、この前提を `verify-origins` による Typed Core 全体の一括検査へ再配置した。
origin を型成分として引数位置の関数に固定すると、異なる origin の関数を同じ高階関数へ渡せなくなるためである。

### 3.5 初期環境

初期環境は R0、Γ0、Δ0、Π0、constructor 表 C0、δ規則からなる。

**R0（予約 origin ID）**：

```text
R0 = { o-add ↦ prim(add), o-sub ↦ prim(sub), o-mul ↦ prim(mul),
       o-lt ↦ prim(lt), o-le ↦ prim(le), o-eq ↦ prim(eq),
       o-acquire ↦ prim(acquire),
       o-int ↦ type(Int), o-bool ↦ type(Bool), o-unit ↦ type(Unit),
       o-string ↦ type(String), o-never ↦ type(Never), o-res ↦ type(Res),
       o-list ↦ type(List), o-option ↦ type(Option), o-result ↦ type(Result),
       o-type-narrative ↦ typeNarrative }
```

**Γ0（primitive）**：

```text
add : NFn<(Int, Int), Int, {}, ⟨⟩>        値 PrimVal(Reserved(o-add), add)
sub : NFn<(Int, Int), Int, {}, ⟨⟩>        値 PrimVal(Reserved(o-sub), sub)
mul : NFn<(Int, Int), Int, {}, ⟨⟩>        値 PrimVal(Reserved(o-mul), mul)
lt  : NFn<(Int, Int), Bool, {}, ⟨⟩>       値 PrimVal(Reserved(o-lt), lt)
le  : NFn<(Int, Int), Bool, {}, ⟨⟩>       値 PrimVal(Reserved(o-le), le)
eq  : NFn<(Int, Int), Bool, {}, ⟨⟩>       値 PrimVal(Reserved(o-eq), eq)
acquire : NFn<(Int), Owned<Res>, {}, ⟨⟩>  値 PrimVal(Reserved(o-acquire), acquire)
```

Γ0 は elaboration の初期 Γ ではなく、E-Prim（§4.2）と T-Prim（§5.1）だけが引く固定表である。
プログラムの elaboration は Γ = ∅ から始める（§4.1）。

`acquire` は識別子 n を持つ affine 資源値 `resource(n)` を導入する唯一の primitive である。
Owned の move / drop / finalization を Redex model で検査するには、`Owned` 型の値を作る経路が初期環境に一つ要る。

TypeInfo の生成は Γ0 の primitive ではなく、専用構文 `typeMake(spec)`（§4.8）だけが担う。
TypeInfo 生成関数を第一級値として渡す機能は G1 では扱わない。

**Δ0（型名）**：

```text
Int    ↦ TypeRep(Reserved(o-int), Int, Type)
Bool   ↦ TypeRep(Reserved(o-bool), Bool, Type)
Unit   ↦ TypeRep(Reserved(o-unit), Unit, Type)
String ↦ TypeRep(Reserved(o-string), String, Type)
Never  ↦ TypeRep(Reserved(o-never), Never, Type)
Res    ↦ TypeRep(Reserved(o-res), Res, Type)
List   ↦ TypeRep(Reserved(o-list), List, Type -> Type)
Option ↦ TypeRep(Reserved(o-option), Option, Type -> Type)
Result ↦ TypeRep(Reserved(o-result), Result, Type -> Type -> Type)
```

**Π0（capability）**：

```text
typeNarrativeCap ↦ (TypeNarrativeCap, Reserved(o-type-narrative))
```

**C0（constructor 表）**：

```text
true      : () -> Bool
false     : () -> Bool
nil<τ>    : () -> List<τ>
cons<τ>   : (τ, List<τ>) -> List<τ>
none<τ>   : () -> Option<τ>
some<τ>   : (τ) -> Option<τ>
ok<τ, σ>  : (τ) -> Result<τ, σ>
ng<τ, σ>  : (σ) -> Result<τ, σ>
```

**δ規則**（§5.3 で使う。`true()` は値 `Construct(Bool, true)` の略記、`false()` も同様）：

```text
δ(add, m, n) = m + n
δ(sub, m, n) = m - n
δ(mul, m, n) = m × n
δ(lt, m, n)  = true()  （m < n のとき）、false()（それ以外）
δ(le, m, n)  = true()  （m ≤ n のとき）、false()（それ以外）
δ(eq, m, n)  = true()  （m = n のとき）、false()（それ以外）
δ(acquire, n) = resource(n)
```

## 4. elaboration

### 4.1 judgment の形

```text
Γ; Δ; Π; B ⊢ e ⇒ τ ! ε ⟹ c        合成（synthesize）
Γ; Δ; Π; B ⊢ e ⇐ τ ! ε ⟹ c        検査（check）
```

未型付き縮小 Core の項 e が型 τ と Effect row ε を持ち、Typed Core の c へ変換されることを表す。
検査 judgment は、合成した型が期待型と同値（§6.3）であることの確認として定義する。
プログラム全体の elaboration は `∅; Δ0; Π0; ⟨⟩ ⊢ e0 ⇒ τ0 ! ε0 ⟹ c0` として行う。
Γ の初期値は空であり、Γ0（§3.5）は Γ の一部ではない。
primitive 名は E-Prim（§4.2）が PrimVal へ解決するため、初期 Γ に primitive の束縛は要らない。
この導出中に現れる E-Lambda（§4.3）・E-Recur（§4.6）の適用がそれぞれ組み立てる `(ℓ, NFn<(τ1, …, τk), τ, εdecl', ⟨⟩>)` / `(r, NFn<(τ1, …, τk), τ, ε', ⟨⟩>)` をすべて集めた表を Φ0 とし、elaboration 全体の出力は c0 単体ではなく CoreArtifact（§3.3）`⟨Φ0, c0⟩` とする。

**(E-Sub)**

```text
Γ; Δ; Π; B ⊢ e ⇒ τ' ! ε ⟹ c
Δ ⊢ τ' ≡ τ
--------------------------------
Γ; Δ; Π; B ⊢ e ⇐ τ ! ε ⟹ c
```

`Never` は任意の期待型に対して検査を通る（`return e` の型付けに使う）。

```text
Γ; Δ; Π; B ⊢ e ⇒ Never ! ε ⟹ c
--------------------------------
Γ; Δ; Π; B ⊢ e ⇐ τ ! ε ⟹ c
```

G1 の elaboration は flow-sensitive な ownership 解析を行わない。
affine 規律（move 済み place の再利用禁止など）は簡約意味論の Ω 遷移（§5.5）で動的に検査し、静的な flow 解析は G5 の borrow 解析と併せて導入する。

### 4.2 基本規則

**(E-Lit)**

```text
typeof(l) = τ
--------------------------------
Γ; Δ; Π; B ⊢ l ⇒ τ ! {} ⟹ l
```

**(E-Var)**

```text
Γ(x) = τ        τ は Owned<_> の形でない
--------------------------------
Γ; Δ; Π; B ⊢ x ⇒ τ ! {} ⟹ x
```

`Owned<τ>` 型の変数を裸で参照することはできない。
消費は必ず `move x`（E-Move）を経由する。

**(E-Prim)**

```text
x ∉ dom(Γ)        Γ0(x) = τ        Γ0 の x の値が PrimVal(Reserved(o), x)
--------------------------------
Γ; Δ; Π; B ⊢ x ⇒ τ ! {} ⟹ PrimVal(Reserved(o), x)
```

primitive 名は elaboration がその PrimVal へ解決する。
machine は値環境を持たず、簡約は PrimVal に直接 R-Delta（§5.3）を適用する。
局所束縛が同名の場合は `x ∈ dom(Γ)` なので E-Var が適用され、primitive を隠す。

**(E-Let)**

```text
Γ; Δ; Π; B ⊢ e1 ⇒ τ1 ! ε1 ⟹ c1
Γ, x : τ1; Δ; Π; B ⊢ e2 ⇒ τ2 ! ε2 ⟹ c2
--------------------------------
Γ; Δ; Π; B ⊢ let x = e1 in e2 ⇒ τ2 ! ε1 ∪ ε2 ⟹ Let(x : τ1, c1, c2)
```

**(E-Construct-Check)**

```text
C0(K) の宣言を期待型 D の型引数で具体化して (σ1, …, σk) -> D を得る
各 σi は Owned<_> の形でない
Γ; Δ; Π; B ⊢ ei ⇐ σi ! εi ⟹ ci        （i = 1 … k）
--------------------------------
Γ; Δ; Π; B ⊢ construct K(e1, …, ek) ⇐ D ! ε1 ∪ … ∪ εk
  ⟹ Construct(D, K, c1, …, ck)
```

constructor 適用は原則として検査位置で使う。

**(E-Construct-Synth)**

```text
C0(K) の宣言を型引数注釈 τ̄ で具体化して (σ1, …, σk) -> D を得る
各 σi は Owned<_> の形でない
Γ; Δ; Π; B ⊢ ei ⇐ σi ! εi ⟹ ci        （i = 1 … k）
--------------------------------
Γ; Δ; Π; B ⊢ construct K<τ̄>(e1, …, ek) ⇒ D ! ε1 ∪ … ∪ εk
  ⟹ Construct(D, K, c1, …, ck)
```

合成位置では型引数注釈 `construct K<τ̄>(ē)` を必須とする。
D は C0(K) の宣言を具体化して得られる型そのものであり、Typed Core の `Construct` ノードは検査位置・合成位置のどちらを経由しても、この D を自身のフィールドとして保持する。

field 型への `Owned<_>` の禁止は G1 の制限である。
構成済みデータは通常の値として複製されうる（R-Let の置換など）ため、affine 資源を field に入れると place を経由しない複製経路が生まれる。
コンテナ内の affine 資源は、G5 の borrow 設計と併せて扱う。

**(E-Eliminate)** [REQ: RET-003]

```text
Γ; Δ; Π; B ⊢ e0 ⇒ D ! ε0 ⟹ c0        D は C0 のデータ型の具体化
各枝 i：C0(Ki) の field 型を σ̄i として
  Γ, x̄i : σ̄i; Δ; Π; B ⊢ ei ⇐ τ ! εi ⟹ ci
枝は D の constructor をちょうど一度ずつ覆う
--------------------------------
Γ; Δ; Π; B ⊢ eliminate e0 { … } ⇐ τ ! ε0 ∪ ε1 ∪ … ∪ εn
  ⟹ Eliminate(c0, …)
```

`eliminate` は文 Narrative に相当し、boundary を push しない。
各枝の elaboration は B をそのまま受け取るため、枝の中の `return` は外側の最寄りの境界へ解決される。
これが RET-003（文 Narrative は明示的に指定されない限りローカル return boundary を作らない）の calculus 上の表現である。

### 4.3 関数と Narrative 適用

関数引数の署名は `Owned<_>` の形を含みうる。
E-Lambda は `Owned` の仮引数を関数本体の `Scope` と `Let` の連なりへ変換する。
β 簡約（§5.3 R-Beta）は実引数の値を生名の位置へ置換する。
置換の結果として `Let` の右辺に来た値は R-LetOwned が place へ移すため、引数値は place を経由して管理される。

関数は、外側の `Owned<_>` 束縛を closure の捕捉へ変換できる。
E-Lambda は捕捉した値を `Move` で `Curry` の固定引数へ渡し、closure の型を `Owned<NFn …>` とする。
元の place は `Move` によって `Moved` になり、closure の関数位置には `Move` を経由して到達する。
`Recur` と `RecurVal` の `Owned` 捕捉は、再帰本体の複製を一回の `Move` で制限できないため、E-Recur の制限として残す（§4.6）。

**(E-Lambda)** [REQ: EFF-001]

```text
C = ((u1, κ1), …, (un, κn)) = owned-captures(e, (a1, …, ak), Γ)
b fresh
ℓ fresh                                            （CallableId、§3.3）
εdecl' = resolveReturn(B, εdecl)                  （§4.5 の Return ラベル解決）
B' = push(B, FunctionBoundary(b, τ))
Γ, a1 : τ1, …, ak : τk; Δ; Π; B' ⊢ e ⇐ τ ! εbody ⟹ c
εbody \ {Return<b, τ>} ⊆ εdecl'
bodyC = Let(u1 : Owned<κ1>, c1,
             … Let(un : Owned<κn>, cn,
                   Let(ai1 : Owned<τi1>, yi1,
                     … Let(aim : Owned<τim>, yim, c) …)))
LC = Lam(User, ℓ, (c1, …, cn, y1, …, yk),
         Handle(Return<b, τ>, x -> x, Scope(∅, bodyC)))
Ti = Owned<NFn<(κi+1, …, κn, τ1, …, τk), τ, εdecl', ⟨⟩>>

--------------------------------
n = 0 のとき
  Γ; Δ; Π; B ⊢ fn(a1 : τ1, …, ak : τk) -> τ ! εdecl  e
    ⇒ NFn<(τ1, …, τk), τ, εdecl', ⟨⟩> ! {}
    ⟹ LC

n > 0 のとき
  Γ; Δ; Π; B ⊢ fn(a1 : τ1, …, ak : τk) -> τ ! εdecl  e
    ⇒ Owned<NFn<(τ1, …, τk), τ, εdecl', ⟨⟩>> ! (Own)
    ⟹ Let(t1 : T1, Curry(LC, Move(u1)),
         … Let(tn : Tn, Curry(Move(tn-1), Move(un)), Move(tn)) …)
Φ(ℓ) = NFn<(κ1, …, κn, τ1, …, τk), τ, εdecl', ⟨⟩>  （両方の枝に共通）
```

ここで `owned-captures` は、Γ の現在の可視項目から `Owned<κ>` の型を持つ名前を取り、`free-vars(e)` から `(a1, …, ak)` を除いた集合との共通部分を対象にする。
Γ に同名項目が複数あるときは、内側の項目だけを可視とする。
対象の名前は `symbol<?` の昇順に並べ、これを `u1, …, un` とする。
`ui` は捕捉元の surface 名であり、`ci` は捕捉 formal の生名である。
`yi` は、元の位置 i が `Owned` のときは生名、そうでないときは surface が書いた名前そのものである。
`ai` は元の仮引数の surface 名である。
`ti` は外側の `Let` が管理する place の生名であり、`t1, …, tn` は fresh である。
捕捉の `Let` の入れ子は `u1, …, un` の辞書順に並ぶ。
元の仮引数に対応する `Let` の入れ子は仮引数の位置の順序に一致する。
生名は対応する `Let` の右辺にちょうど 1 回だけ現れ、それ以外の位置には現れない。
`Let` の binder は surface が書いた仮引数の名前であり、束縛の様式は `let` である。
Φ に登録する署名は、捕捉位置の型を `Owned<κi>`、元の `Owned` 位置の型を `Owned<τi>` のまま持つ。
生名への読み替えは Core の項の側だけに起こる。
呼出し側は実引数を `Owned<τi>` として検査され、`move p` の形を要求される。
`n = 0` のときは `bodyC` の捕捉 `Let` 連鎖も省く。

関数抽象は自身の FunctionBoundary を push し、body を Return handler と Scope で包む。
`Owned` の仮引数に対応する `Let` はこの Scope の直下に置かれ、R-LetOwned が呼出しごとに place を確保する。
body が合成する Effect row から自身の境界への Return を除いた残りは、宣言 row の部分集合でなければならない。
これが EFF-001（展開後 Core の Effect row は展開前に宣言された Effect の部分集合）の calculus 上の表現である。
ℓ は fresh な CallableId であり、この導出が組み立てる `(ℓ, NFn<(κ1, …, κn, τ1, …, τk), τ, εdecl', ⟨⟩>)` は e0 全体の CoreArtifact の Φ に加わる（§3.3）。GUN（§3.3）により、e0 の elaboration 導出中に現れる他のすべての E-Lambda・E-Recur 適用の ℓ/r とは相異なる。

**(E-Apply)**

```text
Γ; Δ; Π; B ⊢ e0 ⇒ NFn<(τ1, …, τk), τ, ε, Q> ! ε0 ⟹ c0
Γ; Δ; Π; B ⊢ ei ⇐ τi ! εi ⟹ ci        （i = 1 … k）
obligations(Q) ⊆ dom-propositions(Π)
--------------------------------
Γ; Δ; Π; B ⊢ e0(e1, …, ek) ⇒ τ ! ε0 ∪ ε1 ∪ … ∪ εk ∪ ε
  ⟹ Apply(c0, c1, …, ck)
```

適用の Effect は、関数式と引数の Effect に潜在 row ε を合わせた和集合とする。
これはホワイトペーパー §11.5.2 の `combine(εa, εi, εo)` の G1 定義である。
Proof obligation の検査に使う集合は `obligations(⟨φ1, …, φn⟩) = {φ1, …, φn}`、`dom-propositions(Π) = { φ | (φ, O) ∈ range(Π) }` で定める。
Q の各命題は Π に存在しなければならない。
origin の検査は §3.4 のとおり `verify-origins` が Typed Core 全体に対して行う。

### 4.4 curry

**(E-Curry)** [REQ: CUR-001] [REQ: CUR-002]

```text
Γ; Δ; Π; B ⊢ e1 ⇒ F ! εf ⟹ c1        （k ≥ 1）
peel-owned-function(F) = (NFn<(τ1, τ2, …, τk), τ, ε, Q>, owned_f)
Γ; Δ; Π; B ⊢ e2 ⇐ τ1 ! εa ⟹ c2
b = owned_f ∨ owned-type?(τ1)
--------------------------------
Γ; Δ; Π; B ⊢ curry(e1, e2)
  ⇒ (if b then Owned<NFn<(τ2, …, τk), τ, ε, specialize(Q, e2)>>
      else NFn<(τ2, …, τk), τ, ε, specialize(Q, e2)>) ! εf ∪ εa
  ⟹ Curry(c1, c2)
```

curry は先頭引数を固定し、返り値型 τ と潜在 Effect row ε を保存し、Proof obligation を固定引数で特殊化する（CUR-001）。
G1 には Effect 多相がないため `specialize(ε, a) = ε` であり、`specialize(Q, a)` は Q の中の先頭引数への参照を a で置換する。

固定引数の型が `Owned<τ1>` であるか、関数側の型が `Owned<NFn …>` であるとき、結果型も `Owned<NFn 残余>` になる。
どちらも該当しないときは、結果型は従来どおり素の `NFn 残余` である。
関数側の標識は連鎖の次の段へ引き継ぐ。
関数の位置で `Owned<NFn …>` を使うときは `Move` または `CurryVal` を経由する。
`CurryVal` の固定引数は還元後に payload の型で現れるため、宣言型が `Owned<τ1>` のときは payload を `Owned` で包んで照合する。

値レベルの origin は簡約規則（§5.3 R-CurryVal）が §3.4 の origin metafunction を使って定める。
`origin(RecurVal(…)) = User` なので、recur で束縛した関数の curry は User に根ざす派生 origin を持つ。

```text
origin(CurryVal(O', vf, va)) = O' = Derived(origin(vf), Curry(va))
```

curry は新しい `Reserved` origin を決して作らない（CUR-002）。

```text
origin(curry(f, a)) ≠ Reserved(new-id)
```

### 4.5 return と boundary

宣言 row の中の境界 ID を持たないラベル `Return` は、elaboration が次で解決する。

```text
resolveReturn(B, ε) = ε の各 Return を Return<b, τ> に置換
                      （nearestReturn(B) = Frame(b, τ)）
```

**(E-Return)** [REQ: RET-001]

```text
nearestReturn(B) = Frame(b, τ)        Frame は FunctionBoundary または ExpressionBoundary
Γ; Δ; Π; B ⊢ e ⇐ τ ! ε ⟹ c
--------------------------------
Γ; Δ; Π; B ⊢ return e ⇒ Never ! {Return<b, τ>} ∪ ε
  ⟹ Perform(Return<b, τ>, c)
```

`return` の送信先は実行時の探索ではなく、elaboration 時に boundary stack から静的に決まる（RET-001）。
返す式は境界の型 τ に対して検査される。

**(E-NarrativeExpr)** [REQ: RET-002]

```text
b fresh
B' = push(B, ExpressionBoundary(b, τ))
Γ; Δ; Π; B' ⊢ e ⇐ τ ! ε ⟹ c
--------------------------------
Γ; Δ; Π; B ⊢ narrativeExpr(e) ⇐ τ ! ε \ {Return<b, τ>}
  ⟹ Handle(Return<b, τ>, x -> x, Scope(∅, c))
```

式 Narrative は自身の ExpressionBoundary を push する。
その中の `return` は E-Return を通じて境界の型 τ、すなわち当該式の返り値型と unify する（RET-002）。
境界への Return Effect は handler が処理するため、式の外へは漏れない。

### 4.6 recur、yield、suspend

**(E-Recur)** [REQ: RET-003] [REQ: REC-001] [REQ: EFF-001]

```text
e1 の自由変数のうち f と x1, …, xk 以外のものは、Γ で Owned<_> の形の型を持たない
r fresh                                            （CallableId、§3.3。表層名 f とは別に割り当てる）
ε' = resolveReturn(B, εdecl)
Γf = Γ, f : NFn<(τ1, …, τk), τ, ε', ⟨⟩>
Γf, x1 : τ1, …, xk : τk; Δ; Π; B ⊢ e1 ⇐ τ ! εbody ⟹ c1
εbody ⊆ ε'
Γf; Δ; Π; B ⊢ e2 ⇒ τ2 ! ε2 ⟹ c2
Recur(r, f, (y1, …, yk),
      Scope(∅, Let(xi1 : Owned<τi1>, yi1,
                … Let(xim : Owned<τim>, yim, c1) …)),
      c2) ⇓class κc      （§6.2）
κc = Unknown ならば Partial ∈ ε'
--------------------------------
Γ; Δ; Π; B ⊢ recur f(x1 : τ1, …, xk : τk) -> τ ! εdecl = e1 in e2
  ⇒ τ2 ! ε2 ⟹ Recur(r, f, (y1, …, yk),
                     Scope(∅, Let(xi1 : Owned<τi1>, yi1,
                               … Let(xim : Owned<τim>, yim, c1) …)),
                     c2)
  かつ Φ(r) = NFn<(τ1, …, τk), τ, ε', ⟨⟩>
```

`Recur` と `RecurVal` の `Owned` 捕捉は G5c5b2 では扱わない。
R-RecurUnfold（§5.4）は再帰本体を呼出しごとに複製するため、`RecurVal` の型を `Owned` にしても捕捉した値の使用回数を上限づけられない。
この制限は Phase 1 以降へ送る。

R-RecurBind（§5.4）が生成する `RecurVal` は次の形を持つ。

```text
RecurVal(r, f, (y1, …, yk),
         Scope(∅, Let(xi1 : Owned<τi1>, yi1,
                   … Let(xim : Owned<τim>, yim, c1) …)))
```

ここで `Scope` は `Let` の連なりの外側にあり、連なりの直後に元の本体 c1 が来る。
継続 c2 は `Scope` の外にあり、包みの影響を受けない。
再帰の関数名 f は `Scope` の外で束縛され、位置は変わらない。
m が 0 のとき、つまり `Owned` の仮引数が無いとき、`Scope` も `Let` も入らない。節の形はこれまでと同一である。
recur は関数境界を押さないため、包まないと呼出し側の `Scope` へ place が積み上がる。
R-RecurUnfold（§5.4）は本体を複製するが、各呼出しの引数の place はその呼出しの `Scope` が管理する。
計算分類は、継続 c2 を含む Recur 項全体に対して行う（C-Guarded は c2 が f の適用であることも検査する。§6.2）。
r は fresh な CallableId であり、表層名 f そのものを内部識別子として使うのではない（f は同じ CoreArtifact 内の他の `recur` と衝突しうる。§3.3）。この導出が組み立てる `(r, NFn<(τ1, …, τk), τ, ε', ⟨⟩>)` は e0 全体の CoreArtifact の Φ に加わる。GUN（§3.3）により、e0 の elaboration 導出中に現れる他のすべての E-Lambda・E-Recur 適用の ℓ/r とは相異なる。

`recur` は loop の lowering 先となる内部 marker であり、関数境界を push しない（RET-003 の適用対象）。
body の中の `return` は外側の最寄りの境界へ解決される。
これにより、Surface の `for` の body にある `return` が関数境界へ伝播する意味論（ホワイトペーパー §3.2.2）が Core 上で再現される。
body の row 包含 `εbody ⊆ ε'` は、E-Lambda の row 包含と同じ EFF-001 の表現である。

計算分類が Unknown の再帰は、宣言 row に `Partial` を含む場合に限り許可する（ホワイトペーパー §7.1 の扱い）。
分類が保証を持てない場合に Unknown へ落ちること自体は REC-001 の要求である。

**(E-Yield)**

```text
Γ; Δ; Π; B ⊢ e1 ⇒ τ1 ! ε1 ⟹ c1
Γ; Δ; Π; B ⊢ e2 ⇒ τ2 ! ε2 ⟹ c2
--------------------------------
Γ; Δ; Π; B ⊢ yield e1; e2 ⇒ τ2 ! ε1 ∪ ε2 ∪ {Yield<τ1>}
  ⟹ Yield(c1, c2)
```

**(E-Suspend)**

```text
Γ; Δ; Π; B ⊢ e ⇒ τ ! ε ⟹ c
--------------------------------
Γ; Δ; Π; B ⊢ suspend e ⇒ τ ! ε ∪ {Suspend} ⟹ Suspend(c)
```

### 4.7 move と drop

**(E-Move)** [REQ: OWN-001]

```text
Γ(x) = Owned<τ>
--------------------------------
Γ; Δ; Π; B ⊢ move x ⇒ Owned<τ> ! {Own} ⟹ Move(x)
```

**(E-Drop)** [REQ: OWN-002]

```text
Γ; Δ; Π; B ⊢ e ⇒ Owned<τ> ! ε ⟹ c
--------------------------------
Γ; Δ; Π; B ⊢ drop e ⇒ Unit ! ε ∪ {Own} ⟹ Drop(c)
```

**(E-DropVar)** [REQ: OWN-002]

```text
Γ(x) = Owned<τ>
--------------------------------
Γ; Δ; Π; B ⊢ drop x ⇒ Unit ! {Own} ⟹ Drop(Move(x))
```

`Owned` 型の変数は裸で参照できない（E-Var）ため、`drop x` は E-Drop からは導出できない。
E-DropVar が Move を挿入し、place の消費を Move が担う。

E-Move、E-Drop、E-DropVar は row に `Own` を記録する。
関数 body の `Own` は宣言 row の包含（E-Lambda、§4.3）を通じて NFn の潜在 row に残り、Handle が row から除くのは境界の `Return<b, τ>` だけなので、`Own` は一度入った row から消えない。
このため、合成 row に `Own` を含まない項は、自身にも、そこから適用で到達する呼び先の body にも Move / Drop を含まない。

### 4.8 TypeInfo の生成と束縛

**(E-TypeMake)** [REQ: TYP-001] [REQ: TYP-002]

```text
Δ ⊢ spec ⇒ (t, κ)                          （spec の解釈、下記）
authorized(Π)                               （TypeNarrativeCap, _) ∈ Π
--------------------------------
Γ; Δ; Π; B ⊢ typeMake(spec) ⇒ TypeInfo<κ> ! {Compile}
  ⟹ TypeRep(Derived(Reserved(o-type-narrative), Make(t)), t, κ)
```

spec の解釈は次で定める。

```text
Δ(T) = TypeRep(O, t, κ)
--------------------------------
Δ ⊢ T ⇒ (t, κ)

Δ ⊢ spec0 ⇒ (t0, Type -> … -> Type -> Type)        t0 は未適用 constructor、引数 k 個
Δ ⊢ speci ⇒ (τi, Type)        （i = 1 … k、個数一致）
--------------------------------
Δ ⊢ spec0<spec1, …, spek> ⇒ (t0<τ1, …, τk>, Type)
```

kind application は飽和でなければならない（TYP-002）。
部分適用の TypeInfo を型位置（`fn` の注釈など）に置くことはできず、型位置に置けるのは kind が `Type` の TypeInfo だけである。
適用の頭 t0 は未適用 constructor に限り、G1 の組み込み constructor の引数 kind はすべて `Type` である。
TypeInfo の生成には Π に TypeNarrative の capability が必要である。

Make step が記録するのは spec そのものではなく、解釈後の型式 t である。
spec の中の型名（`letType` で束縛した T を含む）は elaboration の Δ でしか解決できず、Δ を持たない verify-origins（§3.4）では照合できないためである。

**(E-LetType)** [REQ: TYP-001]

G1 の `letType` は右辺を `typeMake(spec)` の形に限る。
spec の解釈は Finite なので、elaboration がその場で TypeRep を構成して Δ を拡張できる。

```text
Δ ⊢ spec ⇒ (tT, κ)
authorized(Π)
Δ' = Δ, T ↦ TypeRep(Derived(Reserved(o-type-narrative), Make(tT)), tT, κ)
Γ; Δ'; Π; B ⊢ e2 ⇒ τ2 ! ε2 ⟹ c2
--------------------------------
Γ; Δ; Π; B ⊢ letType T = typeMake(spec) in e2 ⇒ τ2 ! ε2 ∪ {Compile} ⟹ c2
```

TypeRep の構成は elaboration 時に完了するため、出力の Typed Core は c2 だけである。
Compile Effect は結果 row に残し、型 phase の計算を行ったことを宣言に反映させる。
`⊢core`（§5.1）はこの `Compile` を復元できない。
T-Val は `TypeRep(O, t, κ)` を `TypeInfo<κ> ! {}` で型付けし、letType の出力 `c2` 単体から `Compile` を導く規則もないためである。
この乖離は §5.1 の一般対応の例外であり、`Compile` を検査する classify 規則がないため ⇓class の健全性には影響しない（§6.2）。
Δ を拡張する規則はこれと初期環境だけである。
初期環境の TypeRep は type sort の `Reserved` origin を持ち、letType が導入する TypeRep は `Derived(Reserved(o-type-narrative), Make(t))`（t はその TypeRep が保持する型式）を持つ（TYP-001、§7 性質 5）。
手書きの `TypeRep(User, …)` や偽造 origin の TypeRep を Δ へ入れる経路は存在しない。
一般の TypeInfo 計算の実行時 staging は Phase 4（Proof と再帰分類）で扱う。

### 4.9 Proof term

G1 の Proof 値は `ProofRep(O, φ)` である。
未型付き縮小 Core に Proof 値を直接構築する構文はなく、Π0 の capability と、予約 NFn の適用結果だけが ProofRep を導入できる。
`Reserved` origin を持つ ProofRep をユーザー項から構築する経路が存在しないことが、PRF-001（予約 Proof はユーザーコードから forge できない）の calculus 上の表現である。
偽造 origin を持つ手書き Typed Core は `verify-origins` が拒否する。 [REQ: PRF-001]

Proof term の同値上の扱いは §6.3 で定める。

## 5. 簡約意味論

### 5.1 Typed Core の型付け

メタ理論性質（§7）の検査には、elaboration と独立に Typed Core を型付けする judgment が要る。

```text
Γ; Δ; Π; Ξ; Φ ⊢core c : τ ! ε
```

この judgment は §4 の elaboration 規則から入力構文と B を除き、place typing Ξ（§2）と Φ（§3.3 の CoreArtifact）を加えたものに一致する。
ただし E-TypeMake・E-LetType（§4.8）が row に加える `Compile` はこの対応の例外であり、⊢core 側からは復元できない（§4.8 末尾）。
boundary stack が不要なのは、Typed Core では境界が `Handle` ノードとして陽に現れるためである。
変数を型付けする規則は E-Var 対応だけであり、E-Prim に対応する規則はない。
E-Prim は裸の primitive 名を PrimVal へ解決する変換規則であり、⊢core では T-Prim（下記）が PrimVal 値そのものを型付けする。
machine は変数の lookup 規則を持たないため、閉じた構成に裸の変数を残す手書きの Typed Core は well-typed にならず、stuck もこの型付けの失敗として排除される。
elaboration の出力は閉じており place を含まないため、Γ = ∅、Ξ = ∅ で型付けできる。
Ξ が要るのは簡約途中の構成の検査（⊢config、本節末尾）だけである。
一方 Φ は Ξ と異なり、この初期時点で既に空とは限らない。
elaboration 済みの c が `Recur` ノードを含む限り、その `f` の署名は Φ にしか残っていないためである（§3.3）。
Φ は CoreArtifact `⟨Φ, c⟩` の一部として elaboration 時点で確定し、以後の簡約はこれを一切変更しない。
elaboration 規則と重複しない規則だけを挙げる。

**(T-Prim)**

```text
Γ0(name) = τ        Γ0 の name の値が PrimVal(Reserved(o), name)
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core PrimVal(Reserved(o), name) : τ ! {}
```

**(T-Handle)**

```text
Γ; Δ; Π; Ξ; Φ ⊢core c : τ ! ε
Γ, x : τ; Δ; Π; Ξ; Φ ⊢core ch : τ ! εh
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Handle(Return<b, τ>, x -> ch, c) : τ ! (ε \ {Return<b, τ>}) ∪ εh
```

**(T-Perform)** [REQ: RET-002]

```text
Γ; Δ; Π; Ξ; Φ ⊢core c : τ ! ε
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Perform(Return<b, τ>, c) : Never ! ε ∪ {Return<b, τ>}
```

Perform が運ぶ値の型は op の型成分 τ と一致する。
この一致が、境界 b の handler が受け取る値の型を保証する（§7 性質 4 の基礎）。

**(T-Scope)**

```text
Γ; Δ; Π; Ξ; Φ ⊢core c : τ ! ε
π の各 place は dom(Ξ) に含まれる
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Scope(π, c) : τ ! ε
```

**(T-MovePlace)** [REQ: OWN-001]

```text
Ξ(p) = τ
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Move(p) : Owned<τ> ! {Own}
```

**(T-Resource)**

```text
Γ; Δ; Π; Ξ; Φ ⊢core resource(n) : Owned<Res> ! {}
```

**(T-OwnedLeaf)** [REQ: OWN-009]

```text
Γ; Δ; Π; Ξ; Φ ⊢core v : τ ! ε        owned-type?(τ)
------------------------------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core OwnedLeaf(tk, v) : τ ! ε
```

`OwnedLeaf` は payload の型をそのまま持つ実行時の印であり、型をもう一段 `Owned` で包まない。
leaf は値の内部の `Rec` 欄または別の leaf の payload にだけ置き、値の根には置かない。
`tk` は `Λtok` の一意な token であり、型付けだけでは token の重複や状態を判定しない。

**(T-Error)**

```text
p ∈ dom(Ξ)
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Error(p) : τ ! {}
```

`Error(p)` は伝播して終端構成に至るだけのノードなので、`Never` と同様に任意の型で型付けする。
これにより Error を含む構成でも Preservation（§7 性質 1）が文脈の下で成り立つ。

**(T-Recur)**

```text
Φ(r) = NFn(τ1, ..., τk, τ, ε', Q)
Γ, f : NFn(τ1, ..., τk, τ, ε', Q), x1 : τ1, ..., xk : τk; Δ; Π; Ξ; Φ ⊢core c1 : τ ! εbody
εbody ⊆ ε'
Γ, f : NFn(τ1, ..., τk, τ, ε', Q); Δ; Π; Ξ; Φ ⊢core c2 : τ2 ! ε2
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Recur(r, f, (x1, ..., xk), c1, c2) : τ2 ! ε2
```

f の署名は項から消去されているため、この規則は CallableId `r` を鍵に Φ から読み出す（§3.3、§4.6 E-Recur）。表層名 f は Γ を拡張する束縛子としてのみ使い、Φ の検索には使わない（f は他の `Recur` ノードと衝突しうるため。§3.3）。
`c1` を Φ 由来の署名で実際に検査するのは、手書きの Typed Core が signature と body の食い違う `Recur` を偽造できないようにするためである。

**(T-RecurVal)**

```text
Φ(r) = NFn(τ1, ..., τk, τ, ε', Q)
Γ, f : NFn(τ1, ..., τk, τ, ε', Q), x1 : τ1, ..., xk : τk; Δ; Π; Ξ; Φ ⊢core c : τ ! εbody
εbody ⊆ ε'
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core RecurVal(r, f, (x1, ..., xk), c) : NFn(τ1, ..., τk, τ, ε', Q) ! {}
```

RecurVal は R-RecurBind（§5.4）が Recur から作る値であり、その型付けは対応する T-Recur の body 側 premise と同じ形をとる。r は Recur から引き継がれる（§5.4）。

**(T-Lam)**

```text
Φ(ℓ) = NFn(τ1, ..., τk, τ, ε', Q)
Γ, x1 : τ1, ..., xk : τk; Δ; Π; Ξ; Φ ⊢core c : τ ! εbody
εbody ⊆ ε'
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Lam(O, ℓ, (x1, ..., xk), c) : NFn(τ1, ..., τk, τ, ε', Q) ! {}
```

Lam のパラメータ・返り値型・宣言 row は項から消去されているため、この規則は CallableId `ℓ` を鍵に Φ から読み出す（§3.3、§4.3 E-Lambda）。T-RecurVal と同様、body を Φ 由来の署名で検査することで、手書きの Typed Core が signature と body の食い違う `Lam` を偽造できないようにする。O には制約を課さない（§3.4 の verify-origins が別途 O = User を要求する）。

**(T-CurryVal)** [REQ: CUR-002]

```text
Γ; Δ; Π; Ξ; Φ ⊢core vf : F ! {}        （k ≥ 1）
peel-owned-function(F) = (NFn(τ1, τ2, ..., τk, τ, ε, Q), owned_f)
Γ; Δ; Π; Ξ; Φ ⊢core va : A ! {}
A と τ1 が互換である。τ1 が Owned<τ> のときは A を Owned<A> として照合する。
b = owned_f ∨ owned-type?(τ1)
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core CurryVal(O, vf, va)
  : (if b then Owned<NFn(τ2, ..., τk, τ, ε, specialize(Q, va))>
      else NFn(τ2, ..., τk, τ, ε, specialize(Q, va))) ! {}
```

`vf` は値なので T-Lam・T-RecurVal・T-CurryVal のいずれかで再帰的に synthesize でき、`Curry`/`Apply` の呼び出し先位置に直接置かれた生の `Lam`/`RecurVal`（Φ(ℓ)/Φ(r) 経由）も、この位置の期待型を経由せず単独で型付けできる。O の整合は verify-origins（§3.4）が別途検査する。

**(T-Construct)**

```text
C0(K) の宣言を D の型引数で具体化して (σ1, …, σk) -> D を得る
各 σi は Owned<_> の形でない
Γ; Δ; Π; Ξ; Φ ⊢core vi : σi ! {}        （i = 1 … k）
--------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core Construct(D, K, v1, …, vk) : D ! {}
```

`Construct` も `D` を自身のフィールドとして保持するため、`vf` と同様に外部の期待型を経由せず単独で synthesize できる。
これは E-Construct-Check・E-Construct-Synth（§4.2）双方の前提をそのまま Typed Core の型付けへ転写した規則であり、手書きの Typed Core が D と K・field の型を食い違わせて偽造することも防ぐ。

**(T-Val)**：残る値の型付けは、リテラルの typeof、Lam への T-Lam、CurryVal への T-CurryVal、RecurVal への T-RecurVal で定める。
`TypeRep(O, t, κ)` は `TypeInfo<κ>`、`ProofRep(O, φ)` は `Proof<φ>` で型付けする。

構成の well-formedness **⊢config** を次で定める。

```text
dom(Ξ) = dom(H) = dom(Ω)
各 p ∈ dom(H) について ∅; Δ0; Π0; Ξ; Φ ⊢core H(p) : Owned<Ξ(p)> ! {}
∅; Δ0; Π0; Ξ; Φ ⊢core c : τ ! ε
--------------------------------
Ξ; Φ ⊢config ⟨c, H, Ω, Λtok, θ⟩ : τ ! ε
```

`Ξ` は heap の値から導く写像である。heap を place 番号順に走査し、各値をそれまでに確定した `Ξ` の下で型付けし、place の型から外側の `Owned` を取り除いて次の写像へ加える。前方の place を参照する値はこの導出に失敗する。

値の内部に入った所有資源は `(OwnedLeaf tk v)` で表す。leaf の型は payload `v` の型そのものであり、payload が `Owned` 型であることを要求する。値そのものが所有資源である場合は、従来どおり root place と `Ω` で表すため、root 位置の leaf は許さない。leaf は `Rec` の欄、`Construct` の欄、`CurryVal` の関数と固定引数の位置、または leaf の payload の内部に置ける。ただし payload 自体が leaf である直接の入れ子は許さない。`Rec` の欄は label を、`Construct` の欄と `CurryVal` の位置は 0 起点の位置を path の segment とする。未対応の値構成子の内部へ隠した leaf は構成検査で拒否する。
この root 位置の禁止は heap の値と `Ξ` の導出に対する構成検査の規則である。`Yield` の観測 payload や `Curry`、`Apply`、`Let`、`Drop` のような control の producer 値位置では、producer が作る途中の root leaf を許し、その token を後続の縮約で消費または rehome する。

`Λtok` の live 集合は、制御項、`Ω(p)=Available` の root の値、および trace の `obs` の payload を走査して得る。`Moved`/`Dropped` の root の heap entry は履歴なので live 集合から除く。trace の `obs` の payload は観測後も回収前の値として残るため live 集合へ含める。live 集合での token の重複、`Λtok` に無い token、`Available`/`Moved` なのに live 集合へ一度も現れない token、`Dropped` なのに live 集合へ現れる token は不正である。`Dropped` の tombstone が live 集合に現れないことは正しい。

Redex model の `config-ok?` はこの二段の `Ξ` 導出と token 条件を検査する。通常の型検査入口は `OwnedLeaf` の `Rec` 欄を `owned-record-field` で拒否するが、構成検査の再型付けに限って leaf payload の `Owned` を許す。

ここでの Φ は、初期構成を作る CoreArtifact `⟨Φ0, c0⟩` の Φ0 をそのまま指す。
簡約のどの規則も Φ を書き換えないため、Φ は実行全体を通じて不変であり、Preservation（§7 性質 1）は Ξ と c の変化についてだけ述べればよい。

### 5.2 machine 構成と評価文脈

簡約は構成（configuration）の間の小ステップ関係で定める。

```text
⟨c, H, Ω, Λtok, θ⟩ → ⟨c', H', Ω', Λtok', θ'⟩
```

初期構成はプログラム c0 に対して `⟨Scope(∅, c0), ∅, ∅, ∅, ⟨⟩⟩` とする。

評価文脈は二層に分ける。

```text
F ::= []                                          純粋文脈（Scope と Handle を含まない）
    | Apply(v̄, F, c̄) | Let(x : τ, F, c)
    | Construct(D, K, v̄, F, c̄) | Eliminate(F, br̄)
    | Perform(op, F) | Drop(F) | Yield(F, c)
    | Curry(F, c) | Curry(v, F)

E ::= F | E[Scope(π, F)] | E[Handle(op, h, F)]    一般文脈

G ::= F | G[Handle(op, h, F)]                     Scope を含まない一般文脈
```

以降の規則は、明示しない限り一般文脈 E の下で適用される。
項だけを書いた規則 `E[c] → E[c']` は、H、Ω、Λtok、θ を変えない構成遷移 `⟨E[c], H, Ω, Λtok, θ⟩ → ⟨E[c'], H, Ω, Λtok, θ⟩` の略記である。
Perform の伝播規則（R-ScopeAbort、R-HandleSkip、R-HandleReturn）は F の純粋性を条件に使い、内側の frame から順に一段ずつ処理する。
G は R-LetOwned（§5.3）が最寄りの Scope を特定するために使う。
初期構成が最外に Scope を持ち、簡約が Scope を項の外へ運び出さないため、redex を囲む Scope は常に存在する。

### 5.3 関数適用と curry

**(R-Delta)**

```text
E[Apply(PrimVal(O, opname), v1, …, vk)] → E[δ(opname, v1, …, vk)]
```

**(R-Beta)**

```text
E[Apply(Lam(O, ℓ, (x1, …, xk), c), v1, …, vk)] → E[c[v1/x1, …, vk/xk]]
```

ℓ は束縛子ではないため置換の対象にならず、単に破棄される。

**(R-CurryVal)** [REQ: CUR-002]

```text
E[Curry(vf, va)] → E[CurryVal(Derived(origin(vf), Curry(va)), vf, va)]
```

部分適用値の origin は、元の関数の origin に Curry step を積んだ派生 origin である。
`Reserved` を新規に作る遷移はない。

**(R-ApplyCurry)** [REQ: CUR-001]

```text
E[Apply(CurryVal(O, vf, va), v1, …, vk)] → E[Apply(vf, va, v1, …, vk)]
```

**(R-Let)**

```text
E[Let(x : τ, v, c)] → E[c[v/x]]        （τ が Owned<_> の形でないとき）
```

**(R-LetOwned)**

```text
p fresh
--------------------------------
⟨E[Scope(π, G[Let(x : Owned<τ>, v, c)])], H, Ω, Λtok, θ⟩
  → ⟨E[Scope(π · p, G[c[p/x]])], H[p ↦ v], Ω[p ↦ Available], Λtok, θ⟩
```

Owned 値の束縛は place を確保し、最も内側の Scope の管理列 π へ登録する。
文脈 G は Scope を含まないため、割り当て先は redex を囲む最寄りの Scope に一意に定まる（間に Handle frame があってもよい）。
変数 x の出現は place p で置換され、以後の消費は Move(p) を通る。
束縛値が根の `OwnedLeaf(tk, v)` のときは、`v` を place へ移して `tk` を `Dropped` の tombstone とする。
この場合は place と `Ω` が root の所有を引き継ぎ、入れ子の根 leaf は拒否する。

### 5.4 データと再帰

**(R-Eliminate)**

```text
E[Eliminate(Construct(D, Ki, v1, …, vk), …, (Ki(x̄i) -> ci), …)]
  → E[ci[v1/xi1, …, vk/xik]]
```

**(R-RecurBind)**

```text
E[Recur(r, f, (x̄), c1, c2)] → E[c2[RecurVal(r, f, (x̄), c1)/f]]
```

r はそのまま RecurVal へ引き継がれる。

**(R-RecurUnfold)**

```text
E[Apply(RecurVal(r, f, (x1, …, xk), c), v1, …, vk)]
  → E[c[RecurVal(r, f, (x̄), c)/f, v1/x1, …, vk/xk]]
```

**(R-Yield)**

```text
⟨E[Yield(v, c)], H, Ω, Λtok, θ⟩ → ⟨E[c], H, Ω, Λtok, θ · obs(v)⟩
```

**(R-Suspend)**

```text
E[Suspend(c)] → E[c]
```

`Suspend` は 1 step を消費する区切りであり、観測イベントを生成しない。
このため計算分類（§6.2）の guard には数えない。
Suspend を corecursion の生産性 guard として使う設計は、観測意味論の拡張と併せて G2 以降で扱う。

### 5.5 move、drop、affine 検査

**(R-Move)** [REQ: OWN-001]

```text
Ω(p) = Available
--------------------------------
⟨E[Move(p)], H, Ω, Λtok, θ⟩ → ⟨E[H(p)], H, Ω[p ↦ Moved], Λtok, θ⟩
```

**(R-MoveError)** [REQ: OWN-001]

```text
Ω(p) ∈ {Moved, Dropped}
--------------------------------
⟨E[Move(p)], H, Ω, Λtok, θ⟩ → ⟨E[Error(p)], H, Ω, Λtok, θ⟩
```

`Error(p)` は値ではなく、`Perform` と同様に文脈を捨てながら外へ伝播する（§5.6 R-ScopeError、§5.7 R-HandleError）。
最外まで伝播した `⟨Error(p), H, Ω, Λtok, θ⟩` の形の終端構成を **OwnershipError** と呼ぶ。
move 済みまたは drop 済みの place の再利用は、暗黙に進行せず必ずこの終端へ落ちる。
Redex model の負例テストはこの遷移を確認する。

**(R-Drop)** [REQ: OWN-010]

```text
⟨E[Drop(v)], H, Ω, Λtok, θ⟩ → ⟨E[unit], H, Ω, Λtok', θ⟩
  Λtok' = drop-leaves(v, Λtok)
```

Drop の引数は Move を経て取り出された値であり、place の状態遷移は Move 側で済んでいる。
値の内部の leaf は同じ走査で `Available` から `Dropped` へ遷移するが、`R-Drop` は `fin`/`finLeaf` イベントを記録しない。leaf の token が無い、または `Moved`/`Dropped` のときは規則を適用しない。

### 5.6 scope exit と finalization

`finalize(π, H, Ω, Λtok, θ)` を次で定める。

```text
π = ⟨p1, …, pn⟩ のとき、pn から p1 の逆順に走査する。
Ω(pi) = Available である pi の値 H(pi) を走査し、内部 leaf の token を
Λtok[tk ↦ Dropped] としてから Ω[pi ↦ Dropped] とする。
各 leaf の `finLeaf(pi, fp)` を path 順に θ へ追記し、最後に `fin(pi)` を追記する。
Available でない pi には何もしない。leaf の token のいずれか一つでも Available でない場合は
finalize 全体を失敗させ、scope exit 規則を発火させない。
```

**(R-ScopeValue)** [REQ: OWN-002] [REQ: OWN-010]

```text
⟨E[Scope(π, v)], H, Ω, Λtok, θ⟩ → ⟨E[v], H, Ω', Λtok', θ'⟩
  （Ω', Λtok', θ'）= finalize(π, H, Ω, Λtok, θ)
```

scope の正常終了は、その scope が管理する未消費の affine resource を逆順で drop する。
finalize は Available の place だけを Dropped へ遷移させるため、drop は place ごとに高々一度である（OWN-002）。

**(R-ScopeAbort)** [REQ: OWN-003]

```text
⟨E[Scope(π, F[Perform(op, v)])], H, Ω, Λtok, θ⟩ → ⟨E[Perform(op, v)], H, Ω', Λtok', θ'⟩
  （Ω', Λtok', θ'）= finalize(π, H, Ω, Λtok, θ)
```

Perform が scope を越えて外側の handler へ向かうとき、越えられる scope は自身の finalization を実行してから消える。
非局所 return を含むすべての scope exit path が cleanup を実行する（OWN-003）。
F は純粋文脈なので、内側の scope から順に finalization が走る。

**(R-ScopeError)** [REQ: OWN-003]

```text
⟨E[Scope(π, F[Error(p)])], H, Ω, Λtok, θ⟩ → ⟨E[Error(p)], H, Ω', Λtok', θ'⟩
  （Ω', Λtok', θ'）= finalize(π, H, Ω, Λtok, θ)
```

ownership error の伝播も scope exit path であり、越えられる scope は finalization を実行してから消える。
ホワイトペーパー §4.9 の panic 経路の cleanup に相当する。

### 5.7 handler

**(R-HandleValue)**

```text
E[Handle(op, x -> ch, v)] → E[v]
```

**(R-HandleReturn)** [REQ: RET-002]

```text
E[Handle(Return<b, τ>, x -> ch, F[Perform(Return<b, τ>, v)])] → E[ch[v/x]]
```

**(R-HandleSkip)**

```text
op ≠ op'
--------------------------------
E[Handle(op', x -> ch, F[Perform(op, v)])] → E[Perform(op, v)]
```

**(R-HandleError)**

```text
E[Handle(op, x -> ch, F[Error(p)])] → E[Error(p)]
```

handler は自身の op に一致する Perform だけを処理し、一致しない Perform は handler ごと文脈を捨てて外へ伝播する（abortive）。
`Error(p)` は handler の処理対象ではなく、常に handler ごと文脈を捨てて伝播する。
F は純粋文脈なので、Perform と handler の間に Scope があれば R-ScopeAbort が先に適用され、finalization が漏れない。
op の一致は境界 ID b と型 τ の両方の一致である。
型の異なる境界が Return を横取りすることはない（§7 性質 4）。

## 6. 観測と計算分類

### 6.1 観測関係

**観測関係** `c ⇓obs n ⟨u1, …, un⟩` を次で定める。

```text
⟨Scope(∅, c), ∅, ∅, ∅, ⟨⟩⟩ →* ⟨c', H, Ω, Λtok, θ⟩ であって、
θ に含まれる obs イベントの先頭 n 個が obs(u1), …, obs(un) である
有限の簡約列が存在する。
```

観測は `yield` が生成する値の列であり、`fin` と `finLeaf` イベントは観測に数えない。
Productive の意味はこの関係で与える。
計算全体が停止しなくても、各 n について有限ステップで n 個目の観測に到達できればよい。 [REQ: REC-002]

### 6.2 計算分類

**⇓class** は、Typed Core の項に対する保守的な静的解析である。
判定対象は、E-Recur（§4.6）が導出の中で分類する Recur 項と、Recur を含まない elaboration の出力項（§6.3 の型レベル計算を含む）に限る。
place や RecurVal を含む簡約途中の項には適用しない。
判定は、項を生んだ elaboration の導出を参照して行う。
以下の規則が言う「潜在 row」「合成 row」は、その導出が部分項へ与えた row を指す。
pre(f, c)（下記）も guard 部品条件（下記）も、row のうち `Partial`・`Yield<_>`・`Return<_, _>`・`Own` だけを検査し、`Compile` は見ない。
そのため TypeMake・LetType が ⊢core から `Compile` を消去する事実（§4.8、§5.1）は、⇓class の健全性に影響しない。

```text
c ⇓class Finite(p)
c ⇓class Productive(p)
c ⇓class Unknown
```

p は判定根拠（`no-recursion`、`structural`、`guarded`）である。
判定規則は次の四つを上から順に試し、前提が最初に成り立った規則で確定する。
この順序により、複数の規則の前提を同時に満たす項は Finite 側へ分類される。

補助条件 **pre(f, c)** を次で定める。
c の中の、頭が f でないすべての適用 Apply(c0, c1, …, ck) について、c0 の合成型 `NFn<P, R, ε, Q>` の潜在 row ε が `Partial` も `Yield<_>` も含まないとき、pre(f, c) が成り立つ。
E-Recur は Unknown な再帰の宣言 row に `Partial` を要求し（§4.6）、guarded な再帰の合成 row には `Yield` が入る（E-Yield、§4.6）。
このため潜在 row の検査は、呼び先の中に隠れた発散と無限観測の可能性を、呼び先の本体を見ずに検出する。
観測を有限個生成して停止する関数の row も `Yield` を含むため、pre はこれも拒否する。
この過剰な保守性は、row を超える情報を持たない G1 で sound 側に倒した設計である。

**(C-NoRec)**

```text
c に Recur も RecurVal も出現しない
--------------------------------
c ⇓class Finite(no-recursion)
```

**(C-Structural)** [REQ: REC-001]

```text
Recur(r, f, (x1, …, xk), c1, c2) について、
pre(f, c1) かつ pre(f, c2) であり、
c1 と c2 内の f のすべての自由な出現は直接適用 Apply(f, a1, …, ak) の形であり、
ある引数位置 j が存在して、c1 内のすべての適用で
aj は xj を Eliminate で分解して得た field 変数（またはその再分解）である
--------------------------------
Recur(r, f, (x1, …, xk), c1, c2) ⇓class Finite(structural)
```

r は分類に関与しない（Recur の識別だけに使い、条件には現れない）。

引数位置 j は c1 内のすべての適用で共通とする。
継続 c2 の適用には引数位置の条件を課さない。
初回呼び出しの引数が何であっても、body の中の再帰引数が毎回小さくなれば簡約は停止するためである。
f を適用以外の位置（curry の引数、constructor の field、返り値）で使う項は C-Structural の対象外である。

`Owned` の仮引数を持つ `Recur` の本体は `Scope` と `Let` の連なりに包まれる。
分類は署名の `Owned` の位置の個数だけ包みを外してから本体を見る。
外す個数は署名が決める。形を推測して受かるまで剥がすことはしない。
包みを外した本体を見る環境は、`Let` の binder を宣言型 `Owned<τ>` で足したものである。
`Owned` でない位置の構造的減少の判定は、包みの前後で変わらない。
`Owned` の位置そのものを根とする構造的減少は、現行の data 型では書けない。
`Eliminate` は `Owned<τ>` を data 型へ剥がすが、既存の data 型の再帰欄は `(List element)` のように素の型で宣言されている。
再帰欄を `Owned` で宣言する data 型を書く手段が無いため、剥がした先の欄が `Owned` にならない。

**(C-Guarded)** [REQ: REC-002]

**guard 部品条件**：項 c' が guard 部品条件を満たすとは、f が c' に自由に出現せず、pre(f, c') が成り立ち、c' の合成 row が `Return<_, _>` と `Own` のどちらも含まないことである。

guard 条件 `guarded(f, c)` を次の帰納で定める。

- c = Yield(cv, Apply(f, a1, …, ak)) であり、cv と各 ai が guard 部品条件を満たす。
- c = Eliminate(c0, (K1(x̄1) -> c1'), …, (Kn(x̄n) -> cn')) であり、c0 が guard 部品条件を満たし、各枝 ci' が guarded(f, ci') を満たす。

```text
guarded(f, c1)
c2 = Apply(f, a1, …, ak) であり、各 ai が guard 部品条件を満たす
--------------------------------
Recur(r, f, (x1, …, xk), c1, c2) ⇓class Productive(guarded)
```

guarded な body のすべての経路は、観測を一つ生成した直後の tail 位置で f を呼ぶ。
f を呼ばずに終わる経路は許さない。
f-free な基底経路を許すと、`recur f() = unit in f()` のような、観測を生成せず停止する項が Productive に分類され、性質 6 の主張が n = 1 の観測で破れるためである。
観測を有限個生成して停止する再帰は、C-Structural（Finite）が引き受ける。
継続 c2 に f の適用を要求するのは、分類の対象が継続を含む Recur 項全体だからである。
c2 が f を呼ばなければ、body が guarded でも項全体は観測を一つも生成しえない。
`Suspend(□)` の内部は guard ではない。
R-Suspend は観測イベントを生成しないため、`recur f() = suspend f()` のような項を Productive に分類すると、観測を一つも生成しない発散が REC-002 の保証を破る。
guard 部品条件が `Return<_, _>` と `Own` を除くのは、観測列を途中で打ち切る経路を塞ぐためである。
部品の中の Perform(Return) は handler へ abort して以後の観測を捨て、部品の中の Move / Drop は OwnershipError で簡約列を終端しうる。
どちらも「各 n について ⇓obs n が成り立つ」の反例になる。
Move / Drop の検査を構文上の出現ではなく row の `Own` で行うのは、Move / Drop が部品から呼ぶ関数の body に隠れうるためである。
row に現れない OwnershipError はない（`Own` は一度入った row から消えない。§4.7）ので、row の検査は呼び先の中の Move / Drop も本体を見ずに検出する。

guard 部品条件が検査する「合成 row」は、部分項の完全な型ではなく row だけを要求する。

`guarded(f, c)` の第二項（`Eliminate(c0, …)` の c0）には、`Apply(f, a1, …, ak)` の各 ai や `Yield(cv, …)` の cv が持つような局所的な期待型が一般に存在しない。

以前の版では、Typed Core の `Construct` が elaboration によって型引数を消去される（合成位置は checking-only である）ため、期待型のない合成位置の `Construct` は row を復元できないとしていた。
しかし `Construct` は D（具体化されたデータ型）を自身のフィールドとして保持する（§4.2 E-Construct-Synth、§5.1 T-Construct）。
そのため c0 が合成位置の `Construct` であっても、`core-type-of` は D から直接 row を復元でき、この経路で row が定まらない事態は生じない。

それでも classify がある項形式について row を復元できない場合、guard 部品条件は不成立として扱い Unknown 側へ倒してよい。
これは C-Unknown の commentary（後述）が述べる「この解析は sound だが complete ではない」の一例であり、健全性を損なわない。

**(C-Unknown)** [REQ: REC-001]

```text
上のどれにも当てはまらない
--------------------------------
c ⇓class Unknown
```

Recur 項の部分項に別の Recur 定義が現れる場合、その定義の分類は当該定義自身の E-Recur が行い、外側の判定は入れ子の定義を再分類しない。
外側から見た入れ子の関数の適用は、pre の潜在 row 検査が引き受ける。
入れ子が Unknown なら宣言 row の `Partial` が、Productive なら row の `Yield` が pre を破り、外側は C-Unknown へ落ちる。

この解析は sound だが complete ではない。
実際には停止する再帰でも、上の構文条件を満たさなければ Unknown と判定する（REC-001）。
soundness の意味は §7 性質 6 で与える。

### 6.3 型同値

**型同値** `Δ ⊢ τ1 ≡ τ2` は次で定める。

- 基本型と組み込みデータ型は構造的な合同で比較する（`List<τ> ≡ List<τ'>` は `τ ≡ τ'` に帰着する）。
- `NFn<P, R, ε, Q>` は P、R、ε、Q の成分ごとの一致で比較する。
- 型レベル計算（TypeRep の適用）を正規化して比較できるのは、その計算の ⇓class が Finite の場合に限る。 [REQ: PRF-002]
- ⇓class が Productive の型レベル計算は、観測深度の上限までの有限観測で比較する。
- ⇓class が Unknown の型レベル計算と Proof は正規化に使わず、構文的同一性（opaque identity）だけで比較する。 [REQ: PRF-002]
- `Proof<φ1> ≡ Proof<φ2>` は φ1 = φ2 に帰着する。Proof term 本体（ProofRep の値）は型同一性の判定に関与しない（irrelevance）。 [REQ: PRF-003]
- origin は型同値の比較対象ではない。origin は valid-origin と authorized の検査（capability の判定）で使われ、そこでは同値な型を持つ値どうしでも origin が異なれば区別される（provenance は relevant）。 [REQ: PRF-003]

G1 の型言語に現れる型レベル計算は constructor 適用（spec の解釈）だけであり、すべて Finite である。
上の ⇓class ガードは、Phase 4 以降で型レベル計算が拡張されたときも型同値の定義を変えずに済ませるための規定である。
Redex model では、同値判定関数が ⇓class Unknown と分類された入力に対して正規化を試みず opaque identity で比較することを、判定関数の単体テストで確認する。

## 7. メタ理論性質

MVP の Redex model が目標とする性質 1 から 9（ホワイトペーパー §11.5.7）のうち、G1 は 1 から 7 を扱う。
8（borrow safety）と 9（unsafe containment）は G5 で扱う（§9）。

いずれの性質も、redex-check による **bounded counterexample search** で反例を探索する。
探索の上限値と seed は `model/redex/README.md` に固定した値を正とする。
反例が見つからないことは性質の証明ではなく、設定した探索範囲での反例未発見を意味する。

1. **Preservation**：`Ξ; Φ ⊢config ⟨c, H, Ω, Λtok, θ⟩ : τ ! ε`（§5.1）かつ `⟨c, H, Ω, Λtok, θ⟩ → ⟨c', H', Ω', Λtok', θ'⟩` ならば、ある Ξ' ⊇ Ξ について `Ξ'; Φ ⊢config ⟨c', H', Ω', Λtok', θ'⟩ : τ ! ε'` かつ `ε' ⊆ ε` が成り立つ。Φ は簡約で変化しないため同じ Φ を使い回せる（§5.1）。 [REQ: OWN-009]
2. **Progress modulo effects**：well-typed で closed なプログラム c0 の初期構成 `⟨Scope(∅, c0), ∅, ∅, ∅, ⟨⟩⟩` から到達可能な構成は、値であるか、OwnershipError（`⟨Error(p), H, Ω, Λtok, θ⟩` の形の終端構成、§5.5）であるか、次の step を持つ。top-level に到達した `Perform(op, v)` は、op が初期宣言 row に含まれる場合のみ許容される終端とする。到達可能性で量化するのは、R-LetOwned の割り当て先となる Scope の存在（§5.2）を初期構成の形が保証するためである。 [REQ: OWN-010]
3. **Origin integrity**：elaboration の出力 c と、そこから到達可能なすべての構成は `verify-origins(R0, ·)` を満たす。すなわち簡約は偽造 origin を生成しない。 [REQ: NAR-001] [REQ: NAR-002]
4. **Boundary safety**：`Perform(Return<b, τ>, v)` が R-HandleReturn で処理されるのは、同じ境界 ID b と同じ型 τ を持つ handler だけである。 [REQ: RET-002]
5. **TypeInfo integrity**：Δ へ導入されるすべての TypeRep の origin は、初期環境が与える type sort の `Reserved(id)`（R0(id) = type(N)）か、letType が与える `Derived(Reserved(o-type-narrative), Make(t))`（t はその TypeRep が保持する型式）のいずれかである。 [REQ: TYP-001]
6. **Conservative analysis**：`⇓class Finite(p)` と判定された項は、評価 fuel の範囲で簡約が停止する（値、OwnershipError、許容される top-level Perform のいずれかの終端に到達する）。`⇓class Productive(p)` と判定された項は、観測深度上限までの各 n について、fuel の範囲で `c ⇓obs n` の簡約列が存在する。`Unknown` は何も主張しない。 [REQ: REC-001] [REQ: REC-002]
7. **Affine safety**：任意の有限実行 trace において、(a) 各 place p の Move 成功（R-Move）は高々一度であり、(b) p の Dropped への遷移（finalize による）も高々一度であり、(c) `Moved` / `Dropped` の place への Move は `Error(p)` の生成（R-MoveError）以外へ遷移せず、(d) すべての scope exit 経路（R-ScopeValue、R-ScopeAbort、R-ScopeError）が π の Available な place を drop して `fin` イベントを記録する、(e) 値の内部の leaf token も一つの `(p, fp)` につき高々一度だけ `Dropped` となり、対応する `finLeaf(p, fp)` は root の `fin(p)` より先に記録される。明示 drop は Move を経た値の消費であり、place の状態遷移としては (a) の Move 側で数える。 [REQ: OWN-001] [REQ: OWN-002] [REQ: OWN-003] [REQ: OWN-009] [REQ: OWN-010]

## 8. golden program

golden test の正規手書き項、初期環境、期待簡約列を本節で固定する。
Redex model の golden test はこの項をそのまま実装し、期待結果との一致を確認する。
ホワイトペーパー §20 の最小実証プログラムを未型付き縮小 Core で手書きしたものに相当する。
Surface 構文からの elaboration の検証は Phase 1 で行う。

使用する初期環境は §3.5 の全体である。

### 8.1 findPositive

正の要素を最初に見つけたら返す関数である。
`for` + `if` + `return` の lowering 結果に相当し、recur、eliminate、narrativeExpr、return boundary を通す。

```text
findPositive =
  fn(values : List<Int>) -> Result<Int, Unit> ! {}
    narrativeExpr(
      recur loop(rest : List<Int>) -> Result<Int, Unit> ! {Return} =
        eliminate rest {
          nil() => construct ng(unit)
          cons(head, tail) =>
            eliminate lt(0, head) {
              true()  => return construct ok(head)
              false() => loop(tail)
            }
        }
      in loop(values))
```

`Bool` の分解は C0 の `true()` と `false()`（§3.5）に対する `eliminate` である。
`loop` の宣言 row の `Return` は、elaboration が narrativeExpr の境界 bE へ解決する。
簡約列の中の `lt` は、E-Prim が解決した `PrimVal(Reserved(o-lt), lt)` の略記である（§8.2 の `mul` も同様）。

入力は `cons(-1, cons(2, nil))`（型引数の表記は省略、以下同じ）とする。

期待する主要簡約ステップは次のとおりである。

```text
Apply(findPositive, cons(-1, cons(2, nil)))
→ (R-Beta) Handle(Return<bf>, x -> x, Scope(∅,
    Handle(Return<bE>, x -> x, Scope(∅,
      Recur(loop, (rest), body, Apply(loop, values))))))    values は実引数で置換済み
→ (R-RecurBind、R-RecurUnfold) Eliminate(cons(-1, cons(2, nil)), …)
→ (R-Eliminate) cons 枝、head = -1、tail = cons(2, nil)
→ (R-Delta) Apply(lt, 0, -1) → Construct(false)
→ (R-Eliminate) false 枝 → Apply(loopVal, cons(2, nil))
→ (R-RecurUnfold、R-Eliminate) cons 枝、head = 2
→ (R-Delta) Apply(lt, 0, 2) → Construct(true)
→ (R-Eliminate) true 枝 → Perform(Return<bE, Result<Int, Unit>>, Construct(ok, 2))
→ (R-ScopeAbort) 内側 Scope の finalization（π = ∅、イベントなし）
→ (R-HandleReturn) bE の handler が捕捉 → Construct(ok, 2)
→ (R-ScopeValue、R-HandleValue) 外側の Scope と bf の handler を素通り
```

期待する最終値は `Construct(ok, 2)` である。
期待する ⇓class は、`loop` の再帰呼び出しが `rest` の Eliminate で束縛された `tail` に対して行われるため `Finite(structural)` である。

### 8.2 map

curry で作った倍化関数を各要素へ適用する。
`values.map(value => value * 2)` の lowering 結果に相当し、curry、高階適用、構造再帰を通す。

```text
map =
  fn(f : NFn<(Int), Int, {}, ⟨⟩>, values : List<Int>) -> List<Int> ! {}
    recur go(rest : List<Int>) -> List<Int> ! {} =
      eliminate rest {
        nil()       => construct nil()
        cons(h, t)  => construct cons(f(h), go(t))
      }
    in go(values)

doubled = map(curry(mul, 2), cons(-1, cons(2, nil)))
```

期待する主要簡約ステップは次のとおりである。

```text
Curry(PrimVal(Reserved(o-mul), mul), 2)
→ (R-CurryVal) CurryVal(Derived(Reserved(o-mul), Curry(2)), PrimVal(…), 2)
Apply(map, CurryVal(…), cons(-1, cons(2, nil)))
→ (R-Beta、R-RecurBind、R-RecurUnfold、R-Eliminate) cons 枝、h = -1
→ (R-ApplyCurry) Apply(PrimVal(mul), 2, -1)
→ (R-Delta) -2
→ 同様に h = 2 について 4、nil 枝で construct nil()
```

期待する最終値は `Construct(cons, -2, Construct(cons, 4, Construct(nil)))` である。
`CurryVal` の origin が `Derived(Reserved(o-mul), Curry(2))` であり、新規の `Reserved` でないことを golden test で併せて確認する。
期待する ⇓class は `Finite(structural)` である。

## 9. 延期事項（G5 への概略）

borrow、region、unsafe boundary の judgment は G5 で仕様化する。
ホワイトペーパー §11.5.8 に基づく概略は次のとおりである。

- 借用の生存は Ω ではなく静的な記録 Ψ が持ち、Ω は `Available`、`Moved`、`Dropped` の三値のままとする。
- `&x` と `&mut x` の可否は Ψ と σ が決める。共有借用どうしは重なってよい。可変借用は同じ place について排他であり、同じ place の共有借用と region が重なるときは取れない。
- region exit で Ψ から項目を消すことはせず、σ が定める生存範囲の外に出た借用は以後の許可判定に効かなくなる。`Moved` と `Dropped` の place への read、borrow、drop は型エラーとする。
- raw pointer の dereference は `Unsafe` Effect と Proof obligation を要求し（PTR-001）、safe reference の構築には lifetime、alignment、validity の Proof を要求する（PTR-002）。
- G1 が禁止した Owned 値の関数境界越え（引数渡し、closure 捕捉、E-Construct の field、E-Curry の固定引数。§4.3）の担当を次のように分ける。
- 引数渡しは G5c5b1、closure の捕捉と E-Curry の固定引数は G5c5b2、E-Construct の field は G5c5b3 が担当する。
- メタ理論性質 8（borrow safety）と 9（unsafe containment）の bounded 検査を Redex model へ追加する。

このうち `Owned` を取る仮引数は G5c5b1、closure の捕捉と E-Curry の固定引数は G5c5b2 が扱う。
G5c3 段 A では `Let` の宣言型が `Owned` のときに計算した値を載せる形だけを回復する。

G1 が borrow を延期できるのは、Phase 1 の MVP が要求する所有権機能が affine な move / drop まで（ホワイトペーパー §16 Phase 1）であり、G1 の Ω 三値モデルがその範囲を過不足なく覆うためである。
初期 lexical region 解析を NLL 相当の solver と置換可能にする要件（BOR-003）も G5 で扱う。

## 10. 規則と要件 ID の対応

| 要件 ID | 対応する規則、定義 |
|---|---|
| NAR-001 | valid-origin（§3.4）、verify-origins（§3.4）、性質 3 |
| NAR-002 | valid-origin の Derived 規則（§3.4）、R-CurryVal（§5.3）、性質 3 |
| CUR-001 | E-Curry（§4.4）、R-ApplyCurry（§5.3） |
| CUR-002 | E-Curry（§4.4）、R-CurryVal（§5.3） |
| TYP-001 | E-TypeMake、E-LetType（§4.8）、性質 5 |
| TYP-002 | E-TypeMake の spec 解釈（§4.8）、verify-origins の kind 整合（§3.4） |
| RET-001 | E-Return、resolveReturn（§4.5） |
| RET-002 | E-NarrativeExpr（§4.5）、T-Perform（§5.1）、R-HandleReturn（§5.7）、性質 4 |
| RET-003 | E-Eliminate（§4.2）、E-Recur（§4.6） |
| EFF-001 | E-Lambda の row 包含（§4.3）、E-Recur の row 包含（§4.6） |
| PRF-001 | §4.9、verify-origins（§3.4） |
| PRF-002 | 型同値の ⇓class ガード（§6.3） |
| PRF-003 | 型同値の Proof irrelevance と provenance 規定（§6.3） |
| REC-001 | C-Structural、C-Unknown（§6.2）、E-Recur の Partial 要求（§4.6）、性質 6 |
| REC-002 | 観測関係（§6.1）、C-Guarded（§6.2）、性質 6 |
| OWN-001 | E-Move（§4.7）、T-MovePlace（§5.1）、R-Move、R-MoveError（§5.5）、性質 7 |
| OWN-002 | E-Drop、E-DropVar（§4.7）、finalize、R-ScopeValue（§5.6）、性質 7 |
| OWN-003 | R-ScopeAbort、R-ScopeError（§5.6）、性質 7 |
| OWN-009 | T-OwnedLeaf、`Λtok` の token 条件、性質 7 |
| OWN-010 | R-Drop、finalize、R-ScopeValue、性質 7 |

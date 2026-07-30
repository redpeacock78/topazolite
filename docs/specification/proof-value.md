# Topazolite Proof 値と Refinement 仕様

**状態**：G2d 執筆版（codex 実装、claude レビュー前）
**参照**：draft/topazolite_whitepaper_draft_0.4.md §4.6、§6
**関連文書**：core-calculus.md、structural-row.md、proof-search.md、trait.md、requirements.md、glossary.md

## 1. 本仕様の位置づけ

本文書は、G2 の型と値へ Refinement と Untrusted を加え、validate の動的意味論、merge の常在性 witness、obligation の discharge 互換、二層の成果物検証を定める差分仕様である。
本文書に定義がない構文、型付け規則、簡約規則は `core-calculus.md`、`structural-row.md`、`proof-search.md` に従う。
Redex model の G2d 実装は本文書を正とし、実装との乖離が見つかった場合は本文書を先に修正する。

G2d は Proof の値表現と、その成立に必要なカーネル命題の探索規則だけを扱う。
評価文脈 F、E、G は変更せず、動的意味論の拡張は既存の `Apply` が使う δ 規則に限る。

規則には `[REQ: <ID>]` の形で要件 ID を注釈する。
要件 ID の本文は `requirements.md` を正とする。

## 2. 範囲

### 2.1 このサイクルで扱うもの

G2d は次の規則を扱う。

- `Untrusted` と `Refined` の型および値表現。
- validator 正典表から導く validate、導入、射影のカーネル primitive。
- merge の全 non-Never branch に同じ型と可変性で常在する field の witness。
- 大域候補文脈からの discharge を認める obligation の互換判定。
- validator 由来の命題と常在性命題に対する探索分類および候補抽出。
- 初期成果物と到達成果物を分けた origin 検証。

### 2.2 除外するもの

G2d は次の規則を導入しない。

- 型が異なる branch field の join 型と、常在性 witness を使う型付き field 回復。
- Union、Intersection、trait resolution、trait 由来の候補同一性。
- 実際の探索計算、`⇓class` 導出、certificate、termination Proof、priority、provenance の実体化。
- 局所 Proof 束縛の一般機構と、merge 位置を越えた witness の保存。
- 型変数と型 scheme を使う多相 primitive。
- `Safe<T, Context>` とユーザー定義 validator。
- Surface 構文から未型付き縮小 Core への変換。

## 3. 命題と Proof 値

### 3.1 命題の拡張

G2 の命題文法を次のとおり拡張する。

```text
φ ::= ValidNarrativeTrait
    | TypeNarrativeCap
    | (Prop id)
    | (Presence label)
```

**抽象命題** `(Prop id)` は、validator 正典表が名前 id で識別する命題である。
型検査は id の一致だけを見て、命題の内容を解釈しない。

**常在性命題** `(Presence label)` は、merge の全 non-Never branch に label の field が同じ型と可変性で存在したことを表す。
この命題の発行元は §5 の merge に限る。

### 3.2 型と値の拡張

G2 の型と値を次のとおり拡張する。

```text
τ ::= .... | (Untrusted τ) | (Refined τ φ)

v ::= .... | (UVal v) | (RVal (ProofRep O φ) v)
```

**Untrusted 型** `(Untrusted τ)` は、未検証のペイロードを保持する型である。
**Refined 型** `(Refined τ φ)` は、τ のペイロードと命題 φ の Proof を保持する型である。
`UVal` は未検証のペイロードを包み、`RVal` は Proof と検証済みのペイロードを対にする。

`Untrusted` と `Refined` のペイロード型は Owned-free でなければならない。
wrapper が `Owned` を型の内側へ隠すと、外層だけを見る affine 判定を素通りして資源を複製できるためである。

`UVal` と `RVal` は値だけを包む。
このため評価文脈を追加せず、§4 の primitive は評価済みの引数へ δ 規則を適用できる。

### 3.3 型付けと forge 不可

`UVal` と `RVal` の型付けを次で定める。

**(T-UVal)**

```text
Γ; Δ; Π; Ξ; Φ ⊢core v : τ ! ε
owned-free(τ)
------------------------------------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core UVal(v) : Untrusted<τ> ! ε
```

**(T-RVal)**

```text
Γ; Δ; Π; Ξ; Φ ⊢core v : τ ! ε
owned-free(τ)
Γ; Δ; Π; Ξ; Φ ⊢core ProofRep(O, φ) : Proof<φ> ! {}
------------------------------------------------------------
Γ; Δ; Π; Ξ; Φ ⊢core RVal(ProofRep(O, φ), v) : Refined<τ, φ> ! ε
```

[REQ: RFN-001]

型付けは `RVal` の origin が φ を発行できるかを検査しない。
型付けは値の形を扱い、forge の拒否は §7 の成果物検証が担うという既存の役割分担を保つためである。

発行者の正当性とペイロードの束縛は、§4.1 の validator 正典表から導く。
R0、primitive の型、δ 規則、ProofRep の発行者対応、RVal のペイロード検査が同じ表を参照するため、発行者と命題の対応を別の規則へ重複して記録しない。

### 3.4 irrelevance

`Refined τ φ` の型同値は τ の型同値と φ の一致だけを見る。
値が保持する `ProofRep O φ` の origin は型同値に関与しない。

`compat?` は、二つの `Refined` 型の φ が一致し、ペイロード型が再帰的に互換であるときに限って受理する。
`Untrusted` 型の互換もペイロード型の再帰で定める。
`Untrusted τ` と τ、または `Refined τ φ` と τ の間に wrapper を消去する互換規則は置かない。

`unrefine` は `Refined τ φ` から τ の値を取り出す。
この射影は Proof を捨てて型を弱める操作であり、実行時に φ を再検査しない。

### 3.5 UCore と elaboration の拡張

未型付き縮小 Core の注釈用命題と Proof obligation を次で定める。

```text
uφ ::= ValidNarrativeTrait
     | TypeNarrativeCap
     | (Prop id)

uQ ::= (uφ ...)
```

型注釈を次のとおり拡張する。

```text
uτ ::= ....
     | (Untrusted uτ)
     | (Refined uτ uφ)
     | (Proof uφ)
     | (NFn (uτ ...) uτ tε uQ)
```

`resolve-annotation` は `Untrusted` と `Refined` のペイロード型を再帰的に解決し、型の形と Owned-free 制限を検査する。
`resolve-obligations` は G1 の二命題と validator 正典表に存在する `(Prop id)` だけを受理する。

`(Presence label)` は uφ に含めない。
常在性 witness は merge の局所検査だけが発行し、ユーザーが注釈から要求する経路を G2d では与えないためである。

UCore は `UVal` と `RVal` に対応する構文を持たない。
この構文の不在が、§7 の初期成果物検証で両者の出現を拒否する根拠になる。

## 4. validate の動的意味論

### 4.1 カーネル primitive と判定表

**validator 正典表**は、命題ごとに次の五つ組を持つカーネル内部の閉じた表である。

```text
(oid, nm, φ, τ, check)
```

| oid | nm | φ | τ | check |
|---|---|---|---|---|
| `o-valid-port` | `validPort` | `(Prop ValidPort)` | `Int` | 1 以上 65535 以下の整数 |
| `o-non-empty` | `nonEmpty` | `(Prop NonEmpty)` | `String` | 空でない文字列 |

oid は witness を発行する予約 origin ID、nm は primitive 名、φ は命題、τ は Owned-free なペイロード型、check はリテラルに対する決定可能な全域判定である。
R0 と Γ0 への登録、δ 規則、ProofRep の発行者対応、RVal のペイロード束縛、χ の Finite 表は、この表から導く。

各 validator の型は次のとおりである。

```text
validPort :
  NFn<(Untrusted Int),
      Result<Refined<Int, Prop<ValidPort>>, String>,
      {},
      {}>

nonEmpty :
  NFn<(Untrusted String),
      Result<Refined<String, Prop<NonEmpty>>, String>,
      {},
      {}>
```

validator は純粋な全域計算であるため、latent effect と obligation は空である。

[REQ: RFN-001]

### 4.2 δ 規則

validator 正典表に `(oid, nm, φ, τ, check)` があるとき、validate の成功を次で定める。

**(δ-Validate-Ok)**

```text
check(v) = true
------------------------------------------------------------
δ(PrimVal(Reserved(oid), nm), UVal(v))
  = Construct(Result<Refined<τ, φ>, String>,
              ok,
              RVal(ProofRep(Reserved(oid), φ), v))
```

validate の失敗を次で定める。

**(δ-Validate-Ng)**

```text
check(v) = false
------------------------------------------------------------
δ(PrimVal(Reserved(oid), nm), UVal(v))
  = Construct(Result<Refined<τ, φ>, String>,
              ng,
              "<nm>: rejected")
```

失敗メッセージは nm から決定的に構成する。
check は型の合わない値にも偽を返すため、その場合も stuck ではなく `ng` へ簡約する。

[REQ: RFN-001]

### 4.3 導入と射影の primitive

型変数を持たない G2 の型言語に合わせて、導入と射影は有限の単相 primitive とする。

**導入表**は、ペイロード型ごとの Untrusted 導入 primitive を定める。

| oid | nm | τ |
|---|---|---|
| `o-untrusted-int` | `untrustedInt` | `Int` |
| `o-untrusted-string` | `untrustedString` | `String` |

**射影表**は、validator 正典表の命題ごとの Refined 射影 primitive を定める。

| oid | nm | φ | τ |
|---|---|---|---|
| `o-unrefine-port` | `unrefinePort` | `(Prop ValidPort)` | `Int` |
| `o-unrefine-non-empty` | `unrefineNonEmpty` | `(Prop NonEmpty)` | `String` |

導入表は validator 正典表に現れる各ペイロード型を一行ずつ持つ。
射影表は validator 正典表の各行と同じ φ および τ を持つ行を一つずつ持つ。
表の読み込み時にこの網羅性と、三表を通じた oid および primitive 名の一意性を検査する。

各表の行から次の単相型を導く。

```text
(oid, nm, τ) ∈ introduction-table
------------------------------------------------------------
nm : NFn<τ, Untrusted<τ>, {}, {}>

(oid, nm, φ, τ) ∈ projection-table
------------------------------------------------------------
nm : NFn<Refined<τ, φ>, τ, {}, {}>
```

導入の δ 規則は値 v を `UVal(v)` で包む。
値を未検証と宣言する操作は check を必要としない。

```text
(oid, nm, τ) ∈ introduction-table
------------------------------------------------------------
δ(PrimVal(Reserved(oid), nm), v) = UVal(v)
```

射影の δ 規則は、対応する単相型を型検査が保証した `RVal` からペイロードを取り出す。
Proof を捨てて弱める操作であるため、check を再実行しない。

```text
(oid, nm, φ, τ) ∈ projection-table
------------------------------------------------------------
δ(PrimVal(Reserved(oid), nm),
  RVal(ProofRep(O, φ'), v)) = v
```

すべての primitive は既存の `Apply` と R-Delta を使う。
このため評価文脈と既存の簡約規則は変わらない。

## 5. merge の常在性 witness

### 5.1 発行規則

G2a の record merge は Never の branch を合流から除外し、残る branch の field row を型同値かつ可変性一致の構造的交差へ畳み込む。
G2d の merge は、合流型に加えて **witness 集合** W を返す。

非 Never の record 型が `Record<r1>, ..., Record<rn>` であり、その交差が r であるとする。
W は r に残る各 field f について一つの witness を持つ。

```text
r = r1 ⋂ ... ⋂ rn

W = {
  ProofRep(Reserved(o-merge), Presence(f))
  | f ∈ labels(r)
}
```

したがって witness は、全 non-Never branch に同じ型と同じ可変性で存在する field に対してのみ発行する。
一部の branch にしかない field、型が異なる field、可変性が異なる field には発行しない。

[REQ: RFN-002]

### 5.2 witness 集合 W と merge ごとの局所検査

W は型にも成果物にも載せない。
`Presence(f)` は merge の位置を持たないため、成果物全体へ集約すると、ある merge の witness が別の merge の goal を満たしうるためである。

各 merge は自身が返した W だけを候補 entry の列へ変換する。
候補の cid は field label、sid は `root`、pid は `default` とする。
一つの merge では field label が一意であるため、この構成で候補同一性も一意になる。

W の ProofRep は `o-merge` と `Presence(f)` の発行者対応を満たす。
探索側の候補 well-formedness は発行者対応だけを見るため、この ProofRep を候補として受理できる。

局所検査は entry 化した W を候補文脈として、各 `Goal(Presence(f))` が discharge 可能であることを確かめる。
この検査は merge の型付けを受理する追加前提ではなく、witness の発行と候補化が対応することを検査する性質である。

W を merge 位置を越えて保存し、scope 付きで照合する機構は §8 へ送る。

[REQ: RFN-002]

## 6. obligation φ の discharge 互換

### 6.1 判定規則と実運用経路への統合

関数型の obligation を次の規則で比較する。

```text
すべての φ ∈ Q_sub について、
  φ ∈ Q_sup
  または discharge?(Γ_pc, Goal(φ))
------------------------------------------------------------
Q_sub は Q_sup の下で互換
```

`Q_sup` に明示された命題は従来どおり充足済みとして扱う。
明示されていない命題は、候補文脈 Γ_pc から `obligations-dischargeable?` で充足できるときに限って受理する。

`compat?` は Γ_pc を引数に取り、record の `imm` field、`Untrusted` と `Refined` のペイロード、NFn の引数、返り値、obligation の再帰へ同じ文脈を伝える。
`mut` field は型同値で不変に照合するため、`compat?` の文脈を使わない。

型付けは固定の初期候補文脈 Γ_pc⁰ を渡す。
elaboration はその位置の proposition 環境を `candidateize` して得た候補文脈を渡す。
binding policy が `compat?` を直接呼ぶ経路にも同じ文脈を渡す。

候補文脈を省略した `compat?` は空文脈を使う。
この場合は discharge による追加の充足がなく、G2c の完全一致包含と同じ結果になる。

[REQ: RFN-003]

### 6.2 文脈を Γ_pc⁰ に限定する理由

実運用の discharge 互換は、すべての義務位置が共有する大域候補文脈 Γ_pc⁰ に限る。
§5 の W のような位置依存の候補文脈は `compat?` に渡さない。

merge の W で obligation を discharge して関数型の互換を認めると、その関数値が merge を脱出した後の call site では witness が存在しない。
その場合は簡約後の再型付けが失敗し、Preservation が破れる。

Γ_pc⁰ で discharge できる命題はすべての call site で同じ候補を使える。
この制限により、関数値が移動しても obligation の根拠が失われない。

### 6.3 χ 分類と well-formedness の改訂

候補抽出を次で定める。

```text
Σ_goal = project-goal(Γ_pc, sc, goal)
```

`project-goal` は scope から可視な候補を射影し、その後で goal の命題と一致する候補をすべて抽出する。

候補文脈全体の well-formedness と、抽出後の Σ_goal の well-formedness を分ける。
`wf-context?` は各 entry の発行者対応と hook の空性を検査し、goal との命題一致を要求しない。
sid の可視性は `project` と `project-goal` が抽出時に検査する。
`wf-Σ?` は Σ_goal の各候補が goal の命題と一致し、候補単体の条件も満たすことを要求する。

Finite な探索の evidence は `ev = Σ_goal` でなければならない。
採択時には `wf-Σ?(ev, goal)` と `unique(goal, ev, P)` を再検査する。

χ は G1 の命題に加えて、validator 正典表の各 `(Prop id)` を Finite に分類する。
`(Presence label)` は label ごとの表ではなく、命題の形 `(Presence _)` を Finite とする規則で分類する。
χ は SearchResult を参照せず、命題とカーネル表だけから決定する。

[REQ: RFN-003]

## 7. 二層の成果物検証

origin 検証を、elaboration の出力に対する初期層と、簡約で到達した構成に対する到達層へ分ける。

**初期層** `verify-initial-origins` は、既存の origin 検証に加えて、`UVal` と `RVal` の出現を拒否する。
UCore に両者の構文がないため、正当な elaboration 出力には現れない。
初期層は `ProofRep(Reserved(o-merge), Presence(f))` の出現も拒否する。

**到達層** `verify-origins` は、簡約で生じた validator 由来の `ProofRep` と `RVal` を検査する。
`RVal(ProofRep(O, φ), v)` は、validator 正典表に φ の行があり、O がその行の oid に対応し、v のリテラル型が行の τ と一致し、check(v) が真であるときに限って正当である。

forge の拒否は **発行者対応** と **出現許可** に分ける。
発行者対応 `proof-issuer-ok?` は、G2b までの `o-type-narrative` と `TypeNarrativeCap` の組に加え、validator 行の oid と φ の組、および `o-merge` と `Presence(f)` の組を正当とする。
出現許可は `Presence(f)` の ProofRep を初期成果物と到達成果物のどちらでも拒否する。

探索側の候補 well-formedness は発行者対応だけを見る。
発行者対応と出現許可を一つの判定へまとめると、merge が発行した witness が候補 well-formedness を通らず、局所検査で `Goal(Presence(f))` を discharge できないためである。

したがって `o-merge` の witness は §5.2 の局所候補として正当であるが、成果物の値としては不正である。
User origin、命題と oid の不一致、型の違うペイロード、check に失敗するペイロードを持つ `RVal` は到達層で拒否する。

[REQ: RFN-001]

## 8. 範囲外の規則

次の規則は後続層へ送るか、後続層が定めた境界に従う。

- **join 型と型付き field 回復**：異型 `imm` field の Union join と局所 `FieldType` witness は、G2e が `trait.md` §7 として導入した。
  witness による型付き field 回復は未回収であり、`trait.md` §9 へ送る。
  異型 `mut` field の脱落は実装上の狭めであり、ホワイトペーパー §4.5.3 の Union 方針を回収したことを意味しない。
- **Union と Intersection**：有限な Union の正規形と構造型の Intersection 消去は、G2e が `trait.md` §3 として導入した。
  trait の合成は型の Intersection ではなく、正典表と `RequiresBoth` Proof で表す。
- **trait resolution**：表由来の `Implements` 候補、trait hook、候補同一性、scope による coherence は、G2e が `trait.md` §6 として導入した。
  `RequiresBoth` の implicit discharge と合成 trait への `Implements` 導出は未回収である。
- **探索動力学**：探索計算、`⇓class`、certificate、termination Proof、priority、provenance の実体化は探索の後続層で扱う。
- **局所 Proof 束縛**：merge 位置を越えた witness の保存、scope 付き照合、位置依存文脈の `compat?` への供給と併せて後続層で扱う。
- **多相 primitive**：型変数と型 scheme を導入する Phase 1 以降で扱う。
- **文脈付き安全型とユーザー validator**：`Safe<T, Context>` とユーザー定義 validator は Phase 1 以降で扱う。

## 9. 要件と規則の対応

| 要件 ID | 対応する規則、定義 |
|---|---|
| RFN-001 | §3.3 T-UVal と T-RVal、§4.1 判定表、§4.2 δ-Validate-Ok と δ-Validate-Ng、§7 二層の成果物検証 |
| RFN-002 | §5.1 常在性 witness の発行規則、§5.2 merge ごとの局所検査 |
| RFN-003 | §6.1 discharge 互換の判定規則、§6.3 χ 分類と well-formedness の改訂 |

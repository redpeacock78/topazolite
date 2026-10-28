# 証明範囲の一覧

## 1. 位置づけ

この文書は、要件 ID ごとに正典、Redex の試験、F* の命題の対応と検証状態を示す。
F* の命題が検証に通ることは、Redex のモデル全体の正しさを意味しない。
F* の `core` は span と項の形を表す模型であり、型検査はしない。

## 2. F* の注記

命題の注記は結論を述べるトップレベルの `Lemma` の直上に置く。
結論の補題が無い命題は、型に `Tot` を明示するトップレベルの `val` に注記する。
同じ `THM` の注記が複数ある場合、SCOPE 以外の七欄は一致させ、SCOPE には各補題の対象範囲を書く。
既存の自由文コメントは残し、その直後、宣言の直前に注記を置く。

命題の注記は次の八行をこの順で持つ。

| 欄 | 意味 |
| --- | --- |
| `THM` | 命題を識別する `THM-NNN`。 |
| `REQ-FULL` | 命題が要件全体を覆う ID。無い場合は `-`。 |
| `REQ-PART` | 命題が要件の一部を覆う ID。無い場合は `-`。 |
| `SPEC` | 対応する正典文書と節。 |
| `RULE` | 対応する規則名。無い場合は `-`。 |
| `REDEX` | 同じ性質を有限例で検査する試験 path。無い場合は `-`。 |
| `ASSUMPTIONS` | F* の前提述語名。無条件なら `-`。 |
| `SCOPE` | 量化する範囲と対象外の範囲。 |

`SPEC` は `<文書名>§<節>` の形、`REQ-FULL` と `REQ-PART` は要件 ID をカンマ区切りで書く。
`ASSUMPTIONS` には F* の述語名だけを書き、述語で表せない前提は `SCOPE` に書く。
`SCOPE` では CI の F* 検査対象語を使わない。

補助の補題は `//@ AUX: helper THM-NNN`、具体例は `//@ AUX: example REQ-ID` と一行で書く。
複数の命題を支える helper は THM ID をカンマで列挙する。
具体例は全称命題ではないため、要件の状態を「証明済み」にしない。

## 3. 状態

- **証明済み**：F* 命題の `REQ-FULL` が要件全体を覆う。
- **テストのみ**：要件の性質を実際に assert する Redex 試験があるが、要件全体を覆う F* 命題はない。
- **未検証**：上記のどちらにも当たらない。

`REQ-PART` と `AUX: example` は補助証拠として記録し、状態の判定には使わない。
「テストのみ」には `[REQ: ID]` 注記だけでなく、性質を assert する具体的な test-case を示す。

## 4. 一覧

### 命題と結論の宣言

| THM | 宣言 |
| --- | --- |
| THM-001 | `lex` |
| THM-002 | `lex_span_sound` |
| THM-003 | `parse_span_containment` |
| THM-004 | `lower_preserves_span` |
| THM-005 | `keyword_word_reserved` |
| THM-006 | `lower_block_root_span` |
| THM-007 | `lower_decl_bind`, `lower_decl_fn`, `lower_decl_try_bind`, `lower_fields_labels`, `lower_fn_fields`, `lower_proj_label`, `lower_projrec_fields`, `lower_rec_labels`, `proj_fields_spans` |

### 要件ごとの状態と証拠

| 要件 ID | 状態 | 命題 | 補助の証拠 | 根拠の試験 |
| --- | --- | --- | --- | --- |
| NAR-001 | テストのみ | - | - | `model/redex/tests/origins-test.rkt`::`NAR-001: nested forged origin reports its subterm`, `model/redex/tests/origins-test.rkt`::`NAR-001: reserved origin and value sort agree` |
| NAR-002 | テストのみ | - | - | `model/redex/tests/origins-test.rkt`::`NAR-002: origin-of covers every origin-bearing value`, `model/redex/tests/origins-test.rkt`::`NAR-002/CUR-002: derived curry origin is exact` |
| NAR-003 | テストのみ | - | - | `model/redex/tests/origins-trait-test.rkt`::`NAR-003: 偽造した trait Proof の origin を拒否する`, `model/redex/tests/origins-trait-test.rkt`::`NAR-003: 正典の trait 表は全行が trait-origin-ok? を通る` |
| NAR-004 | テストのみ | - | - | `model/redex/tests/search-compose-test.rkt`::`NAR-004: 合成 Proof の親は intersect の派生 origin である` |
| NAR-005 | テストのみ | - | - | `model/redex/tests/own-curry-fixed-test.rkt`::`Owned の固定引数を Move 経由で固定でき、結果型が Owned<NFn 残余> になる` |
| POL-001 | テストのみ | - | - | `model/redex/tests/properties-policy-test.rkt`::`POL-001: R0 の実値が変われば正しい行も拒否される`, `model/redex/tests/policy-test.rkt`::`POL-001: policy-origin-ok? は R0 の実値まで見る` |
| POL-002 | テストのみ | - | - | `model/redex/tests/properties-policy-test.rkt`::`POL-002: 6 操作それぞれで検査が受理と拒否の両方を出す` |
| CUR-001 | テストのみ | - | - | `model/redex/tests/elaborate-test.rkt`::`CUR-001/CUR-002: curry preserves the latent signature`, `model/redex/tests/machine-pure-test.rkt`::`CUR-001/CUR-002: curry records provenance and completes application` |
| CUR-002 | テストのみ | - | - | `model/redex/tests/origins-test.rkt`::`NAR-002/CUR-002: derived curry origin is exact` |
| TYP-001 | テストのみ | - | - | `model/redex/tests/origins-test.rkt`::`TYP-001/TYP-002: TypeRep origin type and kind agree` |
| TYP-002 | テストのみ | - | - | `model/redex/tests/origins-test.rkt`::`TYP-001/TYP-002: TypeRep origin type and kind agree`, `model/redex/tests/elaborate-test.rkt`::`TYP-001/TYP-002: typeMake interprets saturated specifications` |
| TYP-003 | テストのみ | - | - | `model/redex/tests/properties-record-test.rkt`::`TYP-003: 予約型は record の構造的照合でなく型同値を使う` |
| ROW-001 | テストのみ | - | - | `model/redex/tests/typing-binding-test.rkt`::`ROW-001: const 束縛は残余欄を拒否する` |
| ROW-002 | テストのみ | - | - | `model/redex/tests/typing-binding-test.rkt`::`ROW-002: let 束縛は互換な残余欄を保ち、非互換な欄を拒否する` |
| ROW-003 | テストのみ | - | - | `model/redex/tests/properties-test.rkt`::`ROW-003: branch merge is structural intersection` |
| ROW-004 | テストのみ | - | - | `model/redex/tests/properties-test.rkt`::`ROW-004: mutable fields are invariant and inhabited` |
| ROW-005 | テストのみ | - | - | `model/redex/tests/row005-join-test.rkt`::`ROW-005 の join は可変性の食い違う欄を imm にし、片方だけの欄を落とす` |
| VAR-001 | テストのみ | - | - | `model/redex/tests/variance-test.rkt`::`VAR-001: 引数は反変`, `model/redex/tests/variance-test.rkt`::`VAR-001: 返り値は共変` |
| VAR-002 | テストのみ | - | - | `model/redex/tests/variance-test.rkt`::`VAR-002: latent effect は共変の集合包含`, `model/redex/tests/variance-test.rkt`::`VAR-002: Proof obligation は反変の集合包含` |
| VAR-003 | テストのみ | - | - | `model/redex/tests/variance-test.rkt`::`VAR-003: mut field の関数型は型同値の不変に留まる` |
| RFN-001 | テストのみ | - | - | `model/redex/tests/properties-refine-test.rkt`::`RFN-001: 性質1 validate 健全性`, `model/redex/tests/properties-refine-test.rkt`::`RFN-001: 初期項に埋めた UVal と RVal は意味検査の前に落ちる` |
| RFN-002 | テストのみ | - | - | `model/redex/tests/properties-refine-test.rkt`::`RFN-002: 性質2 merge witness 健全性` |
| RFN-003 | テストのみ | - | - | `model/redex/tests/properties-refine-test.rkt`::`RFN-003: 性質3 discharge 互換の方向健全性` |
| TRT-001 | テストのみ | - | - | `model/redex/tests/properties-trait-test.rkt`::`TRT-001: 性質1 shape 一致だけでは Proof を偽造できない` |
| TRT-002 | テストのみ | - | - | `model/redex/tests/properties-trait-test.rkt`::`TRT-002: 性質2 impl と derive の Proof は成果物検証を通る` |
| TRT-003 | テストのみ | - | - | `model/redex/tests/properties-trait-test.rkt`::`TRT-003: 性質3 一意候補は Resolved、重複候補は Ambiguous` |
| TRT-004 | テストのみ | - | - | `model/redex/tests/search-compose-test.rkt`::`TRT-004: 成分が合成でも同じ規則で降りる`, `model/redex/tests/search-compose-test.rkt`::`TRT-004: an invisible component makes the composite incoherent` |
| TRT-005 | テストのみ | - | - | `model/redex/tests/search-compose-test.rkt`::`TRT-005: RequiresBoth is implicit only for a declared intersect row` |
| TRT-006 | テストのみ | - | - | `model/redex/tests/trait-tables-test.rkt`::`TRT-006: 合成 trait は別の合成の成分になれる`, `model/redex/tests/trait-tables-test.rkt`::`TRT-006: 入れ子を足しても intersect-table は非巡回である` |
| TRT-007 | テストのみ | - | - | `model/redex/tests/trait-tables-test.rkt`::`TRT-007: 合成 trait を対象にする impl 行は拒否される` |
| CMP-001 | テストのみ | - | - | `model/redex/tests/properties-trait-test.rkt`::`CMP-001: 性質5 join 型は branch 順序に依らない`, `model/redex/tests/properties-trait-test.rkt`::`CMP-001: 性質6 join は全枝が mut のときだけ mut を保つ` |
| CMP-002 | テストのみ | - | - | `model/redex/tests/type-normalize-test.rkt`::`CMP-002: intersection is erased by row composition`, `model/redex/tests/type-normalize-test.rkt`::`CMP-002: colliding intersection fails to normalize` |
| COH-001 | テストのみ | - | - | `model/redex/tests/trait-scope-test.rkt`::`COH-001: 可視性は祖先到達で決まる` |
| PSR-001 | テストのみ | - | - | `model/redex/tests/properties-search-test.rkt`::`class と SR は互いを導出しない` |
| PSR-002 | テストのみ | - | - | `model/redex/tests/search-admissible-test.rkt`::`PSR-002: 暗黙挿入は有限一意の解決か停止性証明書を要求する` |
| PSR-003 | テストのみ | - | - | `model/redex/tests/properties-search-test.rkt`::`artifact 境界で Unknown 拒否が保たれる` |
| RET-001 | テストのみ | - | - | `model/redex/tests/leave-test.rkt`::`[REQ: RET-001] 式境界より内側の FunctionBoundary は Leave を捕まえる` |
| RET-002 | テストのみ | - | - | `model/redex/tests/leave-test.rkt`::`[REQ: RET-002] probe と型付き境界は到達不能な Leave を合流しない` |
| RET-003 | 未検証 | - | - | - |
| EFF-001 | テストのみ | - | - | `model/redex/tests/elaborate-test.rkt`::`EFF-001: declared rows bound fn and recur bodies` |
| PRF-001 | テストのみ | - | - | `model/redex/tests/origins-test.rkt`::`PRF-001: only the reserved TypeNarrative proof is valid` |
| PRF-002 | 未検証 | - | - | - |
| PRF-003 | 未検証 | - | - | - |
| PRF-004 | テストのみ | - | - | `model/redex/tests/elaborate-discharge-test.rkt`::`PRF-004: 義務列の順序が Discharge の入れ子順になる`, `model/redex/tests/elaborate-discharge-test.rkt`::`PRF-004: 搬送した ProofRep は初期成果物の検証を通る` |
| REC-001 | テストのみ | - | - | `model/redex/tests/classify-test.rkt`::`REC-001: no recursion and structural descent are Finite`, `model/redex/tests/classify-test.rkt`::`REC-001: Discharge 内でも減少しない自己適用は Unknown` |
| REC-002 | テストのみ | - | - | `model/redex/tests/machine-recur-test.rkt`::`REC-002: guarded recur produces every requested observation`, `model/redex/tests/obs-test.rkt`::`REC-002: yield produces the requested observation prefix` |
| MAC-001 | 未検証 | - | - | - |
| SCP-001 | テストのみ | - | - | `model/redex/tests/reassign-typing-test.rkt`::`SCP-001: 再代入は mut を要求し Mutation を記録する`, `model/redex/tests/surface-reassign-test.rkt`::`SCP-001: Surface の program と関数で mut 変数を繰り返し更新する` |
| SCP-002 | テストのみ | - | - | `model/redex/tests/pr-binding-test.rkt`::`置換は label、tag、境界名、primitive 名を書き換えない` |
| OWN-001 | テストのみ | - | - | `model/redex/tests/machine-own-test.rkt`::`OWN-001: move succeeds once and reuse raises OwnershipError` |
| OWN-002 | テストのみ | - | - | `model/redex/tests/machine-own-test.rkt`::`OWN-002: scope finalizes available places once in reverse order` |
| OWN-003 | テストのみ | - | - | `model/redex/tests/abort-frame-cleanup-test.rkt`::`OWN-003/OWN-011: ScopeError は捨てる frame の leaf を Dropped にする` |
| OWN-004 | テストのみ | - | - | `model/redex/tests/owned-narrowing-test.rkt`::`余剰 Owned 欄を落とす narrowing は Proof を求める` |
| BOR-001 | テストのみ | - | - | `model/redex/tests/scope-escape-borrow-test.rkt`::`BOR-001: owner Let の body から借用を外へ出すのを拒否する` |
| BOR-002 | テストのみ | - | - | `model/redex/tests/projection-child-alpha-test.rkt`::`BOR-002: oracle は同じ可変 loan の兄弟射影を二度生存させない` |
| BOR-003 | テストのみ | - | - | `model/redex/tests/region-test.rkt`::`C5: golden program の Scope と分解の region を問い合わせだけで再構成できる` |
| BOR-004 | テストのみ | - | - | `model/redex/tests/borrow-use-test.rkt`::`BOR-004: 共有 Read と可変借用の利用は許し、共有借用への書込みは拒む`, `model/redex/tests/borrow-use-test.rkt`::`BOR-004: 生存中に重なる借用は owner の直接 Read と Assign を拒む` |
| BOR-005 | テストのみ | - | - | `model/redex/tests/borrow-proj-test.rkt`::`BOR-005: 投影借用の mode は親と欄の可変性に従う` |
| BOR-006 | テストのみ | - | - | `model/redex/tests/capability-table-test.rkt`::`Construct は欄ごとの表を作る` |
| VAR-004 | テストのみ | - | - | `model/redex/tests/variance-region-test.rkt`::`共有借用の region は共変である`, `model/redex/tests/variance-region-test.rkt`::`可変借用の region は不変である` |
| BOR-007 | テストのみ | - | - | `model/redex/tests/borrow-fnbound-test.rkt`::`束縛された rp の借用は境界を越えられる` |
| OWN-005 | テストのみ | - | - | `model/redex/tests/own-let-place-test.rkt`::`Eliminate が計算した Record を Owned の束縛へ載せる` |
| OWN-006 | テストのみ | - | - | `model/redex/tests/own-formal-test.rkt`::`Owned の仮引数を 1 つ取る Fn が生名と Let を持つ節へ写る` |
| OWN-007 | テストのみ | - | - | `model/redex/tests/own-capture-test.rkt`::`Owned を 1 件捕捉する closure を elaborate でき、型が Owned<NFn> になる` |
| OWN-008 | テストのみ | - | - | `model/redex/tests/own-curry-fixed-test.rkt`::`Owned の固定引数を Move 経由で固定でき、結果型が Owned<NFn 残余> になる` |
| OWN-009 | テストのみ | - | - | `model/redex/tests/typing-test.rkt`::`config-ok? の拒否理由 owned-duplicate` |
| OWN-010 | テストのみ | - | - | `model/redex/tests/typing-test.rkt`::`config-ok? の拒否理由 path-shape-mismatch` |
| OWN-011 | テストのみ | - | - | `model/redex/tests/abort-frame-cleanup-test.rkt`::`OWN-003/OWN-011: ScopeError は捨てる frame の leaf を Dropped にする` |
| PTR-001 | テストのみ | - | - | `model/redex/tests/properties-unsafe-test.rkt`::`型検査を通った項の raw 操作はすべて Unsafe の内側にある` |
| PTR-002 | テストのみ | - | - | `model/redex/tests/properties-unsafe-test.rkt`::`PtrOffset の静的要求は生成域に現れる` |
| SUR-001 | テストのみ | - | THM-002, THM-003, THM-004, THM-006, THM-007 | `model/redex/tests/surface-lower-test.rkt`::`constructor の lowering は式全体の span を保つ` |
| SUR-002 | テストのみ | - | `lex_escaped_dollar_ok`, `lex_interpolation_ok`, `lex_nested_interpolation_in_hole_ok`, `lex_nested_string_in_hole_ok`, `lex_nested_unclosed_string_span_ok`, `lex_try_pipe_ok`, `lex_unclosed_hole_span_ok` | `model/redex/tests/surface-interpolation-test.rkt`::`[REQ: SUR-002] SUR-002b: 穴の値を連結した文字列へ評価する` |
| SUR-003 | テストのみ | - | - | `model/redex/tests/surface-effect-row-test.rkt`::`SUR-003: row の省略形、括弧形、空形、重複と span` |
| SUR-004 | 未検証 | - | - | - |
| SUR-005 | テストのみ | - | - | `model/redex/tests/surface-derive-test.rkt`::`SUR-005: derive の Proof は返された台帳の下で正規に検証される` |
| SUR-006 | テストのみ | - | - | `model/redex/tests/projrec-typing-test.rkt`::`選んだ欄だけの record になる` |
| SUR-007 | テストのみ | - | - | `model/redex/tests/driver-test.rkt`::`関数宣言と適用が型付きの成果物になる`, `model/redex/tests/driver-test.rkt`::`record リテラルと射影が型付きの成果物になる` |
| SUR-008 | テストのみ | - | - | `model/redex/tests/surface-return-infer-test.rkt`::`SUR-008: 合成位置の省略した戻り型は本体の型になる`, `model/redex/tests/surface-return-infer-test.rkt`::`SUR-008: 検査位置の省略した戻り型は期待型から決まる` |
| SUR-009 | テストのみ | - | - | `model/redex/tests/surface-trait-compose-test.rkt`::`SUR-009: 二項の合成は合成 trait 行と intersect 行を 1 つずつ作る`, `model/redex/tests/surface-trait-compose-test.rkt`::`SUR-009: 三項の合成は隠れた出力を内側に持つ入れ子になる` |
| SUR-010 | テストのみ | - | - | `model/redex/tests/surface-trait-decl-test.rkt`::`a trait declaration becomes a root trait row with a normalized field row`, `model/redex/tests/surface-trait-decl-test.rkt`::`an impl declaration becomes a row and a Let over an Apply of the primitive` |
| SUR-011 | テストのみ | - | - | `model/redex/tests/parser-test.rkt`::`SUR-011: 明示的な戻り型を -> 無しで書くと E-SUR-005 になる` |
| SUR-012 | テストのみ | - | - | `model/redex/tests/elaborate-lambda-infer-test.rkt`::`SUR-012: 期待の関数型から仮引数型を補う`, `model/redex/tests/elaborate-lambda-infer-test.rkt`::`SUR-012: 出力の Typed Core と Φ に #:infer が現れない` |
| SUR-013 | 未検証 | - | `lex_operator_tokens_ok` | - |
| SUR-014 | テストのみ | - | - | `model/redex/tests/surface-when-boundary-test.rkt`::`[REQ: SUR-014] 枝の leave は when の値になり関数の残りが実行される` |
| SUR-015 | テストのみ | - | - | `model/redex/tests/surface-return-test.rkt`::`SUR-015: 関数宣言の return は受理され、早期に戻る` |
| SUR-016 | テストのみ | - | - | `model/redex/tests/surface-type-app-test.rkt`::`SUR-016: 型構成子の適用は UCore の型へ写る` |
| MOD-001 | 未検証 | - | - | - |
| BIT-001 | 未検証 | - | - | - |
| BIT-002 | テストのみ | - | - | `model/redex/tests/lowering-arith-test.rkt`::`every shim primitive lowers to an eta expanded shim call` |
| BIT-003 | テストのみ | - | `lex_bar_amp_ok` | `model/redex/tests/surface-type-op-test.rkt`::`BIT-003: Union の注釈は elaborate と typing を通る`, `model/redex/tests/surface-type-op-test.rkt`::`BIT-003: Record の Intersection は一つの Record に正規化される` |
| BIT-004 | 未検証 | - | - | - |
| ADT-001 | テストのみ | - | - | `model/redex/tests/surface-optional-field-test.rkt`::`ADT-001。省略した欄の p.age は none を返す`, `model/redex/tests/surface-optional-field-test.rkt`::`ADT-001。data 型の constructor の引数に optional の欄を宣言できる`, `model/redex/tests/surface-data-decl-test.rkt`::`ADT-001: data 型宣言は台帳の宣言の形へ写る` |
| PAT-001 | テストのみ | - | - | `model/redex/tests/owned-transit-trace-test.rkt`::`Owned Union の UnionEliminate は marker を外して非資源成分を選ぶ` |
| PRF-005 | テストのみ | - | - | `model/redex/tests/remainder-drop-test.rkt`::`Proof 無しの narrowing は owned-narrowing-needs-proof である` |
| BAK-001 | テストのみ | - | - | `model/redex/tests/properties-lowering-test.rkt`::`BAK-001: Union の Core の観測が lowering の前後で一致する` |
| BAK-002 | 未検証 | - | - | - |
| BAK-003 | 未検証 | - | - | - |
| BAK-004 | 未検証 | - | - | - |
| BAK-005 | 未検証 | - | - | - |
| BAK-006 | 未検証 | - | - | - |
| BAK-007 | 未検証 | - | - | - |
| BAK-008 | 未検証 | - | - | - |
| BAK-009 | 未検証 | - | - | - |
| BAK-010 | 未検証 | - | - | - |
| BAK-011 | 未検証 | - | - | - |
| BAK-012 | 未検証 | - | - | - |
| FFI-001 | 未検証 | - | - | - |
| FFI-002 | 未検証 | - | - | - |
| FFI-003 | 未検証 | - | - | - |
| DIA-001 | テストのみ | - | - | `model/redex/tests/typing-diagnostic-test.rkt`::`入口検査の失敗は細分類した Diagnostic を返す` |
| DIA-002 | テストのみ | - | - | `model/redex/tests/typing-diagnostic-test.rkt`::`棄却節点が根なら primary-span は根を指す` |
| DIA-003 | テストのみ | - | - | `model/redex/tests/typing-diagnostic-test.rkt`::`typing の source-chain は sourceId で kind を分ける` |
| DIA-004 | テストのみ | - | - | `model/redex/tests/diagnostic-render-test.rkt`::`fixture 8 件で 3 形式の 10 観測量が一致する` |
| DIA-005 | テストのみ | - | - | `model/redex/tests/diagnostic-test.rkt`::`diagnostic-of は registry から id と title を引き当てる` |

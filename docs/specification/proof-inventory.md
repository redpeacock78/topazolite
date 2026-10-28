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
| NAR-001 | 未検証 | - | - | - |
| NAR-002 | 未検証 | - | - | - |
| NAR-003 | 未検証 | - | - | - |
| NAR-004 | テストのみ | - | - | `model/redex/tests/search-compose-test.rkt`::`NAR-004: 合成 Proof の親は intersect の派生 origin である` |
| NAR-005 | テストのみ | - | - | `model/redex/tests/own-curry-fixed-test.rkt`::`Owned の固定引数を Move 経由で固定でき、結果型が Owned<NFn 残余> になる` |
| POL-001 | 未検証 | - | - | - |
| POL-002 | 未検証 | - | - | - |
| CUR-001 | 未検証 | - | - | - |
| CUR-002 | 未検証 | - | - | - |
| TYP-001 | 未検証 | - | - | - |
| TYP-002 | 未検証 | - | - | - |
| TYP-003 | 未検証 | - | - | - |
| ROW-001 | 未検証 | - | - | - |
| ROW-002 | 未検証 | - | - | - |
| ROW-003 | 未検証 | - | - | - |
| ROW-004 | 未検証 | - | - | - |
| ROW-005 | 未検証 | - | - | - |
| VAR-001 | 未検証 | - | - | - |
| VAR-002 | 未検証 | - | - | - |
| VAR-003 | 未検証 | - | - | - |
| RFN-001 | 未検証 | - | - | - |
| RFN-002 | 未検証 | - | - | - |
| RFN-003 | 未検証 | - | - | - |
| TRT-001 | 未検証 | - | - | - |
| TRT-002 | 未検証 | - | - | - |
| TRT-003 | 未検証 | - | - | - |
| TRT-004 | 未検証 | - | - | - |
| TRT-005 | 未検証 | - | - | - |
| TRT-006 | 未検証 | - | - | - |
| TRT-007 | 未検証 | - | - | - |
| CMP-001 | 未検証 | - | - | - |
| CMP-002 | 未検証 | - | - | - |
| COH-001 | 未検証 | - | - | - |
| PSR-001 | 未検証 | - | - | - |
| PSR-002 | 未検証 | - | - | - |
| PSR-003 | 未検証 | - | - | - |
| RET-001 | テストのみ | - | - | `model/redex/tests/leave-test.rkt`::`[REQ: RET-001] 式境界より内側の FunctionBoundary は Leave を捕まえる` |
| RET-002 | テストのみ | - | - | `model/redex/tests/leave-test.rkt`::`[REQ: RET-002] probe と型付き境界は到達不能な Leave を合流しない` |
| RET-003 | 未検証 | - | - | - |
| EFF-001 | 未検証 | - | - | - |
| PRF-001 | 未検証 | - | - | - |
| PRF-002 | 未検証 | - | - | - |
| PRF-003 | 未検証 | - | - | - |
| PRF-004 | 未検証 | - | - | - |
| REC-001 | テストのみ | - | - | `model/redex/tests/storage-ok-test.rkt`::`REC-001: value path の純粋な NFn は拒否する` |
| REC-002 | 未検証 | - | - | - |
| MAC-001 | 未検証 | - | - | - |
| SCP-001 | 未検証 | - | - | - |
| SCP-002 | テストのみ | - | - | `model/redex/tests/pr-binding-test.rkt`::`置換は label、tag、境界名、primitive 名を書き換えない` |
| OWN-001 | 未検証 | - | - | - |
| OWN-002 | 未検証 | - | - | - |
| OWN-003 | テストのみ | - | - | `model/redex/tests/abort-frame-cleanup-test.rkt`::`OWN-003/OWN-011: ScopeError は捨てる frame の leaf を Dropped にする` |
| OWN-004 | テストのみ | - | - | `model/redex/tests/owned-narrowing-test.rkt`::`余剰 Owned 欄を落とす narrowing は Proof を求める` |
| BOR-001 | 未検証 | - | - | - |
| BOR-002 | 未検証 | - | - | - |
| BOR-003 | テストのみ | - | - | `model/redex/tests/region-test.rkt`::`C5: golden program の Scope と分解の region を問い合わせだけで再構成できる` |
| BOR-004 | 未検証 | - | - | - |
| BOR-005 | 未検証 | - | - | - |
| BOR-006 | テストのみ | - | - | `model/redex/tests/capability-table-test.rkt`::`Construct は欄ごとの表を作る` |
| VAR-004 | 未検証 | - | - | - |
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
| SUR-001 | 未検証 | - | THM-002, THM-003, THM-004, THM-006, THM-007 | - |
| SUR-002 | テストのみ | - | `lex_escaped_dollar_ok`, `lex_interpolation_ok`, `lex_nested_interpolation_in_hole_ok`, `lex_nested_string_in_hole_ok`, `lex_nested_unclosed_string_span_ok`, `lex_try_pipe_ok`, `lex_unclosed_hole_span_ok` | `model/redex/tests/surface-interpolation-test.rkt`::`[REQ: SUR-002] SUR-002b: 穴の値を連結した文字列へ評価する` |
| SUR-003 | テストのみ | - | - | `model/redex/tests/surface-effect-row-test.rkt`::`SUR-003: row の省略形、括弧形、空形、重複と span` |
| SUR-004 | 未検証 | - | - | - |
| SUR-005 | 未検証 | - | - | - |
| SUR-006 | テストのみ | - | - | `model/redex/tests/projrec-typing-test.rkt`::`選んだ欄だけの record になる` |
| SUR-007 | 未検証 | - | - | - |
| SUR-008 | 未検証 | - | - | - |
| SUR-009 | 未検証 | - | - | - |
| SUR-010 | 未検証 | - | - | - |
| SUR-011 | 未検証 | - | - | - |
| SUR-012 | 未検証 | - | - | - |
| SUR-013 | 未検証 | - | `lex_operator_tokens_ok` | - |
| SUR-014 | テストのみ | - | - | `model/redex/tests/surface-when-boundary-test.rkt`::`[REQ: SUR-014] 枝の leave は when の値になり関数の残りが実行される` |
| SUR-015 | テストのみ | - | - | `model/redex/tests/surface-return-test.rkt`::`SUR-015: 関数宣言の return は受理され、早期に戻る` |
| SUR-016 | テストのみ | - | - | `model/redex/tests/surface-type-app-test.rkt`::`SUR-016: 型構成子の適用は UCore の型へ写る` |
| MOD-001 | 未検証 | - | - | - |
| BIT-001 | 未検証 | - | - | - |
| BIT-002 | テストのみ | - | - | `model/redex/tests/lowering-arith-test.rkt`::`every shim primitive lowers to an eta expanded shim call` |
| BIT-003 | 未検証 | - | `lex_bar_amp_ok` | - |
| BIT-004 | 未検証 | - | - | - |
| ADT-001 | 未検証 | - | - | - |
| PAT-001 | 未検証 | - | - | - |
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
| DIA-004 | 未検証 | - | - | - |
| DIA-005 | テストのみ | - | - | `model/redex/tests/diagnostic-test.rkt`::`diagnostic-of は registry から id と title を引き当てる` |

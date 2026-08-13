# Diagnostic IR と error code registry

本文書は、compiler phase が返す Diagnostic の構造と error code の versioning 規約を定める。

Diagnostic の生成、source-chain の構築、expansion trace の構築、terminal と LSP と JSON の renderer は本文書の規約を入力として後続サイクルで実装する。

## 1. Diagnostic IR の欄

**Diagnostic IR** は、compiler phase が診断を渡すための Racket の transparent struct である。

Diagnostic IR は G1、G2、PR の項ではなく、簡約や型付けの対象でもない。

Diagnostic IR は次の18欄を持つ。

| 欄 | 意味 |
| --- | --- |
| `id` | 安定した error code |
| `severity` | 診断の重さ |
| `category` | error code の分類部を表す記号 |
| `title` | 診断の一行見出し |
| `message` | 診断された事象の説明 |
| `primary-span` | 最小原因を指す primary span |
| `secondary-labels` | 補助 span とラベルの対の列 |
| `notes` | 診断を補足する文章の列 |
| `help` | 対処方法を示す文章の列 |
| `expected` | 期待された値 |
| `found` | 実際に見つかった値 |
| `source-chain` | Surface から Core までの provenance frame の列 |
| `expansion-trace` | macro 展開の履歴 |
| `effect-context` | 診断が生じた効果行の文脈 |
| `proof-context` | 診断が生じた Proof 義務の文脈 |
| `related` | 関連する Diagnostic の列 |
| `fixes` | 機械適用可能な修正候補の列 |
| `backend` | lowering の診断が生じた対象 backend |

`id` は表示と外部連携に使う文字列であり、`category` は分岐に使う記号である。

この二つを別の型にすることで、表示用の連結識別子と処理用の分類値を混同しない。

`category` は `id` の分類部から導出し、構築関数の引数にはしない。

`source-chain` はホワイトペーパー §13.4.1 の `originChain[]` に当たる。

欄名を替えたのは、`core-calculus.md` の `origin` と NAR-002 が値の信頼経路に同じ語を充てており、二つの機構を欄名で判別できなくなるためである。

## 2. schema version 3 の形

**schema version** は、Diagnostic の欄集合と各欄が受け付ける値の形を示す版である。

schema version 3 は、各欄へ次の形を要求する。

| 欄 | schema version 3 の形 |
| --- | --- |
| `id` | registry に存在する code の文字列 |
| `severity` | `'error`、`'warning`、`'note` のいずれか |
| `category` | `id` の分類部と `eq?` で一致する記号 |
| `title` | 改行を含まない空でない文字列 |
| `message` | 空でない文字列。複数行を許す |
| `primary-span` | `span-ok?` を満たす span |
| `secondary-labels` | `(list span label)` の list。label は改行を含まない空でない文字列 |
| `notes` | 改行を含まない空でない文字列の list |
| `help` | 改行を含まない空でない文字列の list |
| `expected` | 任意の値または `#f` |
| `found` | 任意の値または `#f` |
| `source-chain` | §3 の frame の空でない list |
| `expansion-trace` | 空の list |
| `effect-context` | 任意の値または `#f` |
| `proof-context` | 任意の値または `#f` |
| `related` | `(relation span description)` の list。空でもよい |
| `fixes` | 空の list |
| `backend` | `'racket-cs`、`'racketscript`、`#f` のいずれか |

`secondary-labels` の各要素は2要素の list であり、第1要素は `span-ok?` を満たす span、第2要素は空でない文字列である。

`notes` と `help` は list であり、各要素は空でない文字列である。

1 行として出る欄へ改行を禁じるのは、renderer がその欄を 1 行として整形するためである。

`title` は terminal の見出し行と LSP の `message` の第1行、`notes` と `help` は terminal の `=` で始まる補足行、`secondary-labels` のラベルは terminal の位置行、`related` の `relation` と `description` は terminal の related の行と LSP の `relatedInformation` の `message` へ出る。

改行が入ると表示が 2 行へ割れ、1 行として読める行という前提が崩れる。

renderer 側で改行を escape する規則は置かない。

escape は表示を壊さないだけで、1 行の欄へ複数行が入るという producer 側の誤りを隠す。

入口で弾けば、誤りは Diagnostic を作った箇所の error として現れる。

`message` だけは複数行を許す。

`message` は診断ごとの説明であり、Phase 1 以降に複数の文からなる文案が入る欄である。

ここを 1 行に縛ると、`message` を充実させる段階で schema version を上げ直すことになる。

`diagnostic-valid?` はこの形を満たすかを返し、`diagnostic-schema-errors` は満たさない条件の理由を文字列の list で返す。

## 3. source-chain の要素形と schema version 3 の空要求

[REQ: DIA-003] `source-chain` は、その診断が指す構文の由来を Surface から Core の順に並べた frame の列である。

**source-chain frame** は `(list phase kind span)` の3要素の list である。

- `phase`：その frame が指す節点を持ち込んだ層を表す記号。`surface` または `elaborate` のいずれか。
- `kind`：span がどのように得られたかを表す記号。`verbatim`、`synthesized`、`synthetic-span` のいずれか。
- `span`：`span-ok?` を満たす span。

列の先頭は最も source に近い frame である。

`surface` の frame は必ず1つ存在し、`elaborate` の frame はその後ろに並ぶ。

合成された節点であっても、その合成を引き起こした入力の構文が必ずあり、その位置が `surface` の frame になるためである。

`kind` は生成地点の事実を span の `sourceId` より優先して決める。

producer は自分がその節点を合成したかを先に判定し、合成でない場合に限り `sourceId` を見る。

`verbatim` と `synthetic-span` は入力由来の節点にのみ与える値であり、`sourceId` が `#:synthetic` かどうかで両者を分ける。

`synthesized` は予約値であり、Phase 0 の producer は生成しない。

Phase 0 の elaborate は節点を合成しないため、Phase 0 が出す `source-chain` の長さは1であり、`kind` は `verbatim` と `synthetic-span` の2値に限られる。

予約値を許容集合へ最初から含めるのは、Phase 2 の desugaring が節点を合成するようになったときに schema version を上げずに済ませるためである。

`expansion-trace` と `fixes` の2欄は、schema version 3 では空であることを要求する。

これらの欄を埋めるサイクルが要素の形を定め、その変更時に schema version を上げる。

`fixes` は Phase 1 以降、`expansion-trace` は Phase 2 以降が定める。

この空要求は、要素形を未定義のまま受け入れることと、将来の要素形を先取りすることを避ける。

欄そのものは18欄すべてを最初から持つため、後続サイクルは欄の追加を待たずに値を生成できる。

## 4. related の要素形

**related 参照** は `(list relation span description)` の3要素の list である。

- `relation`：関連の種類を表す記号。語彙は固定しないが、綴りに改行を含まない。
- `span`：`span-ok?` を満たす span。
- `description`：空でない文字列。改行を含まない。

Diagnostic を入れ子にしない。

LSP の `DiagnosticRelatedInformation` は location と message の2欄しか持たず、Ariadne の secondary label も同じ形である。

Diagnostic を丸ごと入れ子にすると renderer は大半の欄を捨てることになり、schema 検証が再帰して循環した参照で停止しなくなる余地が残る。

renderer は未知の `relation` を捨てず、記号をそのまま表示する。

Phase 0 の producer は related を生成しないため、G4f1 が定めるのは受け入れる形だけである。

## 5. Phase 0 で形を固定しない欄

`expected`、`found`、`effect-context`、`proof-context` の4欄は、Phase 0 では形を固定しない。

この4欄は任意の値または `#f` を受け、schema version 3 の検証器は値の形を検査しない。

空要求の4欄は「まだ使わないので空」と定める欄であり、この4欄は「使うが形を決めない」と定める欄である。

producer は phase ごとに型項、効果集合、証明対象など異なる値を入れるため、共通の形へ縛ると producer 側の判定経路を歪める。

producer は `details` を文字列化せず、Racket の値のまま `expected` と `found` へ置く。

producer は `details` の先頭を `expected`、次を `actual` とする。

この順を選んだのは、Diagnostic の欄順および renderer の表示順と一致させるためである。

例外表の key allowlist は残す。

表に無い key の `details` 2件は `expected` と `actual` の対ではなく、`found` へ list ごと入る。

既定では `details` の件数だけで配り、意味を推測して `expected` を作らない。

`found` は「実測した型」ではなく、棄却の対象になった値を指す欄である。

renderer が具体的な整形を要求するのは G4f 以降であり、その時点で要素形を定めて schema version を上げる。

この判断は未回収の欄を残すものではなく、schema version 3 が「任意の値または `#f`」を形として定めるものである。

## 6. 二つの version

Diagnostic IR は schema version と registry version の二つの版を持つ。

`diagnostic-schema-version` は G4f1 完了時点で3であり、`diagnostic-registry-version` は2である。

schema version は欄の追加、削除、または欄が受け付ける形の変更で上げる。

registry version は error code を追加または廃止するサイクルごとに上げる。

同じサイクルで複数の code を追加する場合に同じ版を付けるため、registry version は code 一件ごとには上げない。

二つの版を分けるのは、欄の形と code の集合が独立に変更されるためである。

code の追加は renderer の入力形を変えず、欄の追加は既存 code の意味を変えない。

registry の `since`、`deprecated-in`、凍結 fixture は registry version に紐づき、schema version には紐づかない。

## 7. error code の書式と分類

error code は `E-<分類>-<3桁>` の書式を持つ。

分類は `SYN`、`TYP`、`KND`、`EFF`、`RET`、`OWN`、`VAR`、`REC`、`ARI`、`DAT`、`RCD`、`APP`、`PRF`、`ORG`、`LOW` の15種である。

分類部は要件 ID の接頭辞とは別の体系である。

分類部と要件 ID の接頭辞に同じ文字列が現れても、両者の対応関係は定めない。

例えば `TYP` は error code では型検査に関する分類を表し、要件 ID の `TYP-001` を参照するものではない。

## 8. registry に載せる診断

[REQ: DIA-001] elaborate、typing、origins、lowering の 4 phase は、失敗を文字列ではなく Diagnostic IR で返す。

error code registry には、production が返しうる診断だけを載せる。

正常な判定結果である `Unknown`、`Absent`、`Ambiguous`、`obligation-proofs` の `#f` には error code を与えない。

registry の対象は elaborate の reject reason、typing の棄却 key、origins の `forged`、lowering の診断 key である。

test seam のためだけに production が返さない code を registry へ予約しない。

lowering の `capability-diagnostic` を Diagnostic IR へ変換するのは `lower` の層であり、`lower/with-matrix` は capability diagnostic を返す。

## 9. phase ごとの key

registry の `key` は、phase が診断を識別するために使う記号である。

elaborate の `key` は `reject` が第2引数に取る reason 記号である。

typing の `key` は producer が `fail` の第1引数に渡す記号である。

`core-type-of` は key を外へ出さず、`'ill-typed` へ潰した判定だけを返す。

key を Diagnostic へ運ぶのは `core-type-of/diagnostic` である。

origins の `key` は `verify-initial-origins` が返す `(forged ...)` の先頭記号である。

lowering の `key` は `diagnostic-ids` の第1要素であり、feature-id を表す。

lowering の `key` は `capability-diagnostic` の `reason` 文字列ではない。

registry の lowering 行の title は `diagnostic-ids` の第2要素から得る。

## 10. registry の versioning

[REQ: DIA-005] registry は追記のみとし、既存 code の削除、意味の付け替え、番号の再利用を行わない。

code を廃止するときは registry の行を削除せず、`deprecated-in` に廃止した registry version を記録する。

`since` は code を追加した registry version であり、`deprecated-in` がある場合は `since` より大きい。

`since` と `deprecated-in` は、どちらも現在の registry version 以下である。

一度も外部へ出していない code は廃止行として残さず、追加前に取り下げる。

registry version 1 に属する59行は `since` が1である。

registry version 2 で足した typing の48行は `since` が2である。

`deprecated-in` は全107行が `#f` である。

## 11. 凍結 fixture

registry version ごとに、その版を出した時点の code 集合を記録する凍結 fixture を置く。

fixture は `(code phase key)` の組を持ち、test は fixture の全組が現在の registry に同じ組で存在することだけを要求する。

この包含のみの契約は、code の追加では既存 fixture を変更せず、削除、改名、番号の再利用、意味の付け替えで失敗する。

code だけを凍結すると、`E-TYP-012` を残したまま key を別の reason へ替える意味の付け替えを検出できない。

`title` は凍結しない。

文言の推敲は code が指す診断の意味を変えないため、title の変更は許す。

fixture は後方互換性を検査する履歴であり、第二の正典ではない。

現在の code 集合を知るときは `model/redex/diagnostic.rkt` の registry を読む。

## 12. E-TYP-001 の適用条件

`E-TYP-001` は型検査に失敗したが、より具体的な安定 code を割り当てられない場合に使う恒久の fallback である。

G4d4a が性質別の typing 細分類を追加しても、`E-TYP-001` の適用条件を狭めない。

`E-TYP-001` を立てる分岐は `infer` の catch-all だけではなく、枝の形の検査と binding-mode の既定にもある。

現行の `G2m` には、そのいずれへも到達する入力が無い。

この行を registry へ置くのは、producer に未分類時の明示分岐があり、`G2m` を拡張したときに実際に返りうるためである。

§8 の「production が返しうる診断だけを載せる」は、現在の入力集合での到達性ではなく、producer に分岐があることを指す。

`E-TYP-001` の title と message は文言を変更できるが、細分類できない型検査失敗を受けるという条件は変更しない。

## 13. primary-span と producer の規約

[REQ: DIA-002] `primary-span` は、その phase が棄却の判断を下した節点の span である。

「最も深い span を選ぶ」という汎用の述語は定めない。

深さは phase をまたいで一貫した意味を持たないためである。

判断節点の span を取れない入力に限り `(#:span #:synthetic 0 0)` へ落ちる。

判断節点の span を取れる入力で synthetic span へ落としてはならない。

型注釈の内部は包みを剥がすと span を失うため、最近傍の包みの span を使う。

Diagnostic の生成は phase ごとに1箇所へ集約し、registry の引き当てと schema 検証を通る経路を1本にする。

registry に無い reason を受けたときは、汎用 code へ落とさず error にする。

Diagnostic を生成する境界は、判定を行う関数そのものとは限らない。

typing の `core-type-of` と origins の `verify-origins` および `verify-initial-origins` は、それぞれ `'ill-typed` と `(forged ...)` を返す判定のまま残し、その上の adapter が Diagnostic を生成する。

origins が adapter を挟むのは、§1 が定めるとおり Diagnostic IR が項ではなく、metafunction の返り値へ struct を混ぜられないためである。

typing も同じ層の分担に揃え、判定 API と診断 API を分ける。

typing の primary-span は棄却の判断を下した節点の span である。

入口検査だけが投影した形を見て、走査は spanful な節点を受け取る。

`E-TYP-001` は細分類の key を割り当てられない棄却を受ける。

origins の primary-span は根ではなく `(forged <subject>)` の `subject` の span である。

`subject` は棄却の対象になった部分項そのものであり、位置が分かるため根へ丸めない。

lowering の primary-span も棄却の判断を下した節点の span である。

`lower` と `lower-value` は入口検査のためだけに投影し、`make-lowering` の走査は spanful な節点を受け取る。

`fail` は棄却した節点を受け取り、`op` のように span を持たない位置では囲む節点の span を使う。

Diagnostic を生成するのは `lower` と `lower-value` であり、`lower/with-matrix` は §8 のとおり capability diagnostic を返す層のまま残す。

`lower` と `lower-value` は `(values <status> <payload>)` の 2 値を返し、`status` の記号は `'ok` と `'capability` のままである。

Diagnostic 化で替えるのは失敗時の payload だけであり、`status` は失敗の分類を表すため payload の表現形とは独立である。

`capability-diagnostic` の `reason` 文字列は `found` へ入れる。

`backend` は Diagnostic の最上位の欄へ運ぶ。

`lower` と `lower-value` が生成する Diagnostic はすべて `backend` を持ち、他の3 phase の Diagnostic は `#f` を持つ。

phase と `backend` の対応を検査するのは `diagnostic-of` である。

`diagnostic-schema-errors` は Diagnostic 単体を受け取り、それを生成した phase を知らないためである。

`lower/with-matrix` を呼ぶ test は capability diagnostic の `backend` を引き続き読める。

## 14. 3 形式の renderer

[REQ: DIA-004] terminal、LSP、JSON の 3 つの renderer は、同一の Diagnostic IR を入力とする。

3 つは `model/redex/diagnostic-render.rkt` の `render-terminal`、`render-lsp`、`render-json` である。

renderer は Diagnostic を読むだけであり、欄を足さない。

`notes` は producer の欄であり、renderer は書き込まない。

位置の単位は 0 起点の行と 0 起点の UTF-16 code unit である。

1 起点へ直すのは terminal renderer だけであり、LSP の `range` と JSON の byte offset は 0 起点のまま運ぶ。

byte offset から行と列への変換は `model/redex/source-map.rkt` の `span->location` が担い、source の byte 長を超える offset と多 byte 文字の途中を指す offset を error にする。

`render-terminal` と `render-lsp` は source-map を取る。

`render-json` は取らない。JSON の span object が byte offset をそのまま載せるためである。

sourceId が `#:synthetic` の位置は、3 形式とも `<synthetic>` の綴りで示す。

`expected`、`found`、`effect-context`、`proof-context` の 4 欄は Phase 0 で要素形を固定しないため、3 形式とも `~s` で綴りへ写す。

`~a` で写すと文字列の引用符が落ち、記号との区別が付かなくなる。

LSP の `data` の `secondaryLabels` は、各要素を `(hasheq 'range <range> 'message <文字列> 'sourceId <文字列> 'synthetic <真偽>)` とする。

`sourceId` の綴りは JSON の span object と同じ規則に従う。

`range` と `synthetic` だけでは、別の source の同じ座標を指す補足位置を区別できない。

3 形式の一致は `model/redex/tests/diagnostic-render-test.rkt` が 10 の観測量で検査する。

位置の観測量は primary span の開始位置だけであり、`sourceId`、`synthetic`、`start-line`、`start-character` の 4 要素で比べる。

終わりの位置は 3 形式の共通部分に無い。

terminal の位置行は始まりしか出さず、caret も複数行 span を行末で打ち切るためである。

終わりは `source-map-test.rkt` の `location` 全体の検査と、形式ごとの `range`、caret、byte offset の試験が固定する。

`backend` と `message` は観測量に入れない。

`backend` は terminal だけが `#f` の欄の行を出さず、`message` は `title` と等しいとき terminal と LSP が本文行を省くため、3 形式で出力の有無が意図的に食い違う。

2 欄は形式ごとの試験が受け持つ。

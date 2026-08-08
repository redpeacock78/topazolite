# Diagnostic IR と error code registry

本文書は、compiler phase が返す Diagnostic の構造と error code の versioning 規約を定める。

Diagnostic の生成、origin chain の構築、expansion trace の構築、terminal と LSP と JSON の renderer は本文書の規約を入力として後続サイクルで実装する。

## 1. Diagnostic IR の欄

**Diagnostic IR** は、compiler phase が診断を渡すための Racket の transparent struct である。

Diagnostic IR は G1、G2、PR の項ではなく、簡約や型付けの対象でもない。

Diagnostic IR は次の17欄を持つ。

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
| `origin-chain` | Surface から Core までの origin の列 |
| `expansion-trace` | macro 展開の履歴 |
| `effect-context` | 診断が生じた効果行の文脈 |
| `proof-context` | 診断が生じた Proof 義務の文脈 |
| `related` | 関連する Diagnostic の列 |
| `fixes` | 機械適用可能な修正候補の列 |

`id` は表示と外部連携に使う文字列であり、`category` は分岐に使う記号である。

この二つを別の型にすることで、表示用の連結識別子と処理用の分類値を混同しない。

`category` は `id` の分類部から導出し、構築関数の引数にはしない。

## 2. schema version 1 の形

**schema version** は、Diagnostic の欄集合と各欄が受け付ける値の形を示す版である。

schema version 1 は、各欄へ次の形を要求する。

| 欄 | schema version 1 の形 |
| --- | --- |
| `id` | registry に存在する code の文字列 |
| `severity` | `'error`、`'warning`、`'note` のいずれか |
| `category` | `id` の分類部と `eq?` で一致する記号 |
| `title` | 空でない文字列 |
| `message` | 空でない文字列 |
| `primary-span` | `span-ok?` を満たす span |
| `secondary-labels` | `(list span label)` の list |
| `notes` | 空でない文字列の list |
| `help` | 空でない文字列の list |
| `expected` | 任意の値または `#f` |
| `found` | 任意の値または `#f` |
| `origin-chain` | 空の list |
| `expansion-trace` | 空の list |
| `effect-context` | 任意の値または `#f` |
| `proof-context` | 任意の値または `#f` |
| `related` | 空の list |
| `fixes` | 空の list |

`secondary-labels` の各要素は2要素の list であり、第1要素は `span-ok?` を満たす span、第2要素は空でない文字列である。

`notes` と `help` は list であり、各要素は空でない文字列である。

`diagnostic-valid?` はこの形を満たすかを返し、`diagnostic-schema-errors` は満たさない条件の理由を文字列の list で返す。

## 3. schema version 1 の空要求

`origin-chain`、`expansion-trace`、`related`、`fixes` の4欄は、schema version 1 では空であることを要求する。

これらの欄を埋めるサイクルが要素の形を定め、その変更時に schema version を上げる。

origin chain の要素形は G4e が定め、`origin-chain` を埋めるときに schema version は2になる。

この空要求は、要素形を未定義のまま受け入れることと、将来の要素形を先取りすることを避ける。

欄そのものは17欄すべてを最初から持つため、後続サイクルは欄の追加を待たずに値を生成できる。

## 4. Phase 0 で形を固定しない欄

`expected`、`found`、`effect-context`、`proof-context` の4欄は、Phase 0 では形を固定しない。

この4欄は任意の値または `#f` を受け、schema version 1 の検証器は値の形を検査しない。

空要求の4欄は「まだ使わないので空」と定める欄であり、この4欄は「使うが形を決めない」と定める欄である。

producer は phase ごとに型項、効果集合、証明対象など異なる値を入れるため、共通の形へ縛ると producer 側の判定経路を歪める。

producer は `details` を文字列化せず、Racket の値のまま `expected` と `found` へ置く。

既定では `details` の件数だけで配り、意味を推測して `expected` を作らない。

`found` は「実測した型」ではなく、棄却の対象になった値を指す欄である。

renderer が具体的な整形を要求するのは G4f 以降であり、その時点で要素形を定めて schema version を上げる。

この判断は未回収の欄を残すものではなく、schema version 1 が「任意の値または `#f`」を形として定めるものである。

## 5. 二つの version

Diagnostic IR は schema version と registry version の二つの版を持つ。

`diagnostic-schema-version` と `diagnostic-registry-version` は、G4c 完了時点ではともに1である。

schema version は欄の追加、削除、または欄が受け付ける形の変更で上げる。

registry version は error code を追加または廃止するサイクルごとに上げる。

同じサイクルで複数の code を追加する場合に同じ版を付けるため、registry version は code 一件ごとには上げない。

二つの版を分けるのは、欄の形と code の集合が独立に変更されるためである。

code の追加は renderer の入力形を変えず、欄の追加は既存 code の意味を変えない。

registry の `since`、`deprecated-in`、凍結 fixture は registry version に紐づき、schema version には紐づかない。

## 6. error code の書式と分類

error code は `E-<分類>-<3桁>` の書式を持つ。

分類は `SYN`、`TYP`、`KND`、`EFF`、`RET`、`OWN`、`VAR`、`REC`、`ARI`、`DAT`、`RCD`、`APP`、`PRF`、`ORG`、`LOW` の15種である。

分類部は要件 ID の接頭辞とは別の体系である。

分類部と要件 ID の接頭辞に同じ文字列が現れても、両者の対応関係は定めない。

例えば `TYP` は error code では型検査に関する分類を表し、要件 ID の `TYP-001` を参照するものではない。

## 7. registry に載せる診断

[REQ: DIA-001] elaborate、typing、origins、lowering の 4 phase は、失敗を文字列ではなく Diagnostic IR で返す。

error code registry には、production が返しうる診断だけを載せる。

正常な判定結果である `Unknown`、`Absent`、`Ambiguous`、`obligation-proofs` の `#f` には error code を与えない。

registry の対象は elaborate の reject reason、typing の棄却 key、origins の `forged`、lowering の診断 key である。

test seam のためだけに production が返さない code を registry へ予約しない。

lowering の `capability-diagnostic` を Diagnostic IR へ変換するのは `lower` の層であり、`lower/with-matrix` は capability diagnostic を返す。

## 8. phase ごとの key

registry の `key` は、phase が診断を識別するために使う記号である。

elaborate の `key` は `reject` が第2引数に取る reason 記号である。

typing の `key` は producer が `fail` の第1引数に渡す記号である。

`core-type-of` は key を外へ出さず、`'ill-typed` へ潰した判定だけを返す。

key を Diagnostic へ運ぶのは `core-type-of/diagnostic` である。

origins の `key` は `verify-initial-origins` が返す `(forged ...)` の先頭記号である。

lowering の `key` は `diagnostic-ids` の第1要素であり、feature-id を表す。

lowering の `key` は `capability-diagnostic` の `reason` 文字列ではない。

registry の lowering 行の title は `diagnostic-ids` の第2要素から得る。

## 9. registry の versioning

[REQ: DIA-005] registry は追記のみとし、既存 code の削除、意味の付け替え、番号の再利用を行わない。

code を廃止するときは registry の行を削除せず、`deprecated-in` に廃止した registry version を記録する。

`since` は code を追加した registry version であり、`deprecated-in` がある場合は `since` より大きい。

`since` と `deprecated-in` は、どちらも現在の registry version 以下である。

一度も外部へ出していない code は廃止行として残さず、追加前に取り下げる。

registry version 1 に属する59行は `since` が1である。

registry version 2 で足した typing の48行は `since` が2である。

`deprecated-in` は全107行が `#f` である。

## 10. 凍結 fixture

registry version ごとに、その版を出した時点の code 集合を記録する凍結 fixture を置く。

fixture は `(code phase key)` の組を持ち、test は fixture の全組が現在の registry に同じ組で存在することだけを要求する。

この包含のみの契約は、code の追加では既存 fixture を変更せず、削除、改名、番号の再利用、意味の付け替えで失敗する。

code だけを凍結すると、`E-TYP-012` を残したまま key を別の reason へ替える意味の付け替えを検出できない。

`title` は凍結しない。

文言の推敲は code が指す診断の意味を変えないため、title の変更は許す。

fixture は後方互換性を検査する履歴であり、第二の正典ではない。

現在の code 集合を知るときは `model/redex/diagnostic.rkt` の registry を読む。

## 11. E-TYP-001 の適用条件

`E-TYP-001` は型検査に失敗したが、より具体的な安定 code を割り当てられない場合に使う恒久の fallback である。

G4d4a が性質別の typing 細分類を追加しても、`E-TYP-001` の適用条件を狭めない。

`E-TYP-001` を立てる分岐は `infer` の catch-all だけではなく、枝の形の検査と binding-mode の既定にもある。

現行の `G2m` には、そのいずれへも到達する入力が無い。

この行を registry へ置くのは、producer に未分類時の明示分岐があり、`G2m` を拡張したときに実際に返りうるためである。

§7 の「production が返しうる診断だけを載せる」は、現在の入力集合での到達性ではなく、producer に分岐があることを指す。

`E-TYP-001` の title と message は文言を変更できるが、細分類できない型検査失敗を受けるという条件は変更しない。

## 12. primary-span と producer の規約

`primary-span` は、その phase が棄却の判断を下した節点の span である。

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

lowering の primary-span は入力 Core 項の根の span である。

`lower/with-matrix` は入口で `erase-core` を通し、その下の `fail` は feature-id と reason 文字列だけを受け取るため、棄却した部分項を持たない。

Diagnostic を生成するのは `lower` と `lower-value` であり、`lower/with-matrix` は §7 のとおり capability diagnostic を返す層のまま残す。

`lower` と `lower-value` は `(values <status> <payload>)` の 2 値を返し、`status` の記号は `'ok` と `'capability` のままである。

Diagnostic 化で替えるのは失敗時の payload だけであり、`status` は失敗の分類を表すため payload の表現形とは独立である。

`capability-diagnostic` の `reason` 文字列は `found` へ入れる。

`backend` は Diagnostic へ運ばない。

§2 が定める schema version 1 の欄集合に backend を置く欄が無く、欄を足せば schema version を上げることになる。

`lower/with-matrix` を呼ぶ test は capability diagnostic の `backend` を引き続き読める。

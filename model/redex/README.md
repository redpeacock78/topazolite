# G1 Redex Model

仕様: docs/specification/core-calculus.md（規則の正）

## bounded counterexample search の設定（正）

| 項目 | 値 |
|---|---|
| redex-check 試行数 | 1000 |
| 生成項の深さ上限 | 7 |
| 評価 fuel | 10000 |
| 観測深度上限 | 5 |
| discard 上限 | 20000 |
| 乱数 seed | 42 |

実行: `raco test model/redex/tests/properties-test.rkt`

各性質は `attempts`、`accepted`、`discard`、`seed` を出力する。

G2a の構造 row 探索では、record の field 数を 3 以下、record 型と
record リテラルのネストを 2 以下に生成文法で制限する。試行数、項の深さ、
評価 fuel は上表の既存設定をそのまま用いる。

反例が出ないことは性質の証明ではなく、この設定での反例未発見を意味する。
反例が出た場合は実装で回避せず claude へ報告する（改訂手順は実装計画の「実装体制」を参照）。

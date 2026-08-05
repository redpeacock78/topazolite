# Portable Racket backend matrix

Typed Core を Portable Racket へ写す規約と、backend ごとの feature 対応を定める。

## 1. 位置づけと不変条件

Portable Racket は意味論を決定しない。
Typed Core verifier を通過した意味論を実行形式へ写像するだけである。

この不変条件から 2 つが従う。
目標項は型を担がない。
型に依存する規則の選択は、写像の時点で静的に解く。

## 2. Portable Racket profile

（G3b で埋める。）

## 3. 目標言語 PR の構文

（G3b で埋める。）

## 4. 目標機械と観測

（G3b で埋める。）

## 5. lowering 関係と表現規約

（G3b で埋める。）

## 6. 保存の言明

（G3b で埋める。）

## 7. feature 対応表と support の 3 値

feature ごとに、2 つの backend での実現方法を `native`、`shim`、`unsupported`
の 3 値で宣言する。
表は `model/redex/backend-matrix.rkt` が唯一の定義元であり、検査規則は表の行
から生成する。

（conformance suite の義務との対応は G3d で足す。）

## 8. capability diagnostic

非対応 feature に当たったとき、写像は近似的な結果を出さず capability
diagnostic を返す。 [REQ: BAK-003]

診断は feature-id、backend、理由の 3 つを持つ。
診断を返した入力について、写像は目標項を返さない。
部分的な出力と診断を同時に返すことを禁じる。

診断 ID には feature に対応するものと、対応しないものがある。
後者は対応表に無い形に当たったときの fallback と、型符号を作れない入力に当た
ったときの fallback の 2 件であり、backend の能力の話ではないので support 値を
持たない。

## 9. conformance suite の義務

（G3d で埋める。）

## 10. bit 意味論と算術 shim

（G3c で埋める。）

## 11. 要件対応表

（G3d で埋める。）

## 12. 未回収の範囲

（G3d で埋める。）

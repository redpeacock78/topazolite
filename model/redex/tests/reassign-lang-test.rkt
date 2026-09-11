#lang racket
(require rackunit redex/reduction-semantics
         "../lang.rkt" "../ucore.rkt" "../span-core.rkt")

;; P1c2b。SCP-001。Reassign を 5 層の文法が受理する。
(define s '(#:span src 0 1))

(check-true (redex-match? UCore e '(Reassign x 1)))
(check-true (redex-match? UCore+ e `(Reassign ,s (#:var x ,s) (#:lit 1 ,s))))
(check-true (redex-match? G2 c '(Reassign x 1)))
(check-true (redex-match? G2m c '(Reassign x 1)))
(check-true (redex-match? G2+ c `(Reassign ,s (#:var x ,s) (#:lit 1 ,s))))

;; target は任意の項ではない。Rec リテラルへの再代入は文法が弾く。
(check-false (redex-match? G2 c '(Reassign (Rec ((a imm 1))) 1)))
;; G2 には place が無いので、place target は G2m でのみ合法である。
(check-false (redex-match? G2 c '(Reassign 0 1)))
(check-true (redex-match? G2m c '(Reassign 0 1)))

;; MutSlot は G1m の c の atom である。
(check-true (redex-match? G1m c '(MutSlot 0)))
(check-true (redex-match? G2m c '(MutSlot 0)))
(check-true (redex-match? G2m c '(Reassign (MutSlot 0) 1)))
;; 実行時だけの形なので source 側の G2 には無い。
(check-false (redex-match? G2 c '(MutSlot 0)))

;; MutSlot を値にしない。R-ScopeValue と R-Retire の値判定と競合する。
(check-false (redex-match? G2m v '(MutSlot 0)))

;; w は広げない。Move と借用の target は MutSlot を受けない。
(check-false (redex-match? G2m c '(Move (MutSlot 0))))
(check-false (redex-match? G2m c '(BorrowMut (MutSlot 0))))

;; 評価文脈の穴は値の側だけである。
(check-true (redex-match? G2m E (term (Reassign (MutSlot 0) hole))))
(check-true (redex-match? G2m F (term (Reassign (MutSlot 0) hole))))
(check-true (redex-match? G2m G (term (Reassign (MutSlot 0) hole))))
(check-false (redex-match? G2m E (term (Reassign hole 1))))

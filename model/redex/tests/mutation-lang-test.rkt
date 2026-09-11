#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../ucore.rkt")

;; core-calculus.md §3.2。Mutation は ℓ の要素であり、ε に載る。
(test-case "Mutation の Effect label（core-calculus.md §3.2）"
  (check-true (redex-match? G1 ℓ (term Mutation)))
  (check-true (redex-match? G1 ε (term (Mutation))))
  (check-true (redex-match? G1 ε (term (Unsafe Mutation)))))

;; Mutation は関数境界を越えて残るので、宣言 row の 2 層にも要る。
;; 宣言 row と本体 row の突合はここでは検査しない。
;; UCore の e に Assign が無く、Mutation を出す項を UCore へ置けるのは
;; P1c2b が Reassign を足してからである。
(test-case "Mutation が tℓ と uℓ に載る（core-calculus.md §3.2）"
  (check-true (redex-match? UCore tℓ (term Mutation)))
  (check-true (redex-match? UCore uℓ (term Mutation)))
  (check-true (redex-match? UCore tε (term (Mutation))))
  (check-true (redex-match? UCore uε (term (Mutation)))))

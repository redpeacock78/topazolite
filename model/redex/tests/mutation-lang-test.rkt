#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../ucore.rkt"
         "../elaborate.rkt"
         "../traits.rkt")

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

;; core-calculus.md §3.2。宣言 row の許可集合が Mutation を通す。
;; 本体の row は空であり、宣言 row の部分集合になる。
(test-case "Fn の宣言 row に Mutation を書ける（core-calculus.md §3.2）"
  (match-define (list _ type _ _)
    (elab '(Fn () Unit (Mutation) unit)))
  (check-equal? type '(NFn () Unit (Mutation) ())))

;; core-calculus.md §3.2。型注釈の row の許可集合が Mutation を通す。
(test-case "NFn の型注釈に Mutation を書ける（core-calculus.md §3.2）"
  (match-define (list _ type _ _)
    (elab '(Fn ((f (NFn () Int (Mutation) ()))) Int () 1)))
  (check-equal? type '(NFn ((NFn () Int (Mutation) ())) Int () ())))

;; core-calculus.md §3.2。trait template の latent row も Mutation を許す。
(test-case "template-effect? が Mutation を許す（core-calculus.md §3.2）"
  (check-true (template-effect? 'Mutation)))

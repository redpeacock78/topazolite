#lang racket

(require rackunit racket/set
         "../region.rkt"
         "../borrow.rkt")

(define ρ1 (region 100))
(define ρ2 (region 101))

;; psi-join は 3 欄の合併である。
(define Ψa (psi (set '(x 100)) (set) (set)))
(define Ψb (psi (set '(y 101)) (set '(z 100)) (set)))

(check-equal? (psi-join Ψa Ψb)
              (psi (set '(x 100) '(y 101)) (set '(z 100)) (set)))

;; psi-join は可換かつ冪等である。
(check-equal? (psi-join Ψa Ψb) (psi-join Ψb Ψa))
(check-equal? (psi-join Ψa Ψa) Ψa)

;; psi-exit は退場する region の項目だけを削る。
(define Ψc
  (psi (set (list 'x ρ1) (list 'y ρ2))
       (set (list 'z ρ1))
       (set (list 'w ρ2 ρ1))))

;; 段 9 で suspended の退場は親 capability の復帰へ変わる。この期待値は段 9 で動く。
(check-equal? (psi-exit Ψc (set ρ1))
              (psi (set (list 'y ρ2)) (set) (set)))

(check-equal? (psi-exit Ψc (set ρ2))
              (psi (set (list 'x ρ1)) (set (list 'z ρ1)) (set (list 'w ρ2 ρ1))))

;; suspended は 3 つ組の 3 番目、つまり子の region で判定する。
(check-equal? (psi-exit (psi (set) (set) (set (list 'w ρ2 ρ1))) (set ρ1))
              (psi (set) (set) (set)))

;; 空の Ψ は退場で変わらない。
(check-equal? (psi-exit (empty-psi) (set ρ1)) (empty-psi))

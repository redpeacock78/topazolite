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

;; ρ1 の退場で、停止していた (w ρ2 ρ1) は mut の (w ρ2) へ戻る。
(check-equal? (psi-exit Ψc (set ρ1))
              (psi (set (list 'y ρ2)) (set (list 'w ρ2)) (set)))

(check-equal? (psi-exit Ψc (set ρ2))
              (psi (set (list 'x ρ1)) (set (list 'z ρ1)) (set (list 'w ρ2 ρ1))))

;; suspended は 3 つ組の 3 番目、つまり子の region で判定する。
(check-equal? (psi-exit (psi (set) (set) (set (list 'w ρ2 ρ1))) (set ρ1))
              (psi (set) (set (list 'w ρ2)) (set)))

;; 親の ρ2 も同時に退場するときは戻さない。親の借用自体が既に死んでいる。
(check-equal? (psi-exit Ψc (set ρ1 ρ2)) (empty-psi))

;; mut に (x ρ2) があるときは、退避と子の共有借用の両方を行う。
(check-equal? (psi-suspend (psi (set) (set (list 'x ρ2)) (set))
                           'x ρ2 ρ1)
              (psi (set (list 'x ρ1))
                   (set)
                   (set (list 'x ρ2 ρ1))))

;; mut に無いときは共有借用だけを張り、退場時に mut を新規作成しない。
(check-equal? (psi-suspend (empty-psi) 'x ρ2 ρ1)
              (psi (set (list 'x ρ1)) (set) (set)))
(check-equal? (psi-exit (psi-suspend (empty-psi) 'x ρ2 ρ1) (set ρ1))
              (empty-psi))

;; 空の Ψ は退場で変わらない。
(check-equal? (psi-exit (empty-psi) (set ρ1)) (empty-psi))

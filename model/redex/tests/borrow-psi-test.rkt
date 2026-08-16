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

;; Ψ から項目を落とす操作はもう無い。合流は合併のままである。
(let ()
  (define a1 '(RVar 0))
  (define a2 '(RVar 1))
  (define Ψ1 (psi-add-shared (empty-psi) 'x a1))
  (define Ψ2 (psi-add-mut (empty-psi) 'y a2))
  (check-equal? (psi-shared (psi-join Ψ1 Ψ2))
                (set (list 'x a1)))
  (check-equal? (psi-mut (psi-join Ψ1 Ψ2))
                (set (list 'y a2))))

;; mut に (x ρ2) があるときは、退避と子の共有借用の両方を行う。
(check-equal? (psi-suspend (psi (set) (set (list 'x ρ2)) (set))
                           'x ρ2 ρ1)
              (psi (set (list 'x ρ1))
                   (set)
                   (set (list 'x ρ2 ρ1))))

;; mut に無いときは共有借用だけを張り、退場時に mut を新規作成しない。
(check-equal? (psi-suspend (empty-psi) 'x ρ2 ρ1)
              (psi (set (list 'x ρ1)) (set) (set)))

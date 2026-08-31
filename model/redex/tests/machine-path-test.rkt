#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../borrow.rkt"
         "../machine.rkt")

(define rec (term (Rec ((a mut (resource 1))))))

(test-case "heap-walk-path は辿れない path で #f を返す"
  (check-false (heap-walk-path rec (term (b))))
  (check-false (heap-walk-path rec (term (a b))))
  (check-false (heap-walk-path rec (term 0)))
  (check-equal? (heap-walk-path rec (term (a))) (term (resource 1))))

(test-case "value-set-path は失敗を #f として返す"
  (check-false (value-set-path rec (term (b)) (term (resource 2))))
  (check-false (value-set-path rec (term (a b)) (term (resource 2))))
  (check-false (value-set-path rec (term 0) (term (resource 2))))
  (check-equal? (value-set-path rec (term (a)) (term (resource 2)))
                (term (Rec ((a mut (resource 2)))))))

(test-case "proj-borrow-mut は空の path と欠落した label で #f を返す"
  (define H (term ((0 ,rec))))
  (check-false (proj-borrow-mut 0 (term ()) (term ρ) H))
  (check-false (proj-borrow-mut 0 (term (b)) (term ρ) H))
  (check-equal? (proj-borrow-mut 0 (term (a)) (term ρ) H)
                (term (BorrowMutRef 0 (a) ρ))))

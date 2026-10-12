#lang racket/base

(require rackunit
         redex/reduction-semantics
         "../borrow.rkt"
         "../lang.rkt"
         "../region.rkt"
         "../type-shape.rkt")

(define leaf '(OwnedLeaf (tok 1) (resource 1)))
(define marker `(OwnedTransit 9 (Rec ((a imm ,leaf) (b imm 3)))))

(test-case "移送 marker は G2m の値であり G2 の値ではない"
  (check-true (redex-match? G2m v marker))
  (check-false (redex-match? G2 v marker)))

(test-case "移送 marker の子は payload だけである"
  (check-equal? (core-children marker) (list (list-ref marker 2)))
  (check-equal? (core-with-children marker '(7)) '(OwnedTransit 9 7)))

(test-case "移送 marker の内部 token と leaf を一度だけ走査する"
  (check-equal? (collect-tokens marker) '((tok 1)))
  (check-equal? (walk-owned-leaves marker) '(((tok 1) (a))))
  (check-true (contains-owned-leaf? marker))
  (check-false (contains-owned-leaf? '(OwnedTransit 9 7))))

(test-case "移送 marker の place を共通の走査で列挙する"
  (define nested `(Rec ((a imm ,marker) (b imm (OwnedTransit 10 4)))))
  (check-equal? (transit-places nested) '(9 10))
  (check-true (contains-owned-transit? nested))
  (check-false (contains-owned-transit? `(Rec ((a imm ,leaf)))))
  (check-true (owned-transit? marker))
  (check-false (owned-transit? leaf)))

(test-case "移送 marker の内部にある leaf 位置を検査する"
  (check-true (observed-leaf-positions-ok? marker)))

(test-case "移送 marker を含む値の型の正規形を検査する"
  (check-true (core-types-normal? marker)))

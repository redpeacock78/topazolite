#lang racket

(require rackunit
         racket/set
         redex/reduction-semantics
         "../annotate.rkt"
         "../classify.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../type-shape.rkt"
         "../uniquify.rkt")

(test-case "R-Forward は Available の place を Moved にする"
  (check-equal?
   (apply-reduction-relation*
    -->g2/rules
    '(cfg (Forward 0) ((0 (resource 0))) ((0 Available)) () ()))
   '((cfg (resource 0) ((0 (resource 0))) ((0 Moved)) () ()))))

(test-case "Available でない place の Forward は停止する"
  (for ([state '(Moved Dropped)])
    (check-equal?
     (apply-reduction-relation
      -->g2/rules
      `(cfg (Forward 0) ((0 (resource 0))) ((0 ,state)) () ()))
     '())))

(test-case "Forward は注釈と消去の往復で保たれる"
  (check-equal? (erase-core (annotate-core '(Forward x))) '(Forward x)))

(test-case "Forward は領域走査で子を持たず自由変数を持つ"
  (check-equal? (core-children '(Forward x)) '())
  (check-equal? (core-with-children '(Forward x) '()) '(Forward x))
  (check-equal? (core-free-vars '(Forward x)) (set 'x)))

(test-case "Forward は一意化で外側の束縛名に追随する"
  (define renamed
    (uniquify-binders (annotate-core '(Let (x Int) 1 (Forward x)))))
  (match renamed
    [`(Let ,_ ((#:bind ,binder ,_) (#:ty Int ,_)) ,_
            (Forward ,_ (#:var ,operand ,_)))
     (check-equal? operand binder)
     (check-true (binder-has-identifier? binder))]
    [_ (fail (format "Forward を含む Let の形を保てない: ~s" renamed))]))

(test-case "Forward を含む構造的な再帰は根を辿って減少する"
  (define loop-type '(NFn ((List Int)) Int () () () User))
  (define core
    '(Recur list-loop-id loop (xs)
       (Eliminate xs
         ((nil () -> 0)
          (cons (head tail) -> (Apply loop (Forward tail)))))
       (Apply loop (Construct (List Int) nil))))
  (check-equal? (classify core '() `((list-loop-id ,loop-type)))
                '(Finite structural)))

(test-case "Forward は Core の型形状走査で受理される"
  (check-true (core-types-normal? '(Forward x))))

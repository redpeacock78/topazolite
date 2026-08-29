#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (elaboration-of source)
  (match (elab source)
    [(list core type row callables) (list core type row callables)]
    [other (error 'elaboration-of "elaboration failed: ~s" other)]))

(define owned-curry-surface
  '(Let p
       (Apply acquire 1)
       (Let g
            (Fn ((q (Owned Res))) Unit (Own) (Drop q))
            (Curry g (Move p)))))

(test-case
 "Owned の固定引数を Move 経由で固定でき、結果型が Owned<NFn 残余> になる"
 (match-define (list core type row callables)
   (elaboration-of owned-curry-surface))
 (check-equal? type '(Owned (NFn () Unit (Own) ())))
 (check-equal? (core-type-of core '() callables) (list type row)))

(define plain-curry-surface
  '(Fn ((n Int)) (NFn () Int () ()) ()
       (Let g
            (Fn ((a Int) (b Int)) Int () a)
            (Curry (Curry g n) 1))))

(test-case
 "関数側も固定引数側も Owned でなければ素の NFn を返す"
 (match-define (list core type row callables)
   (elaboration-of plain-curry-surface))
 (check-equal? type '(NFn (Int) (NFn () Int () ()) () ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

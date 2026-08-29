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

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

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

;; Owned の関数は Move 経由で呼べる。
(define owned-curry-apply-surface
  '(Fn ((p (Owned Res))) Unit (Own)
       (Let g
            (Fn ((q (Owned Res))) Unit (Own) (Drop q))
            (Let h
                 (Curry g (Move p))
                 (Apply (Move h))))))

(test-case
 "Owned の関数を Move 経由で呼べる"
 (match-define (list core type row callables)
   (elaboration-of owned-curry-apply-surface))
 (check-equal? type '(NFn ((Owned Res)) Unit (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; 中間の place を Move で開く形は関数の位置へ置ける。Task 3 の生成形がこの形を使う。
(define curried-owned-function-core
  '(Curry (Move t) (Move r)))

(define owned-curry-environment
  (list (list 't '(Owned (NFn ((Owned Res)) Unit (Own) ())))
        (list 'r '(Owned Res))))

(test-case
 "Owned の closure を載せた place を Move で開く入れ子の Curry は通る"
 (check-equal? (type-of/raw curried-owned-function-core '() '()
                             owned-curry-environment)
               '(ok ((Owned (NFn () Unit (Own) ())) (Own)))))

;; Move を経ない形は落ちる。関数式は Apply であり、Move でも CurryVal でもない。
(define owned-function-not-moved-core
  '(Apply (Apply mk)))

(define owned-maker-environment
  (list (list 'mk '(NFn () (Owned (NFn () Unit (Own) ())) (Own) ()))))

(test-case
 "Owned の関数を Move を経ずに関数の位置へ置くと owned-function-requires-move で落ちる"
 (check-equal? (key-of (type-of/raw owned-function-not-moved-core '() '()
                                     owned-maker-environment))
               'owned-function-requires-move))

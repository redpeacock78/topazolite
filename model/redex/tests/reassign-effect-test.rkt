#lang racket

(require rackunit racket/match redex/reduction-semantics
         "../lang.rkt" "../typing.rkt" "../borrow.rkt" "../region.rkt")

;; SCP-001。宣言 row に Mutation が無い関数の本体で再代入すると落ちる。
;; P1c2a が入れた undeclared-function-effect の検査がそのまま働くことを固定する。
;; callables の綴りは tests/typing-test.rkt:11-17 の callable-types に倣う。
(define callable-types
  '((loop-id (NFn (Int) Int () ()))
    (mut-loop-id (NFn (Int) Int (Mutation) ()))))

(define (key-of core)
  (match (type-of/raw core '() callable-types '() (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

;; 本体で再代入するが loop-id の宣言 row は空である。
(check-equal?
 (key-of (term (Recur loop-id loop (x)
                      (Let (m mut Int) x
                           (Let (u const Unit) (Reassign m 2) m))
                      (Apply loop 1))))
 'undeclared-function-effect)

;; 宣言 row に Mutation があれば同じ本体が通る。
(check-equal?
 (key-of (term (Recur mut-loop-id loop (x)
                      (Let (m mut Int) x
                           (Let (u const Unit) (Reassign m 2) m))
                      (Apply loop 1))))
 'ok)

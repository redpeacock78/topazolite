#lang racket

(require rackunit
         redex/reduction-semantics
         "../pr-lang.rkt"
         "../pr-machine.rkt")

(define fuel 10000)

;; 目標項を注入して走らせ、終端の config の計算部分を返す。
;; inject-pr が包む一番外の空 scope は、値へ到達したときだけ剥がす。R-PR-ScopeValue
;; は Task 10 で入るので、それまで終端は (PScopeExit () pv) の形で止まる。ここで
;; 剥がしておけば Task 8 から Task 11 まで同じ期待値の書き方で通せる。値でない項が
;; 残った場合は包みごと返し、stuck した形をそのまま見せる。
(define (eval-pr core)
  (match (run-pr (inject-pr core) fuel)
    ['timeout 'timeout]
    [`(pcfg (PScopeExit () ,result) ,_ ,_ ,_)
     #:when (redex-match? PR pv result)
     result]
    [`(pcfg ,result ,_ ,_ ,_) result]))

(test-case
 "δpr implements the shim semantics of spec §9"
 (check-equal? (term (δpr tz:add 2 3)) 5)
 (check-equal? (term (δpr tz:sub 2 3)) -1)
 (check-equal? (term (δpr tz:mul 2 3)) 6)
 (check-equal? (term (δpr tz:lt 2 3)) (term (PTagged k:true)))
 (check-equal? (term (δpr tz:lt 3 2)) (term (PTagged k:false)))
 (check-equal? (term (δpr tz:le 3 3)) (term (PTagged k:true)))
 (check-equal? (term (δpr tz:eq 3 3)) (term (PTagged k:true)))
 (check-equal? (term (δpr tz:eq 3 4)) (term (PTagged k:false)))
 (check-equal? (term (δpr tz:acquire 7)) (term (PResource 7))))

(test-case
 "δpr is undefined outside the table"
 (check-equal? (term (δpr tz:add 1)) (term undefined))
 (check-equal? (term (δpr tz:add 1 2 3)) (term undefined))
 (check-equal? (term (δpr tz:add 1 unit)) (term undefined))
 (check-equal? (term (δpr tz:unknown 1 2)) (term undefined))
 (check-equal? (term (δpr tz:acquire unit)) (term undefined)))

(test-case
 "R-PR-Prim reduces a shim call to its value"
 (check-equal? (eval-pr (term (PPrim tz:add 2 3))) 5)
 (check-equal? (eval-pr (term (PPrim tz:acquire 7)))
               (term (PResource 7))))

(test-case
 "an undefined shim call is stuck, not an exception"
 (check-equal? (eval-pr (term (PPrim tz:add 1 unit)))
               (term (PScopeExit () (PPrim tz:add 1 unit)))))

(test-case
 "inject-pr wraps the term in an empty scope"
 (check-equal? (inject-pr (term 1)) (term (pcfg (PScopeExit () 1) () () ())))
 (check-exn exn:fail:contract?
            (lambda () (inject-pr (term (Apply 1 2))))))

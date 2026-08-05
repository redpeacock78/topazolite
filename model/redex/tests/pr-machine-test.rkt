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

(test-case
 "R-PR-App substitutes the closure environment and the arguments"
 (check-equal? (eval-pr (term (PApp (PClosure () (a) a) 5))) 5)
 ;; penv の束縛も同時に代入する。
 (check-equal?
  (eval-pr (term (PApp (PClosure ((e 7)) (a) (PPrim tz:add e a)) 5)))
  12)
 ;; penv を持つ closure を引数へ渡しても、その鍵を捕獲しない。
 (check-true
  (alpha-equivalent?
   PR
   (term (PClosure ((e 7)) (a) e))
   (eval-pr
    (term (PApp (PClosure () (x) x)
                (PClosure ((e 7)) (a) e))))))
 ;; arity 不一致は stuck する。
 (check-equal? (eval-pr (term (PApp (PClosure () (a) a) 1 2)))
               (term (PScopeExit () (PApp (PClosure () (a) a) 1 2)))))

(test-case
 "R-PR-Curry extends the environment instead of building an intermediate value"
 (check-true
  (alpha-equivalent?
   PR
   (term (PClosure ((a 4)) (b) (PPrim tz:add a b)))
   (eval-pr (term (PRuntime curry (PClosure () (a b) (PPrim tz:add a b)) 4)))))
 ;; 引数を取らない closure への curry は stuck する。
 (check-equal?
  (eval-pr (term (PRuntime curry (PClosure () () 1) 4)))
  (term (PScopeExit () (PRuntime curry (PClosure () () 1) 4)))))

(test-case
 "R-PR-Let substitutes without consulting a type"
 (check-equal? (eval-pr (term (PLet a 3 (PPrim tz:add a a)))) 6))

(test-case
 "R-PR-Letrec builds a self-applying closure"
 ;; 呼び出し 1 回が R-PR-App と R-PR-Letrec の 2 歩になる。
 (check-equal?
  (eval-pr (term (PLetrec f (PLam (a) a) (PApp f 9))))
  9)
 ;; 本当に再帰する例。f が 0 に達するまで自分を呼ぶ。閉包の本体が自分自身へ
 ;; 戻るだけの形になっていると、この検査は timeout を返して落ちる。
 (check-equal?
  (eval-pr
   (term (PLetrec f
                  (PLam (n)
                        (PMatch (PPrim tz:eq n 0)
                                ((k:true () -> 0)
                                 (k:false ()
                                  -> (PPrim tz:add
                                            n
                                            (PApp f (PPrim tz:sub n 1)))))))
                  (PApp f 3))))
  6))

(test-case
 "R-PR-Match selects the branch by tag"
 (check-equal?
  (eval-pr (term (PMatch (PTagged some 4)
                         ((none () -> 0) (some (a) -> a)))))
  4)
 ;; 枝が無ければ stuck する。
 (check-equal?
  (eval-pr (term (PMatch (PTagged other 4) ((none () -> 0)))))
  (term (PScopeExit () (PMatch (PTagged other 4) ((none () -> 0)))))))

(test-case
 "R-PR-Proj requires unique labels"
 (check-equal? (eval-pr (term (PProj (PRec ((f 1) (g 2))) g))) 2)
 (check-equal?
  (eval-pr (term (PProj (PRec ((f 1) (f 2))) f)))
  (term (PScopeExit () (PProj (PRec ((f 1) (f 2))) f))))
 (check-equal?
  (eval-pr (term (PProj (PRec ((f 1))) g)))
  (term (PScopeExit () (PProj (PRec ((f 1))) g)))))

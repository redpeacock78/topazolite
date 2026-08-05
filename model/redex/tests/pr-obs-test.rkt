#lang racket

(require rackunit
         redex/reduction-semantics
         "../pr-lang.rkt"
         "../pr-obs.rkt")

(define depth 5)
(define fuel 10000)

(define pop-a (term (return b:alpha ty:Int)))

(test-case
 "obs-eval-pr returns the observation list and the terminal kind"
 (check-equal? (obs-eval-pr (term 7) depth fuel) (list '() 'value))
 (check-equal?
  (obs-eval-pr (term (PRuntime yield 1 (PRuntime yield 2 3))) depth fuel)
  (list '(1 2) 'value)))

(test-case
 "the terminal kinds carry the same names as obs.rkt"
 (check-equal? (terminal-kind-pr (term 7)) 'value)
 (check-equal? (terminal-kind-pr (term (PError 0))) 'ownership-error)
 (check-equal? (terminal-kind-pr (term (PEffect ,pop-a 1))) 'perform)
 (check-equal? (terminal-kind-pr (term (PApp 1 2))) 'stuck))

(test-case
 "obs-eval-pr reports each terminal kind end to end"
 (check-equal?
  (obs-eval-pr
   (term (PLetOwned a 5 (PLet b (PRuntime move a) (PRuntime move a))))
   depth fuel)
  (list '() 'ownership-error))
 (check-equal? (obs-eval-pr (term (PEffect ,pop-a 1)) depth fuel)
               (list '() 'perform))
 (check-equal? (obs-eval-pr (term (PPrim tz:add 1 unit)) depth fuel)
               (list '() 'stuck)))

(test-case
 "obs-eval-pr stops as soon as the observation depth is reached"
 (check-equal?
  (obs-eval-pr (term (PRuntime yield 1 (PRuntime yield 2 3))) 1 fuel)
  (list '(1) 'observed))
 (check-equal?
  (obs-eval-pr (term (PRuntime yield 1 (PRuntime yield 2 3))) 2 fuel)
  (list '(1 2) 'observed)))

(test-case
 "obs-eval-pr reports timeout instead of looping"
 (check-equal?
  (obs-eval-pr (term (PLetrec f (PLam (a) (PApp f a)) (PApp f 1))) depth 20)
  (list '() 'timeout)))

(test-case
 "obs-eval-pr rejects a negative depth or fuel"
 (check-exn exn:fail:contract?
            (lambda () (obs-eval-pr (term 7) -1 fuel)))
 (check-exn exn:fail:contract?
            (lambda () (obs-eval-pr (term 7) depth -1))))

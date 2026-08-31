#lang racket

(require rackunit
         redex/reduction-semantics
         "../machine.rkt"
         "../obs.rkt")

(define fuel 50)
(define acquire (term (PrimVal (Reserved o-acquire) acquire)))

(test-case "REC-002: yield produces the requested observation prefix"
  (define core (term (Yield 1 (Yield 2 unit))))
  (check-equal? (obs-eval core 0 fuel) '(() observed))
  (check-equal? (obs-eval core 1 fuel) '((1) observed))
  (check-equal? (obs-eval core 2 fuel) '((1 2) observed))
  (check-equal? (obs-eval core 3 fuel) '((1 2) value))
  (check-equal?
   (run (inject core) fuel)
   (term (cfg unit () () () ((obs 1) (obs 2))))))

(test-case "REC-002: Suspend consumes a step without producing an observation"
  (check-equal?
   (obs-eval (term (Suspend (Yield 1 unit))) 1 fuel)
   '((1) observed))
  (check-equal?
   (obs-eval (term (Suspend unit)) 1 fuel)
   '(() value))
  (check-equal?
   (run (inject (term (Suspend unit))) fuel)
   (term (cfg unit () () () ()))))

(test-case "OWN-002/REC-002: fin events are not observations"
  (check-equal?
   (obs-eval
    (term (Let (r (Owned Res))
               (Apply ,acquire 7)
               (Yield 1 unit)))
    2
    fuel)
   '((1) value))
  (define fin-before-observation
    (term (Let (ignored Unit)
               (Scope ()
                      (Let (r (Owned Res))
                           (Apply ,acquire 8)
                           unit))
               (Yield 1 unit))))
  (check-equal?
   (obs-eval fin-before-observation 1 fuel)
   '((1) observed))
  (check-equal?
   (run (inject fin-before-observation) fuel)
   (term (cfg unit
              ((0 (resource 8)))
              ((0 Dropped))
              () ((fin 0) (obs 1))))))

(test-case "obs-eval: terminal outcomes and fuel exhaustion"
  (check-equal? (obs-eval (term 5) 1 fuel) '(() value))
  (check-equal?
   (obs-eval (term (Perform (Return boundary Int) 9)) 1 fuel)
   '(() perform))
  (check-equal?
   (obs-eval
    (term (Let (r (Owned Res))
               (Apply ,acquire 0)
               (Let (used Res) (Move r) (Move r))))
    1
    fuel)
   '(() ownership-error))
  (check-equal? (obs-eval (term (Apply 1 2)) 1 fuel) '(() stuck))
  (check-equal? (obs-eval (term (Suspend unit)) 1 0) '(() timeout)))

(test-case "obs-eval: bounds must be nonnegative integers"
  (check-exn exn:fail:contract?
             (λ () (obs-eval (term unit) -1 fuel)))
  (check-exn exn:fail:contract?
             (λ () (obs-eval (term unit) 1 -1))))

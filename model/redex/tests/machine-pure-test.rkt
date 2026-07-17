#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../origins.rkt")

(define fuel 20)

(define (final-config core)
  (term (cfg ,core () () ())))

(define (scoped core)
  (term (cfg (Scope () ,core) () () ())))

(define (run-core core)
  (match (run (inject core) fuel)
    [`(cfg ,result () () ()) result]
    [result (error 'run-core "unexpected result: ~e" result)]))

(test-case "R-Delta: primitive delta rules reduce applications"
  (for ([case (in-list
               (list (list (term (Apply (PrimVal (Reserved o-add) add) 7 3))
                           (term 10))
                     (list (term (Apply (PrimVal (Reserved o-sub) sub) 7 3))
                           (term 4))
                     (list (term (Apply (PrimVal (Reserved o-mul) mul) 7 3))
                           (term 21))
                     (list (term (Apply (PrimVal (Reserved o-lt) lt) 1 2))
                           (term (Construct true)))
                     (list (term (Apply (PrimVal (Reserved o-le) le) 2 1))
                           (term (Construct false)))
                     (list (term (Apply (PrimVal (Reserved o-eq) eq) 2 2))
                           (term (Construct true)))
                     (list (term (Apply (PrimVal (Reserved o-acquire) acquire)
                                        9))
                           (term (resource 9)))))])
    (match-define (list core expected) case)
    (check-equal? (run (inject core) fuel) (final-config expected))))

(test-case "R-Beta/R-Let: capture-avoiding substitution"
  (check-equal?
   (run (inject (term (Apply (Lam User (x) x) 5))) fuel)
   (final-config (term 5)))
  (check-equal?
   (run-core
    (term (Let (x Int) 3
               (Apply (PrimVal (Reserved o-add) add) x 4))))
   (term 7))

  (define result
    (run-core
     (term (Apply (Lam User (x)
                         (Lam User (y) (Apply x y)))
                  (Lam User (z) y)))))
  (check-true
   (alpha-equivalent?
    G1
    result
    (term (Lam User (fresh)
               (Apply (Lam User (z) y) fresh))))))

(test-case "CUR-001/CUR-002: curry records provenance and completes application"
  (define curried
    (run-core
     (term (Curry (PrimVal (Reserved o-lt) lt) 1))))
  (check-equal?
   curried
   (term (CurryVal (Derived (Reserved o-lt) (Curry 1))
                   (PrimVal (Reserved o-lt) lt)
                   1)))
  (check-equal? (term (origin-of ,curried))
                (term (Derived (Reserved o-lt) (Curry 1))))
  (check-equal?
   (run-core
    (term (Apply (Curry (PrimVal (Reserved o-lt) lt) 1) 2)))
   (term (Construct true))))

(test-case "R-Eliminate: constructor branch selection and field binding"
  (check-equal?
   (run-core
    (term (Eliminate (Construct nil)
                     ((nil () -> 41)
                      (cons (head tail) -> 0)))))
   (term 41))
  (check-equal?
   (run-core
    (term (Eliminate (Construct nil)
                     ((nil () -> 1)
                      (nil () -> 2)))))
   (term 1))
  (check-equal?
   (run-core
    (term (Eliminate (Construct cons 3 (Construct nil))
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Apply (PrimVal (Reserved o-add) add)
                                   head
                                   4))))))
   (term 7)))

(test-case "run: timeout only when another step remains"
  (define reducible
    (inject (term (Apply (Lam User (x) x) 5))))
  (check-equal? (run reducible 0) 'timeout)
  (check-equal? (run (scoped (term 5)) 0) 'timeout)
  (check-equal? (run (final-config (term 5)) 0)
                (final-config (term 5))))

(test-case "pure reduction: malformed redexes remain stuck"
  (define (successors core)
    (apply-reduction-relation -->g1
                              (term (cfg ,core () () ()))))
  (for ([core
         (in-list
          (term ((Apply (Lam User (x) x) 1 2)
                 (Apply (Lam User (x x) x) 3 5)
                 (Apply (Lam User (x) x) (RecurVal f (f) f))
                 (Apply (PrimVal (Reserved o-add) add) 1)
                 (Curry 1 2)
                 (Let (x (Owned Res)) (resource 1) x)
                 (Eliminate (Construct nil)
                            ((cons (head tail) -> head)))
                 (Eliminate (Construct cons 1 (Construct nil))
                            ((cons (head) -> head)))
                 (Eliminate (Construct cons 3 5)
                            ((cons (head head) -> head))))))])
    (check-equal? (successors core) '())))

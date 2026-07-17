#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt")

(define fuel 50)
(define acquire (term (PrimVal (Reserved o-acquire) acquire)))

(test-case "OWN-001: move succeeds once and reuse raises OwnershipError"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 0)
                (Move r))))
    fuel)
   (term (cfg (resource 0)
              ((0 (resource 0)))
              ((0 Moved))
              ())))
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 0)
                (Let (used Res) (Move r) (Move r)))))
    fuel)
   (term (cfg (Error 0)
              ((0 (resource 0)))
              ((0 Moved))
              ())))
  (check-equal?
   (run
    (term (cfg (Move 0)
               ((0 (resource 0)))
               ((0 Dropped))
               ()))
    fuel)
   (term (cfg (Error 0)
              ((0 (resource 0)))
              ((0 Dropped))
              ()))))

(test-case "R-Drop: evaluated values become unit"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 0)
                (Drop (Move r)))))
    fuel)
   (term (cfg unit
              ((0 (resource 0)))
              ((0 Moved))
              ()))))

(test-case "R-LetOwned: deterministic allocation targets the nearest Scope"
  (define source
    (term (cfg
           (Scope ()
                  (Scope ()
                         (Handle (Return b Int)
                                 (answer -> answer)
                                 (Let (r (Owned Res))
                                      (resource 9)
                                      (Move r)))))
           ((0 (resource 0)) (3 (resource 3)))
           ((0 Moved) (3 Moved))
           ())))
  (define expected
    (term (cfg
           (Scope ()
                  (Scope (4)
                         (Handle (Return b Int)
                                 (answer -> answer)
                                 (Move 4))))
           ((0 (resource 0)) (3 (resource 3)) (4 (resource 9)))
           ((0 Moved) (3 Moved) (4 Available))
           ())))
  (match (apply-reduction-relation -->g1 source)
    [(list actual) (check-true (alpha-equivalent? G1m actual expected))]
    [actual (fail-check (format "expected one successor, got ~e" actual))]))

(test-case "OWN-002: scope finalizes available places once in reverse order"
  (check-equal?
   (run
    (inject
     (term (Let (first (Owned Res))
                (Apply ,acquire 10)
                (Let (second (Owned Res))
                     (Apply ,acquire 20)
                     unit))))
    fuel)
   (term (cfg unit
              ((0 (resource 10)) (1 (resource 20)))
              ((0 Dropped) (1 Dropped))
              ((fin 1) (fin 0)))))
  (check-equal?
   (run
    (term (cfg (Scope (0 0) unit)
               ((0 (resource 1)))
               ((0 Available))
               ()))
    fuel)
   (term (cfg unit
              ((0 (resource 1)))
              ((0 Dropped))
              ((fin 0))))))

(test-case "OWN-003: abort and error exits finalize remaining places"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 7)
                (Perform (Return boundary Int) 42))))
    fuel)
   (term (cfg (Perform (Return boundary Int) 42)
              ((0 (resource 7)))
              ((0 Dropped))
              ((fin 0)))))
  (check-equal?
   (run
    (term (cfg (Scope (0)
                      (Scope (1)
                             (Perform (Return boundary Int) 42)))
               ((0 (resource 0)) (1 (resource 1)))
               ((0 Available) (1 Available))
               ()))
    fuel)
   (term (cfg (Perform (Return boundary Int) 42)
              ((0 (resource 0)) (1 (resource 1)))
              ((0 Dropped) (1 Dropped))
              ((fin 1) (fin 0)))))
  (check-equal?
   (run
    (inject
     (term (Let (first (Owned Res))
                (Apply ,acquire 10)
                (Let (second (Owned Res))
                     (Apply ,acquire 20)
                     (Let (used Res)
                          (Move second)
                          (Move second))))))
    fuel)
   (term (cfg (Error 1)
              ((0 (resource 10)) (1 (resource 20)))
              ((0 Dropped) (1 Moved))
              ((fin 0))))))

(test-case "R-HandleError: ownership errors bypass handlers"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 5)
                (Handle (Return boundary Int)
                        (answer -> answer)
                        (Let (used Res)
                             (Move r)
                             (Move r))))))
    fuel)
   (term (cfg (Error 0)
              ((0 (resource 5)))
              ((0 Moved))
              ()))))

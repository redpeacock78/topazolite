#lang racket

(require rackunit
         redex/reduction-semantics
         "../machine.rkt")

(define fuel 50)
(define acquire (term (PrimVal (Reserved o-acquire) acquire)))

(test-case "R-HandleValue: values pass through handlers"
  (check-equal?
   (run
    (inject
     (term (Handle (Return boundary Int)
                   (answer -> 0)
                   7)))
    fuel)
   (term (cfg 7 () () () ()))))

(test-case "RET-002/OWN-003: matching Return handles after scope cleanup"
  (check-equal?
   (run
    (inject
     (term (Handle (Return boundary Int)
                   (answer -> answer)
                   (Scope ()
                          (Let (r (Owned Res))
                               (Apply ,acquire 7)
                               (Perform (Return boundary Int) 42))))))
    fuel)
   (term (cfg 42
              ((0 (resource 7)))
              ((0 Dropped))
              () ((fin 0))))))

(test-case "RET-002: matching Return discards its pure continuation"
  (check-equal?
   (run
    (inject
     (term (Handle (Return boundary Int)
                   (answer -> answer)
                   (Let (ignored Int)
                        (Perform (Return boundary Int) 42)
                        99))))
    fuel)
   (term (cfg 42 () () () ()))))

(test-case "R-HandleSkip: boundary or type mismatch propagates"
  (for ([case
         (in-list
          (list
           (list (term (Return outer Int))
                 (term (Return inner Int)))
           (list (term (Return boundary Bool))
                 (term (Return boundary Int)))))])
    (match-define (list handled performed) case)
    (check-equal?
     (run
      (inject
       (term (Handle ,handled
                     (answer -> 0)
                     (Perform ,performed 7))))
      fuel)
     (term (cfg (Perform ,performed 7) () () () ()))))
  (check-equal?
   (run
    (inject
     (term (Handle (Return outer Int)
                   (answer -> 0)
                   (Let (ignored Int)
                        (Perform (Return inner Int) 7)
                        99))))
    fuel)
   (term (cfg (Perform (Return inner Int) 7) () () () ()))))

(test-case "RET-002: nested handlers select the matching boundary"
  (check-equal?
   (run
    (inject
     (term (Handle (Return outer Int)
                   (outer-answer -> outer-answer)
                   (Handle (Return inner Int)
                           (inner-answer ->
                                         (Apply (PrimVal (Reserved o-add) add)
                                                inner-answer
                                                1))
                           (Perform (Return outer Int) 41)))))
    fuel)
   (term (cfg 41 () () () ())))
  (check-equal?
   (run
    (inject
     (term (Handle (Return outer Int)
                   (outer-answer -> outer-answer)
                   (Handle (Return inner Int)
                           (inner-answer ->
                                         (Apply (PrimVal (Reserved o-add) add)
                                                inner-answer
                                                1))
                           (Perform (Return inner Int) 41)))))
    fuel)
   (term (cfg 42 () () () ()))))

(test-case "top-level Perform: an unhandled Return is terminal"
  (check-equal?
   (run
    (inject (term (Perform (Return boundary Int) 9)))
    fuel)
   (term (cfg (Perform (Return boundary Int) 9) () () () ()))))

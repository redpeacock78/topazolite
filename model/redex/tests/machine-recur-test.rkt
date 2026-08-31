#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../obs.rkt")

(define fuel 100)
(define add (term (PrimVal (Reserved o-add) add)))

(test-case "R-RecurBind: callable ID is preserved"
  (match (run (inject (term (Recur saved-id f (x) x f))) fuel)
    [`(cfg ,result () () () ())
     (check-true
      (alpha-equivalent?
       G1 result (term (RecurVal saved-id f (x) x))))]
    [result (fail (format "unexpected result: ~e" result))]))

(test-case "REC-001: structural recur reaches a value"
  (define length-two
    (term
     (Recur walk-id walk (xs)
            (Eliminate xs
                       ((nil () -> 0)
                        (cons (head tail) ->
                              (Apply ,add 1 (Apply walk tail)))))
            (Apply walk
                   (Construct (List Int) cons 10
                              (Construct (List Int) cons 20
                                         (Construct (List Int) nil)))))))
  (check-equal?
   (run (inject length-two) fuel)
   (term (cfg 2 () () () ()))))

(test-case "REC-002: guarded recur produces every requested observation"
  (define productive
    (term (Recur loop-id loop ()
                 (Yield 1 (Apply loop))
                 (Apply loop))))
  (check-equal? (obs-eval productive 3 fuel)
                '((1 1 1) observed)))

(test-case "recur reduction: malformed binders and arity remain stuck"
  (define (successors core)
    (apply-reduction-relation
     -->g1
     (term (cfg ,core () () () ()))))
  (check-equal?
   (successors
    (term (Apply (RecurVal arity-id f (x) x) 1 2)))
   '())
  (check-equal?
   (successors
    (term (Recur duplicate-id f (f) f (Apply f 1))))
   '()))

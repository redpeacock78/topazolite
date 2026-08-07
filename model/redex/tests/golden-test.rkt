#lang racket

(require racket/match
         rackunit
         redex/reduction-semantics
         "../classify.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt")

(define fuel 10000)

(define (find-recur tree)
  (match tree
    [`(Recur ,_ ,_ ,_ ,_ ,_) tree]
    [(? list? parts)
     (for/or ([part (in-list parts)])
       (find-recur part))]
    [_ #f]))

(define (check-golden source expected-type environment expected-value)
  (match (elab source)
    [(list raw-core type row callables)
     (define core (erase-core raw-core))
     (check-equal? type expected-type)
     (check-equal? row '())
     (check-equal? (term (verify-origins ,R0 ,core)) 'ok)
     (define recur
       (or (find-recur core)
           (fail "elaboration produced no Recur term")))
     (check-equal? (classify recur environment callables)
                   '(Finite structural))
     (check-equal? (run (inject core) fuel)
                   `(cfg ,expected-value () () ()))]
    [result (fail (format "elaboration failed: ~e" result))]))

(define find-positive
  '(Apply
    (Fn ((values (List Int))) (Result Int Unit) ()
        (NarrativeExpr
         (Recur loop ((rest (List Int))) (Result Int Unit) (Return)
                (Eliminate
                 rest
                 ((nil () -> (Construct ng unit))
                  (cons
                   (head tail)
                   ->
                   (Eliminate
                    (Apply lt 0 head)
                    ((true () -> (Return (Construct ok head)))
                     (false () -> (Apply loop tail)))))))
                (Apply loop values))))
    (Construct cons (Types Int)
               -1
               (Construct cons (Types Int)
                          2
                          (Construct nil (Types Int))))))

(define doubled
  '(Apply
    (Fn ((f (NFn (Int) Int () ()))
         (values (List Int)))
        (List Int) ()
        (Recur go ((rest (List Int))) (List Int) ()
               (Eliminate
                rest
                ((nil () -> (Construct nil))
                 (cons
                  (h t)
                  ->
                  (Construct cons (Apply f h) (Apply go t)))))
               (Apply go values)))
    (Curry mul 2)
    (Construct cons (Types Int)
               -1
               (Construct cons (Types Int)
                          2
                          (Construct nil (Types Int))))))

(test-case "RET-002/REC-001: findPositive golden program"
  (check-golden
   find-positive
   '(Result Int Unit)
   '((values (List Int)))
   '(Construct (Result Int Unit) ok 2)))

(test-case "CUR-001/CUR-002/REC-001/NAR-001/NAR-002: map golden program"
  (check-golden
   doubled
   '(List Int)
   '((f (NFn (Int) Int () ()))
     (values (List Int)))
   '(Construct (List Int) cons -2
               (Construct (List Int) cons 4
                          (Construct (List Int) nil))))

  (match-define (list raw-curry-core _ _ _) (elab '(Curry mul 2)))
  (define curry-core (erase-core raw-curry-core))
  (match-define `(cfg ,curried () () ())
    (run (inject curry-core) fuel))
  (check-equal?
   (term (origin-of ,curried))
   '(Derived (Reserved o-mul) (Curry 2)))
  (check-equal? (term (verify-origins ,R0 ,curried)) 'ok))

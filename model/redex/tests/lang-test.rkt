#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt")

(test-case "NAR-001/CUR-002/TYP-001/PRF-001: Typed Core values"
  (for ([value (in-list
                (term ((PrimVal (Reserved o-lt) lt)
                       (TypeRep User Int Type)
                       (ProofRep User ValidNarrativeTrait)
                       (resource 0)
                       (Lam User lam-id (x) x)
                       (CurryVal User 1 2)
                       (RecurVal recur-id f (x) x))))])
    (check-true (redex-match? G1 v value))))

(test-case "RET-002/REC-001/OWN-001: Typed Core terms"
  (for ([core (in-list
               (term ((Apply 1 2)
                      (Let (x Int) 1 x)
                      (Eliminate (Construct (Option Int) some 1)
                                 ((some (x) -> x)))
                      (Move x)
                      (Drop 1)
                      (Yield 1 2)
                      (Suspend 1)
                      (Perform (Return b Int) 1)
                      (Handle (Return b Int) (x -> x) 1)
                      (Scope () 1)
                      (Recur recur-id f (x) x (Apply f 0))
                      (Construct (List Int) cons 1 2))))])
    (check-true (redex-match? G1 c core)))
  (check-true (redex-match? G1m c (term (Scope (0) (Move 0)))))
  (check-true (redex-match? G1m c (term (Error 0)))))

(test-case "RET-002/OWN-002: machine state and context layers"
  (check-true
   (redex-match? G1m config
                 (term (cfg (Scope (0) (Move 0))
                            ((0 (resource 7)))
                            ((0 Available))
                            () ((obs 1) (fin 0))))))
  (check-true (redex-match? G1m F (term (Apply 1 hole 2))))
  (check-true
   (redex-match? G1m E
                 (term (Apply 1 (Scope () hole) 2))))
  (check-true
   (redex-match? G1m G
                 (term (Apply 1
                              (Handle (Return b Int) (x -> x) hole)
                              2))))
  (check-false (redex-match? G1m F (term (Scope () hole))))
  (check-false (redex-match? G1m G (term (Scope () hole)))))

(test-case "EFF-001: Effect rows are duplicate-free sets"
  (check-true (term (row-⊆ () (Own))))
  (check-false (term (row-⊆ (Partial) ())))
  (check-true (term (row-∈ Own (Own Partial))))
  (check-equal? (term (row-∪ (Own) (Partial Own Compile)))
                (term (Own Partial Compile)))
  (check-equal? (term (row-\\ (Own Partial Compile) (Partial)))
                (term (Own Compile))))

(test-case "G2f: step は policy 派生と合成派生を受理する"
  (check-true
   (redex-match? G2m O
                 (term (Derived (Reserved o-language-narrative)
                                (Policy TraitResolution)))))
  (check-true
   (redex-match? G2m O
                 (term (Derived (Reserved o-intersect-print-size)
                                (Compose PrintableSizable
                                         (Reserved o-impl-printable-int)
                                         (Reserved o-derive-sizable-int))))))
  ;; 成分が origin でない形は受理しない。
  (check-false
   (redex-match? G2m O
                 (term (Derived (Reserved o-intersect-print-size)
                                (Compose PrintableSizable))))))

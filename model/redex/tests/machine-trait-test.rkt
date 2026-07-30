#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt")

(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) 20)
    [`(cfg ,result () () ()) result]
    [result (error 'run-g2-core "unexpected result: ~e" result)]))

(define (stuck-g2? core)
  (null? (apply-reduction-relation -->g2 (inject-g2 core))))

(define (trait-primitive name origin)
  `(PrimVal (Reserved ,origin) ,name))

(test-case "an impl primitive produces an Implements proof"
  (check-equal?
   (run-g2-core
    `(Apply ,(trait-primitive 'impl-printable-int
                              'o-impl-printable-int)
            (Rec ())))
   '(ProofRep (Reserved o-impl-printable-int)
              (Implements Int Printable))))

(test-case "a derive primitive follows the same delta rule"
  (check-equal?
   (run-g2-core
    `(Apply ,(trait-primitive 'derive-sizable-int
                              'o-derive-sizable-int)
            (Rec ())))
   '(ProofRep (Reserved o-derive-sizable-int)
              (Implements Int Sizable))))

(test-case "an intersect primitive composes two proofs"
  (check-equal?
   (run-g2-core
    `(Apply
      ,(trait-primitive 'intersect-printable-sizable
                        'o-intersect-print-size)
      (ProofRep (Reserved o-trait-printable)
                (ValidNarrativeTrait Printable))
      (ProofRep (Reserved o-trait-sizable)
                (ValidNarrativeTrait Sizable))))
   '(ProofRep (Reserved o-intersect-print-size)
              (RequiresBoth Printable Sizable))))

(test-case "g2-primitive-name? covers trait but not base primitives"
  (check-true (g2-primitive-name? 'impl-printable-int))
  (check-true (g2-primitive-name? 'derive-sizable-int))
  (check-true (g2-primitive-name? 'intersect-printable-sizable))
  (check-false (g2-primitive-name? 'add)))

(test-case "existing base primitives still reduce"
  (check-equal?
   (run-g2-core
    '(Apply (PrimVal (Reserved o-add) add) 1 2))
   3))

(test-case "an arity mismatch leaves the application stuck"
  (define impl-applied-twice
    `(Apply ,(trait-primitive 'impl-printable-int
                              'o-impl-printable-int)
            (Rec ())
            (Rec ())))
  (check-true (stuck-g2? impl-applied-twice))
  (define intersect-applied-once
    `(Apply ,(trait-primitive 'intersect-printable-sizable
                              'o-intersect-print-size)
            (ProofRep (Reserved o-trait-printable)
                      (ValidNarrativeTrait Printable))))
  (check-true (stuck-g2? intersect-applied-once)))

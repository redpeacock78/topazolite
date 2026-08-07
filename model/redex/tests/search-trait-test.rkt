#lang racket/base

(require rackunit
         "../origins.rkt"
         "../search.rkt"
         "../traits.rkt")

(define (goal proposition) (make-goal proposition))
(define (sigma proposition [sc-ctx '(root)])
  (project-goal Γ-pc0 sc-ctx (goal proposition)))

(test-case "initial context contains the trait global candidates"
  (define context (initial-candidate-context))
  (for ([row (in-list impl-table)])
    (check-true (and (assq (impl-name row) context) #t)
                (format "~s" (impl-name row)))))

(test-case "Γ-pc0 is the initial candidate context"
  (check-equal? Γ-pc0 (initial-candidate-context)))

(test-case "hook-ok? binds a candidate to its trait and impl rows"
  (define kernel
    '(Candidate
      (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
      typeNarrativeCap root default ()))
  (define valid
    '(Candidate
      (ProofRep (Reserved o-impl-printable-int)
                (Implements Int Printable))
      impl-printable-int root default
      (o-trait-printable o-impl-printable-int)))
  (check-true (hook-ok? kernel))
  (check-true (hook-ok? valid))
  (check-false
   (hook-ok?
    '(Candidate
      (ProofRep (Reserved o-impl-printable-int)
                (Implements Int Printable))
      impl-printable-int root default ())))
  (check-false
   (hook-ok?
    '(Candidate
      (ProofRep (Reserved o-impl-printable-int)
                (Implements Int Printable))
      impl-printable-int root default
      (o-trait-sizable o-impl-printable-int))))
  (check-false
   (hook-ok?
    '(Candidate
      (ProofRep (Reserved o-impl-printable-int)
                (Implements Int Printable))
      impl-printable-int root default
      (o-trait-printable o-impl-printable-str-a))))
  (check-false
   (hook-ok?
    '(Candidate
      (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
      typeNarrativeCap root default
      (o-trait-printable o-impl-printable-int)))))

(test-case "candidate identity includes the hook"
  (define base
    '(Candidate
      (ProofRep (Reserved o-impl-printable-int)
                (Implements Int Printable))
      impl-printable-int root default
      (o-trait-printable o-impl-printable-int)))
  (define changed
    '(Candidate
      (ProofRep (Reserved o-impl-printable-int)
                (Implements Int Printable))
      impl-printable-int root default
      (o-trait-sizable o-impl-printable-int)))
  (check-not-equal? (candidate-identity base)
                    (candidate-identity changed)))

(test-case "a unique impl and a derive row resolve"
  (check-equal?
   (resolve-candidates (goal '(Implements Int Printable))
                       (sigma '(Implements Int Printable)))
   (resolved
    '(ProofRep (#:span #:synthetic 0 0)
               (Reserved o-impl-printable-int)
               (Implements Int Printable))))
  (check-equal?
   (resolve-candidates (goal '(Implements Int Sizable))
                       (sigma '(Implements Int Sizable)))
   (resolved
    '(ProofRep (#:span #:synthetic 0 0)
               (Reserved o-derive-sizable-int)
               (Implements Int Sizable)))))

(test-case "duplicate impls are ambiguous"
  (define result
    (resolve-candidates (goal '(Implements String Printable))
                        (sigma '(Implements String Printable))))
  (check-true (ambiguous? result))
  (check-equal? (length (ambiguous-proofs result)) 2))

(test-case "coherence filters by target scope"
  (check-equal? (sigma '(Implements Bool Taggable)) '())
  (check-equal? (length (sigma '(Implements Bool Taggable)
                               '(root s-user)))
                1)
  (check-false
   (discharge? Γ-pc0 default-classifier default-oracle
               (goal '(Implements Bool Taggable))
               '(root)))
  (check-true
   (discharge? Γ-pc0 default-classifier default-oracle
               (goal '(Implements Bool Taggable))
               '(root s-user))))

(test-case "resolution is independent of input order"
  (define proposition '(Implements String Printable))
  (define candidates (sigma proposition))
  (check-equal?
   (resolve-candidates (goal proposition) candidates)
   (resolve-candidates (goal proposition) (reverse candidates))))

(test-case "equivalent raw propositions choose one deterministic candidate"
  (define normalized
    '(Implements (Record ((a Int imm) (z Int imm))) Printable))
  (define permuted
    '(Implements (Record ((z Int imm) (a Int imm))) Printable))
  (define candidate-a
    `(Candidate (ProofRep (Reserved o-test) ,normalized)
                test root default ()))
  (define candidate-z
    `(Candidate (ProofRep (Reserved o-test) ,permuted)
                test root default ()))
  (define expected
    (resolved `(ProofRep (Reserved o-test) ,normalized)))
  (check-equal?
   (resolve-candidates (goal normalized) (list candidate-a candidate-z))
   expected)
  (check-equal?
   (resolve-candidates (goal normalized) (list candidate-z candidate-a))
   expected))

(test-case "project and candidate wf use canonical proposition equality"
  (define normalized
    '(FieldType a (Record ((a Int imm) (z Int imm)))))
  (define context
    '((field-type
       ((FieldType a (Record ((z Int imm) (a Int imm))))
        (Reserved o-merge) field-type root default ()))))
  (define candidates (project-goal context '(root) (goal normalized)))
  (check-equal? (length candidates) 1)
  (check-true (wf-candidate? (car candidates) (goal normalized))))

(test-case "trait proposition shapes are finite"
  (for ([proposition
         (in-list
          '((Implements Int Printable)
            (ValidNarrativeTrait Printable)
            (RequiresBoth Printable Sizable)
            (FieldType a Int)))])
    (check-eq? (default-classifier (goal proposition) Γ-pc0)
               'Finite
               (format "~s" proposition))))

(test-case "unique impl obligations discharge and ambiguous ones do not"
  (check-true
   (obligations-dischargeable? '((Implements Int Printable)) Γ-pc0))
  (check-false
   (obligations-dischargeable? '((Implements String Printable)) Γ-pc0))
  ;; production の入口は root 固定である。
  (check-false
   (obligations-dischargeable? '((Implements Bool Taggable)) Γ-pc0)))

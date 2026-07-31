#lang racket/base

(require rackunit
         racket/list
         redex/reduction-semantics
         "../origins.rkt"
         "../traits.rkt")

(define (trait-constant-name row)
  (string->symbol (format "~a-trait" (trait-name row))))

(define (verify-initial core)
  (term (verify-initial-origins ,R0 ,core)))

(test-case "the trait tables contribute R0 entries"
  (for ([row (in-list trait-table)])
    (check-equal? (assoc (trait-origin row) R0)
                  (list (trait-origin row)
                        (list 'trait (trait-name row)))))
  (for ([row (in-list impl-table)])
    (check-equal? (assoc (impl-oid row) R0)
                  (list (impl-oid row)
                        (list 'prim (impl-name row)))))
  (for ([row (in-list intersect-table)])
    (check-equal? (assoc (intersect-oid row) R0)
                  (list (intersect-oid row)
                        (list 'prim (intersect-name row))))))

(test-case "the trait tables contribute Γ0 entries"
  (for ([row (in-list impl-table)])
    (define trait-row (trait-row-by-name (impl-trait-name row)))
    (define requirements
      (instantiate-requirements
       (trait-template trait-row)
       (impl-target-type row)))
    (check-equal?
     (assoc (impl-name row) Γ0)
     (list (impl-name row)
           (list `(NFn ((Record ,requirements))
                       (Proof (Implements ,(impl-target-type row)
                                          ,(impl-trait-name row)))
                       () ())
                 `(PrimVal (Reserved ,(impl-oid row)) ,(impl-name row))))))
  (for ([row (in-list intersect-table)])
    (check-equal?
     (assoc (intersect-name row) Γ0)
     (list (intersect-name row)
           (list `(NFn ((Proof (ValidNarrativeTrait ,(intersect-left row)))
                        (Proof (ValidNarrativeTrait ,(intersect-right row))))
                       (Proof (RequiresBoth ,(intersect-left row)
                                            ,(intersect-right row)))
                       () ())
                 `(PrimVal (Reserved ,(intersect-oid row))
                           ,(intersect-name row)))))))

(test-case "R0 and Γ0 keys stay unique after appending trait rows"
  (check-equal? (length (map car R0))
                (length (remove-duplicates (map car R0))))
  (check-equal? (length (map car Γ0))
                (length (remove-duplicates (map car Γ0)))))

(test-case "Γ0 holds the sole source of trait validity proofs"
  (for ([row (in-list trait-table)])
    (define name (trait-constant-name row))
    (define proposition `(ValidNarrativeTrait ,(trait-name row)))
    (check-equal?
     (assoc name Γ0)
     (list name
           (list `(Proof ,proposition)
                 `(ProofRep (Reserved ,(trait-origin row)) ,proposition)))
     (format "~s" (trait-name row)))))

(test-case "proof-issuer-ok? accepts trait-table issuers"
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-trait-printable)
                     '(ValidNarrativeTrait Printable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-impl-printable-int)
                     '(Implements Int Printable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-derive-sizable-int)
                     '(Implements Int Sizable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-intersect-print-size)
                     '(RequiresBoth Printable Sizable))))

(test-case "proof-issuer-ok? rejects mismatched trait issuers"
  (check-false
   (proof-issuer-ok? R0 '(Reserved o-impl-taggable-bool)
                     '(Implements Int Printable)))
  (check-false
   (proof-issuer-ok? R0 '(Reserved o-impl-printable-int)
                     '(Implements Bool Printable)))
  (check-false
   (proof-issuer-ok? R0 '(Reserved o-trait-printable)
                     '(ValidNarrativeTrait Sizable))))

(test-case "proof-issuer-ok? compares trait propositions canonically"
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-impl-printable-int)
                     '(Implements (Union Int Int) Printable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-intersect-print-size)
                     '(RequiresBoth Sizable Printable))))

(test-case "FieldType is local-only"
  (define witness
    '(ProofRep (Reserved o-merge) (FieldType f Int)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-merge) '(FieldType f Int)))
  (check-equal? (verify-initial witness) `(forged ,witness)))

(test-case "trait-global-bindings derives one entry per impl row and intersect row"
  (define bindings (trait-global-bindings))
  (check-equal? (length bindings)
                (+ (length impl-table) (length intersect-table)))
  (for ([row (in-list impl-table)])
    (define trait-row (trait-row-by-name (impl-trait-name row)))
    (check-equal?
     (assoc (impl-name row) bindings)
     (list (impl-name row)
           (list `(Implements ,(impl-target-type row)
                              ,(impl-trait-name row))
                 `(Reserved ,(impl-oid row))
                 (impl-name row)
                 'root
                 'default
                 (list (trait-origin trait-row) (impl-oid row))))))
  ;; TRT-005: intersect 行は RequiresBoth 候補を供給する。
  (for ([row (in-list intersect-table)])
    (check-equal?
     (assoc (intersect-name row) bindings)
     (list (intersect-name row)
           (list `(RequiresBoth ,(intersect-left row)
                                ,(intersect-right row))
                 `(Reserved ,(intersect-oid row))
                 (intersect-name row)
                 'root
                 'default
                 (list (intersect-oid row)))))))

(test-case "trait-derived Γ0 values pass initial origin verification"
  (define names
    (append (map trait-constant-name trait-table)
            (map impl-name impl-table)
            (map intersect-name intersect-table)))
  (for ([name (in-list names)])
    (define value (second (second (assoc name Γ0))))
    (check-equal? (verify-initial value) 'ok (format "~s" name))))

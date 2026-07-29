#lang racket/base
(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../validators.rkt")

(test-case "Union and Intersection are G2 types"
  (check-true (redex-match? G2 τ (term (Union Int String))))
  (check-true (redex-match? G2 τ (term (Intersection (Record ()) (Record ())))))
  (check-true (redex-match? G2m τ (term (Union Int String))))
  (check-true (redex-match? G2m τ (term (Intersection (Record ()) (Record ()))))))

(test-case "trait propositions are G2 propositions"
  (check-true (redex-match? G2 φ (term (ValidNarrativeTrait Printable))))
  (check-true (redex-match? G2 φ (term (Implements Int Printable))))
  (check-true (redex-match? G2 φ (term (RequiresBoth Printable Sizable))))
  (check-true (redex-match? G2 φ (term (FieldType f Int))))
  (check-true (redex-match? G2m φ (term (Implements Int Printable)))))

(test-case "owned-free? recurses through Union and Intersection"
  (check-false (owned-free? (term (Union Int (Owned Int)))))
  (check-false (owned-free? (term (Intersection Int (Owned Int)))))
  (check-true (owned-free? (term (Union Int String)))))

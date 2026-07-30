#lang racket/base

(require racket/list
         rackunit
         "../search.rkt")

(define taggable-goal (make-goal '(Implements Bool Taggable)))
(define ambiguous-goal
  (make-goal '(Implements String Printable)))

(define (discharge-in goal sc-ctx)
  (discharge? Γ-pc0
              default-classifier
              default-oracle
              goal
              sc-ctx))

(test-case "a non-root impl is invisible from the root scope"
  (check-equal? (project-goal Γ-pc0 '(root) taggable-goal) '())
  (check-false (discharge-in taggable-goal '(root))))

(test-case "a non-root impl becomes visible in its lineage"
  (define candidates
    (project-goal Γ-pc0 '(root s-user) taggable-goal))
  (check-equal? (length candidates) 1)
  (check-true (wf-Σ? candidates taggable-goal '(root s-user)))
  (check-true (discharge-in taggable-goal '(root s-user))))

(test-case "scope widening does not resolve duplicate global impls"
  (define candidates
    (project-goal Γ-pc0 '(root s-user) ambiguous-goal))
  (check-equal? (length candidates) 2)
  (check-equal? (length (remove-duplicates
                         (map candidate-hook candidates)))
                2)
  (check-equal? (length (remove-duplicates
                         (map candidate-identity candidates)))
                2)
  (check-equal? (resolve-candidates ambiguous-goal candidates)
                (resolve-candidates ambiguous-goal
                                    (reverse candidates)))
  (check-false (discharge-in ambiguous-goal '(root s-user))))

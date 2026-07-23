#lang racket
(require rackunit "../typing.rkt" "../search.rkt")

;; TypeNarrativeCap 義務を持つ NFn への Apply は、Γ_pc⁰ の候補で discharge され受理される。
(define callables
  '((cap-id (NFn (Int) Int () (TypeNarrativeCap)))))
(reset-search-log!)
(check-equal?
 (core-type-of '(Apply (Lam User cap-id (x) x) 1) '() callables)
 '(Int ()))
(check-true (hash-ref (search-log-snapshot) 'finite-resolved-accept #f))

;; Π0 に候補が無い ValidNarrativeTrait 義務は充足できず ill-typed。
(define callables-v
  '((trait-id (NFn (Int) Int () (ValidNarrativeTrait)))))
(reset-search-log!)
(check-equal?
 (core-type-of '(Apply (Lam User trait-id (x) x) 1) '() callables-v)
 'ill-typed)
(check-true (hash-ref (search-log-snapshot) 'finite-absent-reject #f))

;; 義務列が空の Apply は従来どおり受理される（回帰）。
(define callables-0
  '((plain-id (NFn (Int) Int () ()))))
(reset-search-log!)
(check-equal?
 (core-type-of '(Apply (Lam User plain-id (x) x) 1) '() callables-0)
 '(Int ()))
(check-equal? (hash-count (search-log-snapshot)) 0)

#lang racket
(require rackunit "../search.rkt")

(define P '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))

; Goal descriptor
(check-equal? (make-goal 'TypeNarrativeCap) '(Goal TypeNarrativeCap ⊥ext))
(check-true  (goal? (make-goal 'TypeNarrativeCap)))
(check-false (goal? '(Foo)))
(check-equal? (goal-proposition (make-goal 'ValidNarrativeTrait)) 'ValidNarrativeTrait)

; SearchResult コンストラクタと述語
(check-equal? (resolved P) (list 'Resolved P))
(check-equal? Absent 'Absent)
(check-equal? (ambiguous (list P P)) (list 'Ambiguous (list P P)))
(check-true (search-result? (resolved P)))
(check-true (search-result? Absent))
(check-true (search-result? (ambiguous (list P))))
(check-false (search-result? '(Nope)))

; アクセサ
(check-true  (resolved? (resolved P)))
(check-false (resolved? Absent))
(check-true  (absent? Absent))
(check-true  (ambiguous? (ambiguous (list P))))
(check-equal? (resolved-proof (resolved P)) P)
(check-equal? (ambiguous-proofs (ambiguous (list P P))) (list P P))

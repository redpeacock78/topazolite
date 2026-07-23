#lang racket
(require rackunit "../search.rkt")
(require "../origins.rkt")

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

; candidateize は Π0 の各束縛から entry を一つ作る。
; Π0 = ((typeNarrativeCap (TypeNarrativeCap (Reserved o-type-narrative))))
(check-equal?
 (candidateize Π0)
 '((typeNarrativeCap
    (TypeNarrativeCap (Reserved o-type-narrative)
                      typeNarrativeCap root default ()))))

; 決定性: 同じ Π0 に対して同じ Γ_pc⁰ を与える（gensym/counter を使わない）
(check-equal? (candidateize Π0) (candidateize Π0))
(check-equal? Γ-pc0 (candidateize Π0))

; entry アクセサ
(define e (second (first Γ-pc0)))
(check-equal? (entry-phi e) 'TypeNarrativeCap)
(check-equal? (entry-origin e) '(Reserved o-type-narrative))
(check-equal? (entry-cid e) 'typeNarrativeCap)
(check-equal? (entry-sid e) 'root)
(check-equal? (entry-pid e) 'default)
(check-equal? (entry-hook e) '())

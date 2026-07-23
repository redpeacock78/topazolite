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

; project: root scope から可視な entry を候補へ写す
(check-equal?
 (project Γ-pc0 '(root))
 '((Candidate (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
              typeNarrativeCap root default ())))

; 可視でない scope の entry は候補にしない
(check-equal? (project Γ-pc0 '(other)) '())

; 候補アクセサ
(define c (first (project Γ-pc0 '(root))))
(check-equal? (candidate-proof c) '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(check-equal? (candidate-prop c) 'TypeNarrativeCap)
(check-equal? (candidate-origin c) '(Reserved o-type-narrative))
(check-equal? (candidate-cid c) 'typeNarrativeCap)
(check-equal? (candidate-identity c)
              '(TypeNarrativeCap (Reserved o-type-narrative) typeNarrativeCap root default))

; wf-candidate: 命題整合・origin 正当・scope 可視・hook 空
(define goalT (make-goal 'TypeNarrativeCap))
(check-true (wf-candidate? c goalT))
; 命題が食い違う候補は wf でない
(check-false (wf-candidate? c (make-goal 'ValidNarrativeTrait)))
; forge した origin（verify-origins を通らない）は wf でない
(define forged
  '(Candidate (ProofRep (Reserved o-bogus) TypeNarrativeCap) x root default ()))
(check-false (wf-candidate? forged goalT))

; wf-Σ: project の返す候補環境は wf
(check-true (wf-Σ? (project Γ-pc0 '(root)) goalT))
(check-false (wf-Σ? (list forged) goalT))

(define PT '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define cT '(Candidate (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
                       typeNarrativeCap root default ()))
; provenance と cid の異なる第二候補
(define cT2 '(Candidate (ProofRep (Reserved o-type-narrative-b) TypeNarrativeCap)
                        other root default ()))
(define PT2 '(ProofRep (Reserved o-type-narrative-b) TypeNarrativeCap))

; 0 候補 → Absent
(check-equal? (resolve-candidates goalT '()) 'Absent)
; 1 候補 → Resolved
(check-equal? (resolve-candidates goalT (list cT)) (list 'Resolved PT))
; 命題が一致しない候補は集めない
(check-equal? (resolve-candidates (make-goal 'ValidNarrativeTrait) (list cT)) 'Absent)
; 同一性の等しい重複候補は一つへ畳む → Resolved
(check-equal? (resolve-candidates goalT (list cT cT)) (list 'Resolved PT))
; 同一性の異なる複数候補 → Ambiguous、canonical order（cid: other < typeNarrativeCap）
(check-equal? (resolve-candidates goalT (list cT cT2)) (list 'Ambiguous (list PT2 PT)))
; 順序非依存: 並べ替えても同じ SR
(check-equal? (resolve-candidates goalT (list cT2 cT)) (list 'Ambiguous (list PT2 PT)))

(define goalV (make-goal 'ValidNarrativeTrait))

; χ fixture: goal → class
(define chi (make-classifier (list (cons goalT 'Finite) (cons goalV 'Unknown))))
(check-equal? (chi goalT Γ-pc0) 'Finite)
(check-equal? (chi goalV Γ-pc0) 'Unknown)
; 既定 χ: G1 の 2 命題を Finite に写す（SR とは独立に class を定める）
(check-equal? (default-classifier goalT Γ-pc0) 'Finite)
(check-equal? (default-classifier goalV Γ-pc0) 'Finite)

; Ω fixture と certificate
(define cert (make-cert goalT Γ-pc0 PT))
(define omega (make-oracle (list (cons goalT (list (list 'Resolved PT) cert)))))
(check-equal? (omega goalT Γ-pc0) (list (list 'Resolved PT) cert))
(check-false (omega goalV Γ-pc0))
(check-false (default-oracle goalT Γ-pc0))

; cert-valid: 同じ goal・Γ_pc・P に束縛されたときだけ有効
(check-true  (cert-valid? cert goalT Γ-pc0 PT))
(check-false (cert-valid? cert goalV Γ-pc0 PT))          ; 別 goal の流用は不可
(check-false (cert-valid? cert goalT Γ-pc0 '(ProofRep (Reserved o-x) TypeNarrativeCap)))

; unique?: 完全な Σ から (Resolved P) が出れば一意性導出
(define sigmaT (project Γ-pc0 '(root)))
(check-true  (unique? goalT sigmaT PT))
(check-false (unique? goalT '() PT))

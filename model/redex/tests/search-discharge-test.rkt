#lang racket
(require rackunit "../search.rkt" "../origins.rkt")

(define PT '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define goalT (make-goal 'TypeNarrativeCap))
(define goalV (make-goal 'ValidNarrativeTrait))

; Finite/Resolved/unique → 充足
(check-true (discharge? Γ-pc0 default-classifier default-oracle goalT))
; ValidNarrativeTrait は候補が無く Absent → 却下（class は既定 χ で Finite でも SR が Absent）
(check-false (discharge? Γ-pc0 default-classifier default-oracle goalV))

; Unknown は SR によらず却下（PSR-003）
(define chiU (make-classifier (list (cons goalT 'Unknown))))
(check-false (discharge? Γ-pc0 chiU default-oracle goalT))

; Productive: Ω の certificate があれば充足
(define certT (make-cert goalT Γ-pc0 PT))
(define chiP (make-classifier (list (cons goalT 'Productive))))
(define omegaP (make-oracle (list (cons goalT (list (list 'Resolved PT) certT)))))
(check-true (discharge? Γ-pc0 chiP omegaP goalT))
; Productive だが Ω が探索結果を返さない → 却下
(check-false (discharge? Γ-pc0 chiP default-oracle goalT))

; 探索起動の記録: 各 class の枝と採否が記録される
(reset-search-log!)
(discharge? Γ-pc0 default-classifier default-oracle goalT)   ; Finite / Resolved / accept
(discharge? Γ-pc0 default-classifier default-oracle goalV)   ; Finite / Absent / reject
(discharge? Γ-pc0 chiU default-oracle goalT)                 ; Unknown / reject
(define snap (search-log-snapshot))
(check-true (hash-ref snap 'finite-resolved-accept #f))
(check-true (hash-ref snap 'finite-absent-reject #f))
(check-true (hash-ref snap 'unknown-reject #f))

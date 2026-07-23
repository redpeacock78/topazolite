#lang racket
(require rackunit "../search.rkt" "../origins.rkt")

(define PT '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define PT2 '(ProofRep (Reserved o-type-narrative-b) TypeNarrativeCap))
(define goalT (make-goal 'TypeNarrativeCap))
(define sigmaT (project Γ-pc0 '(root)))       ; 完全な Σ、Resolved PT を導く
(define certT (make-cert goalT Γ-pc0 PT))

;; --- Finite ---
; (Finite, Resolved P): 完全な Σ からの一意性導出があり P が一致 → 採択
(check-true  (admissible? goalT Γ-pc0 'Finite (resolved PT) sigmaT))
; 一意性導出はあるが SR の P が Σ 由来の P と食い違う → 却下
(check-false (admissible? goalT Γ-pc0 'Finite (resolved PT2) sigmaT))
; 完全でない Σ（空）では一意性導出が無い → 却下
(check-false (admissible? goalT Γ-pc0 'Finite (resolved PT) '()))
; 一意性証拠が無い → 却下
(check-false (admissible? goalT Γ-pc0 'Finite (resolved PT) #f))
; (Finite, Absent) → 却下
(check-false (admissible? goalT Γ-pc0 'Finite Absent sigmaT))
; (Finite, Ambiguous) → 却下
(check-false (admissible? goalT Γ-pc0 'Finite (ambiguous (list PT PT2)) sigmaT))

;; --- Productive ---
; (Productive, Resolved P): cert が同じ goal・Γ_pc・P に束縛 → 採択
(check-true  (admissible? goalT Γ-pc0 'Productive (resolved PT) certT))
; 別 P の証拠を流用 → 却下
(check-false (admissible? goalT Γ-pc0 'Productive (resolved PT2) certT))
; 別 goal の証拠を流用 → 却下
(check-false (admissible? (make-goal 'ValidNarrativeTrait) Γ-pc0 'Productive (resolved PT) certT))
; certificate が無い → 却下
(check-false (admissible? goalT Γ-pc0 'Productive (resolved PT) #f))
; (Productive, Absent) / (Productive, Ambiguous) → 却下
(check-false (admissible? goalT Γ-pc0 'Productive Absent certT))
(check-false (admissible? goalT Γ-pc0 'Productive (ambiguous (list PT PT2)) certT))

;; --- Unknown ---
; (Unknown, _): どの SearchResult でも却下（PSR-003）
(check-false (admissible? goalT Γ-pc0 'Unknown (resolved PT) sigmaT))
(check-false (admissible? goalT Γ-pc0 'Unknown Absent #f))
(check-false (admissible? goalT Γ-pc0 'Unknown (ambiguous (list PT)) #f))

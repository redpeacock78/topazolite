#lang racket

(require racket/match "origins.rkt")

(provide make-goal goal? goal-proposition
         resolved Absent ambiguous
         search-result? resolved? absent? ambiguous?
         resolved-proof ambiguous-proofs
         candidateize Γ-pc0
         entry-phi entry-origin entry-cid entry-sid entry-pid entry-hook)

;; Goal descriptor: (Goal φ ⊥ext)。⊥ext は型・Effect・lexical 特殊化の拡張点で G2b は空。
(define (make-goal phi) (list 'Goal phi '⊥ext))
(define (goal? x)
  (match x [(list 'Goal _ '⊥ext) #t] [_ #f]))
(define (goal-proposition g) (second g))

;; SearchResult: (Resolved P) | Absent | (Ambiguous (P ...))
(define (resolved P) (list 'Resolved P))
(define Absent 'Absent)
(define (ambiguous ps) (list 'Ambiguous ps))

(define (resolved? sr)  (match sr [(list 'Resolved _) #t] [_ #f]))
(define (absent? sr)    (eq? sr 'Absent))
(define (ambiguous? sr) (match sr [(list 'Ambiguous _) #t] [_ #f]))
(define (search-result? sr) (or (resolved? sr) (absent? sr) (ambiguous? sr)))

(define (resolved-proof sr) (second sr))
(define (ambiguous-proofs sr) (second sr))

;; candidateize: 固定の Π0 を初期候補文脈 Γ_pc⁰ へ変換する。
;; Π0 の各束縛 (name (φ O)) から entry (φ O cid sid pid hook) を作る。
;; cid は name 由来の安定な候補識別子、sid は root scope、pid は既定値。
;; いずれも Π0 から決定的に定め、gensym や counter で採番しない。
(define (candidateize pi0)
  (for/list ([binding (in-list pi0)])
    (match-define (list name (list phi origin)) binding)
    (list name (list phi origin name 'root 'default '()))))

(define Γ-pc0 (candidateize Π0))

;; entry = (φ O cid sid pid hook)
(define (entry-phi e)    (first e))
(define (entry-origin e) (second e))
(define (entry-cid e)    (third e))
(define (entry-sid e)    (fourth e))
(define (entry-pid e)    (fifth e))
(define (entry-hook e)   (sixth e))

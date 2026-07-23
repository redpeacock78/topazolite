#lang racket

(require racket/match
         redex/reduction-semantics
         "origins.rkt")

(provide make-goal goal? goal-proposition
         resolved Absent ambiguous
         search-result? resolved? absent? ambiguous?
         resolved-proof ambiguous-proofs
         candidateize Γ-pc0
         entry-phi entry-origin entry-cid entry-sid entry-pid entry-hook
         project scope-visible?
         candidate-proof candidate-prop candidate-origin
         candidate-cid candidate-sid candidate-pid candidate-identity
         wf-candidate? wf-Σ?)

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

;; project: scope 文脈 sc-ctx から可視な entry だけを候補へ写す。
(define (project gamma-pc sc-ctx)
  (for/list ([binding (in-list gamma-pc)]
             #:when (scope-visible? (entry-sid (second binding)) sc-ctx))
    (define e (second binding))
    (list 'Candidate
          (list 'ProofRep (entry-origin e) (entry-phi e))
          (entry-cid e) (entry-sid e) (entry-pid e) (entry-hook e))))

(define (scope-visible? sid sc-ctx) (and (member sid sc-ctx) #t))

;; cand = (Candidate (ProofRep O φ) cid sid pid hook)
(define (candidate-proof c)  (second c))
(define (candidate-prop c)   (third (candidate-proof c)))
(define (candidate-origin c) (second (candidate-proof c)))
(define (candidate-cid c)    (third c))
(define (candidate-sid c)    (fourth c))
(define (candidate-pid c)    (fifth c))
(define (candidate-hook c)   (sixth c))

;; 候補同一性: requirement shape・provenance・cid・sid・pid。trait 成分 hook は空のため除く。
(define (candidate-identity c)
  (list (candidate-prop c) (candidate-origin c)
        (candidate-cid c) (candidate-sid c) (candidate-pid c)))

;; wf-candidate: 一つの候補が整合であること。
(define (wf-candidate? c goal)
  (and (equal? (candidate-prop c) (goal-proposition goal))
       (origin-ok? (candidate-origin c) (candidate-prop c))
       (scope-visible? (candidate-sid c) '(root))
       (null? (candidate-hook c))))

;; verify-origins を単一 ProofRep に対して通す。
(define (origin-ok? O phi)
  (eq? (term (verify-origins ,R0 (ProofRep ,O ,phi))) 'ok))

;; wf-Σ: すべての候補が wf-candidate を満たす。Finite 完全性は project が構成上保証する。
(define (wf-Σ? sigma goal)
  (andmap (lambda (c) (wf-candidate? c goal)) sigma))

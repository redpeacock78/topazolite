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
         wf-candidate? wf-Σ?
         resolve-candidates
         make-classifier make-oracle make-cert cert-valid? unique?
         default-classifier default-oracle
         admissible?
         discharge? current-search-log search-log-snapshot reset-search-log!)

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

;; resolve-candidates: Finite closed-world の候補解決。全域で、wf-Σ を前提とする。
(define (resolve-candidates goal sigma)
  (define phi (goal-proposition goal))
  ;; goal の命題に shape が一致する候補を集める
  (define matched
    (filter (lambda (c) (equal? (candidate-prop c) phi)) sigma))
  ;; 候補同一性で重複排除（同一性の組が等しい候補だけ一つへ畳む）
  (define deduped (remove-duplicates matched #:key candidate-identity))
  ;; cid の canonical order で並べる（順序非依存）
  (define sorted
    (sort deduped symbol<?
          #:key (lambda (c) (candidate-cid c))))
  (cond [(null? sorted) Absent]
        [(null? (cdr sorted)) (resolved (candidate-proof (car sorted)))]
        [else (ambiguous (map candidate-proof sorted))]))

;; χ: goal と候補文脈から計算クラスへの trusted な写像。SR を参照しない。
;; goal を key に引くため、同値な goal（equal?）は同じ class を得る。
(define (make-classifier table)
  (lambda (goal gamma-pc)
    (cond [(assoc goal table) => cdr]
          [else 'Unknown])))

;; 既定 χ: G1 の 2 命題を Finite に写す。class は SR と独立に φ で定まる。
(define default-classifier
  (make-classifier
   (list (cons (make-goal 'TypeNarrativeCap) 'Finite)
         (cons (make-goal 'ValidNarrativeTrait) 'Finite))))

;; Ω: Productive 探索の結果と certificate を返す trusted な写像。無ければ #f。
(define (make-oracle table)
  (lambda (goal gamma-pc)
    (cond [(assoc goal table) => cdr]
          [else #f])))

;; 既定 Ω: Productive 候補を持たない。
(define default-oracle (make-oracle '()))

;; 一意性 certificate: goal・Γ_pc・候補 P・計算クラスに束縛された証拠。
(define (make-cert goal gamma-pc P) (list 'Cert goal gamma-pc P 'Productive))
(define (cert-valid? cert goal gamma-pc P)
  (equal? cert (list 'Cert goal gamma-pc P 'Productive)))

;; Finite の一意性: 完全な Σ に対して resolve が (Resolved P) を返すことが導出。
(define (unique? goal sigma P)
  (equal? (resolve-candidates goal sigma) (resolved P)))

;; admissible?: 暗黙充足の可否。SR が (Resolved P) の枝だけで真になりうる。
;; ev は現在の探索に束縛された証拠（Finite: 完全な Σ、Productive: certificate）。
(define (admissible? goal gamma-pc class sr ev)
  (match* (class sr)
    [('Finite (list 'Resolved P))
     ;; 完全な Σ からの一意性導出があり、その P が SR の P と一致（PSR-002）。
     ;; unique? が resolve の (Resolved P) 一致を含むため、P の照合はこれで足りる。
     (and ev (unique? goal ev P))]
    [('Productive (list 'Resolved P))
     ;; Ω の certificate が同じ goal・Γ_pc・P に束縛（PSR-002）
     (and ev (cert-valid? ev goal gamma-pc P))]
    [('Unknown _) #f]
    [(_ 'Absent) #f]
    [(_ (list 'Ambiguous _)) #f]
    [(_ _) #f]))

;; 探索起動の記録: 空虚な合格の防止。どの class・SR 枝と採否を通したかを覚える。
(define current-search-log (make-parameter (make-hash)))
(define (reset-search-log!) (current-search-log (make-hash)))
(define (search-log-snapshot) (hash-copy (current-search-log)))
(define (log-branch! key) (hash-set! (current-search-log) key #t))

(define (log-outcome! class sr accepted?)
  (define tag
    (if (eq? class 'Unknown)
        'unknown-reject
        (string->symbol
         (format "~a-~a-~a"
                 (string-downcase (symbol->string class))
                 (cond [(resolved? sr) 'resolved]
                       [(absent? sr) 'absent]
                       [else 'ambiguous])
                 (if accepted? 'accept 'reject)))))
  (log-branch! tag))

;; discharge?: 義務充足の judgment。χ で class を得て、class に応じて SR と証拠を得る。
(define (discharge? gamma-pc chi omega goal [sc-ctx '(root)])
  (define class (chi goal gamma-pc))
  (define-values (sr ev)
    (case class
      [(Finite)
       (define sigma (project gamma-pc sc-ctx))
       (values (resolve-candidates goal sigma) sigma)]
      [(Productive)
       (match (omega goal gamma-pc)
         [(list sr cert) (values sr cert)]
         [_ (values Absent #f)])]
      [else (values Absent #f)]))
  (define accepted? (admissible? goal gamma-pc class sr ev))
  (log-outcome! class sr accepted?)
  accepted?)

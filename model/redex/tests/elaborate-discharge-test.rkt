#lang racket

(require racket/match
         rackunit
         redex/reduction-semantics
         "../elaborate.rkt"
         "../lang.rkt"
         "../origins.rkt"
         "../typing.rkt"
         "properties-test.rkt")

;; elaborate-test.rkt の success は redex-match? G1 c で成功を検査する。
;; Discharge は G2 の項形式なので、この層の成功検査は G2 で行う。
(define (elaborated source)
  (match (elab source)
    [(and result (list _ _ _ _)) result]
    [other (fail-check (format "elaboration failed: ~s" other))]))

;; 成果物のどこに Discharge が現れるかは Lam と Handle の入れ子に依存する。
;; 連なりだけを取り出し、φ の順序を成果物の形から独立に観測する。
(define (find-discharge term)
  (match term
    [`(Discharge ,_ ,_) term]
    [(? list?) (ormap find-discharge term)]
    [_ #f]))

(define (discharge-proofs term)
  (let loop ([subject (find-discharge term)] [proofs '()])
    (match subject
      [`(Discharge ,proof ,inner) (loop inner (cons proof proofs))]
      [_ (reverse proofs)])))

(define (discharge-base term)
  (let loop ([subject (find-discharge term)])
    (match subject
      [`(Discharge ,_ ,inner) (loop inner)]
      [_ subject])))

(define PT '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define PP '(ProofRep (Reserved o-impl-printable-int)
                      (Implements Int Printable)))

(define one-source
  '(Fn ((f (NFn () Int () (TypeNarrativeCap)))) Int () (Apply f)))

;; 義務の並び順が成果物の入れ子順になることを見るため、2 件を別の命題にする。
;; どちらも Γ-pc⁰ から Resolved で解ける。
(define two-source
  '(Fn ((f (NFn () Int () (TypeNarrativeCap (Implements Int Printable)))))
       Int ()
       (Apply f)))

(test-case "PRF-004: 単一義務の Apply は選択した Proof で包まれる"
  (match-define (list core type _row callables) (elaborated one-source))
  (check-true (redex-match? G2 c core))
  (check-equal? (discharge-proofs core) (list PT))
  (match (discharge-base core)
    [`(Apply ,_ ...) (void)]
    [other (fail-check (format "Discharge の基底が Apply でない: ~s" other))])
  (check-equal? (core-type-of core '() callables) (list type '())))

(test-case "PRF-004: 義務列の順序が Discharge の入れ子順になる"
  (match-define (list core _type _row _callables) (elaborated two-source))
  (check-equal? (discharge-proofs core) (list PT PP)))

(test-case "PRF-004: 包まれた成果物は G1 の core ではない"
  ;; inject ではなく inject-g2 を使う根拠を固定する。
  (match-define (list core _type _row _callables) (elaborated one-source))
  (check-false (redex-match? G1 c core)))

(test-case "PRF-004: 搬送した ProofRep は初期成果物の検証を通る"
  (match-define (list core _type _row _callables) (elaborated one-source))
  (check-equal? (term (verify-initial-origins ,R0 ,core)) 'ok))

(test-case "PRF-004: 包んでも Progress と Preservation は保たれる"
  (check-true (preservation-g2? one-source))
  (check-true (progress-g2? one-source)))

(test-case "PRF-004: 充足できない義務は従来どおり拒否される"
  (check-equal?
   (elab '(Fn ((f (NFn () Int () (ValidNarrativeTrait)))) Int () (Apply f)))
   '(err (unsatisfied-proof-obligation (ValidNarrativeTrait)))))

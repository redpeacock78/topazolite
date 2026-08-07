#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../erase.rkt"
         "../typing.rkt")

(define cap-proof '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define printable-proof
  (erase-core
   (first (obligation-proofs '((Implements Int Printable)) Γ-pc0))))

(define (verify-initial core)
  (term (verify-initial-origins ,R0 ,core)))

;; ---- 構文 ----

(test-case "PRF-004: Discharge は G2 と G2m の c である"
  (define core `(Discharge ,cap-proof (Apply (Lam User cap-id (x) x) 1)))
  (check-true (redex-match? G2 c core))
  (check-true (redex-match? G2m c core)))

;; ---- 型付け ----

(define callables-1
  '((cap-id (NFn (Int) Int () (TypeNarrativeCap)))))
(define callables-2
  '((two-id (NFn (Int) Int ()
                 (TypeNarrativeCap (Implements Int Printable))))))

(test-case "PRF-004: φ 列が義務列と一致する連なりは型付く"
  (check-equal?
   (core-type-of `(Discharge ,cap-proof (Apply (Lam User cap-id (x) x) 1))
                 '() callables-1)
   '(Int ()))
  (check-equal?
   (core-type-of `(Discharge ,cap-proof
                    (Discharge ,printable-proof
                      (Apply (Lam User two-id (x) x) 1)))
                 '() callables-2)
   '(Int ())))

(test-case "PRF-004: 基底が Apply でない項を包むと型付かない"
  (check-equal?
   (core-type-of `(Discharge ,cap-proof 1) '() callables-1)
   'ill-typed))

(test-case "PRF-004: φ 列が義務列と一致しなければ型付かない"
  ;; 欠落
  (check-equal?
   (core-type-of `(Discharge ,cap-proof (Apply (Lam User two-id (x) x) 1))
                 '() callables-2)
   'ill-typed)
  ;; 余剰
  (check-equal?
   (core-type-of `(Discharge ,cap-proof
                    (Discharge ,printable-proof
                      (Apply (Lam User cap-id (x) x) 1)))
                 '() callables-1)
   'ill-typed)
  ;; 順序の入れ替え
  (check-equal?
   (core-type-of `(Discharge ,printable-proof
                    (Discharge ,cap-proof
                      (Apply (Lam User two-id (x) x) 1)))
                 '() callables-2)
   'ill-typed))

;; ---- 機械意味論 ----

(define (step-once core)
  (match (apply-reduction-relation -->g2 (inject-g2 core))
    [(list `(cfg (Scope () ,result) () () ())) result]
    [results (error 'step-once "unexpected: ~e" results)]))

(test-case "PRF-004: Discharge は 1 段で消え、内側は先に還元されない"
  (define inner '(Apply (Lam User f (x) x) 1))
  (define one `(Discharge ,cap-proof ,inner))
  (check-equal? (step-once one) inner)
  ;; 連なりは外側から一段ずつ消える。段数は連なりの長さと同じ。
  (define two `(Discharge ,cap-proof (Discharge ,printable-proof ,inner)))
  (check-equal? (step-once two) `(Discharge ,printable-proof ,inner))
  (check-equal? (step-once (step-once two)) inner))

;; ---- 検証層 ----

(test-case "PRF-004: 搬送された ProofRep は初期成果物で検証される"
  (check-equal?
   (verify-initial `(Discharge ,cap-proof (Apply (Lam User cap-id (x) x) 1)))
   'ok)
  ;; R0 に無い issuer は落ちる。
  (check-not-equal?
   (verify-initial
    `(Discharge (ProofRep (Reserved o-merge) TypeNarrativeCap)
                (Apply (Lam User cap-id (x) x) 1)))
   'ok))

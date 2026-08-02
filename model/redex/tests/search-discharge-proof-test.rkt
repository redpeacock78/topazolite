#lang racket/base

(require rackunit
         racket/list
         "../origins.rkt"
         "../search.rkt")

;; Productive 分類の goal に、指定した P を返す Ω を組む。
(define (productive-pair goal proof)
  (values (make-classifier (list (cons goal 'Productive)))
          (make-oracle
           (list (cons goal
                       (list (resolved proof)
                             (make-cert goal Γ-pc0 proof)))))))

(test-case "PRF-004: discharge/proof は投影せず 3 値を返す"
  (define goal (make-goal '(Implements Int Printable)))
  (define-values (accepted? class sr)
    (discharge/proof Γ-pc0 default-classifier default-oracle goal))
  (check-true accepted?)
  (check-equal? class 'Finite)
  (check-true (resolved? sr)))

(test-case "PRF-004: obligation-proofs は義務の並び順で Proof を返す"
  (define proofs
    (obligation-proofs '(TypeNarrativeCap (Implements Int Printable))
                       Γ-pc0))
  (check-equal? (length proofs) 2)
  (check-equal? (first proofs)
                '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
  ;; 2 件目の origin は探索が選んだ候補に依存するため、形と命題だけを固定する。
  (check-equal? (length (second proofs)) 3)
  (check-equal? (first (second proofs)) 'ProofRep)
  (check-equal? (third (second proofs)) '(Implements Int Printable)))

(test-case "PRF-004: 充足できない義務は #f になる"
  (check-equal? (obligation-proofs '(ValidNarrativeTrait) Γ-pc0)
                (list #f)))

;; ---- Productive の P を信用しない ----

(test-case "PRF-004: ProofRep の形でない P は搬送しない"
  (define goal (make-goal '(Implements Int Sizable)))
  (define-values (chi omega) (productive-pair goal 'bogus-proof))
  ;; 探索そのものは受理する。落とすのは搬送の入口である。
  (define-values (accepted? _class _sr)
    (discharge/proof Γ-pc0 chi omega goal))
  (check-true accepted?)
  (check-equal? (obligation-proofs '((Implements Int Sizable)) Γ-pc0 chi omega)
                (list #f)))

(test-case "PRF-004: 要求した φ と異なる命題の P は搬送しない"
  (define goal (make-goal '(Implements Int Sizable)))
  ;; issuer も出現許可も通るが、命題が食い違う。
  (define-values (chi omega)
    (productive-pair goal
                     '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap)))
  (define-values (accepted? _class _sr)
    (discharge/proof Γ-pc0 chi omega goal))
  (check-true accepted?)
  (check-equal? (obligation-proofs '((Implements Int Sizable)) Γ-pc0 chi omega)
                (list #f)))

(test-case "PRF-004: 正しい issuer を持つ局所 witness も搬送しない"
  (define goal (make-goal '(Presence a)))
  (define proof '(ProofRep (Reserved o-merge) (Presence a)))
  ;; proof-issuer-ok? は o-merge 由来として受理する。
  (check-true (proof-issuer-ok? R0 '(Reserved o-merge) '(Presence a)))
  ;; proof-occurrence-ok? が成果物への出現を禁じているため、入口で落ちる。
  (check-false (proof-occurrence-ok? '(Presence a)))
  (define-values (chi omega) (productive-pair goal proof))
  (define-values (accepted? _class _sr)
    (discharge/proof Γ-pc0 chi omega goal))
  (check-true accepted?)
  (check-equal? (obligation-proofs '((Presence a)) Γ-pc0 chi omega)
                (list #f)))

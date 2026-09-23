#lang racket

;; [REQ: PRF-005] 構造型 narrowing で余剰 field を drop する場合の
;; RemainderSafelyDropped Proof の構築と消費。

(require rackunit
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../lang.rkt"
         "../type-equiv.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../region.rkt"
         "../typing.rkt")

(define actual '(Record ((x (Owned Res) imm) (y Int imm))))
(define expected '(Record ((y Int imm))))

(define wide '(Record ((a (Owned Res) imm) (b Int imm))))
(define narrow '(Record ((b Int imm))))
(define phi `(RemainderSafelyDropped ,wide ,narrow))
(define proof `(ProofRep (Reserved o-narrow) ,phi))

;; 基底が φ の τ_actual より広く、余剰欄にも Owned がある組。
(define wider
  '(Record ((a (Owned Res) imm) (b Int imm) (c (Owned Res) imm))))

;; 入れ子の欄で Owned を失う対。kind は 'reject である。
(define reject-wide '(Record ((a (Record ((p (Owned Res) imm))) imm))))
(define reject-narrow '(Record ((a (Record ()) imm))))
(define reject-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,reject-wide ,reject-narrow)))

;; 余剰が Int だけの width narrowing。kind は 'ok である。
(define ok-wide '(Record ((a Int imm) (b Int imm))))
(define ok-narrow '(Record ((b Int imm))))
(define ok-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,ok-wide ,ok-narrow)))

;; 基底の型と一致しない narrowing の型対。Discharge の基底検査で拒む。
(define other-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,ok-wide ,narrow)))

;; 残余 drop 以外の義務。混在の検査に使う。
(define cap-proof '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))

(define narrowing-environment
  `((f (NFn (,narrow) ,narrow () () () User))
    (g (NFn (,reject-narrow) ,reject-narrow () () () User))
    (h (NFn (,ok-narrow) ,ok-narrow () () () User))
    (k (NFn (,ok-narrow) ,ok-narrow () () (TypeNarrativeCap) User))
    (s ,wide)
    (s-wider ,wider)
    (s-reject ,reject-wide)
    (s-ok ,ok-wide)))

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (type-of core [environment '()])
  (first (core-type-of core '() '() environment)))

(test-case
 "RemainderSafelyDropped は φ として言語に合う"
 (check-true
  (redex-match? G2 φ
                (list 'RemainderSafelyDropped actual expected))))

(test-case
 "両側の型を正規化してから比べる"
 ;; 同じ row を別の欄順で書いた 2 つの型は、正規化すると同じ鍵になる。
 (define reordered '(Record ((y Int imm) (x (Owned Res) imm))))
 (check-true
  (proposition-equiv? `(RemainderSafelyDropped ,actual ,expected)
                      `(RemainderSafelyDropped ,reordered ,expected))))

(test-case
 "発行者は Reserved o-narrow だけを認める"
 (define phi `(RemainderSafelyDropped ,actual ,expected))
 (check-true  (proof-issuer-ok? R0 '(Reserved o-narrow) phi))
 (check-false (proof-issuer-ok? R0 '(Reserved o-merge) phi)))

(test-case
 "探索の既定分類はこの命題を拾わない"
 ;; spec §4.3。既定節 [_ #f] が効くことを、明示の節を足さずに押さえる。
 (check-equal?
  (default-classifier
    (make-goal `(RemainderSafelyDropped ,actual ,expected))
    Γ-pc0)
  'Unknown))

(test-case
 "置き場所で出現の可否が入れ替わる"
 ;; spec §4.3。proof-occurrence-ok? は 2 つ目の引数で Discharge の proof 欄
 ;; を走っているかを受け取る。既定は #f であり、search.rkt の
 ;; transportable-proof はこの既定のまま呼ぶ。
 (define phi `(RemainderSafelyDropped ,actual ,expected))
 (check-false (proof-occurrence-ok? phi))
 (check-true  (proof-occurrence-ok? phi #t)))

(test-case
 "単独の ProofRep は forged になり、Discharge の中の同じ値は通る"
 ;; spec §4.3。verify-origins は項を一様に走るため、Discharge の proof 欄
 ;; だけを見分ける分岐が要る。この 2 件が同時に成り立つことを押さえる。
 ;; 後者は正当な Discharge を forged にしないことの回帰である。
 (define proof
   `(ProofRep (Reserved o-narrow)
              (RemainderSafelyDropped ,actual ,expected)))
 (check-equal? (term (verify-origins ,R0 ,proof))
               `(forged ,proof))
 (check-equal? (term (verify-origins ,R0 (Discharge ,proof 1)))
               'ok))

(test-case "Proof 無しの narrowing は owned-narrowing-needs-proof である"
  (check-equal? (key-of '(Apply f s) narrowing-environment)
                'owned-narrowing-needs-proof))

(test-case "基底が τ_actual より広く余剰に Owned があると通らない"
  (check-equal? (key-of `(Apply f (Discharge ,proof s-wider))
                        narrowing-environment)
                'owned-narrowing-needs-proof))

(test-case "Discharge で包むと通り、型は τ_expected である"
  (check-equal? (type-of `(Apply f (Discharge ,proof s))
                         narrowing-environment)
                narrow))

(test-case "'reject を返す narrowing は Discharge で包んでも通らない"
  (check-equal? (key-of `(Apply g (Discharge ,reject-proof s-reject))
                        narrowing-environment)
                'owned-narrowing-rejected))

(test-case "'ok を返す narrowing を包んでも通る"
  (check-equal? (type-of `(Apply h (Discharge ,ok-proof s-ok))
                         narrowing-environment)
                ok-narrow))

(test-case "φ の τ_actual が基底の型と一致しないと通らない"
  (check-equal? (key-of `(Apply f (Discharge ,other-proof s))
                        narrowing-environment)
                'type-mismatch))

(test-case "残余 drop と他の義務を重ねると discharge-mixed-obligation である"
  (check-equal? (key-of `(Apply k
                              (Discharge ,proof
                                         (Discharge ,cap-proof s-ok)))
                        narrowing-environment)
                'discharge-mixed-obligation))

(test-case "2 枚重ねると discharge-remainder-chain である"
  (check-equal? (key-of `(Apply f
                              (Discharge ,proof
                                         (Discharge ,proof s)))
                        narrowing-environment)
                'discharge-remainder-chain))

(test-case "origin が o-narrow 以外なら受理しない"
  (check-equal?
   (key-of `(Apply f
                    (Discharge (ProofRep (Reserved o-type-narrative) ,phi)
                               s))
            narrowing-environment)
   'discharge-proof-issuer))

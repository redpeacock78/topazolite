#lang racket

;; [REQ: PRF-005] 構造型 narrowing で余剰 field を drop する場合の
;; RemainderSafelyDropped Proof の構築と消費。

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../type-equiv.rkt"
         "../origins.rkt"
         "../search.rkt")

(define actual '(Record ((x (Owned Res) imm) (y Int imm))))
(define expected '(Record ((y Int imm))))

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

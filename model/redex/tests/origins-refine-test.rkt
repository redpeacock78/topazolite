#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../origins.rkt")

(define (verify core)
  (term (verify-origins ,R0 ,core)))

(define (verify-initial core)
  (term (verify-initial-origins ,R0 ,core)))

(define port-witness '(ProofRep (Reserved o-valid-port) (Prop ValidPort)))
(define empty-witness '(ProofRep (Reserved o-non-empty) (Prop NonEmpty)))
(define merge-witness '(ProofRep (Reserved o-merge) (Presence a)))

;; RFN-003: 発行者対応。判定表の行が対応づける oid と φ の組だけを認める。
(check-true (proof-issuer-ok? R0 '(Reserved o-valid-port) '(Prop ValidPort)))
(check-true (proof-issuer-ok? R0 '(Reserved o-non-empty) '(Prop NonEmpty)))
(check-false (proof-issuer-ok? R0 '(Reserved o-valid-port) '(Prop NonEmpty)))
(check-false (proof-issuer-ok? R0 '(Reserved o-add) '(Prop ValidPort)))
(check-false (proof-issuer-ok? R0 'User '(Prop ValidPort)))
(check-false (proof-issuer-ok? R0 '(Reserved o-valid-host)
                              '(Prop ValidHost)))

;; RFN-002: 常在性 witness の発行者は merge だけである。
(check-true (proof-issuer-ok? R0 '(Reserved o-merge) '(Presence a)))
(check-false (proof-issuer-ok? R0 '(Reserved o-valid-port) '(Presence a)))
(check-false (proof-issuer-ok? R0 'User '(Presence a)))

;; NAR-001 の既存の対応は変わらない。
(check-true (proof-issuer-ok? R0 '(Reserved o-type-narrative)
                             'TypeNarrativeCap))
(check-false (proof-issuer-ok? R0 '(Reserved o-merge) 'TypeNarrativeCap))

;; RFN-003: 到達成果物では validate 由来の witness を許す。
(check-equal? (verify `(RVal ,port-witness 8080)) 'ok)
(check-equal? (verify `(RVal ,empty-witness "a")) 'ok)
(check-equal? (verify '(UVal 8080)) 'ok)

;; RFN-001: ペイロード束縛検査。τ が判定表の行と食い違う RVal を落とす。
(check-equal? (verify `(RVal ,port-witness "8080"))
              `(forged (RVal ,port-witness "8080")))
;; check が偽になるペイロードを載せた RVal も落とす。validate を通さずに
;; 手で組めば作れてしまうため、この検査が偽造の入口を閉じる。
(check-equal? (verify `(RVal ,port-witness 70000))
              `(forged (RVal ,port-witness 70000)))
(check-equal? (verify `(RVal ,empty-witness ""))
              `(forged (RVal ,empty-witness "")))

;; RFN-003: 発行者が対応しない witness を載せた RVal を落とす。
(check-equal? (verify `(RVal ,empty-witness 8080))
              `(forged (RVal ,empty-witness 8080)))

;; RFN-002: 出現許可。常在性 witness はどちらの層にも現れてはならない。
(check-equal? (verify merge-witness) `(forged ,merge-witness))
(check-equal? (verify-initial merge-witness) `(forged ,merge-witness))
(check-equal? (verify `(Let (x (Proof (Presence a))) ,merge-witness x))
              `(forged ,merge-witness))

;; RFN-001: 初期成果物の層。UCore は UVal と RVal の構文を持たないため、
;; elaboration の出力にこれらが現れたら偽造である。
(check-equal? (verify-initial '(UVal 8080)) '(forged (UVal 8080)))
(check-equal? (verify-initial `(RVal ,port-witness 8080))
              `(forged (RVal ,port-witness 8080)))
(check-equal? (verify-initial '(Apply (PrimVal (Reserved o-add) add)
                                      1 (UVal 2)))
              '(forged (UVal 2)))

;; 初期層は到達層の判定もすべて課す。
(check-equal? (verify-initial '(PrimVal (Reserved o-add) sub))
              '(forged (PrimVal (Reserved o-add) sub)))
(check-equal? (verify-initial '(Apply (PrimVal (Reserved o-add) add) 1 2)) 'ok)

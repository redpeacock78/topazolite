#lang racket
(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../origins.rkt")

(define fuel 40)

;; heap が空の項用: (cfg result () () ()) を unwrap する
(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) fuel)
    [`(cfg ,result () () ()) result]
    [result (error 'run-g2-core "unexpected: ~e" result)]))

(define (stuck-g2? core)
  (null? (apply-reduction-relation -->g2 (inject-g2 core))))

(define (prim name oid) (term (PrimVal (Reserved ,oid) ,name)))

;; RFN-001: R0 と Γ0 が判定表の行から生成されている。
(check-equal? (assoc 'o-valid-port R0) '(o-valid-port (prim validPort)))
(check-equal? (assoc 'o-non-empty R0) '(o-non-empty (prim nonEmpty)))
(check-equal? (assoc 'o-untrusted-int R0)
              '(o-untrusted-int (prim untrustedInt)))
(check-equal? (assoc 'o-unrefine-port R0)
              '(o-unrefine-port (prim unrefinePort)))
;; RFN-002: witness の発行者 id も R0 に載る。
(check-equal? (assoc 'o-merge R0) '(o-merge merge))
;; 既存 origin は残る。
(check-equal? (assoc 'o-add R0) '(o-add (prim add)))

(check-equal?
 (assoc 'validPort Γ0)
 '(validPort ((NFn ((Untrusted Int))
                   (Result (Refined Int (Prop ValidPort)) String)
                   () ())
              (PrimVal (Reserved o-valid-port) validPort))))
(check-equal?
 (assoc 'untrustedInt Γ0)
 '(untrustedInt ((NFn (Int) (Untrusted Int) () ())
                 (PrimVal (Reserved o-untrusted-int) untrustedInt))))
(check-equal?
 (assoc 'unrefineNonEmpty Γ0)
 '(unrefineNonEmpty ((NFn ((Refined String (Prop NonEmpty))) String () ())
                     (PrimVal (Reserved o-unrefine-non-empty)
                              unrefineNonEmpty))))

;; RFN-001: 導入 primitive は値を無検査で包む。
(check-equal? (run-g2-core (term (Apply ,(prim 'untrustedInt 'o-untrusted-int)
                                        8080)))
              (term (UVal 8080)))
(check-equal? (run-g2-core
               (term (Apply ,(prim 'untrustedString 'o-untrusted-string)
                            "localhost")))
              (term (UVal "localhost")))

;; RFN-001: validate 成功は ok 側へ witness 付きの RVal を返す。
(check-equal?
 (run-g2-core (term (Apply ,(prim 'validPort 'o-valid-port) (UVal 8080))))
 (term (Construct (Result (Refined Int (Prop ValidPort)) String)
                  ok
                  (RVal (ProofRep (Reserved o-valid-port) (Prop ValidPort))
                        8080))))

;; RFN-001: validate 失敗は ng 側へ決定的なメッセージを返す。
(check-equal?
 (run-g2-core (term (Apply ,(prim 'validPort 'o-valid-port) (UVal 70000))))
 (term (Construct (Result (Refined Int (Prop ValidPort)) String)
                  ng
                  "validPort: rejected")))
(check-equal?
 (run-g2-core (term (Apply ,(prim 'nonEmpty 'o-non-empty) (UVal ""))))
 (term (Construct (Result (Refined String (Prop NonEmpty)) String)
                  ng
                  "nonEmpty: rejected")))
(check-equal?
 (run-g2-core (term (Apply ,(prim 'nonEmpty 'o-non-empty) (UVal "a"))))
 (term (Construct (Result (Refined String (Prop NonEmpty)) String)
                  ok
                  (RVal (ProofRep (Reserved o-non-empty) (Prop NonEmpty))
                        "a"))))

;; RFN-001: 射影 primitive は Proof を捨ててペイロードを返す。
(check-equal?
 (run-g2-core
  (term (Apply ,(prim 'unrefinePort 'o-unrefine-port)
               (RVal (ProofRep (Reserved o-valid-port) (Prop ValidPort))
                     8080))))
 (term 8080))

;; RFN-001: validate は UVal 以外の引数で stuck する（δ が undefined を返す）。
(check-true (stuck-g2? (term (Apply ,(prim 'validPort 'o-valid-port) 8080))))
(check-true (stuck-g2? (term (Apply ,(prim 'unrefinePort 'o-unrefine-port)
                                    (UVal 8080)))))

;; 既存の δ は変わらない。acquire は 1 引数だが新しい節へ吸われない。
(check-equal? (run-g2-core (term (Apply (PrimVal (Reserved o-acquire) acquire)
                                        1)))
              (term (resource 1)))
(check-equal? (run-g2-core (term (Apply (PrimVal (Reserved o-add) add) 1 2)))
              (term 3))

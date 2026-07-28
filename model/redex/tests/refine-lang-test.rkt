#lang racket
(require rackunit
         redex/reduction-semantics
         "../compat.rkt"
         "../lang.rkt"
         "../type-equiv.rkt")

;; RFN-001: Untrusted と Refined は G2 と G2m の型である。
(check-true (redex-match? G2 τ (term (Untrusted Int))))
(check-true (redex-match? G2 τ (term (Refined Int (Prop ValidPort)))))
(check-true (redex-match? G2m τ (term (Untrusted String))))
(check-true (redex-match? G2m τ (term (Refined String (Prop NonEmpty)))))
;; RFN-001: G1 の型言語は拡張しない。
(check-false (redex-match? G1 τ (term (Untrusted Int))))

;; RFN-001: 抽象命題は G2 の命題である。
(check-true (redex-match? G2 φ (term (Prop ValidPort))))
;; RFN-002: 常在性命題は G2 の命題であり、G1 には無い。
(check-true (redex-match? G2 φ (term (Presence a))))
(check-false (redex-match? G1 φ (term (Presence a))))

;; RFN-001: UVal と RVal は G2m の値である。
(check-true (redex-match? G2m v (term (UVal 8080))))
(check-true
 (redex-match? G2m v
               (term (RVal (ProofRep (Reserved o-valid-port)
                                     (Prop ValidPort))
                           8080))))
(check-false (redex-match? G1m v (term (UVal 8080))))

;; RFN-001: type-equiv? は τ の構造と φ の一致だけを見る（PRF-003 の irrelevance）。
(check-true (type-equiv? '(Untrusted Int) '(Untrusted Int)))
(check-false (type-equiv? '(Untrusted Int) '(Untrusted String)))
(check-true (type-equiv? '(Refined Int (Prop ValidPort))
                         '(Refined Int (Prop ValidPort))))
(check-false (type-equiv? '(Refined Int (Prop ValidPort))
                          '(Refined Int (Prop NonEmpty))))
(check-false (type-equiv? '(Refined Int (Prop ValidPort)) '(Untrusted Int)))
;; 既存型の判定は変えない。
(check-true (type-equiv? '(Owned Res) '(Owned Res)))
(check-false (type-equiv? '(Owned Res) 'Res))
(check-false (type-equiv? '(Refined Int (Prop ValidPort)) 'Int))

;; RFN-001: compat? は φ の一致と τ の compat? 再帰で判定する。
(check-true (compat? '(Refined Never (Prop ValidPort))
                     '(Refined Int (Prop ValidPort))))
(check-false (compat? '(Refined Int (Prop ValidPort))
                      '(Refined Int (Prop NonEmpty))))
(check-true (compat? '(Untrusted Never) '(Untrusted Int)))
(check-false (compat? '(Untrusted Int) '(Refined Int (Prop ValidPort))))
(check-false (compat? '(Untrusted Int) 'Int))
(check-false (compat? 'Int '(Untrusted Int)))
;; record field 経由でも新構成子の互換が伝播する。
(check-true (compat? '(Record ((a (Refined Never (Prop ValidPort)) imm)))
                     '(Record ((a (Refined Int (Prop ValidPort)) imm)))))

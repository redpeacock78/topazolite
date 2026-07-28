#lang racket
(require rackunit "../typing.rkt")

;; RFN-001: UVal はペイロードの型を Untrusted で包む。
(check-equal? (core-type-of '(UVal 1) '() '()) '((Untrusted Int) ()))
(check-equal? (core-type-of '(UVal "localhost") '() '())
              '((Untrusted String) ()))

;; RFN-001: RVal は witness の命題を型へ持ち上げる。
(check-equal?
 (core-type-of '(RVal (ProofRep (Reserved o-valid-port) (Prop ValidPort))
                      8080)
               '() '())
 '((Refined Int (Prop ValidPort)) ()))

;; RFN-002: 型付けは witness の発行者を見ない。常在性 witness を載せた RVal も
;; 型は付く。成果物としての出現の可否は Task 5 の検証が決める。
(check-equal?
 (core-type-of '(RVal (ProofRep (Reserved o-merge) (Presence a)) 1) '() '())
 '((Refined Int (Presence a)) ()))

;; RFN-001: Owned を部分に含むペイロードは拒否する。owned-type? は外層しか
;; 見ないため、この検査がないと (UVal (Rec ((a imm (resource 1))))) のような
;; 経路で線形資源が複製できてしまう。
(check-equal? (core-type-of '(UVal (resource 1)) '() '()) 'ill-typed)
(check-equal?
 (core-type-of '(RVal (ProofRep (Reserved o-valid-port) (Prop ValidPort))
                      (resource 1))
               '() '())
 'ill-typed)

;; RFN-001: 型注釈の側でも Owned を含む Untrusted と Refined は ill-formed で
;; ある。expected 型として置いても通らない。
(check-false (core-check '(UVal 1) '() '() '(Untrusted (Owned Res)) '()))
(check-false (core-check '(UVal 1) '() '()
                         '(Untrusted (List (Owned Res))) '()))
(check-false (core-check '(UVal 1) '() '()
                         '(Refined (Owned Res) (Prop ValidPort)) '()))

;; RFN-001: Untrusted と Refined の内側の record も一意ラベルを要求する。
(check-false (core-check '(UVal (Rec ((a imm 1))))
                         '() '()
                         '(Untrusted (Record ((a Int imm) (a Bool mut))))
                         '()))

;; VAR-001..003 との整合: checking 位置では compat? を通る。Never は bottom。
(check-true (core-check '(UVal 1) '() '() '(Untrusted Int) '()))

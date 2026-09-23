#lang racket

(require rackunit "../compat.rkt")

; 余剰 field を許す width subsumption
(check-true  (compat? '(Record ((a Int imm) (b Bool imm))) '(Record ((a Int imm)))))
; 要求 field 欠落は不可
(check-false (compat? '(Record ((a Int imm))) '(Record ((a Int imm) (b Bool imm)))))
; imm は covariant（Never は任意型の下位）
(check-true  (compat? '(Record ((a Never imm))) '(Record ((a Int imm)))))
; mut は invariant
(check-false (compat? '(Record ((a Never mut))) '(Record ((a Int mut)))))
(check-true  (compat? '(Record ((a Int mut))) '(Record ((a Int mut)))))
; ROW-005: mut field は imm の要求を満たす（書き込み能力を捨てる方向）
(check-true  (compat? '(Record ((a Int mut))) '(Record ((a Int imm)))))
; 降格した位置の型は共変に再帰する
(check-true  (compat? '(Record ((a Never mut))) '(Record ((a Int imm)))))
; 逆方向は能力を増やすため不可
(check-false (compat? '(Record ((a Int imm))) '(Record ((a Int mut)))))
; 可変性の記号が imm / mut のいずれでもない row は受理しない
(check-false (compat? '(Record ((a Int bogus))) '(Record ((a Int imm)))))
; Never は bottom
(check-true  (compat? 'Never '(Record ((a Int imm)))))
(check-true  (compat? 'Never 'Int))
; 予約型は type-equiv? 経路（構造化しない）
(check-true  (compat? '(List Int) '(List Int)))
(check-false (compat? '(List Int) '(List Bool)))
; Owned は内部型不変
(check-true  (compat? '(Owned Int) '(Owned Int)))
(check-false (compat? '(Owned Never) '(Owned Int)))

; NFn の O は不変位置の compat? では比較しない。
(define nfn-user '(NFn () Int () () () User))
(define nfn-reserved '(NFn () Int () () () (Reserved o-add)))
(check-true (compat? `(Owned ,nfn-user) `(Owned ,nfn-reserved)))
(check-true (compat? `(BorrowedMut ,nfn-user 0)
                     `(BorrowedMut ,nfn-reserved 0)))
(check-true (compat? `(Record ((f ,nfn-user mut)))
                     `(Record ((f ,nfn-reserved mut)))))

#lang racket
(require rackunit "../typing.rkt")

; 両枝が record を返す → 共通 field の交差
; true -> (Rec ((a imm 1) (b imm unit))), false -> (Rec ((a imm 2) (c imm unit)))
; 交差は (Record ((a Int imm)))
(check-equal?
 (core-type-of
  '(Eliminate (Construct Bool true)
     ((true () -> (Rec ((a imm 1) (b imm unit))))
      (false () -> (Rec ((a imm 2) (c imm unit))))))
  '() '())
 '((Record ((a Int imm))) ()))

; 可変性が食い違う共通ラベルは結果が imm へ降格するため、mut 枝の書き込みは拒否
(check-equal?
 (core-type-of
  '(Eliminate (Construct Bool true)
     ((true () -> (Rec ((a imm 1))))
      (false () -> (Rec ((a mut 2))))))
  '() '())
 'ill-typed)

; Never 枝の吸収: 一方が Perform で Never を synth（typing.rkt:369 で (Never …)）、
; 他方が record。Never 枝は交差から除外され、残る record 枝の型がそのまま result-type になる。
; Perform は Return effect を row へ載せるため、結果 row に (Return boundary Int) が現れる。
(check-equal?
 (core-type-of
  '(Eliminate (Construct Bool true)
     ((true () -> (Rec ((a imm 1))))
      (false () -> (Perform (Return boundary Int) 1))))
  '() '())
 '((Record ((a Int imm))) ((Return boundary Int))))

; 全枝が Never（非 Never 枝が 0 本）→ result-type は Never
(check-equal?
 (core-type-of
  '(Eliminate (Construct Bool true)
     ((true () -> (Perform (Return boundary Int) 1))
      (false () -> (Perform (Return boundary Int) 2))))
  '() '())
 '(Never ((Return boundary Int))))

; 非 Never 枝に record と非 record が混在 → 型エラー
(check-equal?
 (core-type-of
  '(Eliminate (Construct Bool true)
     ((true () -> (Rec ((a imm 1))))
      (false () -> 2)))
  '() '())
 'ill-typed)

; check 位置: expected が record のとき、各枝を compat? で受理（width subsumption）
(check-true
 (core-check
  '(Eliminate (Construct Bool true)
     ((true () -> (Rec ((a imm 1) (b imm unit))))
      (false () -> (Rec ((a imm 2) (c imm unit))))))
  '() '() '(Record ((a Int imm))) '()))

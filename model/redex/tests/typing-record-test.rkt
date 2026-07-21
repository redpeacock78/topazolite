#lang racket
(require rackunit "../typing.rkt")

; Rec の synthesis（field を synth、可変性を保持）
(check-equal? (core-type-of '(Rec ((a imm 1) (b imm unit))) '() '())
              '((Record ((a Int imm) (b Unit imm))) ()))
; ラベル重複は型エラー（core-type-of は #f でなく 'ill-typed を返す）
(check-equal? (core-type-of '(Rec ((a imm 1) (a imm 2))) '() '()) 'ill-typed)
; Proj の synthesis
(check-equal? (core-type-of '(Proj (Rec ((a imm 1) (b imm unit))) a) '() '())
              '(Int ()))
; 存在しない field の射影は型エラー
(check-equal? (core-type-of '(Proj (Rec ((a imm 1))) z) '() '()) 'ill-typed)
; checking 位置の width subsumption（余剰 field を許す）
; core-check は (core places callables expected row) の順で boolean を返す
(check-true (core-check '(Rec ((a imm 1) (b imm unit)))
                        '() '() '(Record ((a Int imm))) '()))

; Owned field 拒否: (resource 1) は (Owned Res) に synth されるため、
; record の field に置くと型エラー（record 値の field に Owned を許さない）
(check-equal? (core-type-of '(Rec ((a imm (resource 1)))) '() '()) 'ill-typed)

; 重複ラベルの record 型を expected に置くと ill-formed で弾かれる（type? が G2m τ
; かつ field-row-unique? を要求。§3.2）
(check-false (core-check '(Rec ((a imm 1)))
                         '() '() '(Record ((a Int imm) (a Bool mut))) '()))

; Suspend を field に含む Rec は field effect の和として row (Suspend) を返す（§7.5）
(check-equal? (core-type-of '(Rec ((a imm (Suspend 1)))) '() '())
              '((Record ((a Int imm))) (Suspend)))
; その Proj は scrutinee の effect (Suspend) を保つ
(check-equal? (core-type-of '(Proj (Rec ((a imm (Suspend 1)))) a) '() '())
              '(Int (Suspend)))

#lang racket
(require rackunit "../diagnostic.rkt" "../typing.rkt")

(define opt-env '((r (Record ((a Int imm) (b Int imm opt))))))
(define (code-of result)
  (and (diagnostic? result) (diagnostic-id result)))

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
; かつ field-row-unique? を要求。structural-row.md §2.2）
(check-false (core-check '(Rec ((a imm 1)))
                         '() '() '(Record ((a Int imm) (a Bool mut))) '()))

; Suspend を field に含む Rec は field effect の和として row (Suspend) を返す
; （structural-row.md §5.4）
(check-equal? (core-type-of '(Rec ((a imm (Suspend 1)))) '() '())
              '((Record ((a Int imm))) (Suspend)))
; その Proj は scrutinee の effect (Suspend) を保つ
(check-equal? (core-type-of '(Proj (Rec ((a imm (Suspend 1)))) a) '() '())
              '(Int (Suspend)))

; optional 欄は optional 専用診断で拒否し、未知欄は従来の診断を保つ。
(check-equal?
 (code-of (core-type-of/diagnostic '(Proj r b) '() '() opt-env))
 "E-RCD-012")
(check-equal?
 (code-of (core-type-of/diagnostic '(Proj r z) '() '() opt-env))
 "E-RCD-009")
(check-equal? (core-type-of '(Proj r a) '() '() opt-env) '(Int ()))

; ProjOpt は optional の欄だけを (Option τ) として射影する。
(check-equal? (core-type-of '(ProjOpt Int r b) '() '() opt-env)
              '((Option Int) ()))
; required の欄と τ の不一致は E-RCD-013、未知欄と record 以外は従来の診断を保つ。
(check-equal?
 (code-of (core-type-of/diagnostic '(ProjOpt Int r a) '() '() opt-env))
 "E-RCD-013")
(check-equal?
 (code-of (core-type-of/diagnostic '(ProjOpt Bool r b) '() '() opt-env))
 "E-RCD-013")
(check-equal?
 (code-of (core-type-of/diagnostic '(ProjOpt Int r z) '() '() opt-env))
 "E-RCD-009")
(check-equal?
 (code-of (core-type-of/diagnostic '(ProjOpt Int 1 b) '() '() '()))
 "E-RCD-007")

; 入れ子の optional 欄を some 枝で射影し、none 枝と同じ Option 型へ合流する。
(check-equal?
 (core-type-of
  '(Eliminate (ProjOpt (Record ((c Int imm opt))) n o)
     ((some (inner) -> (ProjOpt Int inner c))
      (none () -> (Construct (Option Int) none))))
  '() '()
  '((n (Record ((o (Record ((c Int imm opt))) imm opt))))))
 '((Option Int) ()))

; 入れ子の optional row も型検査の入口で例外にならない。
(check-not-exn
 (lambda ()
   (core-type-of
    '(Let (x const
           (Record ((a Int imm)
                    (b (Record ((c Int imm opt))) imm opt))))
       (Rec ((a imm 1)))
       (Proj x a))
    '() '())))

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

; ProjOpt は欄の型が互換なら、presence によらず (Option τ) として射影する。
(check-equal? (core-type-of '(ProjOpt Int r b) '() '() opt-env)
              '((Option Int) ()))
; Absent は Rec の欄の値としてだけ optional を表す。
(check-equal?
 (core-type-of '(Rec ((a imm 1) (b imm (Absent Int)))) '() '())
 '((Record ((a Int imm) (b Int imm opt))) ()))
(check-equal?
 (core-type-of '(Rec ((owned imm (Absent (Owned Res))))) '() '())
 '((Record ((owned (Owned Res) imm opt))) ()))
; optional 欄の型は値の置換後も推論型に残る。
(define absent-record
  '(Rec ((a imm 1) (b imm (Absent Int)))))
(check-equal?
 (core-type-of `(Let (r const ,(second (first opt-env)))
                      ,absent-record
                      (ProjOpt Int r b))
               '() '())
 '((Option Int) ()))
(check-equal?
 (core-type-of
  '(Let (y const (Record ((a Int imm) (b Int imm opt))))
     (Rec ((a imm 1) (b imm (Absent Int))))
     (Let (n const (Record ((inner (Record ((a Int imm) (b Int imm opt))) imm))))
       (Rec ((inner imm y)))
       0))
 '() '())
 '(Int ()))
;; Function の formal へ渡しても absent 欄の型が引数の置換後に残る。
(define absent-parameter-type
  '(NFn ((Record ((a Int imm) (b Int imm opt))))
        (Option Int) () () () User))
(check-equal?
 (core-type-of '(Apply f (Rec ((a imm 1) (b imm (Absent Int)))))
               '() '() `((f ,absent-parameter-type)))
 '((Option Int) ()))
; required の欄も受理し、型不一致は E-RCD-013、未知欄と非 record は従来どおり。
(check-equal? (core-type-of '(ProjOpt Int r a) '() '() opt-env)
              '((Option Int) ()))
(check-equal?
 (code-of (core-type-of/diagnostic '(ProjOpt Bool r b) '() '() opt-env))
 "E-RCD-013")
(check-equal?
 (code-of (core-type-of/diagnostic '(ProjOpt Int r z) '() '() opt-env))
 "E-RCD-009")
(check-equal?
 (code-of (core-type-of/diagnostic '(ProjOpt Int 1 b) '() '() '()))
 "E-RCD-007")
; Rec の欄の位置以外では Absent を値として使えない。
(check-equal? (core-type-of '(Absent Int) '() '()) 'ill-typed)
(check-equal? (core-type-of '(OwnedLeaf (tok 0) (Absent Int)) '() '())
              'ill-typed)

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

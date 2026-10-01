#lang racket
(require rackunit "../typing.rkt")

(define rec2 '(Rec ((a imm 1) (b imm unit))))  ; (Record ((a Int imm) (b Unit imm)))

; const: 残余が空でないと型エラー（ROW-001。core-type-of は 'ill-typed を返す）
(check-equal? (core-type-of `(Let (x const (Record ((a Int imm)))) ,rec2 x) '() '()) 'ill-typed)
; const: 残余が空なら OK、x は必須 field のみ
(check-equal? (core-type-of `(Let (x const (Record ((a Int imm) (b Unit imm)))) ,rec2 (Proj x a)) '() '())
              '(Int ()))
; let: 残余 field を保持し、現 flow で射影できる（ROW-002）
(check-equal? (core-type-of `(Let (x let (Record ((a Int imm)))) ,rec2 (Proj x b)) '() '())
              '(Unit ()))
; let: 非互換 field は compat? で拒否
(check-equal? (core-type-of `(Let (x let (Record ((a Bool imm)))) ,rec2 x) '() '()) 'ill-typed)
; 非 record の T は G1 の Let と同じ（const と let で差なし）
(check-equal? (core-type-of '(Let (x const Int) 1 x) '() '()) '(Int ()))
(check-equal? (core-type-of '(Let (x let Int) 1 x) '() '()) '(Int ()))
; record bound が Never: policy を課さず受理し、x は expected record 型で使える
; ((Perform (Return boundary Int) 1) は Never を synth、row に (Return boundary Int)）
(check-equal?
 (core-type-of `(Let (x const (Record ((a Int imm)))) (Perform (Return boundary Int) 1) (Proj x a)) '() '())
 '(Int ((Return boundary Int))))
; Let の effect row は bound と body の effect の和（structural-row.md §5.4）
(check-equal? (core-type-of '(Let (x const Int) (Suspend 1) x) '() '()) '(Int (Suspend)))

;; Absent が optional の欄を明示するため、通常の互換規則で束縛できる。
(check-equal?
 (core-type-of '(Let (x const (Record ((a Int imm) (b Int imm opt))))
                     (Rec ((a imm 1) (b imm (Absent Int))))
                     x)
               '() '())
 '((Record ((a Int imm) (b Int imm opt))) ()))
;; Core の Rec が欄を省略しても、typing は不在を推測しない。
(check-equal?
 (core-type-of '(Let (x const (Record ((a Int imm) (b Int imm opt))))
                     (Rec ((a imm 1)))
                     x)
               '() '())
 'ill-typed)
;; required 欄の省略と宣言に無い欄の記述は拒否する。
(check-equal?
 (core-type-of '(Let (x const (Record ((a Int imm) (b Int imm opt))))
                     (Rec ((b imm 1)))
                     x)
               '() '())
 'ill-typed)
(check-equal?
 (core-type-of '(Let (x const (Record ((a Int imm) (b Int imm opt))))
                     (Rec ((a imm 1) (z imm 2)))
                     x)
               '() '())
 'ill-typed)
;; 中間束縛を挟むと bound は Rec でないため、optional の型不一致を拒否する。
(check-equal?
 (core-type-of '(Let (p let (Record ((name Int imm))))
                     (Rec ((name imm 1) (age imm unit)))
                     (Let (q const (Record ((name Int imm) (age Int imm opt))))
                          p
                          q))
               '() '())
 'ill-typed)

;; Reassign は Mutability row を追加し、元の by-value 値の型を保つ。
(check-equal?
 (core-type-of
  '(Let (s const (Record ((a Int imm))))
        (Rec ((a imm 1)))
        (Let (x mut (Record ((a Int imm opt))))
             s
             (Let (y const (Record ((a Int imm opt))))
                  (Rec ((a imm 2)))
                  (Let (ignored const Unit)
                       (Reassign x y)
                       (Proj s a)))))
  '() '())
 '(Int (Mutation)))

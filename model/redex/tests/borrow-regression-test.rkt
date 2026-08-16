#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(provide borrow-regression-cases)

;; G5b の借用判定の結果を凍結する。
;; G5c1 は判定の経路を推論と解決と検査の 3 段へ作り直すが、
;; 借用の値がその region の外へ出ない形では結果が変わってはならない。
;; spec §11。行を足してはならない。足すと凍結の意味が消える。

(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (result-of core [environment '()])
  (define ir (build-region-ir core))
  (match (type-of/raw core '() '() environment (Λ-of ir))
    [(list 'ok _) 'ok]
    [(list 'fail key _ _) key]))

(define borrow-regression-cases
  (list
   (list "共有借用は通る"
         `(Scope () (Let (x let (Owned Res)) (resource 1) (Borrow x)))
         'ok)
   (list "共有借用の 2 本は通る"
         `(Scope ()
            (Let (x let (Owned Res)) (resource 1)
              (Yield (Borrow x) (Borrow x))))
         'ok)
   (list "内側 Scope の借用が閉じた後の Move は通る"
         `(Scope ()
            (Let (x let (Owned Res)) (resource 1)
              (Yield (Scope () (Borrow x)) (Move x))))
         'ok)
   (list "可変借用の 2 本は衝突する"
         `(Scope ()
            (Let (x let (Owned Res)) (resource 1)
              (Yield (BorrowMut x) (BorrowMut x))))
         'borrow-conflicting-alias)
   (list "可変借用と共有借用は衝突する"
         `(Scope ()
            (Let (x let (Owned Res)) (resource 1)
              (Yield (BorrowMut x) (Borrow x))))
         'borrow-conflicting-alias)
   (list "借用中の Move は拒む"
         `(Scope ()
            (Let (x let (Owned Res)) (resource 1)
              (Yield (Borrow x) (Move x))))
         'move-borrowed)
   (list "借用中の Drop は拒む"
         `(Scope ()
            (Let (x let (Owned Res)) (resource 1)
              (Yield (Borrow x) (Drop x))))
         'drop-borrowed)
   (list "所有していない束縛の借用は拒む"
         `(Scope () (Let (x let Int) 1 (Borrow x)))
         'borrow-non-owned)))

(for ([entry (in-list borrow-regression-cases)])
  (match-define (list name core expected) entry)
  (check-equal? (result-of core) expected name))

;; 所有者の region が引けない借用は拒む。
;; この 1 件だけ environment を持たせる。infer-borrow は owner の lookup より先に
;; borrow-target-payload の environment lookup を行うため、environment が空だと
;; unbound-variable で落ち、この key へ届かない。
;; environment に x を置き、owner の表を空にした形が、この key へ届く唯一の形である。
(check-equal? (result-of '(Borrow x) '((x (Owned Res))))
              'borrow-unknown-owner-region
              "所有者の region が引けない借用は拒む")

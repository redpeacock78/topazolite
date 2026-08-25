#lang racket

;; [REQ: OWN-005] 計算した値を Owned の束縛へ載せる。

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(define (status core [places '()])
  (define ir (build-region-ir core))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
  (first (type-of/raw core places '() '()
                      (region-ctx ir '() owners (hash)))))

(define (failure core [places '()])
  (define ir (build-region-ir core))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
  (match (type-of/raw core places '() '()
                      (region-ctx ir '() owners (hash)))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

;; 1。Eliminate が計算した Record を Owned の束縛へ載せられる。
;; resource でも Move でもない項が計算した値である。
(test-case
 "Eliminate が計算した Record を Owned の束縛へ載せる"
 (check-equal?
  (status
   '(Scope ()
           (Let (x let (Owned (Record ((a Int imm)))))
                (Eliminate (Construct Bool true)
                           ((true () -> (Rec ((a imm 1))))
                            (false () -> (Rec ((a imm 2))))))
                1)))
  'ok))

;; 2。resource が作った値は今日と同じく通る。
;; 追加した節が既存の経路を塞いでいないことを見る。
(test-case
 "resource が作った Owned の束縛は通る"
 (check-equal?
  (status
   '(Scope ()
           (Let (x let (Owned Res))
                (resource 1)
                1)))
  'ok))

;; Construct の結果も計算値として Owned へ載せられる。
;; check-as/full の Construct 節が呼出し側の compatible? を捨てないことを見る。
(test-case
 "Construct が作った値を Owned の束縛へ載せる"
 (check-equal?
  (status
   '(Scope ()
           (Let (x let (Owned (List Int)))
                (Construct (List Int) nil)
                1)))
  'ok))

;; 3。載せる値の型に借用が入る形は落とす。
;; place へ載せた後は借用の所有者の生存を追えない。
(test-case
 "payload に借用が入る Owned の束縛を落とす"
 (check-equal?
  (failure
   '(Scope (1)
           (Let (y let (BorrowedMut Int (RVar 0)))
                (BorrowMut 1)
                (Let (x let (Owned (BorrowedMut Int (RVar 0))))
                     y
                     1)))
   '((1 Int)))
  'own-binding-borrowed-payload))

;; 4。借用を欄に持つ Record も落とす。判定は型木の全体を歩く。
(test-case
 "借用を欄に持つ Record を Owned の束縛へ載せられない"
 (check-equal?
  (failure
   '(Scope ()
           (Let (x let (Owned (Record ((a (BorrowedMut Int (RVar 0)) imm)))))
                (Rec ((a imm 1)))
                1)))
  'own-binding-borrowed-payload))

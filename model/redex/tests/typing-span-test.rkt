#lang racket

(require rackunit
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../typing.rkt")

(define (id-of core places callables [environment '()])
  (diagnostic-id (core-type-of/diagnostic core places callables environment)))

(check-equal? (id-of 'x '() '()) "E-VAR-006")
(check-equal? (id-of '(Move 3) '() '()) "E-OWN-020")
(check-equal? (id-of '(Scope (3) 1) '() '()) "E-OWN-021")
(check-equal? (id-of '(PrimVal User no-such-prim) '() '()) "E-VAR-007")
(check-equal? (id-of '(Apply 1 2) '() '()) "E-APP-003")
(check-equal? (id-of '(Curry 1 2) '() '()) "E-APP-004")
(check-equal? (id-of '(Proj 1 a) '() '()) "E-RCD-007")
(check-equal? (id-of '(Rec ((a imm 1) (a imm 2))) '() '()) "E-RCD-006")
(check-equal? (id-of '(Eliminate 1 ()) '() '()) "E-DAT-006")
(check-equal? (id-of '(Lam User no-such-callable (x) x) '() '()) "E-APP-005")

;; spanful な入力が spanless な入力と同じ判定を返す。
(define spanless '(Drop (resource 0)))
(define spanful
  '(Drop (#:span src 0 12) (resource (#:span src 6 11) 0)))
(define places '((0 Res)))

(check-equal? (core-type-of spanless places '())
              '(Unit (Own)))
(check-equal? (core-type-of spanful places '())
              '(Unit (Own)))

;; 入口検査は投影した形へ掛ける。spanful でも Core 外の形は落ちる。
(check-equal? (core-type-of '(NotACoreForm (#:span src 0 3)) places '())
              'ill-typed)

(define owned-environment '((x (Owned Res))))
(define move-source '(Move x))
(check-equal? (core-type-of move-source '() '() owned-environment)
              (core-type-of (annotate-core move-source)
                            '()
                            '()
                            owned-environment))
(check-equal? (core-type-of move-source '() '() owned-environment)
              '((Owned Res) (Own)))

(define handle-source
  '(Handle (Return boundary Int)
           (x -> x)
           1))
(check-equal? (core-type-of handle-source '() '())
              (core-type-of (annotate-core handle-source) '() '()))
(check-equal? (core-type-of (annotate-core handle-source) '() '())
              '(Int ()))

;; 失敗しても従来の返り値のまま返る。
(check-equal? (core-type-of '(Drop 1) '() '()) 'ill-typed)
(check-equal? (core-check-row '(Drop 1) '() '() 'Unit) #f)

;; 第 1 経路が成功する所有型の Drop。
(check-equal? (core-type-of '(Drop (resource 0)) '((0 Res)) '())
              '(Unit (Own)))

;; 第 1 経路の失敗を局所的に回復し、fallback の check-as へ進む。
(check-equal? (core-type-of '(Drop (Error 0)) '((0 Res)) '())
              '(Unit (Own)))

;; fallback も失敗したときは外側へ抜ける。
(check-equal? (core-type-of '(Drop 1) '((0 Res)) '()) 'ill-typed)

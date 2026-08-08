#lang racket

(require rackunit
         "../annotate.rkt"
         "../typing.rkt")

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

#lang racket

(require rackunit
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

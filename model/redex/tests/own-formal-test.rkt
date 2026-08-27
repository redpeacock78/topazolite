#lang racket

;; G5c5b1。Owned を取る仮引数の符号化を検査する。
(require rackunit
         "../typing.rkt")

;; 段 1
(test-case
 "function-body-environment は Owned の位置に payload の型を与える"
 (define environment '((outer (Owned Res)) (plain Int)))
 (define result
   (function-body-environment environment
                              '(owned0 n)
                              '((Owned Res) Int)))
 (check-equal? (assoc 'owned0 result) '(owned0 Res))
 (check-equal? (assoc 'n result) '(n Int))
 ;; 外側の Owned は落ちる。捕捉の禁止は G5c5b2 まで有効である。
 (check-false (assoc 'outer result))
 (check-equal? (assoc 'plain result) '(plain Int)))

(test-case
 "function-body-environment は Owned が無ければ従来と同じ環境を作る"
 (define environment '((plain Int)))
 (check-equal? (function-body-environment environment '(a b) '(Int Bool))
               '((a Int) (b Bool) (plain Int))))

#lang racket

;; G5c5b1。Owned を取る仮引数の符号化を検査する。
(require rackunit
         "../classify.rkt"
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

;; 段 2
(define owned-callables
  '((callable0 (NFn ((Owned Res) Int) Int () ()))))
(define plain-callables
  '((callable1 (NFn (Int) Int () ()))))

(test-case
 "strip-owned-prefix は Owned が無ければ本体と環境をそのまま返す"
 (define body '(Yield Int (Apply f n)))
 (check-equal? (strip-owned-prefix 'callable1 '(n) body '((n Int))
                                   plain-callables)
               (list body '((n Int)))))

(test-case
 "strip-owned-prefix は Scope と Let の連なりを署名の個数だけ外す"
 (define inner '(Yield Int (Apply f p n)))
 (define body
   `(Scope () (Let (p let (Owned Res)) owned0 ,inner)))
 (define result
   (strip-owned-prefix 'callable0 '(owned0 n) body
                       '((owned0 Res) (n Int)) owned-callables))
 (check-equal? (first result) inner)
 (check-equal? (assoc 'p (second result)) '(p (Owned Res))))

(test-case
 "strip-owned-prefix は契約を満たさない形へ #f を返す"
 (define inner '(Yield Int (Apply f p n)))
 ;; 管理する place を持つ Scope
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope (q) (Let (p let (Owned Res)) owned0 ,inner))
                      '((owned0 Res) (n Int)) owned-callables))
 ;; 宣言型が署名と食い違う Let
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope () (Let (p let (Owned Int)) owned0 ,inner))
                      '((owned0 Res) (n Int)) owned-callables))
 ;; 右辺が仮引数の名前でない Let
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope () (Let (p let (Owned Res)) n ,inner))
                      '((owned0 Res) (n Int)) owned-callables))
 ;; Let が足りない
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope () ,inner)
                      '((owned0 Res) (n Int)) owned-callables))
 ;; Scope が無い
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Let (p let (Owned Res)) owned0 ,inner)
                      '((owned0 Res) (n Int)) owned-callables))
 ;; 契約を満たす Let がもう 1 段続く
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope ()
                              (Let (p let (Owned Res)) owned0
                                   (Let (q let (Owned Res)) owned0 ,inner)))
                      '((owned0 Res) (n Int)) owned-callables)))

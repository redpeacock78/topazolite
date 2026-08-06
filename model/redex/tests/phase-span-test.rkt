#lang racket

(require rackunit
         redex/reduction-semantics
         "../annotate.rkt"
         "../typing.rkt")

;; span.md §7.3: 判定に span を使わない項面の関数は、投影を通してから既存の
;; 走査へ渡す。ここで固定するのは「spanful な項の判定が spanless 版と一致する」
;; ことである。
;; ill-typed 側の一致では契約を固定できない。投影が入っていない実装でも
;; redex-match? が落ちて 'ill-typed になり、同じ値が返るためである。
;; そのため各 test-case は well-typed な項の型が一致することを見る。

(define callable-types
  (term ((identity-id (NFn (Int) Int () ()))
         (binary-id (NFn (Int Int) Int () ())))))

(test-case "span.md §7.3: core-type-of は spanful な c を投影して受理する"
  (define prim '(PrimVal (Reserved o-lt) lt))
  (check-equal? (core-type-of (annotate-core prim) '() '())
                '((NFn (Int Int) Bool () ()) ()))
  (check-equal? (core-type-of (annotate-core prim) '() '())
                (core-type-of prim '() '()))
  ;; #:bind と Lam の span を含む項。
  (define lam '(Lam User identity-id (x) x))
  (check-equal? (core-type-of (annotate-core lam) '() callable-types)
                '((NFn (Int) Int () ()) ()))
  ;; #:lit と Apply の span を含む項。
  (define applied `(Apply (Lam User binary-id (x y) x) 1 2))
  (check-equal? (core-type-of (annotate-core applied) '() callable-types)
                '(Int ()))
  ;; #:ty と #:bind を持つ Let。
  (define bound '(Let (n Int) 1 n))
  (check-equal? (core-type-of (annotate-core bound) '() '())
                (core-type-of bound '() '()))
  (check-equal? (core-type-of (annotate-core bound) '() '())
                '(Int ())))

(test-case "span.md §7.3: core-check-row と core-check も spanful な c を受ける"
  (define prim '(PrimVal (Reserved o-lt) lt))
  (define signature '(NFn (Int Int) Bool () ()))
  (check-equal? (core-check-row (annotate-core prim) '() '() signature)
                '())
  (check-true (core-check (annotate-core prim) '() '() signature '())))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../span-core.rkt"
         "../origins.rkt"
         "../diagnostic.rkt"
         "../macro-expand.rkt")

(test-case
 "G2+ の c が MacroCall を受ける"
 (define call
   '(MacroCall (#:span main 0 10) User twice
               ((#:lit 1 (#:span main 6 7)))))
 (check-true (redex-match? G2+ c call)))

(test-case
 "展開由来の Lam の origin を verify-origins が受ける"
 (define lam
   '(Lam (#:span #:synthetic 1 1)
         (Derived User (Expand twice))
         c0
         ((#:bind x (#:span #:synthetic 2 2)))
         (#:var x (#:span #:synthetic 3 3))))
 (check-equal? (verify-origins/diagnostic R0 lam) 'ok))

(test-case
 "Expand でない step を持つ Lam を verify-origins が拒む"
 (define lam
   '(Lam (#:span #:synthetic 1 1)
         (Derived User (Policy p0))
         c0
         ((#:bind x (#:span #:synthetic 2 2)))
         (#:var x (#:span #:synthetic 3 3))))
 (check-not-equal? (verify-origins/diagnostic R0 lam) 'ok))

(define s-def '(#:span main 0 20))
(define s-arg '(#:span main 8 9))

(test-case
 "妥当な定義は診断を出さない"
 (define defs (list (list 'twice s-def '(x) (list '#:var 'x s-arg))))
 (check-equal? (macro-env-errors defs) '()))

(test-case
 "同じ名前を 2 度定義すると E-MAC-003 を出す"
 (define s2 '(#:span main 30 50))
 (define defs (list (list 'twice s-def '(x) (list '#:var 'x s-arg))
                    (list 'twice s2 '(y) (list '#:var 'y '(#:span main 38 39)))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-003"))
 (check-equal? (diagnostic-primary-span (first ds)) s2)
 (check-equal? (map first (diagnostic-related (first ds))) '(previous-definition)))

(test-case
 "pattern に同じ変数が 2 度現れると E-MAC-005 を出す"
 (define defs (list (list 'twice s-def '(x x) (list '#:var 'x s-arg))))
 (check-equal? (map diagnostic-id (macro-env-errors defs)) '("E-MAC-005")))

(test-case
 "template が pattern に無い変数を参照すると E-MAC-006 を出す"
 (define s-free '(#:span main 12 13))
 (define defs (list (list 'twice s-def '(x) (list '#:var 'y s-free))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-006"))
 (check-equal? (diagnostic-primary-span (first ds)) s-free))

(test-case
 "template の Lam の origin が User でないと E-MAC-004 を出す"
 (define s-lam '(#:span main 10 18))
 (define defs
   (list (list 'twice s-def '(x)
               (list 'Lam s-lam '(Derived User (Expand other)) 'c0
                     (list (list '#:bind 'x '(#:span main 14 15)))
                     (list '#:var 'x '(#:span main 16 17))))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-004"))
 (check-equal? (diagnostic-primary-span (first ds)) s-lam))

(test-case
 "template の中の MacroCall の origin が User でないと E-MAC-004 を出す"
 (define s-call '(#:span main 10 18))
 (define defs
   (list (list 'twice s-def '(x)
               (list 'MacroCall s-call '(Reserved o-add) 'other
                     (list (list '#:var 'x '(#:span main 16 17)))))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-004"))
 (check-equal? (diagnostic-primary-span (first ds)) s-call))

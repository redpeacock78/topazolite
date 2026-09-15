#lang racket

(require rackunit
         redex/reduction-semantics
         "../span-core.rkt"
         "../origins.rkt")

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

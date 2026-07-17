#lang racket

(require rackunit
         redex/reduction-semantics)

(define-language L
  (e ::= number))

(test-case "smoke: redex-lib define-language"
  (check-true (redex-match? L e 1)))

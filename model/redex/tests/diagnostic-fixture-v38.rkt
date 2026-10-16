#lang racket

;; registry version 38 adds E-RET-005 for missing returns in expression-position when arms.
(require "diagnostic-fixture-v37.rkt")

(provide diagnostic-entries-v38)

(define diagnostic-entries-v38
  (append diagnostic-entries-v37
          '(("E-RET-005" elaborate when-arm-missing-return))))

#lang racket

;; registry version 40 adds E-RET-006 for leave outside an expression boundary.
(require "diagnostic-fixture-v39.rkt")

(provide diagnostic-entries-v40)

(define diagnostic-entries-v40
  (append diagnostic-entries-v39
          '(("E-RET-006" elaborate leave-outside-expression-boundary))))

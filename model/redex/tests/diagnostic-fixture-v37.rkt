#lang racket

;; registry version 37 adds E-RET-004 for missing function-body returns.
(require "diagnostic-fixture-v36.rkt")

(provide diagnostic-entries-v37)

(define diagnostic-entries-v37
  (append diagnostic-entries-v36
          '(("E-RET-004" elaborate function-body-missing-return))))

#lang racket

;; registry version 36 adds the two SUR-002a TryBind elaboration diagnostics.
(require "diagnostic-fixture-v35.rkt")

(provide diagnostic-entries-v36)

(define diagnostic-entries-v36
  (append diagnostic-entries-v35
          '(("E-TYP-032" elaborate try-bind-non-adt)
            ("E-TYP-033" elaborate try-bind-boundary-mismatch))))

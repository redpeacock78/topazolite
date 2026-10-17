#lang racket

;; registry version 39 adds E-BOR-027 for borrow-hidden narrowing.
(require "diagnostic-fixture-v38.rkt")

(provide diagnostic-entries-v39)

(define diagnostic-entries-v39
  (append diagnostic-entries-v38
          '(("E-BOR-027" typing borrow-hidden-by-narrowing))))

#lang racket

;; registry version 35 は typing へ E-OWN-036 を 1 行足す。
;; 直前の凍結 fixture を基底にし、累計 226 組を保つ。

(require "diagnostic-fixture-v34.rkt")

(provide diagnostic-entries-v35)

(define diagnostic-entries-v35
  (append diagnostic-entries-v34
          '(("E-OWN-036" typing forward-invalid-context))))

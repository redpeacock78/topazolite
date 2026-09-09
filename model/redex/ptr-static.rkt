#lang racket

;; unsafe.md §5.2。raw 操作の静的な記録。
;; 判定は持たず、typing.rkt が集めた出現を保持するだけの層である。
(provide (struct-out ptr-request)
         (struct-out ptr-sidecar)
         ptr-sidecar-obligations)

(struct ptr-request (kind node obligations unsafe?) #:transparent)
(struct ptr-sidecar (requests) #:transparent)

;; 同じ kind の出現が異なる集合を要求する形は想定しない。
;; 想定が破れたときに黙って一方を採らないよう、#f で落とす。
(define (ptr-sidecar-obligations sidecar kind)
  (define hits
    (for/list ([r (in-list (ptr-sidecar-requests sidecar))]
               #:when (eq? (ptr-request-kind r) kind))
      (ptr-request-obligations r)))
  (cond
    [(null? hits) #f]
    [(for/and ([h (in-list (cdr hits))]) (equal? h (car hits))) (car hits)]
    [else #f]))

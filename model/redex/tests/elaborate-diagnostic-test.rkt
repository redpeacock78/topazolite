#lang racket

(require rackunit
         "../diagnostic.rkt"
         "../elaborate.rkt")

;; 失敗値から Diagnostic を取り出す。
(define (elab-diagnostic term)
  (match (elab term)
    [`(err ,d) d]
    [other (error 'elab-diagnostic "失敗しなかった: ~s" other)]))

(test-case
 "失敗値の中身が schema を満たす Diagnostic である"
 (define d (elab-diagnostic 'no-such-variable))
 (check-pred diagnostic? d)
 (check-true (diagnostic-valid? d))
 (check-equal? (diagnostic-schema-errors d) '())
 (check-equal? (diagnostic-id d)
               (diagnostic-code-of 'elaborate 'unbound-variable))
 (check-equal? (diagnostic-message d) (diagnostic-title d)))

(test-case
 "details が 1 件なら found にその値が入り expected は #f である"
 (define d (elab-diagnostic 'no-such-variable))
 (check-equal? (diagnostic-found d) 'no-such-variable)
 (check-false (diagnostic-expected d)))

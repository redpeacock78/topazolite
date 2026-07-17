#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt"
         "machine.rkt")

(provide obs-eval)

(define (trace-observations trace)
  (reverse
   (for/fold ([observed '()])
             ([event (in-list trace)])
     (match event
       [`(obs ,value) (cons value observed)]
       [_ observed]))))

(define (terminal-kind core)
  (cond
    [(redex-match? G1m v core) 'value]
    [(redex-match? G1m (Error p) core) 'ownership-error]
    [(redex-match? G1m (Perform op v) core) 'perform]
    [else 'stuck]))

;; Result kind is observed, value, ownership-error, perform, stuck, or timeout.
(define (obs-eval core depth fuel)
  (unless (exact-nonnegative-integer? depth)
    (raise-argument-error 'obs-eval "exact-nonnegative-integer?" depth))
  (unless (exact-nonnegative-integer? fuel)
    (raise-argument-error 'obs-eval "exact-nonnegative-integer?" fuel))
  (let loop ([current (inject core)]
             [remaining fuel])
    (match-define `(cfg ,current-core ,_ ,_ ,trace) current)
    (define all-observed (trace-observations trace))
    (define observed
      (take all-observed (min depth (length all-observed))))
    (cond
      [(= (length observed) depth) (list observed 'observed)]
      [else
       (define next
         (remove-duplicates
          (apply-reduction-relation -->g1 current)
          equal?))
       (cond
         [(null? next) (list observed (terminal-kind current-core))]
         [(zero? remaining) (list observed 'timeout)]
         [(null? (cdr next)) (loop (car next) (sub1 remaining))]
         [else
          (error 'obs-eval
                 "nondeterministic reduction from ~e to ~e"
                 current
                 next)])])))

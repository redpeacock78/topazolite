#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt"
         "machine.rkt")

(provide obs-eval
         obs-eval-g2)

(define (trace-observations trace)
  (reverse
   (for/fold ([observed '()])
             ([event (in-list trace)])
     (match event
       [`(obs ,value) (cons value observed)]
       [_ observed]))))

(define (terminal-kind-g1 core)
  (cond
    [(redex-match? G1m v core) 'value]
    [(redex-match? G1m (Error p) core) 'ownership-error]
    [(redex-match? G1m (Perform op v) core) 'perform]
    [else 'stuck]))

(define (terminal-kind-g2 core)
  (cond
    [(redex-match? G2m v core) 'value]
    [(redex-match? G2m (Error p) core) 'ownership-error]
    [(redex-match? G2m (Perform op v) core) 'perform]
    [else 'stuck]))

;; Result kind is observed, value, ownership-error, perform, stuck, or timeout.
(define (obs-eval/using who inject-core relation terminal-kind
                        core depth fuel)
  (unless (exact-nonnegative-integer? depth)
    (raise-argument-error who "exact-nonnegative-integer?" depth))
  (unless (exact-nonnegative-integer? fuel)
    (raise-argument-error who "exact-nonnegative-integer?" fuel))
  (let loop ([current (inject-core core)]
             [remaining fuel])
    (match-define `(cfg ,current-core ,_ ,_ () ,trace) current)
    (define all-observed (trace-observations trace))
    (define observed
      (take all-observed (min depth (length all-observed))))
    (cond
      [(= (length observed) depth) (list observed 'observed)]
      [else
       (define next
         (remove-duplicates
          (apply-reduction-relation relation current)
          equal?))
       (cond
         [(null? next) (list observed (terminal-kind current-core))]
         [(zero? remaining) (list observed 'timeout)]
         [(null? (cdr next)) (loop (car next) (sub1 remaining))]
         [else
          (error who
                 "nondeterministic reduction from ~e to ~e"
                 current
                 next)])])))

(define (obs-eval core depth fuel)
  (obs-eval/using 'obs-eval inject -->g1 terminal-kind-g1
                  core depth fuel))

(define (obs-eval-g2 core depth fuel)
  (obs-eval/using 'obs-eval-g2 inject-g2 -->g2 terminal-kind-g2
                  core depth fuel))

#lang racket

(require racket/match
         redex/reduction-semantics
         "pr-lang.rkt"
         "pr-machine.rkt")

(provide obs-eval-pr
         terminal-kind-pr)

;; obs.rkt:11 の trace-observations と同じ実装である。obs.rkt は provide して
;; いないため写す。
(define (trace-observations-pr trace)
  (reverse
   (for/fold ([observed '()])
             ([event (in-list trace)])
     (match event
       [`(obs ,value) (cons value observed)]
       [_ observed]))))

;; obs.rkt:19 の terminal-kind-g1 と同じ分類である。種別の名前を揃えるのは、
;; §7.3 の trace 一致が源と目標の種別を直接比べるためである。
(define (terminal-kind-pr core)
  (cond
    [(redex-match? PR pv core) 'value]
    [(redex-match? PR (PError pp) core) 'ownership-error]
    [(redex-match? PR (PEffect pop pv) core) 'perform]
    [else 'stuck]))

;; obs.rkt:34 の obs-eval/using を -->pr に固定した形である。源側は 2 つの機械
;; を共有していたが目標側は 1 つなので、抽象を挟まない。
(define (obs-eval-pr core depth fuel)
  (unless (exact-nonnegative-integer? depth)
    (raise-argument-error 'obs-eval-pr "exact-nonnegative-integer?" depth))
  (unless (exact-nonnegative-integer? fuel)
    (raise-argument-error 'obs-eval-pr "exact-nonnegative-integer?" fuel))
  (let loop ([current (inject-pr core)]
             [remaining fuel])
    (match-define `(pcfg ,current-core ,_ ,_ ,trace) current)
    (define all-observed (trace-observations-pr trace))
    (define observed
      (take all-observed (min depth (length all-observed))))
    (cond
      [(= (length observed) depth) (list observed 'observed)]
      [else
       (define next
         (remove-duplicates (apply-reduction-relation -->pr current) equal?))
       (cond
         [(null? next) (list observed (terminal-kind-pr current-core))]
         [(zero? remaining) (list observed 'timeout)]
         [(null? (cdr next)) (loop (car next) (sub1 remaining))]
         [else
          (error 'obs-eval-pr
                 "nondeterministic reduction from ~e to ~e"
                 current
                 next)])])))

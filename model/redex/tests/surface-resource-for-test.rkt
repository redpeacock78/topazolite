#lang racket

(require rackunit
         racket/list
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (compile source)
  (compile-source/string 'src source))

(define (trace-compiled result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (λ ()
     (define run
       (bounded-trace-g2
        (inject-g2m (erase-core (compiled-execution-core result)))
        10000))
     (check-equal? (execution-outcome run) 'terminal)
     (define configurations (execution-configs run))
     (for ([configuration (in-list configurations)] [index (in-naturals)])
       (define row
         (runtime-row configuration (compiled-callables result)
                      (compiled-type result)))
       (check-not-false row (format "config ~a に runtime-row がある" index))
       (check-true
        (and row (config-ok? configuration (compiled-callables result)
                              (compiled-type result) row))
        (format "config ~a が config-ok? を満たす" index)))
     configurations)))

(define (trace-surface source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a" (diagnostic-id result))
                  "compiled result expected"))
  (and (compiled? result) (trace-compiled result)))

(define (check-accepted source expected-type expected-value)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a" (diagnostic-id result))
                  "compiled result expected"))
  (when (compiled? result)
    (check-equal? (compiled-type result) expected-type)
    (define configurations (trace-compiled result))
    (match (last configurations)
      [`(cfg ,value ,_heap ,_states ,_tokens ,_events)
       (check-equal? value expected-value)]
      [other (fail-check (format "terminal config expected, got ~s" other))])
    configurations))

(define (check-rejected source expected-id)
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)))

(define (config-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (token-state configuration token)
  (define entry (assoc token (config-tokens configuration)))
  (and entry (second entry)))

(define (rule-between before after)
  (for/or ([step (in-list (raw-steps-g2/named before))])
    (and (equal? (second step) after) (first step))))

(define (check-terminal-ledger configurations expected-token-count [carried '()])
  (define terminal (last configurations))
  (define tokens (config-tokens terminal))
  (check-equal? (length tokens) expected-token-count)
  (for ([entry (in-list tokens)])
    (check-equal? (second entry)
                  (if (member (first entry) carried) 'Available 'Dropped)))
  (define drops
    (append*
     (for/list ([before (in-list configurations)]
                [after (in-list (cdr configurations))])
       (for/list ([entry (in-list (config-tokens after))]
                  #:when (and (eq? (second entry) 'Dropped)
                              (eq? (token-state before (first entry)) 'Available)))
         (list (first entry) (rule-between before after))))))
  (for ([entry (in-list tokens)]
        #:unless (member (first entry) carried))
    (define token-drops
      (filter (λ (drop) (equal? (first drop) (first entry))) drops))
    (check-equal? (length token-drops) 1
                  (format "~s は Available から Dropped へ一度だけ遷移する"
                          (first entry)))
    (when (= (length token-drops) 1)
      (check-not-false (second (first token-drops))
                       "drop 規則を trace から特定できる"))))

(test-case "S1 Res を型注釈に書けて資源 List を注釈つき let で作れる"
  (define source
    "let xs: List<Owned<Res>> = cons(acquire(1), cons(acquire(2), nil()))\n()")
  (define configurations (check-accepted source 'Unit 'unit))
  (check-terminal-ledger configurations 2 '()))

(test-case "S2 利用者による Res の宣言は予約名の衝突として拒否する"
  (check-rejected "type Res = Int\n()" "E-SUR-011")
  (check-rejected "trait Res { }\n()" "E-SUR-023")
  (check-rejected "type Res =\n  | mk\n()" "E-SUR-028"))

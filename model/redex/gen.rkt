#lang racket

(require racket/match
         racket/runtime-path
         racket/string
         redex/reduction-semantics
         "elaborate.rkt"
         "lang.rkt"
         "machine.rkt"
         "typing.rkt")

(provide G1gen
         (struct-out bounds)
         (struct-out execution)
         (struct-out search-counts)
         read-bounds
         call-with-search-seed
         make-search-counts
         prepare-elaborable
         note-accepted!
         elaboration-result
         bounded-trace
         config-core
         config-heap
         config-states
         config-events
         config-places
         runtime-row
         row-subset?)

;; Every generated form is a closed UCore term.  Separate nonterminals make the
;; seven searches hit the rules they are intended to check instead of spending
;; the discard budget on arbitrary, overwhelmingly ill-typed syntax.
(define-extended-language G1gen UCore
  (gn ::= -2 -1 0 1 2 7)
  (g-bool ::= (Construct true (Types))
              (Construct false (Types)))
  (gt ::= (TypeMake Int)
          (TypeMake (Spec List Int))
          (TypeMake (Spec Option Bool))
          (TypeMake (Spec Result Int String))
          (LetType Box (TypeMake List)
                   (TypeMake (Spec Box Int))))
  (g-boundary ::=
              (Apply (Fn () Int () (Return gn)))
              (Apply (Fn () Int () (NarrativeExpr (Return gn))))
              (Apply (Fn ((flag Bool)) Int ()
                         (Eliminate flag
                          ((true () -> (Return gn))
                           (false () -> gn))))
                     g-bool))
  (g-productive ::=
                (Recur nats ((counter Int)) Unit ((Yield Int))
                       (Yield counter
                              (Apply nats (Apply add counter 1)))
                       (Apply nats gn)))
  (g-own ::=
         (Let item (Apply acquire gn) unit)
         (Let item (Apply acquire gn) (Move item))
         (Let item (Apply acquire gn) (Drop item))
         (Let item (Apply acquire gn)
              (Let ignored (Drop item) (Drop item)))
         (Let item (Apply acquire gn)
              (Let saved (Move item) (Move item)))
         (Apply (Fn () Int (Own)
                    (Let item (Apply acquire gn) (Return gn)))))
  (g-type ::= gt)
  (ga-list ::= (Construct nil (Types Int))
               (Construct cons (Types Int) gn ga-list))
  (g-analysis ::=
              gn
              (Apply add gn gn)
              (Yield gn unit)
              (Recur constant () Int () gn gn)
              (Recur loop ((items (List Int))) Int ()
                     (Eliminate items
                      ((nil () -> 0)
                       (cons (head tail) -> (Apply loop tail))))
                     (Apply loop ga-list))
              g-productive)
  (g ::= gn
         (Apply add gn gn)
         (Apply sub gn gn)
         (Apply mul gn gn)
         (Apply lt gn gn)
         (Apply le gn gn)
         (Apply eq gn gn)
         (Let value gn value)
         (Apply (Fn ((argument Int)) Int () argument) gn)
         (Apply (Curry add gn) gn)
         g-bool
         ga-list
         unit
         (Drop (Apply acquire gn))
         (Yield gn unit)
         (Suspend unit)
         (Recur constant () Int () gn gn)
         (Recur loop ((items (List Int))) Int ()
                (Eliminate items
                 ((nil () -> 0)
                  (cons (head tail) -> (Apply loop tail))))
                (Apply loop ga-list))
         g-boundary
         g-own
         g-type))

(struct bounds (attempts term-depth fuel observation-depth discard-limit seed)
  #:transparent)
(struct execution (configs outcome) #:transparent)
(struct search-counts (accepted discarded limit) #:mutable #:transparent)

(define-runtime-path readme-path "README.md")

(define (read-setting settings key)
  (hash-ref settings key
            (lambda ()
              (error 'read-bounds "README setting is missing: ~a" key))))

(define (read-bounds)
  (define settings
    (call-with-input-file readme-path
      (lambda (input)
        (for/fold ([found (hash)])
                  ([line (in-lines input)])
          (match (regexp-match #px"^\\|\\s*([^|]+?)\\s*\\|\\s*([0-9]+)\\s*\\|$"
                               line)
            [(list _ key value)
             (hash-set found (string-trim key) (string->number value))]
            [_ found])))))
  (bounds (read-setting settings "redex-check 試行数")
          (read-setting settings "生成項の深さ上限")
          (read-setting settings "評価 fuel")
          (read-setting settings "観測深度上限")
          (read-setting settings "discard 上限")
          (read-setting settings "乱数 seed")))

(define (call-with-search-seed limits thunk)
  (define generator (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator generator])
    (random-seed (bounds-seed limits)))
  (parameterize ([current-pseudo-random-generator generator]
                 [redex-pseudo-random-generator generator])
    (thunk)))

(define (make-search-counts limits)
  (search-counts 0 0 (bounds-discard-limit limits)))

(define elaboration-cache (make-hash))
(define trace-cache (make-hash))

(define (elaboration-result source)
  (hash-ref! elaboration-cache source (lambda () (elab source))))

(define (prepare-elaborable counts source)
  (match (elaboration-result source)
    [(list _ _ _ _) source]
    [_
     (set-search-counts-discarded!
      counts (add1 (search-counts-discarded counts)))
     (when (> (search-counts-discarded counts)
              (search-counts-limit counts))
       (error 'redex-check "elaboration discard limit exceeded"))
     ;; This is deliberately outside G1gen's generated nonterminals, so Redex
     ;; treats it as a generation failure rather than a passing property case.
     '(discarded-elaboration)]))

(define (note-accepted! counts)
  (set-search-counts-accepted!
   counts (add1 (search-counts-accepted counts))))

(define (config-core configuration)
  (match-define `(cfg ,core ,_ ,_ ,_) configuration)
  core)

(define (config-heap configuration)
  (match-define `(cfg ,_ ,heap ,_ ,_) configuration)
  heap)

(define (config-states configuration)
  (match-define `(cfg ,_ ,_ ,states ,_) configuration)
  states)

(define (config-events configuration)
  (match-define `(cfg ,_ ,_ ,_ ,events) configuration)
  events)

(define (config-places configuration)
  (for/list ([entry (in-list (config-heap configuration))])
    (list (first entry) 'Res)))

(define (runtime-row configuration callables type)
  (core-check-row (config-core configuration)
                  (config-places configuration)
                  callables
                  type))

(define (row-subset? left right)
  (term (row-⊆ ,left ,right)))

(define (bounded-trace initial fuel)
  (hash-ref!
   trace-cache
   (list initial fuel)
   (lambda ()
     (let loop ([current initial]
                [remaining fuel]
                [reversed-configs '()])
       (define configs (cons current reversed-configs))
       (define successors
         (remove-duplicates
          (apply-reduction-relation -->g1 current)
          equal?))
       (cond
         [(null? successors)
          (execution (reverse configs) 'terminal)]
         [(zero? remaining)
          (execution (reverse configs) 'timeout)]
         [(null? (cdr successors))
          (loop (car successors) (sub1 remaining) configs)]
         [else
          (error 'bounded-trace
                 "nondeterministic reduction from ~e to ~e"
                 current
                 successors)])))))

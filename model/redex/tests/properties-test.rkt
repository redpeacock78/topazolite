#lang racket

(require racket/list
         racket/match
         racket/set
         rackunit
         redex/reduction-semantics
         "../classify.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../obs.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define limits (read-bounds))

(define (artifact source)
  (match (elaboration-result source)
    [(list core type row callables)
     (values core type row callables)]
    [other (error 'properties-test "prepared term no longer elaborates: ~e"
                  other)]))

(define (successors configuration)
  (remove-duplicates
   (apply-reduction-relation -->g1 configuration)
   equal?))

(define (table-ref table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

(define (configuration-domain configuration)
  (list->set (map first (config-heap configuration))))

(define (adjacent-configs configs)
  (for/list ([before (in-list configs)]
             [after (in-list (cdr configs))])
    (list before after)))

(define (value-config? configuration)
  (redex-match? G1m v (config-core configuration)))

(define (ownership-error-config? configuration)
  (redex-match? G1m (Error p) (config-core configuration)))

(define (permitted-perform-config? configuration declared-row)
  (match (config-core configuration)
    [`(Perform ,operation ,value)
     (and (redex-match? G1m v value)
          (term (row-∈ ,operation ,declared-row)))]
    [_ #f]))

(define (allowed-terminal? configuration declared-row)
  (or (value-config? configuration)
      (ownership-error-config? configuration)
      (permitted-perform-config? configuration declared-row)))

(define (preservation? source)
  (define-values (core type _declared-row callables) (artifact source))
  (define result
    (bounded-trace (inject core) (bounds-fuel limits)))
  (for/and ([pair (in-list (adjacent-configs
                            (execution-configs result)))])
    (define before (first pair))
    (define after (second pair))
    (define before-row (runtime-row before callables type))
    (define after-row (runtime-row after callables type))
    (and before-row
         after-row
         (config-ok? before callables type before-row)
         (config-ok? after callables type after-row)
         (row-subset? after-row before-row)
         (subset? (configuration-domain before)
                  (configuration-domain after)))))

(define (progress? source)
  (define-values (core type declared-row callables) (artifact source))
  (define initial (inject core))
  (define initial-row (runtime-row initial callables type))
  (define result
    (bounded-trace initial (bounds-fuel limits)))
  (and initial-row
       (config-ok? initial callables type initial-row)
       (for/and ([configuration (in-list (execution-configs result))])
         (or (pair? (successors configuration))
             (allowed-terminal? configuration declared-row)))))

(define (origin-ok? core)
  (equal? (term (verify-origins ,R0 ,core)) 'ok))

(define (origin-integrity? source)
  (define-values (core _type _declared-row _callables) (artifact source))
  (define result
    (bounded-trace (inject core) (bounds-fuel limits)))
  (and (origin-ok? core)
       (for/and ([configuration (in-list (execution-configs result))])
         (and (origin-ok? (config-core configuration))
              ;; Property 3 ranges over the whole configuration, including
              ;; values retained in H and the observation trace.
              (for/and ([entry (in-list (config-heap configuration))])
                (origin-ok? (second entry)))
              (for/and ([event (in-list (config-events configuration))])
                (match event
                  [`(obs ,value) (origin-ok? value)]
                  [`(fin ,_) #t]
                  [_ #f]))))))

(define (collect-return-handlers tree)
  (define here
    (match tree
      [`(Handle ,operation (,_ -> ,_) ,_)
       #:when (match operation [`(Return ,_ ,_) #t] [_ #f])
       (list operation)]
      [_ '()]))
  (append here
          (if (list? tree)
              (append-map collect-return-handlers tree)
              '())))

(define (single-step-core core)
  (match (successors `(cfg ,core () () ()))
    [(list next) (config-core next)]
    [other (error 'single-step-core "expected one step, got ~e" other)]))

(define (boundary-safe? source)
  (define-values (core _type _declared-row _callables) (artifact source))
  (define operations (collect-return-handlers core))
  (and (pair? operations)
       (for/and ([operation (in-list operations)])
         (match operation
           [`(Return ,boundary Int)
            (define different-boundary
              `(Return boundary-that-does-not-match Int))
            (define different-type `(Return ,boundary Bool))
            (and
             ;; Equal boundary and type is handled.
             (equal?
              (single-step-core
               `(Handle ,operation (caught -> caught)
                        (Perform ,operation 9)))
              9)
             ;; Either component differing must propagate unchanged.
             (equal?
              (single-step-core
               `(Handle ,operation (caught -> caught)
                        (Perform ,different-boundary 9)))
              `(Perform ,different-boundary 9))
             (equal?
              (single-step-core
               `(Handle ,operation (caught -> caught)
                        (Perform ,different-type (Construct Bool true))))
              `(Perform ,different-type (Construct Bool true))))]
           [_ #f]))))

(define (collect-type-reps tree)
  (define here
    (match tree
      [(and representation `(TypeRep ,_ ,_ ,_)) (list representation)]
      [_ '()]))
  (append here
          (if (list? tree)
              (append-map collect-type-reps tree)
              '())))

(define (canonical-type-rep? representation)
  (match representation
    [`(TypeRep (Reserved ,id) ,type-form ,kind)
     (and (equal? kind (term (kindOf ,type-form)))
          (equal? (assoc type-form Δ0)
                  (list type-form representation))
          (equal? (assoc id R0)
                  (list id `(type ,type-form))))]
    [`(TypeRep (Derived (Reserved o-type-narrative) (Make ,made))
               ,type-form ,kind)
     (and (equal? made type-form)
          (equal? kind (term (kindOf ,type-form)))
          (equal? (assoc 'o-type-narrative R0)
                  '(o-type-narrative typeNarrative)))]
    [_ #f]))

(define (type-info-integrity? source)
  (define-values (core _type _declared-row _callables) (artifact source))
  (define generated (collect-type-reps core))
  (and (pair? generated)
       (andmap canonical-type-rep?
               (append generated (map second Δ0)))))

(define (conservative-analysis? source)
  (define-values (core _type declared-row callables) (artifact source))
  (match (classify core '() callables)
    [`(Finite ,_)
     (define result
       (bounded-trace (inject core) (bounds-fuel limits)))
     (and (eq? (execution-outcome result) 'terminal)
          (allowed-terminal? (last (execution-configs result))
                             declared-row))]
    [`(Productive ,_)
     (for/and ([depth (in-range
                       (add1 (bounds-observation-depth limits)))])
       (match (obs-eval core depth (bounds-fuel limits))
         [(list observed 'observed) (= (length observed) depth)]
         [_ #f]))]
    ['Unknown #t]
    [_ #f]))

(define (tree-count tree wanted)
  (+ (if (equal? tree wanted) 1 0)
     (if (list? tree)
         (for/sum ([part (in-list tree)])
           (tree-count part wanted))
         0)))

(define (event-prefix? before after)
  (and (<= (length before) (length after))
       (equal? before (take after (length before)))))

(define (affine-safety? source)
  (define-values (core _type _declared-row _callables) (artifact source))
  (define result
    (bounded-trace (inject core) (bounds-fuel limits)))
  (define configs (execution-configs result))
  (define pairs (adjacent-configs configs))
  (define places
    (remove-duplicates
     (append-map (lambda (configuration)
                   (map first (config-states configuration)))
                 configs)))
  (and
   (eq? (execution-outcome result) 'terminal)
   (for/and ([pair (in-list pairs)])
     (event-prefix? (config-events (first pair))
                    (config-events (second pair))))
   (for/and ([place (in-list places)])
     (define successful-moves 0)
     (define drops 0)
     (define valid-transitions?
       (for/and ([pair (in-list pairs)])
         (define before (first pair))
         (define after (second pair))
         (define before-state
           (table-ref (config-states before) place))
         (define after-state
           (table-ref (config-states after) place))
         (when (and (eq? before-state 'Available)
                    (eq? after-state 'Moved))
           (set! successful-moves (add1 successful-moves)))
         (when (and (eq? before-state 'Available)
                    (eq? after-state 'Dropped))
           (set! drops (add1 drops)))
         (define new-errors
           (- (tree-count (config-core after) `(Error ,place))
              (tree-count (config-core before) `(Error ,place))))
         (define removed-invalid-moves
           (if (memq before-state '(Moved Dropped))
               (- (tree-count (config-core before) `(Move ,place))
                  (tree-count (config-core after) `(Move ,place)))
               0))
         (and
          (or (and (not before-state) (eq? after-state 'Available))
              (equal? before-state after-state)
              (and (eq? before-state 'Available)
                   (memq after-state '(Moved Dropped))))
          (or (<= new-errors 0)
              (and (memq before-state '(Moved Dropped))
                   (> (tree-count (config-core before) `(Move ,place))
                      (tree-count (config-core after) `(Move ,place)))))
          (or (<= removed-invalid-moves 0)
              (positive? new-errors))
          (or (not (and (eq? before-state 'Available)
                        (eq? after-state 'Dropped)))
              (= (add1 (tree-count (config-events before)
                                   `(fin ,place)))
                 (tree-count (config-events after)
                             `(fin ,place)))))))
     (and valid-transitions?
          (<= successful-moves 1)
          (<= drops 1)
          (<= (tree-count (config-events (last configs))
                          `(fin ,place))
              1)
          (not (eq? (table-ref (config-states (last configs)) place)
                    'Available))))))

(define-syntax-rule (bounded-check test-name pattern property)
  (test-case test-name
    (define counts (make-search-counts limits))
    (define result
      (call-with-search-seed
       limits
       (lambda ()
         (redex-check
          G1gen pattern #:ad-hoc
          (begin
            (note-accepted! counts)
            (property (term pattern)))
          #:attempts (bounds-attempts limits)
          #:attempt-size (lambda (_attempt)
                           (bounds-term-depth limits))
          #:prepare (lambda (source)
                      (prepare-elaborable counts source))
          #:print? #f))))
    (check-equal? result #t)
    (check-true (positive? (search-counts-accepted counts)))
    (printf "~a: attempts=~a accepted=~a discard=~a seed=~a\n"
            test-name
            (bounds-attempts limits)
            (search-counts-accepted counts)
            (search-counts-discarded counts)
            (bounds-seed limits))))

(bounded-check
 "EFF-001/OWN-001: property 1 preservation"
 g preservation?)

(bounded-check
 "EFF-001/RET-003: property 2 progress modulo effects"
 g progress?)

(bounded-check
 "NAR-001/NAR-002: property 3 origin integrity"
 g origin-integrity?)

(bounded-check
 "RET-002: property 4 boundary safety"
 g-boundary boundary-safe?)

(bounded-check
 "TYP-001: property 5 TypeRep provenance"
 g-type type-info-integrity?)

(bounded-check
 "REC-001/REC-002: property 6 conservative analysis"
 g-analysis conservative-analysis?)

(bounded-check
 "OWN-001/OWN-002/OWN-003: property 7 affine safety"
 g-own affine-safety?)

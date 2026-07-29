#lang racket

(require racket/list
         racket/match
         racket/set
         rackunit
         redex/reduction-semantics
         "../classify.rkt"
         "../compat.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../obs.rkt"
         "../origins.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(provide preservation-g2?
         progress-g2?
         initial-origin-ok?
         origin-integrity-g2?
         boundary-safe-g2?
         type-info-integrity-g2?
         conservative-analysis-g2?
         affine-safety-g2?)

(define limits (read-bounds))

(define (artifact source)
  (match (elaboration-result source)
    [(list core type row callables)
     (values core type row callables)]
    [other (error 'properties-test "prepared term no longer elaborates: ~e"
                  other)]))

(define (successors-g1 configuration)
  (remove-duplicates
   (apply-reduction-relation -->g1 configuration)
   equal?))

(define (successors-g2 configuration)
  (remove-duplicates
   (apply-reduction-relation -->g2 configuration)
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

(define (value-config-g1? configuration)
  (redex-match? G1m v (config-core configuration)))

(define (value-config-g2? configuration)
  (redex-match? G2m v (config-core configuration)))

(define (ownership-error-config-g1? configuration)
  (redex-match? G1m (Error p) (config-core configuration)))

(define (ownership-error-config-g2? configuration)
  (redex-match? G2m (Error p) (config-core configuration)))

(define (permitted-perform-config-g1? configuration declared-row)
  (match (config-core configuration)
    [`(Perform ,operation ,value)
     (and (redex-match? G1m v value)
          (term (row-∈ ,operation ,declared-row)))]
    [_ #f]))

(define (permitted-perform-config-g2? configuration declared-row)
  (match (config-core configuration)
    [`(Perform ,operation ,value)
     (and (redex-match? G2m v value)
          (term (row-∈ ,operation ,declared-row)))]
    [_ #f]))

(define (allowed-terminal-g1? configuration declared-row)
  (or (value-config-g1? configuration)
      (ownership-error-config-g1? configuration)
      (permitted-perform-config-g1? configuration declared-row)))

(define (allowed-terminal-g2? configuration declared-row)
  (or (value-config-g2? configuration)
      (ownership-error-config-g2? configuration)
      (permitted-perform-config-g2? configuration declared-row)))

(define (preservation/using source inject-core trace)
  (define-values (core type _declared-row callables) (artifact source))
  (define result
    (trace (inject-core core) (bounds-fuel limits)))
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

(define (preservation? source)
  (preservation/using source inject bounded-trace))

(define (preservation-g2? source)
  (preservation/using source inject-g2 bounded-trace-g2))

(define (progress/using source inject-core trace next-configs allowed-terminal?)
  (define-values (core type declared-row callables) (artifact source))
  (define initial (inject-core core))
  (define initial-row (runtime-row initial callables type))
  (define result
    (trace initial (bounds-fuel limits)))
  (and initial-row
       (config-ok? initial callables type initial-row)
       (for/and ([configuration (in-list (execution-configs result))])
         (or (pair? (next-configs configuration))
             (allowed-terminal? configuration declared-row)))))

(define (progress? source)
  (progress/using source inject bounded-trace
                  successors-g1 allowed-terminal-g1?))

(define (progress-g2? source)
  (progress/using source inject-g2 bounded-trace-g2
                  successors-g2 allowed-terminal-g2?))

(define (origin-ok? core)
  (equal? (term (verify-origins ,R0 ,core)) 'ok))

;; G2d: 初期成果物には UVal と RVal が現れない。到達成果物では validate が
;; 作るため、層ごとに入口を変える。
;; このファイルは req-coverage の g2a-tests に含まれる。裸の RFN-00x を書くと
;; G2a の期待 ID 集合を超えて gate が落ちる。要件 ID は
;; properties-refine-test.rkt 側に置く。
(define (initial-origin-ok? core)
  (equal? (term (verify-initial-origins ,R0 ,core)) 'ok))

(define (origin-integrity/using source inject-core trace)
  (define-values (core _type _declared-row _callables) (artifact source))
  (define result
    (trace (inject-core core) (bounds-fuel limits)))
  (and (initial-origin-ok? core)
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

(define (origin-integrity? source)
  (origin-integrity/using source inject bounded-trace))

(define (origin-integrity-g2? source)
  (origin-integrity/using source inject-g2 bounded-trace-g2))

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

(define (single-step-core/using next-configs core)
  (match (next-configs `(cfg ,core () () ()))
    [(list next) (config-core next)]
    [other (error 'single-step-core "expected one step, got ~e" other)]))

(define (boundary-safe/using source next-configs)
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
              (single-step-core/using
               next-configs
               `(Handle ,operation (caught -> caught)
                        (Perform ,operation 9)))
              9)
             ;; Either component differing must propagate unchanged.
             (equal?
              (single-step-core/using
               next-configs
               `(Handle ,operation (caught -> caught)
                        (Perform ,different-boundary 9)))
              `(Perform ,different-boundary 9))
             (equal?
              (single-step-core/using
               next-configs
               `(Handle ,operation (caught -> caught)
                        (Perform ,different-type (Construct Bool true))))
              `(Perform ,different-type (Construct Bool true))))]
           [_ #f]))))

(define (boundary-safe? source)
  (boundary-safe/using source successors-g1))

(define (boundary-safe-g2? source)
  (boundary-safe/using source successors-g2))

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

(define type-info-integrity-g2? type-info-integrity?)

(define (conservative-analysis/using source inject-core trace
                                     allowed-terminal? observe)
  (define-values (core _type declared-row callables) (artifact source))
  (match (classify core '() callables)
    [`(Finite ,_)
     (define result
       (trace (inject-core core) (bounds-fuel limits)))
     (and (eq? (execution-outcome result) 'terminal)
          (allowed-terminal? (last (execution-configs result))
                             declared-row))]
    [`(Productive ,_)
     (for/and ([depth (in-range
                       (add1 (bounds-observation-depth limits)))])
       (match (observe core depth (bounds-fuel limits))
         [(list observed 'observed) (= (length observed) depth)]
         [_ #f]))]
    ['Unknown #t]
    [_ #f]))

(define (conservative-analysis? source)
  (conservative-analysis/using source inject bounded-trace
                               allowed-terminal-g1? obs-eval))

(define (conservative-analysis-g2? source)
  (conservative-analysis/using source inject-g2 bounded-trace-g2
                               allowed-terminal-g2? obs-eval-g2))

(define (tree-count tree wanted)
  (+ (if (equal? tree wanted) 1 0)
     (if (list? tree)
         (for/sum ([part (in-list tree)])
           (tree-count part wanted))
         0)))

(define (event-prefix? before after)
  (and (<= (length before) (length after))
       (equal? before (take after (length before)))))

(define (affine-safety/using source inject-core trace)
  (define-values (core _type _declared-row _callables) (artifact source))
  (define result
    (trace (inject-core core) (bounds-fuel limits)))
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

(define (affine-safety? source)
  (affine-safety/using source inject bounded-trace))

(define (affine-safety-g2? source)
  (affine-safety/using source inject-g2 bounded-trace-g2))

(define (contains-record? tree)
  (cond
    [(and (pair? tree) (memq (car tree) '(Rec Record))) #t]
    [(pair? tree)
     (or (contains-record? (car tree))
         (contains-record? (cdr tree)))]
    [else #f]))

(module+ test
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

  (define (row-001? source)
    (match (elaboration-result source)
      [`(err (const-record-residual ,residual))
       (pair? residual)]
      [_ #f]))

  (define (row-002? source)
    (match (elaboration-result source)
      [(list core 'Unit row callables)
       (and (equal? (core-type-of core '() callables) `(Unit ,row))
            (match (run-g2 (inject-g2 core) (bounds-fuel limits))
              [`(cfg unit ,_ ,_ ,_) #t]
              [_ #f])
            ;; Width compatibility is connected to checking, but remains
            ;; distinct from definitional equality.
            (core-check '(Rec ((a imm 1) (b mut unit)))
                        '() '() '(Record ((a Int imm))) '())
            (not (type-equiv?
                  '(Record ((a Int imm) (b Unit mut)))
                  '(Record ((a Int imm)))))
            ;; An incompatible required field is rejected.
            (match (elaboration-result
                    '(Let (record let (Record ((a Bool imm))))
                          (Rec ((a imm 1)))
                          record))
              [`(err (type-mismatch ,_ ,_)) #t]
              [_ #f]))]
      [_ #f]))

  (define (row-003? core)
    (and
     (equal? (core-type-of core '() '())
             '((Record ((a Int imm))) ()))
     ;; Never branches do not constrain the structural intersection.
     (equal?
      (core-type-of
       '(Eliminate (Construct Bool true)
          ((true () -> (Rec ((a imm 1))))
           (false () -> (Perform (Return boundary Int) 1))))
       '() '())
      '((Record ((a Int imm))) ((Return boundary Int))))))

  (define (row-004? core)
    (and
     (equal? (core-type-of core '() '())
             '((Record ((a Int mut))) ()))
     (redex-match? G2m v core)
     ;; Mutable fields are invariant; immutable fields remain covariant.
     (not (compat? '(Record ((a Never mut)))
                   '(Record ((a Int mut)))))
     (compat? '(Record ((a Never imm)))
              '(Record ((a Int imm))))
     ;; G1's affine restriction remains in force for record fields.
     (equal? (core-type-of '(Rec ((a imm (resource 1)))) '() '())
             'ill-typed)))

  (define-syntax-rule (bounded-row-check test-name pattern property)
    (test-case test-name
      (define counts (make-search-counts limits))
      (define record-accepted (box 0))
      (define result
        (call-with-search-seed
         limits
         (lambda ()
           (redex-check
            G2gen pattern #:ad-hoc
            (begin
              (note-accepted! counts)
              (when (contains-record? (term pattern))
                (set-box! record-accepted
                          (add1 (unbox record-accepted))))
              (property (term pattern)))
            #:attempts (bounds-attempts limits)
            #:attempt-size (lambda (_attempt)
                             (bounds-term-depth limits))
            #:print? #f))))
      (check-equal? result #t)
      (check-true (positive? (search-counts-accepted counts)))
      (check-true (positive? (unbox record-accepted)))
      (printf "~a: attempts=~a accepted=~a record-accepted=~a seed=~a\n"
              test-name
              (bounds-attempts limits)
              (search-counts-accepted counts)
              (unbox record-accepted)
              (bounds-seed limits))))

  (bounded-row-check "ROW-001: const rejects residual fields"
                     g-row-const row-001?)
  (bounded-row-check "ROW-002: let preserves compatible residual fields"
                     g-row-let row-002?)
  (bounded-row-check "ROW-003: branch merge is structural intersection"
                     g-row-merge row-003?)
  (bounded-row-check "ROW-004: mutable fields are invariant and inhabited"
                     g-row-mut row-004?))

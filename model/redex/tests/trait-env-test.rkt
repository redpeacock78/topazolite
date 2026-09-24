#lang racket

(require rackunit
         racket/set
         redex/reduction-semantics
         "../backend-matrix.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../traits.rkt")

(define (no-fail reason kind key)
  (error 'test "~s ~s ~s" reason kind key))

(define custom-env
  (make-trait-env
   #:trait (append trait-table
                   (list '(o-trait-env-test EnvTest root ((value Self imm)))))
   #:impl (append impl-table
                  (list '(o-impl-env-test impl-env-test impl EnvTest Int root)))
   #:intersect intersect-table
   #:scope scope-parent-table
   #:fail no-fail))

(define (custom-ledger)
  (make-trait-ledger custom-env #:fail no-fail))

(define scoped-env
  (make-trait-env #:trait trait-table
                  #:impl impl-table
                  #:intersect intersect-table
                  #:scope (append scope-parent-table '((child root)))
                  #:fail no-fail))

(define (scoped-ledger)
  (make-trait-ledger scoped-env #:fail no-fail))

(define no-intersect-env
  (make-trait-env #:trait trait-table
                  #:impl impl-table
                  #:intersect '()
                  #:scope scope-parent-table
                  #:fail no-fail))

(define (no-intersect-ledger)
  (make-trait-ledger no-intersect-env #:fail no-fail))

(define (user-impl-resolves?)
  (pair? (project-goal (current-Γ-pc0) '(root)
                       (make-goal '(Implements Int EnvTest)))))

(define (user-impl-core)
  '(Apply (PrimVal (Reserved o-impl-env-test) impl-env-test)
          (Rec ((value imm 1)))))

(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) 40)
    [`(cfg ,result () () () ()) result]
    [other (error 'run-g2-core "unexpected result: ~s" other)]))

(define (run-user-impl)
  (run-g2-core (user-impl-core)))

(define (proof-rep? value)
  (and (pair? value) (eq? (car value) 'ProofRep)))

(define (lowering-reason-for name)
  (define-values (status result)
    (lower/with-matrix `(PrimVal (Reserved o-impl-env-test) ,name)
                       'racket-cs backend-features))
  (and (eq? status 'capability)
       (capability-diagnostic-feature-id result)))

(test-case
 "canonical env matches the module tables"
 (check-equal? (trait-env-trait-rows canonical-trait-env) trait-table)
 (check-equal? (trait-env-impl-rows canonical-trait-env) impl-table)
 (check-equal? (trait-env-intersect-rows canonical-trait-env) intersect-table)
 (check-equal? (trait-env-scope-rows canonical-trait-env) scope-parent-table))

(test-case
 "indices agree with a linear scan"
 (for ([row (in-list trait-table)])
   (check-eq? (trait-row-by-name (trait-name row) canonical-trait-env) row)
   (check-eq? (trait-row-by-oid (trait-origin row) canonical-trait-env) row))
 (for ([row (in-list impl-table)])
   (check-eq? (impl-row-by-oid (impl-oid row) canonical-trait-env) row)
   (check-eq? (impl-row-by-name (impl-name row) canonical-trait-env) row)
   (check-equal? (impl-rows-by-trait (impl-trait-name row) canonical-trait-env)
                 (filter (λ (candidate)
                           (eq? (impl-trait-name candidate)
                                (impl-trait-name row)))
                         impl-table)))
 (for ([row (in-list intersect-table)])
   (check-eq? (intersect-row-by-oid (intersect-oid row) canonical-trait-env) row)
   (check-eq? (intersect-row-by-name (intersect-name row) canonical-trait-env) row))
 (check-equal?
  (list->seteq (trait-primitive-names canonical-trait-env))
  (trait-env-primitive-names canonical-trait-env))
 (for ([name (in-list (trait-primitive-names canonical-trait-env))])
   (check-true (trait-primitive-name? name canonical-trait-env))))

(test-case
 "index construction does not depend on row order"
 (define shuffled
   (make-trait-env #:trait (reverse trait-table)
                   #:impl (reverse impl-table)
                   #:intersect (reverse intersect-table)
                   #:scope scope-parent-table
                   #:fail no-fail))
 (for ([row (in-list trait-table)])
   (check-eq? (trait-row-by-name (trait-name row) shuffled) row))
 (for ([row (in-list impl-table)])
   (check-eq? (impl-row-by-name (impl-name row) shuffled) row))
 (for ([row (in-list intersect-table)])
   (check-eq? (intersect-row-by-name (intersect-name row) shuffled) row)))

(test-case
 "fail is called for a duplicate trait name"
 (define calls '())
 (define result
   (make-trait-env #:trait (append trait-table (list (first trait-table)))
                   #:impl impl-table
                   #:intersect intersect-table
                   #:scope scope-parent-table
                   #:fail (λ (reason kind key)
                            (set! calls (list reason kind key))
                            'failed)))
 (check-eq? result 'failed)
 (check-equal? calls
               (list 'surface-trait-name-collision 'trait-name
                     (trait-name (first trait-table)))))

(test-case
 "an impl row naming an undeclared trait is an internal error"
 (check-exn
  #rx"names an undeclared trait"
  (λ ()
    (make-trait-env
     #:trait trait-table
     #:impl (append impl-table
                    (list '(o-impl-test impl-test impl NoSuchTrait Int root)))
     #:intersect intersect-table
     #:scope scope-parent-table
     #:fail no-fail))))

(test-case
 "an intersect row out of canonical order is an internal error"
 (define row (first intersect-table))
 (check-exn
  #rx"not in canonical trait order"
  (λ ()
    (make-trait-env
     #:trait trait-table
     #:impl impl-table
     #:intersect (append intersect-table
                         (list (list 'o-intersect-test 'intersect-test
                                     (intersect-right row)
                                     (intersect-left row)
                                     (intersect-output row))))
     #:scope scope-parent-table
     #:fail no-fail))))

(test-case
 "instantiate-requirements keeps a nested Self label"
 (check-equal?
  (instantiate-requirements '((f (Record ((Self Self imm))) imm)) 'Int)
  '((f (Record ((Self Int imm))) imm))))

(test-case
 "a trait row may use Self as a record label"
 (define env
   (make-trait-env
    #:trait (append trait-table
                    (list '(o-trait-user-Foo Foo root
                            ((Self Int imm)
                             (g (Record ((Self Self imm))) imm)))))
    #:impl (append impl-table
                   (list '(o-impl-user-Foo-1 impl-user-Foo-1 impl Foo Bool root)))
    #:intersect intersect-table
    #:scope scope-parent-table
    #:fail no-fail))
 (define foo (trait-row-by-name 'Foo env))
 (check-equal? (trait-constant-name foo) 'Foo-trait)
 (check-equal?
  (instantiate-requirements (trait-template foo) 'Bool)
  '((Self Int imm) (g (Record ((Self Bool imm))) imm))))

(test-case
 "the canonical ledger reproduces R0 and gamma0"
 (check-equal? (trait-ledger-r0 canonical-trait-ledger) R0)
 (check-equal? (trait-ledger-gamma0 canonical-trait-ledger) Γ0))

(test-case
 "the parameter is dynamically scoped"
 (define custom (custom-ledger))
 (parameterize ([current-trait-ledger custom])
   (check-eq? (current-trait-ledger) custom)
   (check-eq? (current-trait-env) custom-env)
   (check-equal? (current-R0) (trait-ledger-r0 custom))
   (check-equal? (current-Γ0) (trait-ledger-gamma0 custom))
   (check-not-false (assoc 'o-impl-env-test (current-trait-r0-entries)))
   (check-not-false (assoc 'impl-env-test (current-trait-gamma0-entries)))
   (check-not-false (assoc 'impl-env-test (trait-global-bindings)))
   (parameterize ([current-trait-ledger canonical-trait-ledger])
     (check-eq? (current-trait-ledger) canonical-trait-ledger))
   (check-eq? (current-trait-ledger) custom))
 (check-eq? (current-trait-ledger) canonical-trait-ledger)
 ;; 例外で脱出しても既定へ戻る。
 (with-handlers ([symbol? void])
   (parameterize ([current-trait-ledger custom]) (raise 'boom)))
 (check-eq? (current-trait-ledger) canonical-trait-ledger))

(test-case
 "a trait row colliding with a kernel R0 key fails"
 (define calls '())
 (define env
   (make-trait-env #:trait (cons (list 'o-int 'Collide 'root '())
                                 trait-table)
                   #:impl impl-table
                   #:intersect intersect-table
                   #:scope scope-parent-table
                   #:fail no-fail))
 (check-eq? (make-trait-ledger env
                               #:fail (λ (reason kind key)
                                        (set! calls (list reason kind key))
                                        'failed))
            'failed)
 (check-equal? (second calls) 'origin-id))

(test-case
 "trait-origin-ok? rejects an R0 without the reserved narrative"
 (define stripped
   (for/list ([row (in-list R0)]
              #:unless (eq? (first row) 'o-language-narrative))
     row))
 (check-false (trait-origin-ok? stripped (first trait-table)
                                canonical-trait-env)))

(test-case
 "a custom ledger resolves a user impl through project-goal"
 (parameterize ([current-trait-ledger (custom-ledger)])
   (check-true (user-impl-resolves?))))

(test-case
 "a custom ledger runs the user impl primitive"
 (parameterize ([current-trait-ledger (custom-ledger)])
   (check-true (proof-rep? (run-user-impl)))))

(test-case
 "verify-origins reads R0 and the trait rows from the ledger"
 (parameterize ([current-trait-ledger (custom-ledger)])
   (define proof (run-user-impl))
   (check-equal? (term (verify-origins ,(current-R0) ,proof)) 'ok)
   (parameterize ([current-trait-ledger canonical-trait-ledger])
     (check-not-equal? (term (verify-origins ,(current-R0) ,proof)) 'ok))))

(test-case
 "current-Γ-pc0 follows the ledger and is built once per ledger"
 (check-equal? (current-Γ-pc0) Γ-pc0)
 (parameterize ([current-trait-ledger (custom-ledger)])
   (check-not-equal? (current-Γ-pc0) Γ-pc0)
   (check-eq? (current-Γ-pc0) (current-Γ-pc0))))

(test-case
 "lowering classifies custom primitives; trait entries exclude kernel names"
 (parameterize ([current-trait-ledger (custom-ledger)])
   (check-equal? (lowering-reason-for 'impl-env-test) 'trait-primitive)
   (for ([name (in-list '(add sub mul lt le eq acquire))])
     (check-false (assq name (current-trait-gamma0-entries))))))

(test-case
 "scope-visible? follows the ledger scope rows"
 (parameterize ([current-trait-ledger (scoped-ledger)])
   (check-true (scope-visible? 'root '(child))))
 (check-false (scope-visible? 'root '(child))))

(test-case
 "compose-candidates reads intersect rows from the ledger"
 (define goal (make-goal '(Implements Int PrintableSizable)))
 (check-equal? (length (project-goal (current-Γ-pc0) '(root) goal)) 1)
 (parameterize ([current-trait-ledger (no-intersect-ledger)])
   (check-equal? (project-goal (current-Γ-pc0) '(root) goal) '())))

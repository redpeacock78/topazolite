#lang racket

(require rackunit
         racket/set
         redex/reduction-semantics
         (only-in "../gen.rkt" elaboration-result bounded-trace-g2 execution-configs)
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
 "call-with-trait-ledger is dynamically scoped"
 (define custom (custom-ledger))
 (check-equal? (call-with-trait-ledger custom (λ () 42)) 42)
 (call-with-trait-ledger
  custom
  (λ ()
   (check-eq? (current-trait-ledger) custom)
   (check-eq? (current-trait-env) custom-env)
   (check-equal? (current-R0) (trait-ledger-r0 custom))
   (check-equal? (current-Γ0) (trait-ledger-gamma0 custom))
   (check-not-false (assoc 'o-impl-env-test (current-trait-r0-entries)))
   (check-not-false (assoc 'impl-env-test (current-trait-gamma0-entries)))
   (check-not-false (assoc 'impl-env-test (trait-global-bindings)))
   (call-with-trait-ledger
    canonical-trait-ledger
    (λ () (check-eq? (current-trait-ledger) canonical-trait-ledger)))
   (check-eq? (current-trait-ledger) custom)))
 (check-eq? (current-trait-ledger) canonical-trait-ledger)
 ;; 例外で脱出しても既定へ戻る。
 (with-handlers ([symbol? void])
   (call-with-trait-ledger custom (λ () (raise 'boom))))
 (check-eq? (current-trait-ledger) canonical-trait-ledger))

;; spec §5.2。Redex の metafunction は項だけを鍵にキャッシュするので、
;; 同じ項を異なる台帳で走らせたときに結果が混ざらないことを両方の順で見る。
(test-case
 "the same term reduces per ledger in either order"
 (define core (inject-g2 (user-impl-core)))
 (define (proof-result? r)
   (match r [`(cfg (ProofRep ,_ ,_) ,_ ...) #t] [_ #f]))
 (define custom (custom-ledger))
 (check-true (proof-result? (call-with-trait-ledger custom (λ () (run-g2 core 40)))))
 (check-false (proof-result? (run-g2 core 40)))
 (check-true (proof-result? (call-with-trait-ledger custom (λ () (run-g2 core 40))))))

(test-case
 "reading a custom ledger with Redex caching enabled is an error"
 (check-false (parameter? current-trait-ledger))
 (call-with-trait-ledger
  (custom-ledger)
  (λ ()
    (check-exn #rx"custom ledger read with Redex caching enabled"
               (λ () (parameterize ([caching-enabled? #t])
                       (current-trait-ledger))))))
 (call-with-trait-ledger
  canonical-trait-ledger
  (λ ()
    (check-eq? (parameterize ([caching-enabled? #t]) (current-trait-ledger))
               canonical-trait-ledger))))

(test-case
 "call-with-trait-ledger turns Redex caching off only for a custom ledger"
 (define outer (caching-enabled?))
 (call-with-trait-ledger canonical-trait-ledger
                         (λ () (check-equal? (caching-enabled?) outer)))
 (call-with-trait-ledger (custom-ledger) (λ () (check-false (caching-enabled?))))
 (parameterize ([caching-enabled? #f])
   (call-with-trait-ledger canonical-trait-ledger
                           (λ () (check-false (caching-enabled?)))))
 ;; 既定の台帳の外側から custom の台帳へ入り、抜けると外側へ戻る。
 (parameterize ([caching-enabled? #t])
   (call-with-trait-ledger
    canonical-trait-ledger
    (λ ()
      (check-true (caching-enabled?))
      (call-with-trait-ledger (custom-ledger) (λ () (check-false (caching-enabled?))))
      (check-true (caching-enabled?))
      (check-eq? (current-trait-ledger) canonical-trait-ledger))))
 (check-equal? (caching-enabled?) outer))

;; gen.rkt の 2 つの表も項（原文）だけを鍵にするので、同じ規律に従うことを見る。
(test-case
 "gen.rkt caches follow the ledger"
 (define custom (custom-ledger))
 (define (elaborated?)
   (match (elaboration-result 'impl-env-test) [(list _ _ _ _) #t] [_ #f]))
 (check-true (call-with-trait-ledger custom elaborated?))
 (check-false (elaborated?))
 (check-true (call-with-trait-ledger custom elaborated?))
 (define core (inject-g2 (user-impl-core)))
 (define (traced-proof?)
   (match (last (execution-configs (bounded-trace-g2 core 40)))
     [`(cfg (ProofRep ,_ ,_) ,_ ...) #t] [_ #f]))
 (check-true (call-with-trait-ledger custom traced-proof?))
 (check-false (traced-proof?))
 (check-true (call-with-trait-ledger custom traced-proof?)))

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
 (check-true (call-with-trait-ledger (custom-ledger) user-impl-resolves?)))

(test-case
 "a custom ledger runs the user impl primitive"
 (check-true (call-with-trait-ledger (custom-ledger)
                                     (λ () (proof-rep? (run-user-impl))))))

(test-case
 "verify-origins reads R0 and the trait rows from the ledger"
 (call-with-trait-ledger
  (custom-ledger)
  (λ ()
    (define proof (run-user-impl))
    (check-equal? (term (verify-origins ,(current-R0) ,proof)) 'ok)
    (call-with-trait-ledger
     canonical-trait-ledger
     (λ ()
       (check-not-equal? (term (verify-origins ,(current-R0) ,proof)) 'ok))))))

(test-case
 "current-Γ-pc0 follows the ledger and is built once per ledger"
 (check-equal? (current-Γ-pc0) Γ-pc0)
 (call-with-trait-ledger
  (custom-ledger)
  (λ ()
    (check-not-equal? (current-Γ-pc0) Γ-pc0)
    (check-eq? (current-Γ-pc0) (current-Γ-pc0)))))

(test-case
 "lowering classifies custom primitives; trait entries exclude kernel names"
 (call-with-trait-ledger
  (custom-ledger)
  (λ ()
    (check-equal? (lowering-reason-for 'impl-env-test) 'trait-primitive)
    (for ([name (in-list '(add sub mul lt le eq acquire))])
      (check-false (assq name (current-trait-gamma0-entries)))))))

(test-case
 "scope-visible? follows the ledger scope rows"
 (check-true (call-with-trait-ledger
              (scoped-ledger)
              (λ () (scope-visible? 'root '(child)))))
 (check-false (scope-visible? 'root '(child))))

(test-case
 "compose-candidates reads intersect rows from the ledger"
 (define goal (make-goal '(Implements Int PrintableSizable)))
 (check-equal? (length (project-goal (current-Γ-pc0) '(root) goal)) 1)
 (check-equal?
  (call-with-trait-ledger
   (no-intersect-ledger)
   (λ () (project-goal (current-Γ-pc0) '(root) goal)))
  '()))

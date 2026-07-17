#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt"
         "origins.rkt")

(provide -->g1
         inject
         run)

(define-metafunction G1m
  δ : nm v ... -> any
  [(δ add n_1 n_2) ,(+ (term n_1) (term n_2))]
  [(δ sub n_1 n_2) ,(- (term n_1) (term n_2))]
  [(δ mul n_1 n_2) ,(* (term n_1) (term n_2))]
  [(δ lt n_1 n_2)
   ,(if (< (term n_1) (term n_2))
        (term (Construct true))
        (term (Construct false)))]
  [(δ le n_1 n_2)
   ,(if (<= (term n_1) (term n_2))
        (term (Construct true))
        (term (Construct false)))]
  [(δ eq n_1 n_2)
   ,(if (= (term n_1) (term n_2))
        (term (Construct true))
        (term (Construct false)))]
  [(δ acquire n) (resource n)]
  [(δ nm v ...) undefined])

;; Redex's substitute uses the binding forms declared by G1.  Keeping the
;; simultaneous substitution here also makes arity mismatches non-reducible
;; instead of raising a metafunction exception.
(define-metafunction G1m
  substitute* : c (x ...) (v ...) -> any
  [(substitute* c_body (x ...) (v_arg ...))
   (substitute c_body (x v_arg) ...)
   (side-condition
    (and (= (length (term (x ...)))
            (length (term (v_arg ...))))
         (not (check-duplicates (term (x ...))))))]
  [(substitute* c_body (x ...) (v_arg ...)) #f])

(define-metafunction G1m
  select-branch : K (v ...) (br ...) -> any
  [(select-branch K (v_arg ...)
                  ((K (x ...) -> c_body) br_rest ...))
   (substitute* c_body (x ...) (v_arg ...))]
  [(select-branch K (v_arg ...)
                  ((K_other (x_other ...) -> c_other) br_rest ...))
   (select-branch K (v_arg ...) (br_rest ...))]
  [(select-branch K (v_arg ...) ()) #f])

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

(define (table-ref table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

(define (table-set table key value)
  (if (assoc key table)
      (for/list ([entry (in-list table)])
        (if (equal? (first entry) key)
            (list key value)
            entry))
      (append table (list (list key value)))))

(define (fresh-place heap states)
  (for/fold ([next 0])
            ([entry (in-list (append heap states))])
    (max next (add1 (first entry)))))

(define (finalize/proc places states trace)
  (define-values (final-states reversed-events)
    (for/fold ([states states]
               [events '()])
              ([place (in-list (reverse places))])
      (if (eq? (table-ref states place) 'Available)
          (values (table-set states place 'Dropped)
                  (cons (list 'fin place) events))
          (values states events))))
  (list final-states (append trace (reverse reversed-events))))

(define-metafunction G1m
  finalize : π Ω θ -> any
  [(finalize π Ω θ)
   ,(finalize/proc (term π) (term Ω) (term θ))])

(define (unique-binders? term)
  (and (match term
         [`(Lam ,_ ,parameters ,_)
          (not (check-duplicates parameters))]
         [`(Recur ,function ,parameters ,_ ,_)
          (not (check-duplicates (cons function parameters)))]
         [`(RecurVal ,function ,parameters ,_)
          (not (check-duplicates (cons function parameters)))]
         [`(,_ ,parameters -> ,_)
          #:when (list? parameters)
          (not (check-duplicates parameters))]
         [_ #t])
       (or (not (list? term))
           (andmap unique-binders? term))))

;; Construct fields are evaluated by E; (Construct K v ...) is already a value,
;; so the data rule needs no separate administrative transition.
(define -->g1/rules
  (reduction-relation
   G1m
   #:domain config

   (--> (cfg (in-hole E (Apply (PrimVal O nm) v_arg ...)) H Ω θ)
        (cfg (in-hole E v_result) H Ω θ)
        (where v_result (δ nm v_arg ...))
        R-Delta)

   (--> (cfg (in-hole E (Apply (Lam O (x ...) c_body)
                               v_arg ...))
             H Ω θ)
        (cfg (in-hole E c_result) H Ω θ)
        (where c_result
               (substitute* c_body (x ...) (v_arg ...)))
        R-Beta)

   (--> (cfg (in-hole E (Curry ov_f v_arg)) H Ω θ)
        (cfg (in-hole E
                      (CurryVal (Derived O_f (Curry v_arg))
                                ov_f
                                v_arg))
             H Ω θ)
        (where O_f (origin-of ov_f))
        R-CurryVal)

   (--> (cfg (in-hole E
                      (Apply (CurryVal O v_f v_fixed)
                             v_arg ...))
             H Ω θ)
        (cfg (in-hole E (Apply v_f v_fixed v_arg ...)) H Ω θ)
        R-ApplyCurry)

   (--> (cfg (in-hole E (Let (x τ) v_bound c_body)) H Ω θ)
        (cfg (in-hole E c_result) H Ω θ)
        (side-condition (not (owned-type? (term τ))))
        (where c_result (substitute c_body x v_bound))
        R-Let)

   (--> (cfg (in-hole E_outer
                      (Scope (p_managed ...)
                             (in-hole G_inner
                                      (Let (x τ_owned)
                                           v_bound
                                           c_body))))
             H Ω θ)
        (cfg (in-hole E_outer
                      (Scope (p_managed ... p_new)
                             (in-hole G_inner c_result)))
             H_new Ω_new θ)
        (side-condition (owned-type? (term τ_owned)))
        (where p_new ,(fresh-place (term H) (term Ω)))
        (where c_result (substitute c_body x p_new))
        (where H_new
               ,(table-set (term H) (term p_new) (term v_bound)))
        (where Ω_new
               ,(table-set (term Ω) (term p_new) 'Available))
        R-LetOwned)

   (--> (cfg (in-hole E
                      (Eliminate (Construct K v_arg ...)
                                 (br ...)))
             H Ω θ)
        (cfg (in-hole E c_result) H Ω θ)
        (where c_result
               (select-branch K (v_arg ...) (br ...)))
        R-Eliminate)

   (--> (cfg (in-hole E (Move p)) H Ω θ)
        (cfg (in-hole E v_result) H Ω_new θ)
        (where Available ,(table-ref (term Ω) (term p)))
        (where v_result ,(table-ref (term H) (term p)))
        (where Ω_new ,(table-set (term Ω) (term p) 'Moved))
        R-Move)

   (--> (cfg (in-hole E (Move p)) H Ω θ)
        (cfg (in-hole E (Error p)) H Ω θ)
        (where state_old ,(table-ref (term Ω) (term p)))
        (side-condition (memq (term state_old) '(Moved Dropped)))
        R-MoveError)

   (--> (cfg (in-hole E (Drop v_arg)) H Ω θ)
        (cfg (in-hole E unit) H Ω θ)
        R-Drop)

   (--> (cfg (in-hole E_outer (Scope π_managed v_result)) H Ω θ)
        (cfg (in-hole E_outer v_result) H Ω_final θ_final)
        (where (Ω_final θ_final) (finalize π_managed Ω θ))
        R-ScopeValue)

   (--> (cfg (in-hole E_outer
                      (Scope π_managed
                             (in-hole F_inner (Perform op v_arg))))
             H Ω θ)
        (cfg (in-hole E_outer (Perform op v_arg)) H Ω_final θ_final)
        (where (Ω_final θ_final) (finalize π_managed Ω θ))
        R-ScopeAbort)

   (--> (cfg (in-hole E_outer
                      (Scope π_managed
                             (in-hole F_inner (Error p_error))))
             H Ω θ)
        (cfg (in-hole E_outer (Error p_error)) H Ω_final θ_final)
        (where (Ω_final θ_final) (finalize π_managed Ω θ))
        R-ScopeError)

   (--> (cfg (in-hole E_outer
                      (Handle op
                              (x -> c_handler)
                              (in-hole F_inner (Error p_error))))
             H Ω θ)
        (cfg (in-hole E_outer (Error p_error)) H Ω θ)
        R-HandleError)))

;; Binding-aware matching freshens binders before destructuring.  Check the raw
;; configuration first so repeated source binders cannot be freshened apart.
(define (raw-steps config)
  (if (unique-binders? config)
      (apply-reduction-relation -->g1/rules config)
      '()))

(define -->g1
  (reduction-relation
   G1m
   #:domain config
   (--> config_before
        config_after
        (where (config_prefix ... config_after config_suffix ...)
               ,(raw-steps (term config_before)))
        R-Step)))

(define (inject core)
  (unless (redex-match? G1 c core)
    (raise-argument-error 'inject "G1 core term" core))
  `(cfg (Scope () ,core) () () ()))

(define (run config fuel)
  (unless (redex-match? G1m config config)
    (raise-argument-error 'run "G1m configuration" config))
  (unless (exact-nonnegative-integer? fuel)
    (raise-argument-error 'run "exact-nonnegative-integer?" fuel))
  (let loop ([current config]
             [remaining fuel])
    (define next
      (remove-duplicates
       (apply-reduction-relation -->g1 current)
       equal?))
    (cond
      [(null? next) current]
      [(zero? remaining) 'timeout]
      [(null? (cdr next)) (loop (car next) (sub1 remaining))]
      [else
       (error 'run
              "nondeterministic reduction from ~e to ~e"
              current
              next)])))

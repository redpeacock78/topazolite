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

(define (unique-binders? term)
  (and (match term
         [`(Lam ,_ ,parameters ,_)
          (not (check-duplicates parameters))]
         [`(Recur ,_ ,parameters ,_ ,_)
          (not (check-duplicates parameters))]
         [`(RecurVal ,_ ,parameters ,_)
          (not (check-duplicates parameters))]
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

   (--> (cfg (in-hole E
                      (Eliminate (Construct K v_arg ...)
                                 (br ...)))
             H Ω θ)
        (cfg (in-hole E c_result) H Ω θ)
        (where c_result
               (select-branch K (v_arg ...) (br ...)))
        R-Eliminate)))

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

#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt")

(provide Δ0
         Γ0
         Π0
         R0
         kindOf
         origin-of
         verify-origins)

(define R0
  (term ((o-add (prim add))
         (o-sub (prim sub))
         (o-mul (prim mul))
         (o-lt (prim lt))
         (o-le (prim le))
         (o-eq (prim eq))
         (o-acquire (prim acquire))
         (o-int (type Int))
         (o-bool (type Bool))
         (o-unit (type Unit))
         (o-string (type String))
         (o-never (type Never))
         (o-res (type Res))
         (o-list (type List))
         (o-option (type Option))
         (o-result (type Result))
         (o-type-narrative typeNarrative))))

(define Γ0
  (term ((add ((NFn (Int Int) Int () ())
               (PrimVal (Reserved o-add) add)))
         (sub ((NFn (Int Int) Int () ())
               (PrimVal (Reserved o-sub) sub)))
         (mul ((NFn (Int Int) Int () ())
               (PrimVal (Reserved o-mul) mul)))
         (lt ((NFn (Int Int) Bool () ())
              (PrimVal (Reserved o-lt) lt)))
         (le ((NFn (Int Int) Bool () ())
              (PrimVal (Reserved o-le) le)))
         (eq ((NFn (Int Int) Bool () ())
              (PrimVal (Reserved o-eq) eq)))
         (acquire ((NFn (Int) (Owned Res) () ())
                   (PrimVal (Reserved o-acquire) acquire))))))

(define Δ0
  (term ((Int (TypeRep (Reserved o-int) Int Type))
         (Bool (TypeRep (Reserved o-bool) Bool Type))
         (Unit (TypeRep (Reserved o-unit) Unit Type))
         (String (TypeRep (Reserved o-string) String Type))
         (Never (TypeRep (Reserved o-never) Never Type))
         (Res (TypeRep (Reserved o-res) Res Type))
         (List (TypeRep (Reserved o-list) List (Type -> Type)))
         (Option (TypeRep (Reserved o-option) Option (Type -> Type)))
         (Result (TypeRep (Reserved o-result)
                          Result
                          (Type -> (Type -> Type)))))))

(define Π0
  (term ((typeNarrativeCap
          (TypeNarrativeCap (Reserved o-type-narrative))))))

(define (kind-of/proc type-form)
  (case type-form
    [(List Option) '(Type -> Type)]
    [(Result) '(Type -> (Type -> Type))]
    [else 'Type]))

(define-metafunction G1
  kindOf : t -> κ
  [(kindOf t) ,(kind-of/proc (term t))])

(define-metafunction G1
  origin-of : v -> O
  [(origin-of (Lam O (x ...) c)) O]
  [(origin-of (PrimVal O nm)) O]
  [(origin-of (CurryVal O v_1 v_2)) O]
  [(origin-of (TypeRep O t κ)) O]
  [(origin-of (ProofRep O φ)) O]
  [(origin-of (RecurVal f (x ...) c)) User])

(define (lookup table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

(define (valid-origin? r0 origin)
  (match origin
    ['User #t]
    [`(Reserved ,id) (and (assoc id r0) #t)]
    [`(Derived ,parent ,_) (valid-origin? r0 parent)]
    [_ #f]))

(define (origin-of/proc value)
  (match value
    [`(Lam ,origin ,_ ,_) origin]
    [`(PrimVal ,origin ,_) origin]
    [`(CurryVal ,origin ,_ ,_) origin]
    [`(TypeRep ,origin ,_ ,_) origin]
    [`(ProofRep ,origin ,_) origin]
    [`(RecurVal ,_ ,_ ,_) 'User]
    [_ #f]))

(define (reserved-type-rep? value)
  (for/or ([entry (in-list Δ0)])
    (equal? value (second entry))))

(define (origin-shape-valid? r0 value)
  (match value
    [`(PrimVal ,origin ,primitive)
     (and (valid-origin? r0 origin)
          (match origin
            [`(Reserved ,id)
             (equal? (lookup r0 id) `(prim ,primitive))]
            [_ #f]))]
    [`(Lam ,origin ,_ ,_)
     (and (valid-origin? r0 origin)
          (eq? origin 'User))]
    [`(CurryVal ,origin ,function ,argument)
     (define parent (origin-of/proc function))
     (and parent
          (valid-origin? r0 origin)
          (equal? origin `(Derived ,parent (Curry ,argument))))]
    [`(TypeRep ,origin ,type-form ,kind)
     (and (valid-origin? r0 origin)
          (equal? kind (kind-of/proc type-form))
          (or (and (match origin [`(Reserved ,_) #t] [_ #f])
                   (reserved-type-rep? value))
              (match origin
                [`(Derived (Reserved o-type-narrative) (Make ,made))
                 (equal? made type-form)]
                [_ #f])))]
    [`(ProofRep ,origin ,proposition)
     (and (valid-origin? r0 origin)
          (equal? origin '(Reserved o-type-narrative))
          (eq? proposition 'TypeNarrativeCap))]
    [_ #t]))

(define (origin-bearing-value? value)
  (and (pair? value)
       (memq (car value) '(Lam PrimVal CurryVal TypeRep ProofRep))))

(define (verify-origins/proc r0 core)
  (define (walk-list terms)
    (cond
      [(null? terms) 'ok]
      [else
       (define result (walk (car terms)))
       (if (eq? result 'ok)
           (walk-list (cdr terms))
           result)]))
  (define (walk term)
    (cond
      [(and (origin-bearing-value? term)
            (not (origin-shape-valid? r0 term)))
       `(forged ,term)]
      [(list? term) (walk-list term)]
      [else 'ok]))
  (walk core))

(define-metafunction G1m
  verify-origins : any c -> any
  [(verify-origins any_R0 c)
   ,(verify-origins/proc (term any_R0) (term c))])

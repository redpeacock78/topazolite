#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../origins.rkt")

(define (verify core)
  (term (verify-origins ,R0 ,core)))

(define (verify-with r0 core)
  (term (verify-origins ,r0 ,core)))

(test-case "NAR-001/TYP-001: initial origin environments"
  (check-equal? (length R0) 17)
  (check-equal? (length Γ0) 7)
  (check-equal? (length Δ0) 9)
  (check-equal? (length Π0) 1)
  (check-equal? (assoc 'o-type-narrative R0)
                (term (o-type-narrative typeNarrative)))
  (check-equal? (assoc 'lt Γ0)
                (term (lt ((NFn (Int Int) Bool () ())
                           (PrimVal (Reserved o-lt) lt)))))
  (check-equal? (assoc 'List Δ0)
                (term (List (TypeRep (Reserved o-list)
                                    List
                                    (Type -> Type)))))
  (check-equal? (assoc 'typeNarrativeCap Π0)
                (term (typeNarrativeCap
                       (TypeNarrativeCap
                        (Reserved o-type-narrative)))))
  (check-equal? (term (kindOf Int)) (term Type))
  (check-equal? (term (kindOf List)) (term (Type -> Type)))
  (check-equal? (term (kindOf Result))
                (term (Type -> (Type -> Type))))
  (check-equal? (term (kindOf (List Int))) (term Type))
  (check-equal? (term (origin-of (RecurVal recur-id f (x) x)))
                (term User))
  (for ([entry (in-list Γ0)])
    (check-equal? (verify (second (second entry))) 'ok))
  (for ([entry (in-list Δ0)])
    (check-equal? (verify (second entry)) 'ok)))

(test-case "NAR-002: origin-of covers every origin-bearing value"
  (define derived (term (Derived (Reserved o-lt) (Curry 1))))
  (for ([case (in-list
               (list (list (term (Lam User lam-id (x) x)) (term User))
                     (list (term (PrimVal (Reserved o-lt) lt))
                           (term (Reserved o-lt)))
                     (list (term (CurryVal ,derived 1 2)) derived)
                     (list (term (TypeRep (Reserved o-int) Int Type))
                           (term (Reserved o-int)))
                     (list (term (ProofRep (Reserved o-type-narrative)
                                           TypeNarrativeCap))
                           (term (Reserved o-type-narrative)))))])
    (match-define (list value expected) case)
    (check-equal? (term (origin-of ,value)) expected))
  (check-true (in-domain? (origin-of (PrimVal (Reserved o-lt) lt))))
  (check-false (in-domain? (origin-of 5)))
  (check-false (in-domain? (origin-of (Construct true)))))

(test-case "NAR-001: reserved origin and value sort agree"
  (check-equal? (verify (term (PrimVal (Reserved o-lt) lt))) 'ok)
  (check-equal? (verify (term (PrimVal (Reserved forged-id) lt)))
                (term (forged (PrimVal (Reserved forged-id) lt))))
  (check-equal? (verify (term (PrimVal (Reserved o-add) lt)))
                (term (forged (PrimVal (Reserved o-add) lt))))
  (check-equal? (verify (term (Lam (Reserved o-lt) lam-id (x) x)))
                (term (forged (Lam (Reserved o-lt) lam-id (x) x)))))

(test-case "NAR-002/CUR-002: derived curry origin is exact"
  (define valid
    (term (CurryVal (Derived (Reserved o-lt) (Curry 1))
                    (PrimVal (Reserved o-lt) lt)
                    1)))
  (check-equal? (verify valid) 'ok)
  (check-equal?
   (verify
    (term (CurryVal (Derived User (Curry 1))
                    (RecurVal recur-id f (x) x)
                    1)))
   'ok)
  (check-equal?
   (verify
    (term (CurryVal (Derived (Reserved o-add) (Curry 1))
                    (PrimVal (Reserved o-lt) lt)
                    1)))
   (term (forged
          (CurryVal (Derived (Reserved o-add) (Curry 1))
                    (PrimVal (Reserved o-lt) lt)
                    1))))
  (check-equal?
   (verify
    (term (CurryVal (Derived (Reserved o-lt) (Curry 2))
                    (PrimVal (Reserved o-lt) lt)
                    1)))
   (term (forged
          (CurryVal (Derived (Reserved o-lt) (Curry 2))
                    (PrimVal (Reserved o-lt) lt)
                    1))))
  (check-equal?
   (verify
    (term (CurryVal (Reserved o-lt)
                    (PrimVal (Reserved o-lt) lt)
                    1)))
   (term (forged
          (CurryVal (Reserved o-lt)
                    (PrimVal (Reserved o-lt) lt)
                    1)))))

(test-case "PRF-001: only the reserved TypeNarrative proof is valid"
  (check-equal?
   (verify (term (ProofRep (Reserved o-type-narrative)
                           TypeNarrativeCap)))
   'ok)
  (check-equal?
   (verify (term (ProofRep (Reserved forged-id) TypeNarrativeCap)))
   (term (forged
          (ProofRep (Reserved forged-id) TypeNarrativeCap))))
  (check-equal?
   (verify (term (ProofRep (Reserved o-type-narrative)
                           ValidNarrativeTrait)))
   (term (forged
          (ProofRep (Reserved o-type-narrative)
                    ValidNarrativeTrait))))
  (for ([bad (in-list
              (term ((ProofRep User TypeNarrativeCap)
                     (ProofRep (Derived (Reserved o-type-narrative)
                                        (Make Int))
                               TypeNarrativeCap))))])
    (check-equal? (verify bad) (term (forged ,bad)))))

(test-case "TYP-001/TYP-002: TypeRep origin, type, and kind agree"
  (check-equal?
   (verify (term (TypeRep (Derived (Reserved o-type-narrative)
                                  (Make Int))
                          Int Type)))
   'ok)
  (check-equal?
   (verify (term (TypeRep (Reserved o-list)
                          List (Type -> Type))))
   'ok)
  (for ([bad (in-list
              (term ((TypeRep (Derived (Reserved o-type-narrative)
                                      (Make Int))
                              Int (Type -> Type))
                     (TypeRep (Derived (Reserved o-type-narrative)
                                      (Make Bool))
                              Int Type)
                     (TypeRep (Derived (Reserved o-int) (Make Int))
                              Int Type)
                     (TypeRep (Derived (Reserved o-type-narrative)
                                      (Curry 0))
                              Int Type)
                     (TypeRep User Int Type)
                     (TypeRep (Reserved o-list) List Type)
                     (TypeRep (Reserved o-int) Bool Type))))])
    (check-equal? (verify bad) (term (forged ,bad)))))

(test-case "NAR-001: nested forged origin reports its subterm"
  (check-equal? (verify (term (Error 0))) 'ok)
  (define forged-prim (term (PrimVal (Reserved forged-id) lt)))
  (for ([nested
         (in-list
          (list (term (Apply 0 ,forged-prim))
                (term (Lam User lam-id () ,forged-prim))
                (term (Handle (Return b Int)
                              (x -> ,forged-prim)
                              0))
                (term (Eliminate (Construct some 1)
                                 ((some (x) -> ,forged-prim))))))])
    (check-equal? (verify nested) (term (forged ,forged-prim)))))

(test-case "NAR-001/TYP-001/PRF-001: verifier honors the supplied R0 sorts"
  (define reserved-type
    (term (TypeRep (Reserved o-int) Int Type)))
  (define derived-type
    (term (TypeRep (Derived (Reserved o-type-narrative) (Make Int))
                   Int Type)))
  (define proof
    (term (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)))
  (check-equal? (verify-with (term ((o-int (prim add)))) reserved-type)
                (term (forged ,reserved-type)))
  (check-equal?
   (verify-with (term ((o-type-narrative (prim add)))) derived-type)
   (term (forged ,derived-type)))
  (check-equal? (verify-with (term ((o-type-narrative (prim add)))) proof)
                (term (forged ,proof))))

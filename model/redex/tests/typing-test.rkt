#lang racket

(require rackunit
         redex/reduction-semantics
         "../typing.rkt")

(define empty '())
(define callable-types
  (term ((identity-id (NFn (Int) Int () ()))
         (binary-id (NFn (Int Int) Int () ()))
         (yield-id (NFn () Unit ((Yield Int)) ()))
         (loop-id (NFn (Int) Int () ()))
         (owned-parameter-id (NFn ((Owned Res)) Unit () ()))
         (capture-id (NFn () (Owned Res) (Own) ())))))

(test-case "T-Prim/T-MovePlace: synthesis uses Γ0 and Ξ"
  (check-equal?
   (core-type-of (term (PrimVal (Reserved o-lt) lt)) empty empty)
   (term ((NFn (Int Int) Bool () ()) ())))
  (check-equal?
   (core-type-of (term (Move 0)) (term ((0 Res))) empty)
   (term ((Owned Res) (Own))))
  (check-equal? (core-type-of (term x) empty empty) 'ill-typed)
  (check-equal?
   (core-type-of (term (PrimVal User lt)) empty empty)
   'ill-typed))

(test-case "EFF-001: T-Lam synthesizes from Φ and checks its body"
  (check-equal?
   (core-type-of
    (term (Lam User identity-id (x) x))
    empty callable-types)
   (term ((NFn (Int) Int () ()) ())))
  (check-equal?
   (core-type-of
    (term (Lam User yield-id () (Yield 1 unit)))
    empty callable-types)
   (term ((NFn () Unit ((Yield Int)) ()) ())))
  (check-equal?
   (core-type-of
    (term (Lam User identity-id (x) unit))
    empty callable-types)
   'ill-typed)
  (check-equal?
   (core-type-of (term (Lam User missing-id (x) x)) empty callable-types)
   'ill-typed)
  (check-equal?
   (core-type-of
    (term (Lam User owned-parameter-id (item) unit))
    empty callable-types)
   'ill-typed)
  (check-equal?
   (core-type-of
    (term (Let (owned-item (Owned Res))
               (resource 1)
               (Lam User capture-id () (Move owned-item))))
    empty callable-types)
   'ill-typed))

(test-case "CUR-001/CUR-002: callable values synthesize through curry"
  (define binary
    (term (Lam User binary-id (x y) x)))
  (define expected
    (term ((NFn (Int) Int () ()) ())))
  (check-equal?
   (core-type-of (term (Apply ,binary 1 2)) empty callable-types)
   (term (Int ())))
  (check-equal?
   (core-type-of (term (Curry ,binary 1)) empty callable-types)
   expected)
  (check-equal?
   (core-type-of (term (CurryVal User ,binary 1)) empty callable-types)
   expected)
  ;; Reduction may duplicate a callable value; GUN gates elaboration only.
  (check-equal?
   (core-type-of
    (term (Let (first Int)
               (Apply (Lam User identity-id (x) x) 1)
               (Apply (Lam User identity-id (x) x) 2)))
    empty callable-types)
   (term (Int ()))))

(test-case "REC-001: T-Recur and T-RecurVal use Φ(r)"
  (check-equal?
   (core-type-of
    (term (Recur loop-id loop (x) x (Apply loop 1)))
    empty callable-types)
   (term (Int ())))
  (check-equal?
   (core-type-of
    (term (RecurVal loop-id loop (x) x))
    empty callable-types)
   (term ((NFn (Int) Int () ()) ())))
  (check-equal?
   (core-type-of
    (term (Recur loop-id loop (x) unit (Apply loop 1)))
    empty callable-types)
   'ill-typed))

(test-case "T-Val/T-Eliminate: checking supplies erased constructor types"
  (check-equal? (core-type-of (term (Construct nil)) empty empty)
                'ill-typed)
  (check-true
   (core-check (term (Construct nil))
               empty empty (term (List Int)) empty))
  (check-true
   (core-check (term (Construct cons 1 (Construct nil)))
               empty empty (term (List Int)) empty))
  (check-false
   (core-check (term (Construct cons unit (Construct nil)))
               empty empty (term (List Int)) empty))
  (check-equal?
   (core-type-of
    (term (Let (xs (List Int))
               (Construct nil)
               (Eliminate xs
                          ((nil () -> 0)
                           (cons (head tail) -> head)))))
    empty empty)
   (term (Int ())))
  (check-equal?
   (core-type-of
    (term (Let (xs (List Int))
               (Construct nil)
               (Eliminate xs ((nil () -> 0)))))
    empty empty)
   'ill-typed))

(test-case "RET-002: Perform and Handle track the resolved Return label"
  (define performed
    (term (Perform (Return boundary Int) 7)))
  (check-equal?
   (core-type-of performed empty empty)
   (term (Never ((Return boundary Int)))))
  (check-equal?
   (core-type-of
    (term (Handle (Return boundary Int)
                  (result -> result)
                  ,performed))
    empty empty)
   (term (Int ()))))

(test-case "OWN-001/REC-002: Scope, Drop, Yield, and Suspend compose rows"
  (define places (term ((0 Res))))
  (check-equal?
   (core-type-of (term (Scope (0) (Drop (Move 0)))) places empty)
   (term (Unit (Own))))
  (check-equal?
   (core-type-of (term (Yield 1 (Suspend unit))) empty empty)
   (term (Unit (Suspend (Yield Int)))))
  (check-equal?
   (core-type-of (term (Scope (1) unit)) places empty)
   'ill-typed)
  (check-true
   (core-check (term (Error 0)) places empty (term Bool) empty)))

(test-case "T-Val: resource, TypeRep, and ProofRep synthesize"
  (check-equal? (core-type-of (term (resource 9)) empty empty)
                (term ((Owned Res) ())))
  (check-equal?
   (core-type-of (term (TypeRep User List (Type -> Type))) empty empty)
   (term ((TypeInfo (Type -> Type)) ())))
  (check-equal?
   (core-type-of (term (ProofRep User ValidNarrativeTrait)) empty empty)
   (term ((Proof ValidNarrativeTrait) ()))))

(test-case "T-Config: reconstructs Ξ and checks all domains"
  (define good
    (term (cfg (Scope (0) (Move 0))
               ((0 (resource 7)))
               ((0 Available))
               ())))
  (check-true
   (config-ok? good empty (term (Owned Res)) (term (Own))))
  (check-true
   (config-ok?
    (term (cfg (Error 0)
               ((0 (resource 7)))
               ((0 Moved))
               ()))
    empty (term Int) empty))
  (check-false
   (config-ok?
    (term (cfg unit ((0 (resource 7))) () ()))
    empty (term Unit) empty))
  (check-false
   (config-ok?
    (term (cfg unit
               ((0 (resource 7)) (0 (resource 8)))
               ((0 Available) (0 Moved))
               ()))
    empty (term Unit) empty))
  (check-false
   (config-ok?
    (term (cfg unit ((0 1)) ((0 Available)) ()))
    empty (term Unit) empty)))

(test-case "typing environments must be finite maps"
  (check-equal?
   (core-type-of (term (Move 0)) (term ((0 Res) (0 Int))) empty)
   'ill-typed)
  (check-equal?
   (core-type-of
    (term (Lam User identity-id (x) x))
    empty
    (term ((identity-id (NFn (Int) Int () ()))
           (identity-id (NFn (Bool) Bool () ())))))
   'ill-typed))

#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../origins.rkt"
         "../typing.rkt")

(define (type-origin type)
  (match type
    [`(Owned (NFn ,_ ,_ ,_ ,_ ,_ ,o)) o]
    [`(NFn ,_ ,_ ,_ ,_ ,_ ,o) o]
    [_ #f]))

(define parity-lam
  (term (Lam User parity-lam (x) x)))
(define parity-binary
  (term (Lam User parity-binary (x y) x)))
(define parity-owned-binary
  (term (Lam User parity-owned-binary (owned n)
             (Handle (Return boundary Int)
                     (return-value -> return-value)
                     (Scope ()
                            (Let (owned-copy let (Owned Res))
                                 owned
                                 n))))))

(define parity-callables
  (term ((parity-lam (NFn (Int) Int () () () User))
         (parity-binary (NFn (Int Int) Int () () () User))
         (parity-owned-binary
          (NFn ((Owned Res) Int) Int () () () User)))))

(define plain-curry
  (term (CurryVal (Derived User (Curry 1)) ,parity-binary 1)))

(define owned-leaf (term (OwnedLeaf (tok 0) (resource 1))))
(define owned-curry-inner
  (term (CurryVal (Derived User (Curry ,owned-leaf))
                  ,parity-owned-binary
                  ,owned-leaf)))
(define owned-curry
  (term (CurryVal
         (Derived (Derived User (Curry ,owned-leaf))
                  (Curry 1))
         ,owned-curry-inner
         1)))

(define parity-fixtures
  (list parity-lam
        (term (PrimVal (Reserved o-lt) lt))
        plain-curry
        owned-curry))

(define (synth-type value)
  (define result
    (with-config-typing
     (lambda () (core-type-of value '() parity-callables))))
  (check-not-equal? result 'ill-typed)
  (first result))

(define (value-origin value)
  (define origin (term (origin-of/g2 ,value)))
  (check-not-false origin)
  origin)

(test-case
 "Owned の固定引数は Owned<NFn> を合成する"
 (check-true
  (match (synth-type owned-curry)
    [`(Owned (NFn ,_ ,_ ,_ ,_ ,_ ,_)) #t]
    [_ #f])))

(test-case
 "合成した型の O は値の origin と一致する"
 (for ([fixture (in-list parity-fixtures)])
   (define type (synth-type fixture))
   (define type-o (type-origin type))
   (check-not-false type-o)
   (check-equal? (curry-payload-erase type-o)
                 (curry-payload-erase (value-origin fixture)))))

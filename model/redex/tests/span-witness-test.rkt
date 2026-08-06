#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../span.rkt")

(define s0 (term (#:span main.tz 0 4)))
(define s1 (term (#:span main.tz 5 9)))

(test-case "G1+ の ov は 6 構成子すべてに証人を持つ"
  (for ([value (in-list
                (list (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var x ,s1)))
                      (term (PrimVal ,s0 (Reserved o-lt) lt))
                      (term (CurryVal ,s0 User (#:lit 1 ,s1) (#:lit 2 ,s1)))
                      (term (RecurVal ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                                      (#:var x ,s1)))
                      (term (TypeRep ,s0 User Int Type))
                      (term (ProofRep ,s0 User ValidNarrativeTrait))))])
    (check-true (redex-match? G1+ ov value) (format "~a" value))))

(test-case "G1+ の v は 4 production すべてに証人を持つ"
  (for ([value (in-list
                (list (term (#:lit 1 ,s0))
                      (term (PrimVal ,s0 (Reserved o-lt) lt))
                      (term (Construct ,s0 (#:ty (List Int) ,s1) cons
                                       (#:lit 1 ,s1) (#:lit 2 ,s1)))
                      (term (resource ,s0 0))))])
    (check-true (redex-match? G1+ v value) (format "~a" value))))

(test-case "G1+ の c は 15 production すべてに証人を持つ"
  (for ([core (in-list
               (list (term (#:lit 1 ,s0))
                     (term (#:var x ,s0))
                     (term (Apply ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                     (term (Let ,s0 ((#:bind x ,s1) (#:ty Int ,s1))
                                (#:lit 1 ,s1) (#:var x ,s1)))
                     (term (Construct ,s0 (#:ty (Option Int) ,s1) some (#:lit 1 ,s1)))
                     (term (Eliminate ,s0
                                      (Construct ,s0 (#:ty (Option Int) ,s1) some
                                                 (#:lit 1 ,s1))
                                      ((,s1 some ((#:bind x ,s1)) -> (#:var x ,s1)))))
                     (term (Perform ,s0 (Return b (#:ty Int ,s1)) (#:lit 1 ,s1)))
                     (term (Handle ,s0 (Return b (#:ty Int ,s1))
                                   (,s1 (#:bind x ,s1) -> (#:var x ,s1))
                                   (#:lit 1 ,s1)))
                     (term (Scope ,s0 () (#:lit 1 ,s1)))
                     (term (Recur ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                                  (#:var x ,s1)
                                  (Apply ,s1 (#:var f ,s1) (#:lit 0 ,s1))))
                     (term (Yield ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                     (term (Suspend ,s0 (#:lit 1 ,s1)))
                     (term (Move ,s0 (#:var x ,s1)))
                     (term (Drop ,s0 (#:lit 1 ,s1)))
                     (term (Curry ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))))])
    (check-true (redex-match? G1+ c core) (format "~a" core))))

(test-case "spanless な項は G1+ に一致しない"
  (for ([core (in-list (term ((Apply 1 2)
                              (Let (x Int) 1 x)
                              (Construct (Option Int) some 1)
                              (Eliminate (Construct (Option Int) some 1)
                                         ((some (x) -> x)))
                              (Perform (Return b Int) 1)
                              (Handle (Return b Int) (x -> x) 1)
                              (Scope () 1)
                              (Recur recur-id f (x) x (Apply f 0))
                              (Yield 1 2)
                              (Suspend 1)
                              (Move x)
                              (Drop 1)
                              (Curry 1 2)
                              1
                              x)))])
    (check-false (redex-match? G1+ c core) (format "~a" core)))
  (for ([value (in-list (term ((Lam User lam-id (x) x)
                               (PrimVal User lt)
                               (CurryVal User 1 2)
                               (RecurVal recur-id f (x) x)
                               (TypeRep User Int Type)
                               (ProofRep User ValidNarrativeTrait)
                               (resource 0))))])
    (check-false (redex-match? G1+ v value) (format "~a" value))))

(test-case "span を持たない非終端は G1 と同じものを受理する"
  (for ([type (in-list (term (Int (List Int) (NFn (Int) Bool () ()))))])
    (check-equal? (and (redex-match? G1+ τ type) #t)
                  (and (redex-match? G1 τ type) #t)))
  (check-true (redex-match? G1+ ε (term (Own Partial))))
  (check-true (redex-match? G1+ O (term (Derived User (Make List))))))

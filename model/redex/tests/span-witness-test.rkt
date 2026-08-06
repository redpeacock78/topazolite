#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../elaborate.rkt"
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
    ;; 両辺が偽でも一致するので、まず基底で真であることを固定する。
    (check-true (redex-match? G1 τ type) (format "~a" type))
    (check-equal? (and (redex-match? G1+ τ type) #t)
                  (and (redex-match? G1 τ type) #t)))
  (check-true (redex-match? G1+ ε (term (Own Partial))))
  (check-true (redex-match? G1+ O (term (Derived User (Make List))))))

(test-case "G2+ の追加 production は証人を持つ"
  (for ([core (in-list
               (list (term (Rec ,s0 (((#:lbl a ,s1) imm (#:lit 1 ,s1)))))
                     (term (Proj ,s0 (Rec ,s1 (((#:lbl a ,s1) imm (#:lit 1 ,s1))))
                                 (#:lbl a ,s1)))
                     (term (Let ,s0 ((#:bind x ,s1) const (#:ty Int ,s1))
                                (#:lit 1 ,s1) (#:var x ,s1)))
                     (term (Discharge ,s0 (ProofRep ,s1 User ValidNarrativeTrait)
                                      (#:lit 1 ,s1)))))])
    (check-true (redex-match? G2+ c core) (format "~a" core)))
  (for ([value (in-list
                (list (term (Rec ,s0 (((#:lbl a ,s1) imm (#:lit 1 ,s1)))))
                      (term (UVal ,s0 (#:lit 1 ,s1)))
                      (term (RVal ,s0 (ProofRep ,s1 User (Prop p)) (#:lit 1 ,s1)))))])
    (check-true (redex-match? G2+ v value) (format "~a" value))))

(test-case "G2+ は G1+ の項をすべて受理する"
  (check-true (redex-match? G2+ c (term (Apply ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))))
  (check-true (redex-match? G2+ v (term (resource ,s0 0)))))

(test-case "spanless な G2 の項は G2+ に一致しない"
  (for ([core (in-list (term ((Rec ((a imm 1)))
                              (Proj (Rec ((a imm 1))) a)
                              (Let (x const Int) 1 x)
                              (Discharge (ProofRep User ValidNarrativeTrait) 1))))])
    (check-false (redex-match? G2+ c core) (format "~a" core)))
  (for ([value (in-list (term ((UVal 1)
                               (RVal (ProofRep User (Prop p)) 1))))])
    (check-false (redex-match? G2+ v value) (format "~a" value))))

(test-case "G2+ の型と述語は G2 と同じものを受理する"
  (for ([type (in-list (term ((Record ((a Int imm)))
                              (Untrusted Int)
                              (Refined Int (Prop p))
                              (Union Int Bool)
                              (Intersection Int Bool))))])
    ;; 両辺が偽でも一致するので、まず基底で真であることを固定する。
    (check-true (redex-match? G2 τ type) (format "~a" type))
    (check-equal? (and (redex-match? G2+ τ type) #t)
                  (and (redex-match? G2 τ type) #t)))
  (for ([prop (in-list (term ((Prop p)
                              (Presence a)
                              (ValidNarrativeTrait Printable)
                              (Implements Int Printable)
                              (RequiresBoth Printable Sizable)
                              (FieldType a Int))))])
    ;; 両辺が偽でも一致するので、まず基底で真であることを固定する。
    (check-true (redex-match? G2 φ prop) (format "~a" prop))
    (check-equal? (and (redex-match? G2+ φ prop) #t)
                  (and (redex-match? G2 φ prop) #t))))

(test-case "UCore+ の e は 21 production すべてに証人を持つ"
  (for ([expr (in-list
               (list (term (#:lit 1 ,s0))
                     (term (#:var x ,s0))
                     (term (Fn ,s0 (((#:bind x ,s1) (#:ty Int ,s1)))
                               (#:ty Int ,s1) (#:ef () ,s1) (#:var x ,s1)))
                     (term (Apply ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                     (term (Let ,s0 (#:bind x ,s1) (#:lit 1 ,s1) (#:var x ,s1)))
                     (term (Let ,s0 ((#:bind x ,s1) const (#:ty Int ,s1))
                                (#:lit 1 ,s1) (#:var x ,s1)))
                     (term (Rec ,s0 (((#:lbl a ,s1) imm (#:lit 1 ,s1)))))
                     (term (Proj ,s0 (#:var x ,s1) (#:lbl a ,s1)))
                     (term (Construct ,s0 some (#:lit 1 ,s1)))
                     (term (Construct ,s0 some (Types (#:ty Int ,s1)) (#:lit 1 ,s1)))
                     (term (Eliminate ,s0 (#:var x ,s1)
                                      ((,s1 some ((#:bind y ,s1)) -> (#:var y ,s1)))))
                     (term (Return ,s0 (#:lit 1 ,s1)))
                     (term (NarrativeExpr ,s0 (#:lit 1 ,s1)))
                     (term (Recur ,s0 (#:bind f ,s1) (((#:bind x ,s1) (#:ty Int ,s1)))
                                  (#:ty Int ,s1) (#:ef () ,s1)
                                  (#:var x ,s1) (Apply ,s1 (#:var f ,s1) (#:lit 0 ,s1))))
                     (term (Yield ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                     (term (Suspend ,s0 (#:lit 1 ,s1)))
                     (term (Move ,s0 (#:var x ,s1)))
                     (term (Drop ,s0 (#:lit 1 ,s1)))
                     (term (Curry ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                     (term (TypeMake ,s0 (#:ty (Spec Nat Nat) ,s1)))
                     (term (LetType ,s0 T (TypeMake ,s1 (#:ty (Spec Nat Nat) ,s1))
                                    (#:lit 1 ,s1)))))])
    (check-true (redex-match? UCore+ e expr) (format "~a" expr))))

(test-case "spanless な UCore の項は UCore+ に一致しない"
  (for ([expr (in-list (term ((Fn ((x Int)) Int () x)
                              (Apply 1 2)
                              (Let x 1 x)
                              (Rec ((a imm 1)))
                              (Construct some 1)
                              (Return 1)
                              (TypeMake (Spec Nat Nat))
                              1
                              x)))])
    (check-false (redex-match? UCore+ e expr) (format "~a" expr))))

(test-case "UCore+ は束縛形を宣言しない"
  ;; 束縛形を宣言していれば alpha 同値で真になるが、宣言していないので偽である。
  (check-false
   (alpha-equivalent? UCore+
                      (term (Fn ,s0 (((#:bind x ,s1) (#:ty Int ,s1)))
                                (#:ty Int ,s1) (#:ef () ,s1) (#:var x ,s1)))
                      (term (Fn ,s0 (((#:bind y ,s1) (#:ty Int ,s1)))
                                (#:ty Int ,s1) (#:ef () ,s1) (#:var y ,s1))))))

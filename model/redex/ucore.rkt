#lang racket

(require redex/reduction-semantics
         "lang.rkt")

(provide UCore UCore+)

;; S-expression encoding of the untyped reduced Core from core-calculus.md §3.1.
;; Explicit constructor type arguments use (Types ...), and applied type specs
;; use (Spec head argument ...).
(define-extended-language UCore G1
  (T ::= variable-not-otherwise-mentioned)
  (A ::= Int Bool Unit String Never Res List Option Result T)
  (label ::= variable-not-otherwise-mentioned)
  (m ::= imm mut)
  (bmode ::= const let)
  (tn ::= id)
  (ur ::= ((label uτ m) ...))
  ;; RFN-001: 表層に書ける命題。判定表の (Prop id) を足す。常在性 witness の
  ;; (Presence label) は含めない。merge の局所検査だけで立つ命題である。
  (uφ ::= ValidNarrativeTrait TypeNarrativeCap (Prop id)
          (ValidNarrativeTrait tn)
          (Implements uτ tn)
          (RequiresBoth tn tn))
  (uQ ::= (uφ ...))
  (uτ ::= Int Bool Unit String Never Res
          T
          (List uτ)
          (Option uτ)
          (Result uτ uτ)
          (Owned uτ)
          (Untrusted uτ)
          (Refined uτ uφ)
          (NFn (uτ ...) uτ tε uQ)
          (TypeInfo κ)
          (Proof uφ)
          (Record ur)
          (Union uτ uτ)
          (Intersection uτ uτ))
  (tℓ ::= (Return b uτ) (Yield uτ) Suspend Partial Compile Own)
  (tε ::= (tℓ ...))
  (uℓ ::= Return (Yield uτ) Suspend Partial Compile Own)
  (uε ::= (uℓ ...))
  (spec ::= A (Spec spec spec ...))
  (ubr ::= (K (x ...) -> e))
  (e ::= l
         x
         (Fn ((x uτ) ...) uτ uε e)
         (Apply e e ...)
         (Let x e e)
         (Let (x bmode uτ) e e)
         (Rec ((label m e) ...))
         (Proj e label)
         (Construct K e ...)
         (Construct K (Types uτ ...) e ...)
         (Eliminate e (ubr ...))
         (Return e)
         (NarrativeExpr e)
         (Recur f ((x uτ) ...) uτ uε e e)
         (Yield e e)
         (Suspend e)
         (Move x)
         (Drop e)
         (Curry e e)
         (TypeMake spec)
         (LetType T (TypeMake spec) e)))

;; UCore の項へ span を付けた言語。UCore は束縛形を持たないため、UCore+ も持たない。
;; e と ubr は基底が spanless なので .... を書かない。
(define-extended-language UCore+ UCore
  (rsid ::= #:synthetic)
  (usid ::= variable-not-otherwise-mentioned)
  (sid ::= usid rsid)
  (s ::= (#:span sid natural natural))
  (xs ::= (#:bind x s))
  (ls ::= (#:lbl label s))
  (ts ::= (#:ty uτ s))
  (es ::= (#:ef uε s))
  (sps ::= (#:ty spec s))
  (vr ::= (#:var x s))
  (lt ::= (#:lit l s))
  (ubr ::= (s K (xs ...) -> e))
  (e ::= lt
         vr
         (Fn s ((xs ts) ...) ts es e)
         (Apply s e e ...)
         (Let s xs e e)
         (Let s (xs bmode ts) e e)
         (Rec s ((ls m e) ...))
         (Proj s e ls)
         (Construct s K e ...)
         (Construct s K (Types ts ...) e ...)
         (Eliminate s e (ubr ...))
         (Return s e)
         (NarrativeExpr s e)
         (Recur s xs ((xs ts) ...) ts es e e)
         (Yield s e e)
         (Suspend s e)
         (Move s vr)
         (Drop s e)
         (Curry s e e)
         (TypeMake s sps)
         (LetType s T (TypeMake s sps) e)))

#lang racket

(require redex/reduction-semantics
         "elaborate.rkt"
         "span-core.rkt")

(provide (all-from-out "span-core.rkt") UCore+)

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

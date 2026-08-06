#lang racket

(require redex/reduction-semantics
         "lang.rkt")

(provide Span span-ok? G1+)

;; CanonicalSpan。sourceId は利用者が与える記号か、予約 keyword #:synthetic である。
;; 予約値と利用者の sourceId は値の種類で分かれるため、名前による予約を置かない。
(define-language Span
  (rsid ::= #:synthetic)
  (usid ::= variable-not-otherwise-mentioned)
  (sid ::= usid rsid)
  (s ::= (#:span sid natural natural)))

;; 文法に合い、かつ startByte <= endByte であることを判定する。空 span は許す。
(define (span-ok? t)
  (and (redex-match? Span s t)
       (match t
         [(list '#:span _ start end) (<= start end)]
         [_ #f])))

;; G1 の項へ span を付けた言語。span を持たない非終端（τ κ ℓ ε Q φ t O step π n l
;; x f b K nm id cid）は G1 から引き継ぐ。
;; c v ov br h w op は spanful へ置き換わるため .... を書かない。
(define-extended-language G1+ G1
  (rsid ::= #:synthetic)
  (usid ::= variable-not-otherwise-mentioned)
  (sid ::= usid rsid)
  (s ::= (#:span sid natural natural))
  (xs ::= (#:bind x s))
  (ts ::= (#:ty τ s))
  (vr ::= (#:var x s))
  (lt ::= (#:lit l s))
  (w ::= vr)
  (op ::= (Return b ts))
  (br ::= (s K (xs ...) -> c))
  (h ::= (s xs -> c))
  (c ::= v
         vr
         (Apply s c c ...)
         (Let s (xs ts) c c)
         (Construct s ts K c ...)
         (Eliminate s c (br ...))
         (Perform s op c)
         (Handle s op h c)
         (Scope s π c)
         (Recur s cid xs (xs ...) c c)
         (Yield s c c)
         (Suspend s c)
         (Move s w)
         (Drop s c)
         (Curry s c c))
  (v ::= lt
         ov
         (Construct s ts K v ...)
         (resource s n))
  (ov ::= (Lam s O cid (xs ...) c)
          (PrimVal s O nm)
          (CurryVal s O v v)
          (RecurVal s cid xs (xs ...) c)
          (TypeRep s O t κ)
          (ProofRep s O φ))
  #:binding-forms
  (Lam s O cid ((#:bind x s_b) ...) c #:refers-to (shadow x ...))
  (Let s ((#:bind x s_b) ts) c_1 c_2 #:refers-to x)
  (s K ((#:bind x s_b) ...) -> c #:refers-to (shadow x ...))
  (s (#:bind x s_b) -> c #:refers-to x)
  (Recur s cid (#:bind f s_f) ((#:bind x s_b) ...)
         c_1 #:refers-to (shadow f x ...)
         c_2 #:refers-to f)
  (RecurVal s cid (#:bind f s_f) ((#:bind x s_b) ...)
            c #:refers-to (shadow f x ...)))

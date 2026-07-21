#lang racket

(require redex/reduction-semantics)

(provide G1
         G2
         G1m
         G2m
         row-∪
         row-⊆
         row-∈
         row-\\)

(define-language G1
  (x ::= variable-not-otherwise-mentioned)
  (f ::= variable-not-otherwise-mentioned)
  (b ::= variable-not-otherwise-mentioned)
  (K ::= variable-not-otherwise-mentioned)
  (nm ::= variable-not-otherwise-mentioned)
  (id ::= variable-not-otherwise-mentioned)
  (cid ::= variable-not-otherwise-mentioned)
  (n ::= integer)
  (l ::= integer unit string)

  (τ ::= Int Bool Unit String Never Res
         (List τ)
         (Option τ)
         (Result τ τ)
         (Owned τ)
         (NFn (τ ...) τ ε Q)
         (TypeInfo κ)
         (Proof φ))
  (κ ::= Type (κ -> κ))
  (ℓ ::= (Return b τ) (Yield τ) Suspend Partial Compile Own)
  (ε ::= (ℓ ...))
  (Q ::= (φ ...))
  (φ ::= ValidNarrativeTrait TypeNarrativeCap)
  (t ::= τ List Option Result)

  (O ::= User
         (Reserved id)
         (Derived O step))
  (step ::= (Curry v)
            (Make t)
            (Expand nm))

  (op ::= (Return b τ))
  (w ::= x)
  (π ::= ())
  (br ::= (K (x ...) -> c))
  (h ::= (x -> c))

  (c ::= v
         x
         (Apply c c ...)
         (Let (x τ) c c)
         (Construct τ K c ...)
         (Eliminate c (br ...))
         (Perform op c)
         (Handle op h c)
         (Scope π c)
         (Recur cid f (x ...) c c)
         (Yield c c)
         (Suspend c)
         (Move w)
         (Drop c)
         (Curry c c))
  (v ::= l
         ov
         (Construct τ K v ...)
         (resource n))
  (ov ::= (Lam O cid (x ...) c)
          (PrimVal O nm)
          (CurryVal O v v)
          (RecurVal cid f (x ...) c)
          (TypeRep O t κ)
          (ProofRep O φ))

  #:binding-forms
  (Lam O cid (x ...) c #:refers-to (shadow x ...))
  (Let (x τ) c_1 c_2 #:refers-to x)
  (K (x ...) -> c #:refers-to (shadow x ...))
  (x -> c #:refers-to x)
  (Recur cid f (x ...)
         c_1 #:refers-to (shadow f x ...)
         c_2 #:refers-to f)
  (RecurVal cid f (x ...) c #:refers-to (shadow f x ...)))

(define-extended-language G2 G1
  (label ::= variable-not-otherwise-mentioned)
  (m ::= imm mut)
  (bmode ::= const let)
  (r ::= ((label τ m) ...))
  (τ ::= .... (Record r))
  (c ::= ....
         (Rec ((label m c) ...))
         (Proj c label)
         (Let (x bmode τ) c c))
  (v ::= .... (Rec ((label m v) ...)))

  #:binding-forms
  (Let (x bmode τ) c_1 c_2 #:refers-to x))

(define-extended-language G1m G1
  (p ::= natural)
  (w ::= .... p)
  (π ::= (p ...))
  (c ::= .... (Error p))

  (state ::= Available Moved Dropped)
  (H ::= ((p v) ...))
  (Ω ::= ((p state) ...))
  (event ::= (obs v) (fin p))
  (θ ::= (event ...))
  (config ::= (cfg c H Ω θ))

  (F ::= hole
         (Apply v ... F c ...)
         (Let (x τ) F c)
         (Construct τ K v ... F c ...)
         (Eliminate F (br ...))
         (Perform op F)
         (Drop F)
         (Yield F c)
         (Curry F c)
         (Curry v F))
  (E ::= hole
         (Apply v ... E c ...)
         (Let (x τ) E c)
         (Construct τ K v ... E c ...)
         (Eliminate E (br ...))
         (Perform op E)
         (Drop E)
         (Yield E c)
         (Curry E c)
         (Curry v E)
         (Scope π E)
         (Handle op h E))
  (G ::= hole
         (Apply v ... G c ...)
         (Let (x τ) G c)
         (Construct τ K v ... G c ...)
         (Eliminate G (br ...))
         (Perform op G)
         (Drop G)
         (Yield G c)
         (Curry G c)
         (Curry v G)
         (Handle op h G)))

(define-extended-language G2m G1m
  (label ::= variable-not-otherwise-mentioned)
  (m ::= imm mut)
  (bmode ::= const let)
  (r ::= ((label τ m) ...))
  (τ ::= .... (Record r))
  (c ::= ....
         (Rec ((label m c) ...))
         (Proj c label)
         (Let (x bmode τ) c c))
  (v ::= .... (Rec ((label m v) ...)))

  (F ::= ....
         (Rec ((label m v) ... (label m F) (label m c) ...))
         (Proj F label)
         (Let (x bmode τ) F c))
  (E ::= ....
         (Rec ((label m v) ... (label m E) (label m c) ...))
         (Proj E label)
         (Let (x bmode τ) E c))
  (G ::= ....
         (Rec ((label m v) ... (label m G) (label m c) ...))
         (Proj G label)
         (Let (x bmode τ) G c))

  #:binding-forms
  (Let (x bmode τ) c_1 c_2 #:refers-to x))

(define-metafunction G1
  row-∈ : ℓ ε -> boolean
  [(row-∈ ℓ ()) #f]
  [(row-∈ ℓ (ℓ ℓ_rest ...)) #t]
  [(row-∈ ℓ (ℓ_other ℓ_rest ...))
   (row-∈ ℓ (ℓ_rest ...))])

(define-metafunction G1
  row-add : ε ℓ -> ε
  [(row-add (ℓ_0 ...) ℓ) (ℓ_0 ...)
   (where #t (row-∈ ℓ (ℓ_0 ...)))]
  [(row-add (ℓ_0 ...) ℓ) (ℓ_0 ... ℓ)])

(define-metafunction G1
  row-∪ : ε ε -> ε
  [(row-∪ ε ()) ε]
  [(row-∪ ε (ℓ ℓ_rest ...))
   (row-∪ (row-add ε ℓ) (ℓ_rest ...))])

(define-metafunction G1
  row-⊆ : ε ε -> boolean
  [(row-⊆ () ε) #t]
  [(row-⊆ (ℓ ℓ_rest ...) ε)
   (row-⊆ (ℓ_rest ...) ε)
   (where #t (row-∈ ℓ ε))]
  [(row-⊆ (ℓ ℓ_rest ...) ε) #f])

(define-metafunction G1
  row-\\ : ε ε -> ε
  [(row-\\ () ε) ()]
  [(row-\\ (ℓ ℓ_rest ...) ε)
   (row-\\ (ℓ_rest ...) ε)
   (where #t (row-∈ ℓ ε))]
  [(row-\\ (ℓ ℓ_rest ...) ε)
   (ℓ ℓ_kept ...)
   (where #f (row-∈ ℓ ε))
   (where (ℓ_kept ...) (row-\\ (ℓ_rest ...) ε))])

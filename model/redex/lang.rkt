#lang racket

(require redex/reduction-semantics)

(provide G1
         G1m
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
         (Construct K c ...)
         (Eliminate c (br ...))
         (Perform op c)
         (Handle op h c)
         (Scope π c)
         (Recur f (x ...) c c)
         (Yield c c)
         (Suspend c)
         (Move w)
         (Drop c)
         (Curry c c))
  (v ::= l
         (Lam O (x ...) c)
         (PrimVal O nm)
         (CurryVal O v v)
         (RecurVal f (x ...) c)
         (Construct K v ...)
         (resource n)
         (TypeRep O t κ)
         (ProofRep O φ)))

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
         (Construct K v ... F c ...)
         (Eliminate F (br ...))
         (Perform op F)
         (Drop F)
         (Yield F c)
         (Curry F c)
         (Curry v F))
  (E ::= hole
         (Apply v ... E c ...)
         (Let (x τ) E c)
         (Construct K v ... E c ...)
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
         (Construct K v ... G c ...)
         (Eliminate G (br ...))
         (Perform op G)
         (Drop G)
         (Yield G c)
         (Curry G c)
         (Curry v G)
         (Handle op h G)))

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

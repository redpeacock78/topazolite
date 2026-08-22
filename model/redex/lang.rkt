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
  ;; 寿命変数と具体的な region を同じ欄に置く（spec §3.1）。
  ;; 別の構文にするのは、同じ空間に採番すると解決前の変数と解決済みの
  ;; region を型の上で区別できなくなるからである。
  (ρ ::= natural (RVar natural))
  (l ::= integer unit string)

  (τ ::= Int Bool Unit String Never Res
         (List τ)
         (Option τ)
         (Result τ τ)
         (Owned τ)
         (Borrowed τ ρ)
         (BorrowedMut τ ρ)
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
            (Expand nm)
            (Policy nm)
            (Compose nm O O))

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
  (tn ::= id)
  ;; region 引数の名前。r は同じ言語の record row であるため使えない。
  (rp ::= variable-not-otherwise-mentioned)
  (ρ ::= .... (RParam rp))
  (τ ::= .... (Record r) (Untrusted τ) (Refined τ φ)
         (Union τ τ) (Intersection τ τ)
         (ForallRegion (rp ...) τ))
  (φ ::= .... (Prop id) (Presence label)
         (ValidNarrativeTrait tn) (Implements τ tn)
         (RequiresBoth tn tn) (FieldType label τ))
  (c ::= ....
         (Rec ((label m c) ...))
         (Proj c label)
         (Let (x bmode τ) c c)
         (Discharge (ProofRep O φ) c)
         (Borrow w)
         (BorrowMut w)
         (Reborrow c)
         (ProjBorrow c label)
         (Read c)
         (Assign c c)
         (RegionLam (rp ...) c)
         (RegionApp c (ρ ...)))
  (v ::= ....
         (Rec ((label m v) ...))
         (UVal v)
         (RVal (ProofRep O φ) v)
         (RegionLam (rp ...) c))

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
  ;; field path。空の列が root capability を表す。
  (fp ::= (label ...))
  (m ::= imm mut)
  (bmode ::= const let)
  (r ::= ((label τ m) ...))
  (tn ::= id)
  (rp ::= variable-not-otherwise-mentioned)
  (ρ ::= .... (RParam rp))
  (τ ::= .... (Record r) (Untrusted τ) (Refined τ φ)
         (Union τ τ) (Intersection τ τ)
         (ForallRegion (rp ...) τ))
  (φ ::= .... (Prop id) (Presence label)
         (ValidNarrativeTrait tn) (Implements τ tn)
         (RequiresBoth tn tn) (FieldType label τ))
  (c ::= ....
         (Rec ((label m c) ...))
         (Proj c label)
         (Let (x bmode τ) c c)
         (Discharge (ProofRep O φ) c)
         (Borrow w)
         (BorrowMut w)
         (Reborrow c)
         (BorrowAt ρ own w)
         (BorrowMutAt ρ own w)
         (ReborrowAt ρ own c)
         (ProjBorrowAt ρ own c label)
         (Read c)
         (Assign c c)
         (RegionLam (rp ...) c)
         (RegionApp c (ρ ...)))
  (own ::= (Own w fp))
  (v ::= ....
         (Rec ((label m v) ...))
         (UVal v)
         (RVal (ProofRep O φ) v)
         (BorrowRef p fp ρ)
         (BorrowMutRef p fp ρ)
         (RegionLam (rp ...) c))

  (F ::= ....
         (Rec ((label m v) ... (label m F) (label m c) ...))
         (Proj F label)
         (Let (x bmode τ) F c)
         (ReborrowAt ρ own F)
         (ProjBorrowAt ρ own F label)
         (Read F)
         (Assign F c)
         (Assign v F)
         (RegionApp F (ρ ...)))
  (E ::= ....
         (Rec ((label m v) ... (label m E) (label m c) ...))
         (Proj E label)
         (Let (x bmode τ) E c)
         (ReborrowAt ρ own E)
         (ProjBorrowAt ρ own E label)
         (Read E)
         (Assign E c)
         (Assign v E)
         (RegionApp E (ρ ...)))
  (G ::= ....
         (Rec ((label m v) ... (label m G) (label m c) ...))
         (Proj G label)
         (Let (x bmode τ) G c)
         (ReborrowAt ρ own G)
         (ProjBorrowAt ρ own G label)
         (Read G)
         (Assign G c)
         (Assign v G)
         (RegionApp G (ρ ...)))

  #:binding-forms
  (Let (x bmode τ) c_1 c_2 #:refers-to x))

(define-metafunction G2
  row-∈ : ℓ ε -> boolean
  [(row-∈ ℓ ()) #f]
  [(row-∈ ℓ (ℓ ℓ_rest ...)) #t]
  [(row-∈ ℓ (ℓ_other ℓ_rest ...))
   (row-∈ ℓ (ℓ_rest ...))])

(define-metafunction G2
  row-add : ε ℓ -> ε
  [(row-add (ℓ_0 ...) ℓ) (ℓ_0 ...)
   (where #t (row-∈ ℓ (ℓ_0 ...)))]
  [(row-add (ℓ_0 ...) ℓ) (ℓ_0 ... ℓ)])

(define-metafunction G2
  row-∪ : ε ε -> ε
  [(row-∪ ε ()) ε]
  [(row-∪ ε (ℓ ℓ_rest ...))
   (row-∪ (row-add ε ℓ) (ℓ_rest ...))])

(define-metafunction G2
  row-⊆ : ε ε -> boolean
  [(row-⊆ () ε) #t]
  [(row-⊆ (ℓ ℓ_rest ...) ε)
   (row-⊆ (ℓ_rest ...) ε)
   (where #t (row-∈ ℓ ε))]
  [(row-⊆ (ℓ ℓ_rest ...) ε) #f])

(define-metafunction G2
  row-\\ : ε ε -> ε
  [(row-\\ () ε) ()]
  [(row-\\ (ℓ ℓ_rest ...) ε)
   (row-\\ (ℓ_rest ...) ε)
   (where #t (row-∈ ℓ ε))]
  [(row-\\ (ℓ ℓ_rest ...) ε)
   (ℓ ℓ_kept ...)
   (where #f (row-∈ ℓ ε))
   (where (ℓ_kept ...) (row-\\ (ℓ_rest ...) ε))])

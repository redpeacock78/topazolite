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

  ;; raw pointer の成分。許可される識別子の集合は validators.rkt が閉じる。
  ;; `mut` は record row の可変性を表す literal であり、Redex は同名の非終端を
  ;; その参照として解釈するため、pointer の可変性は `ptrmut` として分離する。
  (ptrmut ::= Const Mut)
  (nul ::= NonNull Nullable)
  (align ::= (Align natural))
  (as ::= (AddrSpace id))
  (prov ::= (Prov id))

  (τ ::= Int Bool Unit String Never Res
         (List τ)
         (Option τ)
         (Result τ τ)
         (Owned τ)
         (Borrowed τ ρ)
         (BorrowedMut τ ρ)
         (RawPtr τ ptrmut nul align as prov)
         (NFn (τ ...) τ ε Q)
         (TypeInfo κ)
         (Proof φ))
  (κ ::= Type (κ -> κ))
  (ℓ ::= (Return b τ) (Yield τ) Suspend Partial Compile Own Unsafe Mutation)
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
            ;; trait 名は G1 の既存の名前の非終端 nm を使う。trait 専用の tn は
            ;; G2 で初めて導入されるため、G1 では literal になってしまう。
            (Trait nm)
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
         (Curry c c)
         (OwnLeaf c))
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
  ;; P1c2b。SCP-001。binding は既定で immutable であり、再代入には mut を要求する。
  (bmode ::= const let mut)
  (r ::= ((label τ m) ...))
  (tn ::= id)
  ;; region 引数の名前。r は同じ言語の record row であるため使えない。
  (rp ::= variable-not-otherwise-mentioned)
  ;; NonNull は nul の literal でもあるため、PtrProp の識別子だけは
  ;; `id` に加えて明示的に受け入れる。
  (ptr-prop-id ::= id NonNull)
  (ρ ::= .... (RParam rp))
  (τ ::= .... (Record r) (Untrusted τ) (Refined τ φ)
         (Union τ τ) (Intersection τ τ)
         (ForallRegion (rp ...) τ))
  (φ ::= .... (Prop id) (Presence label)
         (ValidNarrativeTrait tn) (Implements τ tn)
         (RequiresBoth tn tn) (FieldType label τ)
         (PtrProp ptr-prop-id τ))
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
         ;; P1c2b。SCP-001。source 層の target は binder だけである。
         (Reassign w c)
         (RegionLam (rp ...) c)
         (RegionApp c (ρ ...))
         ;; pointer 操作と unsafe boundary（unsafe.md §4.2、§6.1）。
         (AddressOf c)
         (PtrOffset c c)
         (RawLoad c)
         (RawStore c c)
         (FromRawPtr c ρ)
         (Unsafe c))
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
  ;; P1c2b。SCP-001。Reassign 専用の実行時 target。
  ;; w を広げると Move や BorrowMut の target も MutSlot を受理してしまう。
  (mw ::= w (MutSlot p))
  (π ::= (p ...))
  ;; MutSlot は mut binding が指す place の読み口である。値ではない。
  (c ::= .... (Error p) (MutSlot p))

  (state ::= Available Moved Dropped)
  ;; 値の内部に置く所有資源の印。根の値には置かず、config-ok? が拒否する。
  (v ::= .... (OwnedLeaf tk v))
  ;; record の field 名。借用だけでなく G1m の値走査も使うため、
  ;; G2m ではなくこの共通機械言語に置く。
  (label ::= variable-not-otherwise-mentioned)
  ;; path の segment。record は label、位置指定は natural を使う。
  (fseg ::= label natural)
  (fp ::= (fseg ...))
  (H ::= ((p v) ...))
  (Ω ::= ((p state) ...))
  ;; 値の内部の Owned 資源を識別する token。
  (tk ::= (tok natural))
  ;; token の状態。root の所有を持つ Ω とは別の写像である。
  (tkstate ::= Available Moved Observed Dropped)
  (Λtok ::= ((tk tkstate) ...))
  (event ::= (obs v) (fin p) (finLeaf p (fseg fseg ...)))
  (θ ::= (event ...))
  (config ::= (cfg c H Ω Λtok θ))

  (F ::= hole
         (Apply v ... F c ...)
         (Let (x τ) F c)
         (Construct τ K v ... F c ...)
         (Eliminate F (br ...))
         (Perform op F)
         (Drop F)
         (Yield F c)
         (Curry F c)
         (Curry v F)
         (OwnLeaf F))
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
         (Handle op h E)
         (OwnLeaf E))
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
         (Handle op h G)
         (OwnLeaf G)))

(define-extended-language G2m G1m
  (m ::= imm mut)
  (bmode ::= const let mut)
  (r ::= ((label τ m) ...))
  (tn ::= id)
  (rp ::= variable-not-otherwise-mentioned)
  (ptr-prop-id ::= id NonNull)
  (ρ ::= .... (RParam rp))
  (τ ::= .... (Record r) (Untrusted τ) (Refined τ φ)
         (Union τ τ) (Intersection τ τ)
         (ForallRegion (rp ...) τ))
  (φ ::= .... (Prop id) (Presence label)
         (ValidNarrativeTrait tn) (Implements τ tn)
         (RequiresBoth tn tn) (FieldType label τ)
         (PtrProp ptr-prop-id τ))
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
         (Reassign mw c)
         (RegionLam (rp ...) c)
         (RegionApp c (ρ ...))
         ;; pointer 操作と unsafe boundary（unsafe.md §4.2、§6.1）。
         (AddressOf c)
         (PtrOffset c c)
         (RawLoad c)
         (RawStore c c)
         (FromRawPtr c ρ)
         (Unsafe c))
  (own ::= (Own w fp))
  (v ::= ....
         (Rec ((label m v) ...))
         (UVal v)
         (RVal (ProofRep O φ) v)
         (BorrowRef p fp ρ)
         (BorrowMutRef p fp ρ)
         ;; unsafe.md §4.3。ptrmut を実行時にも運ぶ。
         (PtrVal p fp ptrmut prov)
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
         (Reassign mw F)
         (RegionApp F (ρ ...))
         (AddressOf F)
         (PtrOffset F c)
         (PtrOffset v F)
         (RawLoad F)
         (RawStore F c)
         (RawStore v F)
         (FromRawPtr F ρ)
         (Unsafe F))
  (E ::= ....
         (Rec ((label m v) ... (label m E) (label m c) ...))
         (Proj E label)
         (Let (x bmode τ) E c)
         (ReborrowAt ρ own E)
         (ProjBorrowAt ρ own E label)
         (Read E)
         (Assign E c)
         (Assign v E)
         (Reassign mw E)
         (RegionApp E (ρ ...))
         (AddressOf E)
         (PtrOffset E c)
         (PtrOffset v E)
         (RawLoad E)
         (RawStore E c)
         (RawStore v E)
         (FromRawPtr E ρ)
         (Unsafe E))
  (G ::= ....
         (Rec ((label m v) ... (label m G) (label m c) ...))
         (Proj G label)
         (Let (x bmode τ) G c)
         (ReborrowAt ρ own G)
         (ProjBorrowAt ρ own G label)
         (Read G)
         (Assign G c)
         (Assign v G)
         (Reassign mw G)
         (RegionApp G (ρ ...))
         (AddressOf G)
         (PtrOffset G c)
         (PtrOffset v G)
         (RawLoad G)
         (RawStore G c)
         (RawStore v G)
         (FromRawPtr G ρ)
         (Unsafe G))

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

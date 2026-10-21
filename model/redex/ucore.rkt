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
  (bmode ::= const let mut)
  (tn ::= id)
  (ur ::= (urf ...))
  (urf ::= (label uτ m) (label uτ m pr))
  (pr ::= opt)
  ;; RFN-001: 表層に書ける命題。判定表の (Prop id) を足す。常在性 witness の
  ;; (Presence label) は含めない。merge の局所検査だけで立つ命題である。
  (uφ ::= ValidNarrativeTrait TypeNarrativeCap (Prop id)
          (ValidNarrativeTrait tn)
          (Implements uτ tn)
          (RequiresBoth tn tn))
  (uQ ::= (uφ ...))
  (uτ ::= Int Bool Unit String Never Res
          T
          (Data T (uτ ...))
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
  ;; Fn の仮引数と戻り型は、型か #:infer のどちらかで表す。
  (uret ::= uτ #:infer)
  ;; Fn の宣言 row は、省略時に空と区別する。
  (uεr ::= uε #:infer)
  ;; Loop の Leave だけは外側の式境界へ解決するため、Loop 専用の row を持つ。
  (uℓloop ::= uℓ Leave)
  ;; loop 印だけは本体から row を推論できる。
  (uεloop ::= (uℓloop ...) #:infer)
  ;; loop 印だけは初回実引数から仮引数型を推論できる。
  (uτloop ::= uτ #:infer)
  (tℓ ::= (Return b uτ) (Yield uτ) Suspend Partial Compile Own Mutation)
  (tε ::= (tℓ ...))
  (uℓ ::= Return (Yield uτ) Suspend Partial Compile Own Mutation)
  (uε ::= (uℓ ...))
  (spec ::= A (Spec spec spec ...))
  (ubr ::= (K (x ...) -> e)
           (uτ x -> e))
  (uifclause ::= (e e))
  (e ::= l
         x
         (TraitCall T label (e ...))
         (StrHole e)
         (Fn ((x uret) ...) uret uεr e)
         (Apply e e ...)
         (Let x e e)
         (Let (x bmode) e e)
         (Let (x bmode uτ) e e)
         (Rec ((label m e) ...))
         (Proj e label)
         (Construct K e ...)
         (Construct K (Types uτ ...) e ...)
         (Eliminate e (ubr ...))
         ;; SUR-014b1。Surface の lowering が作る印であり、elaborate が明示形の if へ展開する。
         (IfSome (uifclause uifclause ...))
         ;; SUR-014b2a。関数本体の文の mode を elaborate へ伝える印である。
         (BlockBody e)
         ;; SUR-004a1a。Surface の block scope 境界を elaborate へ伝える印である。
         (LexicalScope e)
         (Return e)
         (Leave e)
         (NarrativeExpr e)
         (TryBind x e e)
         (Recur f ((x uτ) ...) uret uε e e)
         ;; SUR-014c0b2。for lowering 専用の固定点計算用 loop 印。
         (Loop f ((x uτloop) ...) uret uεloop e (e ...))
         (FnDecl f ((x uτ) ...) uret uε e e)
         (Yield e e)
         (Suspend e)
         (Move x)
         ;; P1c2b。SCP-001。mut binding への再代入。target は Move と同じ綴りである。
         (Reassign x e)
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
  (tsloop ::= ts (#:infer s))
  ;; SUR-008。結果欄の span は関数全体のものである。
  (tr ::= ts (#:infer s))
  (es ::= (#:ef uε s))
  (esloop ::= (#:ef uεloop s))
  ;; SUR-003。省略 row の span は関数全体のものである。
  (esr ::= es (#:ef #:infer s))
  (sps ::= (#:ty spec s))
  (vr ::= (#:var x s))
  ;; t は Surface の then block span であり、SBlock の lowering 後も
  ;; some と true branch の primary span を保つために節へ残す。
  (uifclause+ ::= (s s e e))
  (lt ::= (#:lit l s))
  (ubr ::= (s K (xs ...) -> e)
           (s ts xs -> e))
  (e ::= lt
         vr
         (TraitCall s T ls (e ...))
         (StrHole s e)
         (Fn s ((xs tr) ...) tr esr e)
         (Apply s e e ...)
         (Let s xs e e)
         (Let s (xs bmode) e e)
         (Let s (xs bmode ts) e e)
         (Rec s ((ls m e) ...))
         (Proj s e ls)
         (Construct s K e ...)
         (Construct s K (Types ts ...) e ...)
         (Eliminate s e (ubr ...))
         (IfSome s (uifclause+ uifclause+ ...) s)
         (BlockBody s e)
         (LexicalScope s e)
         (Return s e)
         (Leave s e)
         (NarrativeExpr s e)
         (TryBind s xs e e)
         (Recur s xs ((xs ts) ...) tr es e e)
         (Loop s xs ((xs tsloop) ...) tr esloop e (e ...))
         (FnDecl s xs ((xs ts) ...) tr es e e)
         (Yield s e e)
         (Suspend s e)
         (Move s vr)
         (Reassign s vr e)
         (Drop s e)
         (Curry s e e)
         (TypeMake s sps)
         (LetType s T (TypeMake s sps) e)))

#lang racket

(require redex/reduction-semantics
         "lang.rkt")

(provide Span span-ok? span-of entry-span G1+ G2+
         peel-node peel-branch branch-span
         peel-ty peel-bind peel-lbl peel-ef
         wrapper-span)

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

;; span.md §7.4: 節点の照合は span を剥いだ形の上で行い、子は spanful のまま残す。
;; 節ごとの pattern を二重に持たないため、剥がしをこの 1 箇所へ寄せる。
;; 先頭が #:var か #:lit なら第 3 要素、それ以外なら第 2 要素が span である。
;; この 2 つの形は表層 AST と G2+ の Core 節点の双方に当てはまるため、
;; elaborate.rkt から移して 3 つの producer で共有する。
(define (span-of node)
  (match node
    [(list (or '#:var '#:lit) _ s) s]
    [(list _ (and s (list '#:span _ _ _)) _ ...) s]
    [_ (error 'span-of "span を持たない節点である: ~s" node)]))

;; diagnostic.md §12: 判断節点の span を取れるならそれを、取れないときだけ
;; synthetic へ落ちる。順序を逆にすると source span があるのに synthetic を返す
;; 実装になる。
(define (entry-span term)
  (define s
    (with-handlers ([exn:fail? (lambda (_) #f)])
      (span-of term)))
  (if (and s (span-ok? s)) s '(#:span #:synthetic 0 0)))

(define (peel-node node)
  (match node
    [(list '#:lit l _) l]
    [(list '#:var x _) x]
    [(list head (list '#:span _ _ _) rest ...) (cons head rest)]
    [_ node]))

;; ubr は span を先頭へ持つ。head を持たないため peel-node と別に扱う。
(define (branch-span branch)
  (match branch
    [(list (and s (list '#:span _ _ _)) _ ...) s]
    [_ (error 'branch-span "span を持たない分岐である: ~s" branch)]))

(define (peel-branch branch)
  (match branch
    [(list (list '#:span _ _ _) rest ...) rest]
    [_ branch]))

;; 型注釈・束縛・label・作用 row の包み。spanless な入力にも使えるよう、
;; 包みでない値はそのまま返す。resolve-annotation は入れ子の型からも呼ばれ、
;; 内側の型は §4.2 の通り包みを持たないためである。
(define (peel-ty t)   (match t [(list '#:ty type _) type] [_ t]))
(define (peel-bind t) (match t [(list '#:bind x _) x] [_ t]))
(define (peel-lbl t)  (match t [(list '#:lbl label _) label] [_ t]))
(define (peel-ef t)   (match t [(list '#:ef row _) row] [_ t]))

;; 包みの span。(#:ty τ s)、(#:bind x s)、(#:lbl label s)、(#:ef ε s) は
;; いずれも第 3 要素へ span を持つ。span-of は節点の第 2 要素を読むため
;; 包みには使えない。両者を 1 つの関数へまとめると、節点の第 2 要素が
;; 偶然 span に見える包みを取り違える余地が残るので、別の名前で分ける。
(define (wrapper-span t)
  (match t
    [(list (or '#:ty '#:bind '#:lbl '#:ef) _ (and s (list '#:span _ _ _))) s]
    [_ (error 'wrapper-span "span を持たない包みである: ~s" t)]))

;; G1 の項へ span を付けた言語。span を持たない非終端（τ κ ℓ ε Q φ t π n l
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
  ;; O は spanless である（span.md §4）。基底の step は (Curry v) であり、
  ;; G1+ が v を spanful へ置き換えると O の内側まで span を要求してしまう。
  ;; 内側の値を文法で spanless と書き下すには G1 の v から c までを複製する
  ;; 必要があるため、受理を any へ広げる。O の妥当性は文法ではなく
  ;; origins.rkt の valid-origin? と origin-shape-valid? が判定する。
  (step ::= (Curry any)
            (Make t)
            (Expand nm)
            (Policy nm)
            (Compose nm O O))
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

;; G2 の項へ span を付けた言語。基底の G1+ がすでに spanful なので、
;; c と v は .... で引き継いだうえで G2 の追加 production を足す。
;; τ と φ は G2 が G1 へ足した production を改めて足す。
(define-extended-language G2+ G1+
  (label ::= variable-not-otherwise-mentioned)
  (m ::= imm mut)
  (bmode ::= const let)
  (r ::= ((label τ m) ...))
  (tn ::= id)
  (τ ::= .... (Record r) (Untrusted τ) (Refined τ φ) (Union τ τ) (Intersection τ τ))
  (φ ::= .... (Prop id) (Presence label) (ValidNarrativeTrait tn)
         (Implements τ tn) (RequiresBoth tn tn) (FieldType label τ))
  (ls ::= (#:lbl label s))
  (c ::= ....
         (Rec s ((ls m c) ...))
         (Proj s c ls)
         (Let s (xs bmode ts) c c)
         (Discharge s (ProofRep s O φ) c))
  (v ::= ....
         (Rec s ((ls m v) ...))
         (UVal s v)
         (RVal s (ProofRep s O φ) v))
  #:binding-forms
  (Let s ((#:bind x s_b) bmode ts) c_1 c_2 #:refers-to x))

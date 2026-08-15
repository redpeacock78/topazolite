#lang racket

(require racket/match
         racket/set
         racket/generic
         redex/reduction-semantics
         "lang.rkt"
         "erase.rkt")

(provide core-children core-with-children core-points core-node
         (struct-out region)
         (struct-out region-ir)
         (struct-out lexical-region-ir)
         gen:region-solver region-solver?
         region-at region-outlives? regions-overlap? regions-exiting-at region-owning
         region->rho rho->region
         region-parent region-contains?
         region-ir-ok? lexical-region-ir-ok? build-region-ir annotate-regions)

;; 意味的な子。c の位置に来る部分項だけが子である（docs/specification/region.md §3）。
;; span、束縛子、型注釈、label、op、O、cid、π、構築子名 K は子に数えない。
;; 子の並びは項の書き順に従う。
;;
;; Construct と Rec は c 側と v 側で同じ形を持つため、1 つの節が両方を受ける。
;; 形が同じでも production は 2 つあり、その網羅は試験の側で押さえる。
(define (core-children t)
  (match t
    [`(Apply ,c_f ,c_a ...) (cons c_f c_a)]
    [`(Let (,_ ...) ,c_1 ,c_2) (list c_1 c_2)]
    [`(Construct ,_ ,_ ,cs ...) cs]
    [`(Eliminate ,c ,brs)
     (cons c (for/list ([br (in-list brs)]) (last br)))]
    [`(Perform ,_ ,c) (list c)]
    [`(Handle ,_ ,h ,c) (list (last h) c)]
    [`(Scope ,_ ,c) (list c)]
    [`(Recur ,_ ,_ ,_ ,c_1 ,c_2) (list c_1 c_2)]
    [`(Yield ,c_1 ,c_2) (list c_1 c_2)]
    [`(Suspend ,c) (list c)]
    [`(Drop ,c) (list c)]
    [`(Curry ,c_1 ,c_2) (list c_1 c_2)]
    [`(Rec ((,_ ,_ ,cs) ...)) cs]
    [`(Proj ,c ,_) (list c)]
    [`(Discharge (ProofRep ,_ ,_) ,c) (list c)]
    [`(Lam ,_ ,_ ,_ ,c) (list c)]
    [`(RecurVal ,_ ,_ ,_ ,c) (list c)]
    [`(UVal ,v) (list v)]
    [`(RVal (ProofRep ,_ ,_) ,v) (list v)]
    [`(CurryVal ,_ ,v_1 ,v_2) (list v_1 v_2)]
    [`(Reborrow ,c) (list c)]
    [`(ReborrowAt ,_ ,c) (list c)]
    [`(Borrow ,_) '()]
    [`(BorrowMut ,_) '()]
    [`(BorrowAt ,_ ,_) '()]
    [`(BorrowMutAt ,_ ,_) '()]
    [`(BorrowRef ,_ ,_) '()]
    [`(BorrowMutRef ,_ ,_) '()]
    [`(Move ,_) '()]
    [`(PrimVal ,_ ,_) '()]
    [`(TypeRep ,_ ,_ ,_) '()]
    [`(ProofRep ,_ ,_) '()]
    [`(resource ,_) '()]
    ;; l ::= integer unit string、x ::= variable-not-otherwise-mentioned。
    ;; 素の値をまとめて空へ落とさず、G2 の production に属することを確かめる。
    [(? exact-integer?) '()]
    [(? string?) '()]
    [(? symbol? s)
     #:when (or (redex-match? G2 x s) (redex-match? G2 l s))
     '()]
    [other (error 'core-children "Core の形ではない: ~s" other)]))

;; core-children の逆。子の並びを差し替えた同じ形を返す。
;; 節の並びは core-children と 1 対 1 で対応させる。片方だけ足すと
;; annotate-regions が子を落とす。
(define (core-with-children t children)
  (define (first-child) (first children))
  (match t
    [`(Apply ,_ ,_ ...) `(Apply ,@children)]
    [`(Let ,binder ,_ ,_) `(Let ,binder ,(first children) ,(second children))]
    [`(Construct ,τ ,K ,_ ...) `(Construct ,τ ,K ,@children)]
    [`(Eliminate ,_ ,brs)
     `(Eliminate ,(first children)
                 ,(for/list ([br (in-list brs)] [c (in-list (rest children))])
                    (append (drop-right br 1) (list c))))]
    [`(Perform ,op ,_) `(Perform ,op ,(first-child))]
    [`(Handle ,op ,h ,_)
     `(Handle ,op
              ,(append (drop-right h 1) (list (first children)))
              ,(second children))]
    [`(Scope ,π ,_) `(Scope ,π ,(first-child))]
    [`(Recur ,cid ,f ,xs ,_ ,_)
     `(Recur ,cid ,f ,xs ,(first children) ,(second children))]
    [`(Yield ,_ ,_) `(Yield ,(first children) ,(second children))]
    [`(Suspend ,_) `(Suspend ,(first-child))]
    [`(Drop ,_) `(Drop ,(first-child))]
    [`(Curry ,_ ,_) `(Curry ,(first children) ,(second children))]
    [`(Rec ((,ls ,ms ,_) ...)) `(Rec ,(map list ls ms children))]
    [`(Proj ,_ ,label) `(Proj ,(first-child) ,label)]
    [`(Discharge ,proof-rep ,_) `(Discharge ,proof-rep ,(first-child))]
    [`(Lam ,O ,cid ,xs ,_) `(Lam ,O ,cid ,xs ,(first-child))]
    [`(RecurVal ,cid ,f ,xs ,_) `(RecurVal ,cid ,f ,xs ,(first-child))]
    [`(UVal ,_) `(UVal ,(first-child))]
    [`(RVal ,proof-rep ,_) `(RVal ,proof-rep ,(first-child))]
    [`(CurryVal ,O ,_ ,_) `(CurryVal ,O ,(first children) ,(second children))]
    [`(Reborrow ,_) `(Reborrow ,(first-child))]
    [`(ReborrowAt ,ρ ,_) `(ReborrowAt ,ρ ,(first-child))]
    [_
     (unless (null? children)
       (error 'core-with-children "子を持たない形へ子を与えた: ~s" t))
     t]))

;; point は根から目的の節点までの意味的な子の添字列である。
;; 定義域は elaboration が返す Core、すなわち G2 の項である。
;; erase-core を入口に通すため、spanful な項を渡しても同じ結果になる。
(define (core-points core)
  (let walk ([t (erase-core core)] [prefix '()])
    (cons (reverse prefix)
          (append*
           (for/list ([k (in-list (core-children t))]
                      [i (in-naturals)])
             (walk k (cons i prefix)))))))

;; point が Core の節点を指さないとき、#f を返さず error を出す。
;; #f を返すと、呼び出し側が「point が無効である」と「その位置に region が
;; 無い」を区別できない。
(define (core-node core point)
  (for/fold ([t (erase-core core)]) ([i (in-list point)])
    (let ([kids (core-children t)])
      (unless (and (exact-nonnegative-integer? i) (< i (length kids)))
        (error 'core-node "Core の節点を指さない point: ~s" point))
      (list-ref kids i))))

;; region 識別子。id は採番の都合であり、消費側は同一性だけを読む。
(struct region (id) #:transparent)

;; region 識別子の採番。すべての build と solver の実行を通じて fresh である。
;; build ごとに 0 へ戻さないのは、独立な ir 2 つの ρ が同じ自然数になると
;; per-IR bridge が由来を判別できなくなるためである（spec §5）。
;; counter は provide しない。採番値の大小、連番、間隔は契約に含めない。
(define region-counter 0)

(define (fresh-region!)
  (define ρ (region region-counter))
  (set! region-counter (add1 region-counter))
  ρ)

;; Core API の 5 method と per-IR bridge の 2 method を宣言する（spec 5 節）。
;; 型の中へ region を書くため、region 識別子を Redex の項へ落とす手段が要る。
;; bridge は Core API とは別の契約であり、4.1 節の本数には数えない。
(define-generics region-solver
  (region-at region-solver point)
  (region-outlives? region-solver ρ_long ρ_short)
  (regions-overlap? region-solver ρ_1 ρ_2)
  (regions-exiting-at region-solver point)
  (region-owning region-solver p)
  (region->rho region-solver ρ)
  (rho->region region-solver n))

;; 3 成分。outlives は直接の制約だけを持ち、推移閉包は持たない。
;; owners は region から、その region が管理する place 列 π への有限写像である。
(struct region-ir (regions outlives owners) #:transparent)

;; inspection API。docs/specification/region.md §6 の adapter 性質を試験する側だけが読む。
;; G5b は読まない。
;; regions-overlap? が呼ぶため、構造体の定義より前へ置く。
(define (region-parent ir ρ)
  (hash-ref (lexical-region-ir-parents ir) ρ #f))

;; 反射的である。ρ は自身を包む。
;; 反射でないと、region がそれ自身と重ならないことになり C2 の意味が壊れる。
(define (region-contains? ir ρ_outer ρ_inner)
  (let loop ([ρ ρ_inner] [fuel (set-count (region-ir-regions ir))])
    (cond
      [(equal? ρ ρ_outer) #t]
      [(zero? fuel) #f]
      [else
       (match (region-parent ir ρ)
         [#f #f]
         [p (loop p (sub1 fuel))])])))

;; 問い合わせの定義域を Core の節点を指す point に限る。
;; adapter は build のときの Core を持たないため、build で列挙した point の
;; 集合をそのまま持つ。
(define (check-point ir point)
  (unless (set-member? (lexical-region-ir-points ir) point)
    (error 'region-query "Core の節点を指さない point: ~s" point)))

(define (lexical-root ir)
  (for/first ([ρ (in-set (region-ir-regions ir))]
              #:unless (hash-has-key? (lexical-region-ir-parents ir) ρ))
    ρ))

;; lexical adapter が持つ内部の表。IR の接点には出さない。
;; parents は Scope の入れ子から読んだ親子関係、at-table は Scope の point から
;; その Scope が開く region への写像、points は Core の全 point である。
(struct lexical-region-ir region-ir (parents at-table points)
  #:transparent
  #:methods gen:region-solver
  [(define (region-at ir point)
     (check-point ir point)
     (or (for/or ([n (in-range (length point) -1 -1)])
           (hash-ref (lexical-region-ir-at-table ir) (take point n) #f))
         (lexical-root ir)))
   ;; outlives における到達可能性。0 歩を含むため反射的である。
   (define (region-outlives? ir ρ_long ρ_short)
     (let loop ([frontier (list ρ_long)] [seen (set)])
       (match frontier
         ['() #f]
         [(cons ρ rest)
          (cond
            [(equal? ρ ρ_short) #t]
            [(set-member? seen ρ) (loop rest seen)]
            [else
             (loop (append rest
                           (for/list ([pair (in-set (region-ir-outlives ir))]
                                      #:when (equal? (first pair) ρ))
                             (second pair)))
                   (set-add seen ρ))])])))
   ;; lexical では、同時に生きる 2 つの region は必ず一方が他方を包む。
   (define (regions-overlap? ir ρ_1 ρ_2)
     (or (region-contains? ir ρ_1 ρ_2) (region-contains? ir ρ_2 ρ_1)))
   ;; point は節点を指す名前であり、時点そのものではない。
   ;; 退場は、その節点の評価が完了する時点を指す。lexical では Scope 節点の
   ;; 評価完了が finalize の呼び出し地点であり、core-calculus.md §5.6 の
   ;; R-ScopeValue、R-ScopeAbort、R-ScopeError が発火する地点と一致する。
   (define (regions-exiting-at ir point)
     (check-point ir point)
     (match (hash-ref (lexical-region-ir-at-table ir) point #f)
       [#f (set)]
       [ρ (set ρ)]))
   ;; core API の 5 本目（docs/specification/region.md §4.1）。
   ;; 実行時の config で place から owner region を引く（spec §7.2）。
   ;; owners から導けるため、region-ir-ok? の 8 条件は増やさない。
   ;;
   ;; 引けない p を root region へ落とさない。root は最も長生きするため、
   ;; 黙って root にすると BOR-001 の判定がすべて通ってしまう。
   (define (region-owning ir p)
     (define found
       (for/list ([(ρ π) (in-hash (region-ir-owners ir))]
                  #:when (memv p π))
         ρ))
     (match found
       [(list ρ) ρ]
       ['() (error 'region-owning "所有者が無い place である: ~s" p)]
       [_ (error 'region-owning "所有者が 2 つ以上ある place である: ~s" p)]))
   ;; 写像は 1 つの ir の中でだけ有効である。別の ir の region や ρ を渡すのは
   ;; error であり、solver が異なる場合も同じ solver の別の実行結果である場合も
   ;; 区別しない。判別は数の由来ではなく ir の所属表への membership で行う。
   (define (region->rho self ρ)
     (unless (set-member? (region-ir-regions self) ρ)
       (error 'region->rho "この ir に属さない region である: ~s" ρ))
     (region-id ρ))

   (define (rho->region self n)
     (define ρ (region n))
     (unless (set-member? (region-ir-regions self) ρ)
       (error 'rho->region "この ir に属さない ρ である: ~s" n))
     ρ)])

(define (place-list? v)
  (and (list? v) (andmap exact-nonnegative-integer? v)))

;; docs/specification/region.md §5 の 8 条件。Core と対で検査するのは、条件 7 と 8 が Core の全 point を
;; 走るためである。and は順に評価されるため、器の形が壊れた IR で問い合わせを
;; 呼ぶ前に止まる。
(define (region-ir-ok? ir core)
  (define regions (region-ir-regions ir))
  (define outlives (region-ir-outlives ir))
  (define owners (region-ir-owners ir))
  (and
   ;; 器の形。
   (set? regions)
   (for/and ([ρ (in-set regions)]) (region? ρ))
   (set? outlives)
   (for/and ([pair (in-set outlives)])
     (and (list? pair) (= 2 (length pair)) (andmap region? pair)))
   (hash? owners)
   (for/and ([v (in-hash-values owners)]) (place-list? v))
   ;; 3 成分の間の整合。
   (not (set-empty? regions))
   (for/and ([pair (in-set outlives)])
     (andmap (lambda (ρ) (set-member? regions ρ)) pair))
   (equal? (list->set (hash-keys owners)) regions)
   ;; 問い合わせの返値。
   (for/and ([point (in-list (core-points core))])
     (and (subset? (regions-exiting-at ir point) regions)
          (set-member? regions (region-at ir point))))))

;; docs/specification/region.md §5 の 2 条件。lexical adapter だけが満たす。
(define (lexical-region-ir-ok? ir)
  (define regions (region-ir-regions ir))
  (define parents (lexical-region-ir-parents ir))
  (and
   (for/and ([(child parent) (in-hash parents)])
     (and (set-member? regions child) (set-member? regions parent)))
   (let ([roots (for/list ([ρ (in-set regions)]
                           #:unless (hash-has-key? parents ρ))
                  ρ)])
     (and (= 1 (length roots))
          ;; 循環が無いこと。どの region からも高々 |regions| 歩で根へ届く。
          (for/and ([ρ (in-set regions)])
            (let loop ([ρ ρ] [fuel (set-count regions)])
              (cond
                [(not (hash-has-key? parents ρ)) #t]
                [(zero? fuel) #f]
                [else (loop (hash-ref parents ρ) (sub1 fuel))])))))))

;; lexical adapter。erase-core を通した項を 1 度だけ歩く。
;; 採番は歩いた順である。C6 が要求するのは外延的な同型であり、採番の安定性
;; ではないため、この順序に意味を持たせない。
(define (build-region-ir core)
  (define erased (erase-core core))
  (define root (fresh-region!))
  (define parents (make-hash))
  (define at-table (make-hash))
  (define owners (make-hash (list (cons root '()))))
  (define outlives (mutable-set))
  (let walk ([t erased] [prefix '()] [current root])
    (define point (reverse prefix))
    (define inner
      (match t
        [`(Scope ,π ,_)
         (define ρ (fresh-region!))
         (hash-set! parents ρ current)
         (hash-set! at-table point ρ)
         (hash-set! owners ρ π)
         ;; 親が子より長生きする。直接の制約だけを入れ、推移閉包は入れない。
         (set-add! outlives (list current ρ))
         ρ]
        [_ current]))
    (for ([k (in-list (core-children t))] [i (in-naturals)])
      (walk k (cons i prefix) inner)))
  (lexical-region-ir
   (list->set (cons root (hash-keys parents)))
   (list->set (set->list outlives))
   (freeze owners)
   (freeze parents)
   (freeze at-table)
   (list->set (core-points erased))))

;; 注釈前の core を 1 回走査し、借用の 3 形へ region を注入する。
;; point の数え方は core-children を使うため region.md §3 と自動的に一致する。
;; ρ は region->rho で natural へ落とす。項に載るのは natural であり、
;; Λ.owners と Ψ が持つのは region 構造体である。
(define (annotate-regions core ir)
  (let walk ([t core] [point '()])
    (define (here) (region->rho ir (region-at ir point)))
    (match t
      [(or `(BorrowAt ,_ ,_) `(BorrowMutAt ,_ ,_) `(ReborrowAt ,_ ,_))
       (error 'annotate-regions "注釈済みの core を再び受けた: ~s" t)]
      [`(Borrow ,w) `(BorrowAt ,(here) ,w)]
      [`(BorrowMut ,w) `(BorrowMutAt ,(here) ,w)]
      [`(Reborrow ,c) `(ReborrowAt ,(here) ,(walk c (append point '(0))))]
      [_
       (core-with-children
        t
        (for/list ([k (in-list (core-children t))] [i (in-naturals)])
          (walk k (append point (list i)))))])))

(define (freeze h)
  (for/hash ([(k v) (in-hash h)]) (values k v)))

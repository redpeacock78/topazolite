#lang racket

(require racket/match
         racket/set
         "region.rkt"
         "region-param.rkt"
         "span-core.rkt")

(provide (struct-out region-ctx)
         empty-region-ctx
         enter-child
         region-ctx-add-owner region-ctx-owner
         region-ctx-add-token region-ctx-token region-ctx-field-table
         region-ctx-source region-ctx-summary
         (struct-out borrow-capability)
         (struct-out psi)
         (struct-out borrow-request)
         (struct-out use-request)
         empty-psi
         psi-join
         psi-suspend
         check-region-annotation
         own-agrees?
         check-borrows
         psi-add-shared
         psi-add-mut
         borrow-typed?
         unbound-borrowed-type?
         borrow-designator?
         borrow-token-key capability-field-table capability-branch-bindings
         field-path?
         path-prefix?
         capability-overlap?)

;; Λ（region 文脈）。spec §3.1。
;; 木を下る向きにだけ流れる不変の値である。parameterize を使わない。
;; ir は build-region-ir が返した region IR、point は現在の節点を指す point、
;; owners は designator から region 識別子への写像、tokens は借用の値を束縛した
;; 変数からその借用が指す designator の集合への写像である。
;; 集合にするのは Eliminate の分岐合流が 2 つ以上の所有者を返しうるためである。
;; 段 9 の Reborrow は集合の全要素を停止する。docs/specification/borrow.md §5。
(struct region-ctx (ir point owners tokens) #:transparent)

;; §5.4。tokens の値。keys は capability の集合、source は §8.1 の起点の
;; α 集合である。summary は関数の値を束ねた名前が運ぶ出現局所の要約であり、
;; 借用でない束縛にも付く。fields は構築子の label と欄の位置ごとの
;; capability 表である。いずれも #f のときは、読む側が今までどおり
;; 型から取り直す。
(struct borrow-capability (keys source summary fields) #:transparent)

(define (empty-region-ctx)
  (region-ctx #f '() (hash) (hash)))

;; 部分項へ降りる。親の Λ は変わらないため、戻るときの復帰は要らない。
;; 子の添字は docs/specification/region.md §3 の表が正である。
(define (enter-child Λ i)
  (struct-copy region-ctx Λ
               [point (append (region-ctx-point Λ) (list i))]))

(define (region-ctx-add-owner Λ w ρ)
  (struct-copy region-ctx Λ
               [owners (hash-set (region-ctx-owners Λ) w ρ)]))

(define (region-ctx-owner Λ w)
  (hash-ref (region-ctx-owners Λ) w #f))

(define (region-ctx-add-token Λ x ws [source #f] [summary #f] [fields #f])
  (struct-copy region-ctx Λ
               [tokens (hash-set (region-ctx-tokens Λ) x
                                 (borrow-capability ws source summary fields))]))

(define (region-ctx-token Λ x)
  (define entry (hash-ref (region-ctx-tokens Λ) x #f))
  (cond
    [(borrow-capability? entry) (borrow-capability-keys entry)]
    ;; 既存の単体試験と外部の region-ctx 構築が持つ旧形式を読み取り専用で
    ;; 受ける。新しい書込み口 region-ctx-add-token は必ず capability を保存する。
    [(set? entry) entry]
    [else (set)]))

(define (region-ctx-source Λ x)
  (define entry (hash-ref (region-ctx-tokens Λ) x #f))
  (and (borrow-capability? entry) (borrow-capability-source entry)))

(define (region-ctx-summary Λ x)
  (define entry (hash-ref (region-ctx-tokens Λ) x #f))
  (and (borrow-capability? entry) (borrow-capability-summary entry)))

;; 移行中の Λ.tokens に旧来の生の集合が残っていても #f を返す。
;; 表を持たない束縛と区別する必要が無いためである。
(define (region-ctx-field-table Λ x)
  (define entry (hash-ref (region-ctx-tokens Λ) x #f))
  (and (borrow-capability? entry) (borrow-capability-fields entry)))

;; Ψ は評価順に流れる permission 状態である。Λ と違い、木を下る向きだけでは
;; 足りない。(Let (y τ) (Reborrow x) c_body) の c_body は (Reborrow x) の
;; 兄弟であり、c_1 で取った借用が c_2 へ届かなければ BOR-002 を判定できない。
(struct psi (shared mut suspended) #:transparent)

;; 段 1 が立てる判定の要求。段 3 が σ の上で判定する。spec §7.3。
(struct borrow-request (w fp mode alpha node) #:transparent)
(struct use-request (w fp operation source point-region node kind otherwise) #:transparent)

(define (empty-psi) (psi (set) (set) (set)))

;; 分岐の合流。どれか 1 つの経路で生きている借用を生きているものとして扱う。
(define (psi-join Ψ_1 Ψ_2)
  (psi (set-union (psi-shared Ψ_1) (psi-shared Ψ_2))
       (set-union (psi-mut Ψ_1) (psi-mut Ψ_2))
       (set-union (psi-suspended Ψ_1) (psi-suspended Ψ_2))))

;; Reborrow で親の可変借用を子 region の間だけ停止する。
;; mut に実在する項目だけを suspended へ退避する。親が共有借用の
;; designator は mut に無いので、退場時に項目を新規作成しない。
(define (psi-suspend Ψ w fp α_parent α_child)
  (define held? (set-member? (psi-mut Ψ) (list w fp α_parent)))
  (psi (set-add (psi-shared Ψ) (list w fp α_child))
       (if held?
           (set-remove (psi-mut Ψ) (list w fp α_parent))
           (psi-mut Ψ))
       (if held?
           (set-add (psi-suspended Ψ) (list w fp α_parent α_child))
           (psi-suspended Ψ))))

;; spec §3.1。fp は label の列である。空の列が root を指す。
(define (field-path? fp)
  (and (list? fp) (andmap symbol? fp)))

;; spec §3.2。fp_1 が fp_2 の接頭辞か。
(define (path-prefix? fp_1 fp_2)
  (cond
    [(null? fp_1) #t]
    [(null? fp_2) #f]
    [(equal? (car fp_1) (car fp_2)) (path-prefix? (cdr fp_1) (cdr fp_2))]
    [else #f]))

;; spec §3.2。root が同じで、一方の path が他方の接頭辞のときだけ重なる。
(define (capability-overlap? w_1 fp_1 w_2 fp_2)
  (and (equal? w_1 w_2)
       (or (path-prefix? fp_1 fp_2)
           (path-prefix? fp_2 fp_1))))

;; 注釈済みの形の ρ は、走査位置の region と一致していなければならない。
;; 一致しない項は annotate-regions を通していない項か、別の ir で注釈した項である。
;; どちらも入力の誤りとして診断する。
(define (check-region-annotation Λ ρ node fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-region-mismatch node))
  (define expected (region->rho ir (region-at ir (region-ctx-point Λ))))
  (unless (equal? ρ expected) (fail 'borrow-region-mismatch node)))

;; own の欄と designator が同じ capability を指すか（spec §5.3）。
;; w が place なら root が w で path は空、借用値なら root/path が一致する。
;; 実行時には R-LetOwnedB の置換後だけが来るため、それ以外は偽にする。
(define (own-agrees? w root fp)
  (match w
    [`(BorrowRef ,p ,fp-w ,_) (and (equal? p root) (equal? fp-w fp))]
    [`(BorrowMutRef ,p ,fp-w ,_) (and (equal? p root) (equal? fp-w fp))]
    [(? exact-nonnegative-integer? p) (and (equal? p root) (null? fp))]
    [_ #f]))

;; 段 3。σ の上で BOR-002 と使用を判定する。spec §7.3 と §8。
;; sigma-ref は typing 側から渡す。borrow.rkt は typing.rkt を require しない。
(define (check-borrows ir σ Ψ requests sigma-ref fail)
  ;; infer-eliminate は attempts と check-as の双方で枝を走査するため、
  ;; 同じ借用要求が重複して収集される。要求は出来事を表すので重複は
  ;; 別 alias ではなく、順序を保ったまま一度だけ判定する。
  (define borrows (remove-duplicates (filter borrow-request? requests)))
  (define uses (filter use-request? requests))
  (define (ρ-of r) (sigma-ref σ (borrow-request-alpha r)))
  ;; 停止中の親は、その子の寿命に完全に含まれる要求との対だけを
  ;; BOR-002 から除く。子の外へはみ出す要求は親が復帰する区間で
  ;; 衝突し得るため、通常どおり判定する。
  (define (suspended-pair? a b)
    (for/or ([e (in-set (psi-suspended Ψ))])
      (define w-parent (first e))
      (define fp-parent (second e))
      (define α-parent (third e))
      (define α-child (fourth e))
      (define ρ-child (sigma-ref σ α-child))
      (define (inside-child? r)
        (define ρ (ρ-of r))
        (and ρ-child ρ (region-outlives? ir ρ-child ρ)))
      (and (capability-overlap? w-parent fp-parent
                                (borrow-request-w a)
                                (borrow-request-fp a))
           (or (and (equal? α-parent (borrow-request-alpha a))
                    (inside-child? b))
               (and (equal? α-parent (borrow-request-alpha b))
                    (inside-child? a))))))
  ;; BOR-002。同じ w の対を決定的な順序で見る。
  (define ordered
    (sort borrows
          (lambda (a b)
            (define wa (format "~s" (borrow-request-w a)))
            (define wb (format "~s" (borrow-request-w b)))
            (if (string=? wa wb)
                (< (alpha-order a) (alpha-order b))
                (string<? wa wb)))))
  (for* ([i (in-range (length ordered))]
         [j (in-range (add1 i) (length ordered))])
    (define a (list-ref ordered i))
    (define b (list-ref ordered j))
    (when (and (capability-overlap? (borrow-request-w a) (borrow-request-fp a)
                                   (borrow-request-w b) (borrow-request-fp b))
               (or (eq? (borrow-request-mode a) 'mut)
                   (eq? (borrow-request-mode b) 'mut))
               (not (suspended-pair? a b))
               (regions-overlap? ir (ρ-of a) (ρ-of b)))
      (fail 'borrow-conflicting-alias (borrow-request-node b))))
  ;; §8.2。所有者への直接の操作と、capability を通した操作を分ける。
  (define (overlapping? r u)
    (and (capability-overlap? (borrow-request-w r) (borrow-request-fp r)
                              (use-request-w u) (use-request-fp u))
         (region-outlives? ir (ρ-of r) (use-request-point-region u))))

  ;; 起点そのものが停止しているか。停止した親を通した使用は
  ;; operation と mode によらず拒む。条件 3 より先に見る。
  (define (source-suspended? u)
    (for/or ([e (in-set (psi-suspended Ψ))])
      (and (set-member? (use-request-source u) (third e))
           (region-outlives? ir (sigma-ref σ (fourth e))
                             (use-request-point-region u)))))

  ;; 条件 2。α_o が source の要素の親として suspended に入っているか。
  (define (parent-of-source? r u)
    (for/or ([e (in-set (psi-suspended Ψ))])
      (and (equal? (borrow-request-alpha r) (third e))
           (set-member? (use-request-source u) (fourth e)))))

  ;; 条件 3。read は mut とだけ競合する。assign と move は両方と競合する。
  (define (mode-conflict? operation mode)
    (if (eq? operation 'read) (eq? mode 'mut) #t))

  (define (use-blocked? u)
    (cond
      [(set-empty? (use-request-source u))
       (for/or ([r (in-list ordered)]) (overlapping? r u))]
      [(source-suspended? u) #t]
      [else
       (for/or ([r (in-list ordered)])
         (and (overlapping? r u)
              (not (set-member? (use-request-source u)
                                (borrow-request-alpha r)))
              (not (parent-of-source? r u))
              (mode-conflict? (use-request-operation u)
                              (borrow-request-mode r))))]))

  ;; 使用。覆う借用が 1 つも無いとき、otherwise を持つ要求だけがその key
  ;; で落ちる。§7.4-7.5。
  (for ([u (in-list uses)])
    (cond
      [(use-blocked? u) (fail (use-kind u) (use-request-node u))]
      [(use-request-otherwise u)
       (fail (use-request-otherwise u) (use-request-node u))]
      [else (void)])))

(define (alpha-order r)
  (match (borrow-request-alpha r)
    [`(RVar ,k) k]
    [_ -1]))

(define (use-kind u) (use-request-kind u))

(define (psi-add-shared Ψ w fp ρ)
  (struct-copy psi Ψ [shared (set-add (psi-shared Ψ) (list w fp ρ))]))

(define (psi-add-mut Ψ w fp ρ)
  (struct-copy psi Ψ [mut (set-add (psi-mut Ψ) (list w fp ρ))]))

(define (borrow-typed? type)
  (match type
    [`(Borrowed ,_ ,_) #t]
    [`(BorrowedMut ,_ ,_) #t]
    [_ #f]))

;; docs/specification/borrow.md §8。型木のどこかに、region 欄が束縛された (RParam rp) でない
;; 借用型が現れるかを返す。
;; 型構築子を列挙せずリストを盲目に降りるため、型文法の拡張に追従する。
;; Borrowed と BorrowedMut の節を先に置くのは、region 欄そのものを盲目に
;; 降りると (RParam rp) の rp が型の葉として扱われるからである。
(define (unbound-borrowed-type? type [bound-params (bound-region-params)])
  (let walk ([t type])
    (match t
      [`(Borrowed ,payload ,ρ)
       (or (not (bound-region-param? ρ bound-params)) (walk payload))]
      [`(BorrowedMut ,payload ,ρ)
       (or (not (bound-region-param? ρ bound-params)) (walk payload))]
      [(? list? ts) (ormap walk ts)]
      [_ #f])))

(define (bound-region-param? ρ bound-params)
  (match ρ
    [`(RParam ,rp) (set-member? bound-params rp)]
    [_ #f]))

;; c が作る借用が指す designator の集合を返す。
;; Reborrow が親の token を特定するために使う（段 9）。
;; Let と Scope と Eliminate を通すのは、借用の値を束縛してから
;; reborrow する形を同じ key へ落とすためである。
;;
;; 入口で peel-node を通す。type-of/raw は span 付きの core をそのまま infer へ
;; 渡すため、生の形だけを match すると Let の bound や Reborrow の operand が
;; span 付きのときに末尾の [_ (set)] へ落ちる。落ちると Λ.tokens から key を
;; 引けず、段 9 の Reborrow が実装誤りの error になる。
;; peel-node は 1 段だけ剥がす。再帰の各段で入口を通るため、これで足りる。
;; w の位置も (#:var x span) になりうるため、その場で剥がす。
;; 分岐は span を先頭に持ち head を持たないため、peel-branch を使う。
;;
;; locals は operand の内側で束縛された名前から token への写像である。
;; Λ.tokens は外側の Let が張った束縛だけを持つ。operand 自身が Let のとき
;; その束縛は Λ に無い。(Reborrow (Let (y let (BorrowedMut Int ρ)) (BorrowMut x) y))
;; がその形であり、locals を持たないと y の対応を失う。
;; locals は Λ.tokens より先に見る。内側の束縛子は外側の同名を遮蔽する。
;;
;; designator が locals にも Λ.tokens にも無いときは、対応を辿れないため
;; E-BOR-020 で落とす（borrow-token-key の #:fail）。
;; borrow-designator? は §8.1 の起点を取る位置でも使う。typing.rkt の
;; use-source が、operand が designator のときだけ写した起点を読む。
(define (borrow-designator? w)
  (or (symbol? w) (exact-nonnegative-integer? w)))

;; 移行中の Λ.tokens/locals に旧来の designator 集合が残っていても、
;; 要求へ流す境界では capability の形へ揃える。
(define (capability-key key)
  (if (and (pair? key) (list? (cdr key)))
      key
      (cons key '())))

(define (capability-set keys)
  (for/set ([key (in-set keys)]) (capability-key key)))

(define (only ws) (cons ws #f))

;; locals には移行前の生の集合が入りうる。組の形へ揃える。
(define (capability-value entry)
  (cond
    [(pair? entry) entry]
    [(set? entry) (only entry)]
    [else (only (set))]))

;; 分岐が合流した表の合併。borrow.md と spec 3.1 節の規則である。
;; ws は合併し、tbl は両方が表のときだけ合併し、片方でも #f なら #f とする。
(define (table-join t_1 t_2)
  (and t_1 t_2
       (for/fold ([acc t_1]) ([(k v) (in-hash t_2)])
         (define prev (hash-ref acc k #f))
         (hash-set acc k
                   (if prev
                       (cons (set-union (car prev) (car v))
                             (table-join (cdr prev) (cdr v)))
                       v)))))

;; scrutinee の表から分岐 K の束縛子へ張る値を並べる。
;; 表が無い、または鍵が無い束縛子へは空の token と #f を張る。
;; capability-of と branch-contexts がこの 1 つの規則を共有する。
(define (capability-branch-bindings tbl K binders)
  (for/list ([_ (in-list binders)] [i (in-naturals 0)])
    (if (hash? tbl)
        (hash-ref tbl (cons K i) (cons (set) #f))
        (cons (set) #f))))

;; capability の集合と表を同時に返す 1 本の走査である。
;; 返り値は (cons ws tbl) の組であり、ws は capability の集合、
;; tbl は (cons K i) から同じ組への hash か #f である。
;;
;; #:fail は現行の borrow-token-key がすでに辿っている枝、すなわち ws を
;; 運ぶ枝だけに伝える。表だけを取るための再帰（Let の非借用の束縛、
;; RegionApp の本体、Eliminate の scrutinee）へは渡さない。渡すと、いま
;; 診断を出さずに通っている programme が E-BOR-020 で落ちる。
(define (capability-of Λ c [locals (hash)] #:fail [fail #f])
  (define (recur c* [locals* locals])
    (capability-of Λ c* locals* #:fail fail))
  (define (ws-of c* [locals* locals]) (car (recur c* locals*)))
  ;; 表だけを取る再帰。fail を伝えない。
  (define (table-of c* [locals* locals])
    (cdr (capability-of Λ c* locals*)))
  (match (peel-node c)
    [`(Borrow ,w) (only (set (cons (peel-node w) '())))]
    [`(BorrowMut ,w) (only (set (cons (peel-node w) '())))]
    [`(BorrowAt ,_ ,_ ,w) (only (set (cons (peel-node w) '())))]
    [`(BorrowMutAt ,_ ,_ ,w) (only (set (cons (peel-node w) '())))]
    [`(BorrowRef ,p ,fp ,_) (only (set (cons (peel-node p) fp)))]
    [`(BorrowMutRef ,p ,fp ,_) (only (set (cons (peel-node p) fp)))]
    [`(Reborrow ,c_1) (only (ws-of c_1))]
    [`(ReborrowAt ,_ ,_ ,c_1) (only (ws-of c_1))]
    [`(ProjBorrowAt ,_ ,_ ,c_1 ,label)
     (define child-caps
       (for/set ([k (in-set (ws-of c_1))])
         (cons (car k) (append (cdr k) (list label)))))
     ;; 射影を重ねた後の累積 path 全体を検証する。単一 label の検査では
     ;; field-path? の定義域（複数要素の列）を実際には検査できない。
     (for ([cap (in-set child-caps)])
       (unless (field-path? (cdr cap))
         (if fail
             (fail 'unresolved-borrow-owner c)
             (error 'borrow-token-key "invalid field path: ~s" (cdr cap)))))
     (only child-caps)]
    [(? borrow-designator? w)
     (define designator (peel-node w))
     (define entry
       (cond
         [(hash-ref locals designator #f) => capability-value]
         [else (cons (region-ctx-token Λ designator)
                     (region-ctx-field-table Λ designator))]))
     (define ws (car entry))
     (cond
       [(not (set-empty? ws)) (cons (capability-set ws) (cdr entry))]
       [fail (fail 'unresolved-borrow-owner c)]
       [else (cons (set) (cdr entry))])]
    [`(Eliminate ,scrutinee ,brs)
     ;; scrutinee を辿るのは表を得るためだけである。Eliminate 全体の値は
     ;; 分岐の本体の値であって scrutinee の値ではないため、ws は合併しない。
     (define tbl_s (table-of scrutinee))
     (define results
       (for/list ([br (in-list brs)])
         (match-define `(,K (,parameters ...) -> ,body) (peel-branch br))
         (define binders (map peel-bind parameters))
         (define bindings (capability-branch-bindings tbl_s K binders))
         (define locals_branch
           (for/fold ([acc_l locals]) ([x (in-list binders)]
                                       [entry (in-list bindings)])
             (hash-set acc_l x entry)))
         (recur body locals_branch)))
     (if (null? results)
         (only (set))
         (for/fold ([acc (car results)]) ([r (in-list (cdr results))])
           (cons (set-union (car acc) (car r))
                 (table-join (cdr acc) (cdr r)))))]
    [`(Scope ,_ ,body) (recur body)]
    [`(Proj ,c_1 ,_) (only (ws-of c_1))]
    [`(Suspend ,c_1) (only (ws-of c_1))]
    [`(Yield ,_ ,c_next) (recur c_next)]
    [`(Handle ,_ ,handler ,body)
     (match-define `(,name -> ,c_h) (peel-branch handler))
     (only (set-union (ws-of body)
                      (ws-of c_h (hash-set locals (peel-bind name)
                                           (cons (set) #f)))))]
    [`(Rec (,fields ...))
     (only (for/fold ([acc (set)]) ([field (in-list fields)])
             (set-union acc (ws-of (third field)))))]
    [`(Construct ,_ ,K ,fields ...)
     (define entries (for/list ([field (in-list fields)]) (recur field)))
     (cons (for/fold ([acc (set)]) ([e (in-list entries)])
             (set-union acc (car e)))
           (for/hash ([e (in-list entries)] [i (in-naturals 0)])
             (values (cons K i) e)))]
    ;; R-RegionApp は包みを剥がすだけで値を変えない。関数の位置が RegionLam
    ;; であればその本体の表をそのまま通す。ws は借用を作らないため空である。
    ;; region-lam-parts は span の有無の両方に対応する。
    [`(RegionApp ,f ,_)
     (define parts (region-lam-parts f))
     (cons (set) (and parts (table-of (third parts))))]
    ;; (,name ,rest ...) は bmode 付きの (x bmode τ) と G1 の (x τ) の両方に合う。
    ;; 宣言型はどちらの形でも最後の要素である。
    ;; 束縛子へ張る token は、宣言型が借用のときだけ bound から計算する。
    ;; place は非負整数であるため、borrow-designator? は place と整数リテラルを
    ;; 区別できない。非借用の束縛で bound を辿ると、(Let (y let Int) 1 y)
    ;; の 1 が designator の節へ落ち、fail 付きの呼出しで E-BOR-020 になる。
    ;; 宣言型で切ると、この取り違えが起きない。
    ;; 表の側にこの制限は要らない。整数リテラルからは表が作れず #f になる。
    [`(Let (,name ,rest ...) ,bound ,body)
     (define borrowed? (borrow-typed? (peel-ty (last rest))))
     (define entry
       (if borrowed?
           (recur bound)
           (cons (set) (table-of bound))))
     (recur body (hash-set locals (peel-bind name) entry))]
    [_ (only (set))]))

(define (borrow-token-key Λ c [locals (hash)] #:fail [fail #f])
  (car (capability-of Λ c locals #:fail fail)))

(define (capability-field-table Λ c [locals (hash)] #:fail [fail #f])
  (cdr (capability-of Λ c locals #:fail fail)))

#lang racket

(require racket/match
         racket/set
         "region.rkt"
         "region-param.rkt"
         "span-core.rkt"
         "erase.rkt"
         "data-env.rkt"
         "schema.rkt"
         "type-equiv.rkt")

(provide (struct-out region-ctx)
         empty-region-ctx
         enter-child
         region-ctx-add-owner region-ctx-owner
         region-ctx-add-token region-ctx-token region-ctx-field-table
         region-ctx-variant-views capability-variant-views
         region-ctx-source region-ctx-summary
         (struct-out borrow-capability)
         (struct-out capability-entry)
         formal-capability-entry
         (struct-out flow-entry)
         (struct-out flow-state)
         (struct-out psi)
         (struct-out borrow-request)
         (struct-out borrow-sidecar)
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
         point-after-decomposition?
         unbound-borrowed-type?
         borrow-designator?
         borrow-token-key capability-field-table capability-field-entries
         capability-of
         capability-branch-bindings
         capability-union-binding
         capability-flow-of handle-return-capability
         capability-projection-bindings
         table-join capability-entry-join
         path-wf? record-path? owner-path?
         collect-tokens owned-leaf? contains-owned-leaf?
         owned-transit? contains-owned-transit? transit-places
         leaf-positions-ok? walk-owned-leaves walk-owned-leaves-for-drop
         observed-leaf-positions-ok?
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
;; capability 表、variants は variant に依存する view の集合である。
;; borrowed-view? は借用を含む値ではなく、借用 view 自体かを示す。
(struct borrow-capability (keys source summary fields variants borrowed-view?) #:transparent)

;; variant に依存する印は、通常の path と混同しないよう別欄に保持する。
(struct capability-entry
  (keys variants fields borrowed-view? source-alphas declared-lifetime)
  #:transparent)

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

(define (region-ctx-add-token Λ x ws [source #f] [summary #f] [fields #f]
                              [variants (set)] [borrowed-view? #f])
  (struct-copy region-ctx Λ
               [tokens (hash-set (region-ctx-tokens Λ) x
                                 (borrow-capability ws source summary fields
                                                    variants borrowed-view?))]))

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

(define (region-ctx-variant-views Λ)
  (for/fold ([views (set)]) ([entry (in-hash-values (region-ctx-tokens Λ))])
    (if (borrow-capability? entry)
        (set-union views (borrow-capability-variants entry))
        views)))

;; Ψ は評価順に流れる permission 状態である。Λ と違い、木を下る向きだけでは
;; 足りない。(Let (y τ) (Reborrow x) c_body) の c_body は (Reborrow x) の
;; 兄弟であり、c_1 で取った借用が c_2 へ届かなければ BOR-002 を判定できない。
;; flow は permission と独立して流れる mut の型状態である。
(struct flow-entry (declared current pins) #:transparent)
(struct flow-state (normal escapes) #:transparent)
(struct psi (shared mut suspended flow) #:transparent)

;; 段 1 が立てる判定の要求。段 3 が σ の上で判定する。spec §7.3。
(struct borrow-request (w fp mode alpha rho-borrow node point) #:transparent)
;; spec §4.4。型検査が段 3 で受理した借用要求と、それを解く σ の組。
;; box の生参照ではなく呼び出し終了時に確定した不変の値であり、alpha は未解決のまま持つ。
;; 消費側が sigma で解いて静的側の借用集合を作る。
(struct borrow-sidecar (requests sigma) #:transparent)
(struct use-request (w fp operation source point-region point node kind otherwise)
  #:transparent)

(define (empty-psi) (psi (set) (set) (set) (flow-state (hash) (hash))))

;; Permission だけを合流する。flow は呼び出し側の枝規則が別に合流する。
(define (psi-join Ψ_1 Ψ_2)
  (psi (set-union (psi-shared Ψ_1) (psi-shared Ψ_2))
       (set-union (psi-mut Ψ_1) (psi-mut Ψ_2))
       (set-union (psi-suspended Ψ_1) (psi-suspended Ψ_2))
       (psi-flow Ψ_1)))

;; Reborrow で親の可変借用を子 region の間だけ停止する。
;; mut に実在する項目だけを suspended へ退避する。親が共有借用の
;; designator は mut に無いので、退場時に項目を新規作成しない。
;; suspended の末尾に Reborrow の節点と構文上の位置を持つ。
(define (psi-suspend Ψ w fp α_parent α_child child-mode node
                     [point #f] [window #f])
  (unless (memq child-mode '(shared mut))
    (raise-argument-error 'psi-suspend "(or/c 'shared 'mut)" child-mode))
  (define held?
    (for/or ([entry (in-set (psi-mut Ψ))])
      (and (equal? (first entry) w)
           (equal? (third entry) α_parent)
           (path-prefix? (second entry) fp))))
  (define child-entry (list w fp α_child))
  (psi (if (eq? child-mode 'shared)
           (set-add (psi-shared Ψ) child-entry)
           (psi-shared Ψ))
       ;; 窓の後で親を再開できるよう、窓付き停止では親の候補を残す。
       (if (and (not window)
                (set-member? (psi-mut Ψ) (list w fp α_parent)))
           (set-remove (psi-mut Ψ) (list w fp α_parent))
           (if (eq? child-mode 'mut)
               (set-add (psi-mut Ψ) child-entry)
               (psi-mut Ψ)))
       (if held?
           (set-add (psi-suspended Ψ)
                    (list w fp α_parent α_child node point window))
           (psi-suspended Ψ))
       (psi-flow Ψ)))

;; path の形そのもの。segment は record の label、位置 natural、union payload である。
(define (path-wf? fp)
  (and (list? fp)
       (andmap (lambda (seg)
                 (or (symbol? seg)
                     (equal? seg '(Payload))
                     (exact-nonnegative-integer? seg)))
               fp)))

;; 借用と射影が使う path。record の label だけを辿る。
(define (record-path? fp)
  (and (list? fp) (andmap symbol? fp)))

;; 所有値の走査が使う path。位置指定も許す。
(define (owner-path? fp)
  ;; owner-path? と path-wf? は同じ segment alphabet を意図的に共有する。
  (path-wf? fp))

;; 値のグラフから token を出現順に集める。重複は保持するので、呼び出し側が
;; 同じ token の複数出現を検出できる。
(define (collect-tokens value)
  (match value
    [`(OwnedLeaf ,tk ,payload) (cons tk (collect-tokens payload))]
    [`(OwnedTransit ,_ ,payload) (collect-tokens payload)]
    [`(Absent ,_) '()]
    [`(UnionVal ,_ ,_ ,payload) (collect-tokens payload)]
    ;; CurryVal の origin は生成履歴であり、固定引数と同じ値を複製して
    ;; 持つことがあるため走査しない。
    [`(CurryVal ,_origin ,function ,fixed)
     (append (collect-tokens function)
             (collect-tokens fixed))]
    [`(RecRewriteOpen (,fields ...))
     (append-map (lambda (field) (collect-tokens (last field))) fields)]
    [(? list?) (append-map collect-tokens value)]
    [_ '()]))

(define (owned-leaf? value)
  (and (list? value)
       (pair? value)
       (eq? (first value) 'OwnedLeaf)))

;; 値のどこかに leaf があるか。位置の妥当性は問わない。
(define (contains-owned-leaf? value)
  (match value
    [`(OwnedTransit ,_ ,payload) (contains-owned-leaf? payload)]
    [`(UnionVal ,_ ,_ ,payload) (contains-owned-leaf? payload)]
    [_ (or (owned-leaf? value)
           (and (list? value) (ormap contains-owned-leaf? value)))]))

;; 移送 marker の place を値全体から前順で集める。
;; contains-owned-transit? も同じ列挙結果を使う。
(define (transit-places value)
  (define (walk current)
    (match (peel-node current)
      [`(OwnedTransit ,place ,payload) (cons place (walk payload))]
      [`(CurryVal ,_origin ,function ,fixed)
       (append (walk function) (walk fixed))]
      [(? list? parts) (append-map walk parts)]
      [_ '()]))
  (walk value))

(define (contains-owned-transit? value)
  (pair? (transit-places value)))

(define (owned-transit? value)
  (match (peel-node value)
    [`(OwnedTransit ,_ ,_) #t]
    [_ #f]))

;; 値の内部の Owned leaf を、その path とともに前順で列挙する。
;; 根の位置の leaf は返さない。根の所有は place と Ω が持つ。
;; b3b で辿る子は Rec と Construct の欄、CurryVal の 2 つの位置、leaf の
;; payload であり、未対応の構成子を汎用 list として辿らない。
(define (walk-owned-leaves/internal value include-root?)
  (define (walk current path root?)
    (match current
      [`(OwnedLeaf ,tk ,payload)
       (append (if (or include-root? (not root?))
                   (list (list tk (reverse path)))
                   '())
               (walk payload path #f))]
      [`(OwnedTransit ,_ ,payload) (walk payload path root?)]
      [`(Absent ,_) '()]
      [`(Rec ((,names ,_modes ,values) ...))
       (append-map (lambda (name child)
                     (walk child (cons name path) #f))
                   names
                   values)]
      [`(Construct ,_type ,_constructor ,fields ...)
       (append-map (lambda (index child)
                     (walk child (cons index path) #f))
                   (range (length fields))
                   fields)]
      [`(UnionVal ,_ ,_ ,payload)
       (walk payload (cons '(Payload) path) #f)]
      [`(CurryVal ,_own ,function ,fixed)
       (append (walk function (cons 0 path) #f)
               (walk fixed (cons 1 path) #f))]
      [_ '()]))
  (walk value '() #t))

(define (walk-owned-leaves value)
  (walk-owned-leaves/internal value #f))

;; Drop は値そのものが leaf のときも token を消費する。finalize 用の
;; walk-owned-leaves は root を除くため、ここでは root を含めて列挙する。
;; Drop は path を event へ出さず token だけを更新するため、root の空 path
;; を finLeaf の生成へ流用してはならない。
(define (walk-owned-leaves-for-drop value)
  (walk-owned-leaves/internal value #t))

;; leaf が回収走査で辿れる位置にだけ現れるかを判定する。Rec の欄と
;; Construct の欄と leaf の payload だけを許し、その他の構成子は leaf を
;; 含まないことを要求して fail-closed にする。
(define (walk-leaf-positions current)
  (match current
    [`(OwnedLeaf ,_tk ,payload)
     (and (not (owned-leaf? payload))
          (walk-leaf-positions payload))]
    [`(OwnedTransit ,_ ,payload) (walk-leaf-positions payload)]
    [`(Absent ,_) #t]
    [`(Rec ((,_name ,_mode ,values) ...))
     (andmap walk-leaf-positions values)]
    [`(Construct ,_type ,_constructor ,fields ...)
     (andmap walk-leaf-positions fields)]
    [`(UnionVal ,_ ,_ ,payload) (walk-leaf-positions payload)]
    [`(CurryVal ,_own ,function ,fixed)
     (and (walk-leaf-positions function)
          (walk-leaf-positions fixed))]
    [(? list?)
     (andmap (lambda (child) (not (contains-owned-leaf? child))) current)]
    [_ #t]))

;; 根の位置の leaf と marker は Ω の root 所有と二重に数えるため拒否する。
(define (leaf-positions-ok? value)
  (and (not (owned-leaf? value))
       (not (owned-transit? value))
       (walk-leaf-positions value)))

;; obs の payload は観測した値そのものなので、根が leaf であることは正当である。
;; 根 leaf の直下の入れ子と未対応の構成子の内部へ隠れた leaf は拒否する。
(define (observed-leaf-positions-ok? value)
  (walk-leaf-positions value))

;; spec §3.2。fp_1 が fp_2 の接頭辞か。
(define (path-prefix? fp_1 fp_2)
  (cond
    [(null? fp_1) #t]
    [(null? fp_2) #f]
    [(equal? (car fp_1) (car fp_2)) (path-prefix? (cdr fp_1) (cdr fp_2))]
    [else #f]))

;; Core の point は core-children の評価順に並ぶ木の path である。
;; Reborrow の operand（子 0）の評価は停止開始より前に終わる。
(define (point-after-reborrow? reborrow-point use-point)
  (cond
    [(equal? reborrow-point use-point) #f]
    [(path-prefix? reborrow-point use-point)
     (not (zero? (list-ref use-point (length reborrow-point))))]
    [(path-prefix? use-point reborrow-point) #f]
    [else
     (let loop ([left reborrow-point] [right use-point])
       (cond
         [(equal? (car left) (car right))
          (loop (cdr left) (cdr right))]
         [else (< (car left) (car right))]))]))

;; Handle と Recur の制御境界を跨ぐ point は線形順に比較できない。
(define (linear-point-order? ir earlier later)
  (or (not (lexical-region-ir? ir))
      (for/and ([entry (in-set (lexical-region-ir-control-order-barriers ir))])
        (match entry
          [(list barrier 'recur)
           (not (and (> (length earlier) (length barrier))
                     (> (length later) (length barrier))
                     (path-prefix? barrier earlier)
                     (path-prefix? barrier later)))]
          [(list barrier 'handle)
           (or (not (and (> (length earlier) (length barrier))
                         (> (length later) (length barrier))
                         (path-prefix? barrier earlier)
                         (path-prefix? barrier later)))
               (equal? (list-ref earlier (length barrier))
                       (list-ref later (length barrier))))]
          [_ #t]))))

(define (point-after-decomposition? ir decomposition later)
  (and (not (path-prefix? decomposition later))
       (linear-point-order? ir decomposition later)
       (let loop ([left decomposition] [right later])
         (cond
           [(or (null? left) (null? right)) #f]
           [(equal? (car left) (car right)) (loop (cdr left) (cdr right))]
           [else (< (car left) (car right))]))))

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
  ;; shortcut: σ に RegionLam 内の RVar が無いときは停止を使わない。σ の
  ;; 解決写像を呼出し側へ伝える経路が入ったら拡張する。
  (define (resolved-suspension? entry)
    (define (resolved-region term)
      (and (or (not (lifetime-var? term))
               (hash-has-key? σ (lifetime-var-index term)))
           (sigma-ref σ term)))
    (define resolved? (and (resolved-region (third entry))
                           (resolved-region (fourth entry))))
    resolved?)
  (define (inside-window? window start point include-start?)
    (and window point
         (path-prefix? window point)
         (or (and include-start? (equal? start point))
             (point-after-reborrow? start point))))
  (define (request-in-window? request other)
    (define entries
      (for/list ([entry (in-set (psi-suspended Ψ))]
                 #:when (and (resolved-suspension? entry)
                             (equal? (borrow-request-alpha request)
                                     (fourth entry))
                             (seventh entry)))
        entry))
    (or (null? entries)
        (not (and (borrow-request-point request)
                  (borrow-request-point other)))
        (for/or ([entry (in-list entries)])
          (and (inside-window? (seventh entry) (sixth entry)
                              (borrow-request-point request) #t)
               (inside-window? (seventh entry) (sixth entry)
                               (borrow-request-point other) #f)))))
  (define (borrow-windows? request)
    (for/or ([entry (in-set (psi-suspended Ψ))])
      (and (resolved-suspension? entry)
           (equal? (borrow-request-alpha request) (fourth entry))
           (seventh entry))))
  ;; Scope で終わる loan は、退場後の point と重ならない。
  (define (scope-ended-before? request later-point)
    (and (lexical-region-ir? ir)
         (borrow-request-point request)
         later-point
         (for/or ([scope-point (in-set (lexical-region-ir-points ir))])
           (and (set-member? (regions-exiting-at ir scope-point)
                             (ρ-of request))
                (path-prefix? scope-point (borrow-request-point request))
                (if (region-decomposition-point? ir scope-point)
                    (point-after-decomposition? ir scope-point later-point)
                    (and (linear-point-order? ir scope-point later-point)
                         (point-after-reborrow? scope-point later-point)))))))
  (define (borrow-pair-overlaps? a b)
    (define a-window? (borrow-windows? a))
    (define b-window? (borrow-windows? b))
    (define points-known?
      (and (borrow-request-point a) (borrow-request-point b)))
    (define regions? (regions-overlap? ir (ρ-of a) (ρ-of b)))
    (cond
      [(and points-known?
            (or (scope-ended-before? a (borrow-request-point b))
                (scope-ended-before? b (borrow-request-point a))))
       #f]
      [(and a-window? b-window? points-known?)
       (or (request-in-window? a b) (request-in-window? b a))]
      [(and a-window? b-window?) regions?]
      [a-window? (and regions? (request-in-window? a b))]
      [b-window? (and regions? (request-in-window? b a))]
      [else regions?]))
  ;; 停止中の親は、その子の寿命に完全に含まれる要求との対だけを
  ;; BOR-002 から除く。子の外へはみ出す要求は親が復帰する区間で
  ;; 衝突し得るため、通常どおり判定する。
  (define (suspended-pair? a b)
    (for/or ([e (in-set (psi-suspended Ψ))]
             #:when (resolved-suspension? e))
      (define w-parent (first e))
      (define fp-parent (second e))
      (define α-parent (third e))
      (define α-child (fourth e))
      (define reborrow-node (fifth e))
      (define ρ-child (sigma-ref σ α-child))
      (define window (seventh e))
      ;; 孫にも停止を伝えるが、各辺の窓と reborrow の包含を保つ。
      (define (suspended-descendant? target request)
        (let loop ([pending (list α-child)] [seen (set)])
          (match pending
            ['() #f]
            [(cons alpha rest)
             (cond
               [(equal? alpha target) #t]
               [(set-member? seen alpha) (loop rest seen)]
               [else
                (define children
                  (for/list ([edge (in-set (psi-suspended Ψ))]
                             #:when
                             (and (resolved-suspension? edge)
                                  (equal? alpha (third edge))
                                  (capability-overlap?
                                   w-parent fp-parent
                                   (first edge) (second edge))
                                  (or (not (seventh edge))
                                      (and (borrow-request-point request)
                                           (inside-window?
                                            (seventh edge) (sixth edge)
                                            (borrow-request-point request) #t)))
                                  (let ([ρ-parent (sigma-ref σ (third edge))]
                                        [ρ-edge-child (sigma-ref σ (fourth edge))]
                                        [ρ-request (ρ-of request)])
                                    (and ρ-parent ρ-edge-child ρ-request
                                         (region-outlives? ir ρ-parent
                                                           ρ-edge-child)
                                         (region-outlives? ir ρ-edge-child
                                                           ρ-request)))))
                    (fourth edge)))
                (loop (append rest children) (set-add seen alpha))])])))
      (define (inside-child? r)
        (define ρ (ρ-of r))
        (if (and window (borrow-request-point r))
            (and (suspended-descendant? (borrow-request-alpha r) r)
                 (inside-window? window (sixth e)
                                 (borrow-request-point r) #t))
            (and (or (>= (alpha-order r) (alpha-term-order α-child))
                     (equal? (borrow-request-node r) reborrow-node))
                 ρ-child ρ (region-outlives? ir ρ-child ρ))))
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
  ;; source を持つ使用では、停止違反を個別の BOR-002 競合より先に調べる。
  ;; source が空の owner 使用はこの判定に当たらず、overlapping? で調べる。
  (define (source-suspended? u)
    (for/or ([e (in-set (psi-suspended Ψ))]
             #:when (resolved-suspension? e))
      (and (set-member? (use-request-source u) (third e))
           (capability-overlap? (first e) (second e)
                                (use-request-w u) (use-request-fp u))
           (if (and (seventh e) (use-request-point u))
               (inside-window? (seventh e) (sixth e)
                               (use-request-point u) #f)
               (and (region-outlives? ir (sigma-ref σ (fourth e))
                                      (use-request-point-region u))
                    (if (and (sixth e) (use-request-point u))
                        (point-after-reborrow? (sixth e) (use-request-point u))
                        #t))))))
  (for* ([i (in-range (length ordered))]
         [j (in-range (add1 i) (length ordered))])
    (define a (list-ref ordered i))
    (define b (list-ref ordered j))
    (define conflict?
      (and (capability-overlap? (borrow-request-w a) (borrow-request-fp a)
                                (borrow-request-w b) (borrow-request-fp b))
           (or (eq? (borrow-request-mode a) 'mut)
               (eq? (borrow-request-mode b) 'mut))
           (not (suspended-pair? a b))
           (borrow-pair-overlaps? a b)))
    (when conflict?
      (fail 'borrow-conflicting-alias (borrow-request-node b))))
  ;; §8.2。所有者への直接の操作と、capability を通した操作を分ける。
  (define (overlapping? r u)
    (and (capability-overlap? (borrow-request-w r) (borrow-request-fp r)
                              (use-request-w u) (use-request-fp u))
         ;; ProjBorrow の Read 要求は借用を作る同じ節点で先に評価される。
         (not (and (match (peel-node (borrow-request-node r))
                    [`(ProjBorrow ,_ ,_) #t]
                    [`(ProjBorrowAt ,_ ,_ ,_) #t]
                    [_ #f])
                   (borrow-request-point r)
                   (use-request-point u)
                   (equal? (borrow-request-point r)
                           (use-request-point u))))
         (not (scope-ended-before? r (use-request-point u)))
         ;; 制御境界をまたがない線形順で、生成前の使用を重複扱いしない。
         (not (and (borrow-request-point r)
                   (use-request-point u)
                   (linear-point-order? ir (borrow-request-point r)
                                        (use-request-point u))
                   (point-after-reborrow? (use-request-point u)
                                          (borrow-request-point r))))
         (let ([windowed
                (for/list ([e (in-set (psi-suspended Ψ))]
                           #:when (and (resolved-suspension? e)
                                       (equal? (borrow-request-alpha r)
                                               (fourth e))
                                       (seventh e)))
                  e)])
           (if (and (pair? windowed)
                    (borrow-request-point r)
                    (use-request-point u))
               (for/or ([e (in-list windowed)])
                 (and (inside-window? (seventh e) (sixth e)
                                     (borrow-request-point r) #t)
                      (inside-window? (seventh e) (sixth e)
                                     (use-request-point u) #f)))
               (region-outlives? ir (ρ-of r)
                                 (use-request-point-region u))))))

  ;; 条件 2。α_o が source の要素の親として suspended に入っているか。
  (define (parent-of-source? r u)
    (let loop ([parents (list (borrow-request-alpha r))] [seen (set)])
      (match parents
        ['() #f]
        [(cons parent rest)
         (cond
           [(set-member? seen parent) (loop rest seen)]
           [else
            (define children
              (for/list ([e (in-set (psi-suspended Ψ))]
                         #:when (and (resolved-suspension? e)
                                     (equal? parent (third e))))
                (fourth e)))
            (or (for/or ([child (in-list children)])
                  (set-member? (use-request-source u) child))
                (loop (append rest children) (set-add seen parent)))])])))

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
    (define blocked? (use-blocked? u))
    (cond
      [blocked? (fail (use-kind u) (use-request-node u))]
      [(use-request-otherwise u)
       (fail (use-request-otherwise u) (use-request-node u))]
      [else (void)])))

(define (alpha-order r)
  (alpha-term-order (borrow-request-alpha r)))

(define (alpha-term-order alpha)
  (match alpha
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

;; docs/specification/borrow.md §8。型木のどこかに未束縛の借用型が現れるかを返す。
;; concrete-regions-bound? は materialize 後の構成検査だけで有効にする。
;; Borrowed と BorrowedMut の節を先に置くのは、region 欄を降りると (RParam rp) の
;; rp が型の葉として扱われるからである。Data では具体化した schema の欄を辿る。
(define unbound-borrowed-visited (make-parameter (set)))
(define (unbound-borrowed-type? type [bound-params (bound-region-params)]
                               #:concrete-regions-bound? [concrete-regions-bound? #f])
  (parameterize ([unbound-borrowed-visited (set)])
    (let walk ([t type])
      (match t
        [`(Borrowed ,payload ,ρ)
         (or (not (bound-region-param? ρ bound-params concrete-regions-bound?))
             (walk payload))]
        [`(BorrowedMut ,payload ,ρ)
         (or (not (bound-region-param? ρ bound-params concrete-regions-bound?))
             (walk payload))]
        [`(Data ,name (,arguments ...))
         (define key (cons name arguments))
         (define schema (data-schema name arguments))
         (cond
           [(not schema) #t]
           [(set-member? (unbound-borrowed-visited) key) #f]
           [else
            (parameterize ([unbound-borrowed-visited
                            (set-add (unbound-borrowed-visited) key)])
              (ormap walk (data-field-types name arguments)))])]
        [(? list? ts) (ormap walk ts)]
        [_ #f]))))

(define (bound-region-param? ρ bound-params concrete-regions-bound?)
  (match ρ
    [`(RParam ,rp) (set-member? bound-params rp)]
    [(? exact-nonnegative-integer?) concrete-regions-bound?]
    [`(RVar ,(? exact-nonnegative-integer?)) concrete-regions-bound?]
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

(define (only ws [variants (set)] [borrowed-view? #f])
  (capability-entry ws variants #f borrowed-view? (set) #f))

(define (entry-ws entry)
  (if (capability-entry? entry) (capability-entry-keys entry) (car entry)))

(define (entry-variants entry)
  (if (capability-entry? entry) (capability-entry-variants entry) (set)))

(define (entry-borrowed-view? entry)
  (and (capability-entry? entry)
       (capability-entry-borrowed-view? entry)))

(define (entry-table entry)
  (if (capability-entry? entry) (capability-entry-fields entry) (cdr entry)))

(define (entry-add-variant-view entry variant? [borrowed-view? #f]
                                [inherited-variants (set)])
  (struct-copy capability-entry entry
               [variants
                (set-union (entry-variants entry)
                           inherited-variants
                           (if variant? (entry-ws entry) (set)))]
               [borrowed-view?
                (or (entry-borrowed-view? entry) borrowed-view?)]))

(define (entry-with-keys entry keys)
  (struct-copy capability-entry entry [keys keys]))

(define (entry-with-parts keys variants fields [borrowed-view? #f]
                          [source-alphas (set)] [declared-lifetime #f])
  (capability-entry keys variants fields borrowed-view?
                    source-alphas declared-lifetime))

(define (entry-with-view entry borrowed-view?)
  (struct-copy capability-entry entry [borrowed-view? borrowed-view?]))

;; locals には移行前の生の集合が入りうる。組の形へ揃える。
(define (capability-value entry)
  (cond
    [(capability-entry? entry) entry]
    [(pair? entry) (entry-with-parts (car entry) (set) (cdr entry))]
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
                       (capability-entry-join (list prev v))
                       v)))))

(struct capability-flow (normal effects) #:transparent)

(define (capability-entry-join entries)
  (define present (map capability-value (filter values entries)))
  (and (pair? present)
       (for/fold ([result (car present)]) ([entry (in-list (cdr present))])
         (entry-with-parts
          (set-union (entry-ws result) (entry-ws entry))
          (set-union (entry-variants result) (entry-variants entry))
          (table-join (entry-table result) (entry-table entry))
          (or (entry-borrowed-view? result)
              (entry-borrowed-view? entry))
          (set-union (capability-entry-source-alphas result)
                     (capability-entry-source-alphas entry))
          (and (equal? (capability-entry-declared-lifetime result)
                       (capability-entry-declared-lifetime entry))
               (capability-entry-declared-lifetime result))))))

(define (capability-table-entry-at-path table path)
  (define (select-field fields segment)
    (cond
      [(hash-has-key? fields segment) (list (hash-ref fields segment))]
      [(symbol? segment)
       (define key (cons 'record-field segment))
       (if (hash-has-key? fields key) (list (hash-ref fields key)) '())]
      [(exact-nonnegative-integer? segment)
       (for/list ([(key entry) (in-hash fields)]
                  #:when (and (pair? key)
                              (not (eq? (car key) 'record-field))
                              (equal? (cdr key) segment)))
         entry)]
      [(equal? segment '(Payload)) (hash-values fields)]
      [else '()]))
  (define (aggregate fields)
    (define entries (hash-values fields))
    (capability-entry
     (for/fold ([keys (set)]) ([entry (in-list entries)])
       (set-union keys (entry-ws entry)))
     (for/fold ([variants (set)]) ([entry (in-list entries)])
       (set-union variants (entry-variants entry)))
     fields #f
     (for/fold ([sources (set)]) ([entry (in-list entries)])
       (set-union sources (capability-entry-source-alphas entry)))
     #f))
  (and (hash? table)
       (if (null? path)
           (aggregate table)
           (let loop ([tables (list table)] [remaining path])
             (define selected
               (append-map (lambda (fields)
                             (select-field fields (car remaining)))
                           tables))
             (cond
               [(null? selected) #f]
               [(null? (cdr remaining)) (capability-entry-join selected)]
               [else
                (loop (filter hash?
                              (map entry-table selected))
                      (cdr remaining))])))))

;; 仮引数の型から、formal root の capability 表と leaf ごとの metadata を作る。
;; capability path は射影用、leaf-map path は欄の表と同じ canonical key である。
(define (formal-capability-entry type root)
  (define leaf-map (make-hash))
  (define (remember-leaf path entry)
    (define present? (hash-has-key? leaf-map path))
    (define previous (and present? (hash-ref leaf-map path)))
    (hash-set! leaf-map path
               (cond
                 [(not present?) entry]
                 [(not previous) #f]
                 [(equal? (capability-entry-declared-lifetime previous)
                          (capability-entry-declared-lifetime entry))
                  (capability-entry-join (list previous entry))]
                 [else #f])))
  (define (add-root entry cap-path formal-path lifetime [borrowed-view? #f])
    (define added
      (entry-with-parts
       (set-add (entry-ws entry) (cons root cap-path))
       (entry-variants entry)
       (entry-table entry)
       (or borrowed-view? (entry-borrowed-view? entry))
       (capability-entry-source-alphas entry)
       lifetime))
    (remember-leaf formal-path added)
    added)
  (define (assemble entries fields)
    (entry-with-parts
     (for/fold ([keys (set)]) ([entry (in-list entries)])
       (set-union keys (entry-ws entry)))
     (for/fold ([variants (set)]) ([entry (in-list entries)])
       (set-union variants (entry-variants entry)))
     fields
     #f
     (for/fold ([sources (set)]) ([entry (in-list entries)])
       (set-union sources (capability-entry-source-alphas entry)))))
  (define (walk type cap-path formal-path seen)
    (define normalized (normalize-type (peel-ty type)))
    (match normalized
      [`(Borrowed ,payload ,lifetime)
       (add-root (only (set)) cap-path formal-path lifetime #t)]
      [`(BorrowedMut ,payload ,lifetime)
       (add-root (only (set)) cap-path formal-path lifetime #t)]
      [`(Record ,row)
       (define fields
         (for/list ([field (in-list row)])
           (define label (first field))
           (define child-cap-path (append cap-path (list label)))
           (define field-key (cons 'record-field label))
           (cons field-key
                 (walk (second field) child-cap-path
                       (append formal-path (list field-key)) seen))))
       (assemble (map cdr fields)
                 (for/hash ([field (in-list fields)])
                   (values (car field) (cdr field))))]
      [`(Union ,_ ,_)
       (define members (union-members normalized))
       (define fields
         (for/list ([raw-member (in-list members)])
           (define member (normalize-type raw-member))
           (define child-cap-path (append cap-path '(Payload)))
           (cons member
                 (walk member child-cap-path
                       (append formal-path (list member)) seen))))
       (assemble (map cdr fields)
                 (for/hash ([field (in-list fields)])
                   (values (car field) (cdr field))))]
      [`(Owned ,inner) (walk inner cap-path formal-path seen)]
      [`(Untrusted ,inner) (walk inner cap-path formal-path seen)]
      [`(Refined ,inner ,_) (walk inner cap-path formal-path seen)]
      [_
       (define schema (constructor-schema normalized))
       (cond
         [(not schema)
          (only (set))]
         [(set-member? seen normalized)
          (if (unbound-borrowed-type? normalized (set))
              (add-root (only (set)) cap-path formal-path #f)
              (only (set)))]
         [else
          (define fields
            (append-map
             (lambda (constructor)
               (for/list ([field-type (in-list (second constructor))]
                          [index (in-naturals)])
                 (define constructor-key (cons (first constructor) index))
                 (cons constructor-key
                       (walk field-type
                             (append cap-path (list index))
                             (append formal-path (list constructor-key))
                             (set-add seen normalized)))))
             schema))
          (define result
            (assemble (map cdr fields)
                      (for/hash ([field (in-list fields)])
                        (values (car field) (cdr field)))))
          result])]))
  (define entry (walk type '() '() (set)))
  (values entry
          (for/hash ([(path leaf) (in-hash leaf-map)])
            (values path leaf))))

(define (capability-effects-join flows)
  (for/fold ([effects (hash)]) ([flow (in-list flows)])
    (for/fold ([effects effects]) ([(boundary entry)
                                   (in-hash (capability-flow-effects flow))])
      (hash-update effects boundary
                   (lambda (previous)
                     (capability-entry-join (list previous entry)))
                   (lambda () entry)))))

(define (capability-operation-key operation)
  (erase-core operation))

(define (handle-return-capability flow operation)
  (define captured
    (hash-ref (capability-flow-effects flow)
              (capability-operation-key operation)
              (only (set))))
  (match (peel-node operation)
    [`(Return ,_ ,type)
     (if (borrow-typed? (peel-ty type))
         (entry-with-view captured #t)
         (entry-with-view (entry-with-keys captured (set)) #f))]
    [_ (only (set))]))

;; 各 operation の payload capability と、通常完了の capability を別々に保つ。
;; Handle は通常値をそのまま返し、捕捉した payload だけを handler へ渡す。
(define (capability-flow-of Λ c [locals (hash)] #:apply-entry [apply-entry #f])
  (define (walk Λ* c* locals*)
    (define (child-flow child index [locals** locals*])
      (walk (enter-child Λ* index) child locals**))
    (define (join-branches flows)
      (capability-flow
       (capability-entry-join (map capability-flow-normal flows))
       (capability-effects-join flows)))
    (define (sequence children [build (lambda ()
                                       (capability-of
                                        Λ* c* locals* #:apply-entry apply-entry))])
      (let loop ([remaining children] [index 0] [effects (hash)])
        (cond
          [(null? remaining) (capability-flow (build) effects)]
          [else
           (define next (child-flow (car remaining) index))
           (define effects*
             (capability-effects-join
              (list (capability-flow #f effects) next)))
           (if (capability-flow-normal next)
               (loop (cdr remaining) (add1 index) effects*)
               (capability-flow #f effects*))])))
    (define (sequence-entries children build)
      (let loop ([remaining children] [index 0] [entries '()] [effects (hash)])
        (cond
          [(null? remaining)
           (capability-flow (build (reverse entries)) effects)]
          [else
           (define next (child-flow (car remaining) index))
           (define effects*
             (capability-effects-join
              (list (capability-flow #f effects) next)))
           (if (capability-flow-normal next)
               (loop (cdr remaining)
                     (add1 index)
                     (cons (capability-flow-normal next) entries)
                     effects*)
               (capability-flow #f effects*))])))
    (define (branch-flow scrutinee-entry branches union?)
      (define ws (entry-ws scrutinee-entry))
      (define table (entry-table scrutinee-entry))
      (define borrowed-view? (entry-borrowed-view? scrutinee-entry))
      (join-branches
       (for/list ([branch (in-list branches)]
                  [branch-index (in-naturals 1)])
         (if union?
             (let* ([plain
                     (match branch
                       [(list (list '#:span _ _ _) _ ...) (peel-ubr branch)]
                       [_ branch])])
               (match-define `(,member ,binder -> ,body) plain)
               (define binding
                 (capability-union-binding table member ws borrowed-view? #f
                                           borrowed-view?
                                           (entry-variants scrutinee-entry)))
               (walk (enter-child Λ* branch-index) body
                     (hash-set locals* (peel-bind binder) binding)))
             (let ()
               (match-define `(,constructor (,binders ...) -> ,body)
                 (peel-branch branch))
               (define bindings
                 (if (hash? table)
                     (capability-branch-bindings
                      table constructor binders
                      (and borrowed-view?
                           (variant-constructor? constructor))
                      borrowed-view?
                      (set))
                     (capability-projection-bindings
                      ws binders
                      (and borrowed-view? (variant-constructor? constructor))
                      borrowed-view?
                      (entry-variants scrutinee-entry))))
               (define branch-locals
                 (for/fold ([current locals*])
                           ([binder (in-list binders)]
                            [binding (in-list bindings)])
                   (hash-set current (peel-bind binder) binding)))
               (walk (enter-child Λ* branch-index) body branch-locals))))))
    (match (peel-node c*)
      [`(Perform ,operation ,payload)
       (define payload-flow (child-flow payload 0))
       (define effects (capability-flow-effects payload-flow))
       (define key (capability-operation-key operation))
       (define effects*
         (if (capability-flow-normal payload-flow)
             (hash-update effects key
                          (lambda (previous)
                            (capability-entry-join
                             (list previous
                                   (capability-flow-normal payload-flow))))
                          (lambda ()
                            (capability-flow-normal payload-flow)))
             effects))
       (capability-flow #f effects*)]
      [`(Handle ,operation ,handler ,body)
       ;; core-children の順は handler=0, body=1。評価順とは異なる。
       (define body-flow (child-flow body 1))
       (define key (capability-operation-key operation))
       (define captured? (hash-has-key? (capability-flow-effects body-flow) key))
       (define captured (handle-return-capability body-flow operation))
       (define handler-flow
         (if captured?
             (match (peel-branch handler)
               [`(,binder -> ,handler-body)
                (walk (enter-child Λ* 0) handler-body
                      (hash-set locals* (peel-bind binder) captured))])
             (capability-flow #f (hash))))
       (define propagated
         (hash-remove (capability-flow-effects body-flow) key))
       (define effects
         (capability-effects-join
          (list (capability-flow #f propagated) handler-flow)))
       (capability-flow
        (capability-entry-join
         (list (capability-flow-normal body-flow)
               (capability-flow-normal handler-flow)))
        effects)]
      [`(Let (,binder ,rest ...) ,bound ,body)
       (define bound-flow (child-flow bound 0))
       (define body-flow
         (if (capability-flow-normal bound-flow)
             (let* ([entry (capability-flow-normal bound-flow)]
                    [binding
                     (if (borrow-typed? (peel-ty (last rest)))
                         (entry-with-view entry #t)
                         (entry-with-view (entry-with-keys entry (set)) #f))])
               (walk (enter-child Λ* 1) body
                     (hash-set locals* (peel-bind binder) binding)))
             (capability-flow #f (hash))))
       (capability-flow
        (capability-flow-normal body-flow)
        (capability-effects-join (list bound-flow body-flow)))]
      [`(Eliminate ,scrutinee (,branches ...))
       (define scrutinee-flow (child-flow scrutinee 0))
       (if (capability-flow-normal scrutinee-flow)
           (let ([branches-flow
                  (branch-flow (capability-flow-normal scrutinee-flow)
                               branches #f)])
             (capability-flow
              (capability-flow-normal branches-flow)
              (capability-effects-join (list scrutinee-flow branches-flow))))
           scrutinee-flow)]
      [`(EliminateAt ,scrutinee (,branches ...))
       (define-values (plain-branches _regions)
         (peel-annotated-data-branches branches))
       (walk Λ* `(Eliminate ,scrutinee ,plain-branches) locals*)]
      [`(UnionEliminate ,scrutinee ,branches)
       (define scrutinee-flow (child-flow scrutinee 0))
       (if (capability-flow-normal scrutinee-flow)
           (let ([branches-flow
                  (branch-flow (capability-flow-normal scrutinee-flow)
                               branches #t)])
             (capability-flow
              (capability-flow-normal branches-flow)
              (capability-effects-join (list scrutinee-flow branches-flow))))
           scrutinee-flow)]
      [`(UnionEliminateAt ,scrutinee ,branches)
       (define-values (plain-branches _regions)
         (peel-annotated-union-branches branches))
       (walk Λ* `(UnionEliminate ,scrutinee ,plain-branches) locals*)]
      [`(Scope ,_ ,body) (child-flow body 0)]
      [`(Yield ,first ,next)
       (define first-flow (child-flow first 0))
       (if (capability-flow-normal first-flow)
           (let ([next-flow (child-flow next 1)])
             (capability-flow
              (capability-flow-normal next-flow)
              (capability-effects-join (list first-flow next-flow))))
           first-flow)]
      [`(Construct ,_ ,constructor ,fields ...)
       (sequence-entries
        fields
        (lambda (entries)
          (entry-with-parts
           (for/fold ([all (set)]) ([entry (in-list entries)])
             (set-union all (entry-ws entry)))
           (for/fold ([all (set)]) ([entry (in-list entries)])
             (set-union all (entry-variants entry)))
           (for/hash ([entry (in-list entries)] [index (in-naturals)])
             (values (cons constructor index) entry)))))]
      [`(Rec (,fields ...))
       (define field-labels (map first fields))
       (sequence-entries
        (map third fields)
        (lambda (entries)
          (entry-with-parts
           (for/fold ([all (set)]) ([entry (in-list entries)])
             (set-union all (entry-ws entry)))
           (for/fold ([all (set)]) ([entry (in-list entries)])
             (set-union all (entry-variants entry)))
           (for/hash ([label (in-list field-labels)]
                      [entry (in-list entries)])
             (values (cons 'record-field (peel-lbl label)) entry)))))]
      [`(UnionInject ,_ ,member-type ,payload)
       (sequence-entries
        (list payload)
        (lambda (entries)
          (define entry (first entries))
          (entry-with-parts
           (entry-ws entry) (entry-variants entry)
           (hash (normalize-type (peel-ty member-type)) entry))))]
      [`(UnionVal ,_ ,member-type ,payload)
       (sequence-entries
        (list payload)
        (lambda (entries)
          (define entry (first entries))
          (entry-with-parts
           (entry-ws entry) (entry-variants entry)
           (hash (normalize-type (peel-ty member-type)) entry))))]
      ;; Function bodies are definitions, while Recur's continuation executes now.
      [`(Lam ,_ ...)
       (capability-flow
        (capability-of Λ* c* locals* #:apply-entry apply-entry) (hash))]
      [`(Recur ,_ ,_ ,_ ,_ ,continuation) (child-flow continuation 1)]
      [`(RecurVal ,_ ,_ ,_ ,_)
       (capability-flow
        (capability-of Λ* c* locals* #:apply-entry apply-entry) (hash))]
      [`(RegionLam ,_ ,_)
       (capability-flow
        (capability-of Λ* c* locals* #:apply-entry apply-entry) (hash))]
      [`(RegionApp ,_ ,_)
       (capability-flow
        (capability-of Λ* c* locals* #:apply-entry apply-entry) (hash))]
      [_ (sequence (core-children (peel-node c*))) ]))
  (walk Λ c locals))

;; scrutinee の表から分岐 K の束縛子へ張る値を並べる。
;; variant が複数ある data の分解では、各欄の path を variant view として記録する。
;; capability-of と branch-contexts がこの 1 つの規則を共有する。
(define (capability-branch-bindings tbl K binders [variant? #f]
                                   [borrowed-view? #f]
                                   [inherited-variants (set)])
  (for/list ([_ (in-list binders)] [i (in-naturals 0)])
    (entry-add-variant-view
     (if (hash? tbl)
         (capability-value (hash-ref tbl (cons K i) (only (set))))
         (only (set)))
     variant? borrowed-view? inherited-variants)))

;; 借用した data 値を Eliminate したとき、束縛子へ張る capability。
;; scrutinee の capability の path の末尾へ 0 起点の欄の位置を積む。
;; 位置を path の segment として作る producer はここだけである。
;; 構成子名を segment へ入れないのは、実行時に選ばれる分岐が 1 つだけで、
;; core-calculus.md §6.2 の leaf の path も位置だけで欄を指すためである。
;; ws が空なら空の token を張る。表も capability も無い場合の結果は
;; capability-branch-bindings が表を持たないときと同じである。
(define (capability-projection-bindings ws binders [variant? #f]
                                       [borrowed-view? #f]
                                       [inherited-variants (set)])
  (for/list ([_ (in-list binders)] [i (in-naturals 0)])
    (define keys
      (for/set ([k (in-set ws)])
        (cons (car k) (append (cdr k) (list i)))))
    (entry-add-variant-view (only keys inherited-variants)
                            variant? borrowed-view? inherited-variants)))

(define (capability-union-binding tbl member ws [variant? #f] [fallback #f]
                                  [borrowed-view? #f]
                                  [inherited-variants (set)])
  (define entry
    (cond
      [fallback (capability-value fallback)]
      [(hash? tbl)
       (capability-value
        (hash-ref tbl (normalize-type (peel-ty member)) (only (set))))]
      [else
       (only (if (set? ws)
                 (for/set ([cap (in-set ws)])
                   (cons (car cap) (append (cdr cap) '((Payload)))))
                 (set)))]))
  (entry-add-variant-view
   entry variant? borrowed-view?
   (if (or fallback (hash? tbl)) (set) inherited-variants)))

(define (capability-variant-views Λ c [locals (hash)] #:apply-entry [apply-entry #f])
  (entry-variants (capability-of Λ c locals #:apply-entry apply-entry)))

(define (variant-constructor? constructor)
  (or (memq constructor '(true false nil cons none some ok ng))
      (match (data-constructor constructor)
        [(list name _)
         (match (data-decl name)
           [`(,_ (,parameters ...) (,constructors ...))
            (> (length constructors) 1)]
           [_ #f])]
        [_ #f])))

;; capability の集合と表を同時に返す 1 本の走査である。
;; 返り値は集合、欄表、variant 印、借用 view の有無を持つ capability-entry。
;;
;; #:fail は現行の borrow-token-key がすでに辿っている枝、すなわち ws を
;; 運ぶ枝だけに伝える。表だけを取るための再帰（Let の非借用の束縛、
;; RegionApp の本体、Eliminate と UnionEliminate の scrutinee）へは渡さない。
;; 渡すと、いま診断を出さずに通っている programme が E-BOR-020 で落ちる。
(define (capability-of Λ c [locals (hash)] #:fail [fail #f]
                       #:allow-empty-keys? [allow-empty-keys? #f]
                       #:apply-entry [apply-entry #f])
  (define (recur c* [locals* locals] [index #f])
    (capability-of (if index (enter-child Λ index) Λ) c* locals*
                   #:fail fail
                   #:allow-empty-keys? allow-empty-keys?
                   #:apply-entry apply-entry))
  (define (ws-of c* [locals* locals]) (entry-ws (recur c* locals*)))
  ;; 表だけを取る再帰。fail を伝えない。
  (define (table-of c* [locals* locals] [index #f])
    (entry-table (capability-of (if index (enter-child Λ index) Λ)
                                c* locals*)))
  (define (member-key type) (normalize-type (peel-ty type)))
  (define (field-key label) (cons 'record-field (peel-lbl label)))
  (define (field-entry c* label)
    ;; Record の束縛は自身の ws が空でも field 表に借用を持てる。
    (define table-parent (capability-of (enter-child Λ 0) c* locals
                                        #:apply-entry apply-entry))
    (define table (entry-table table-parent))
    (if (hash? table)
        (capability-value (hash-ref table (field-key label) (only (set))))
        (let ([parent (recur c* locals 0)])
          (entry-with-keys parent (entry-ws parent)))))
  (define (projborrow-entry operand label)
    (define parent (recur operand locals 0))
    (define child-caps
      (for/set ([k (in-set (entry-ws parent))])
        (cons (car k) (append (cdr k) (list (peel-lbl label))))))
    (for ([cap (in-set child-caps)])
      (unless (owner-path? (cdr cap))
        (if fail
            (fail 'unresolved-borrow-owner c)
            (error 'borrow-token-key "invalid field path: ~s" (cdr cap)))))
    (only child-caps (entry-variants parent) #t))
  (define (field-table-for-root root)
    (define direct (region-ctx-field-table Λ root))
    (or (and (hash? direct) direct)
        (for/fold ([joined #f])
                  ([(name token) (in-hash (region-ctx-tokens Λ))]
                   #:when (and (borrow-capability? token)
                               (hash? (borrow-capability-fields token))
                               (for/or ([cap (in-set
                                              (borrow-capability-keys token))])
                                 (equal? (car cap) root))))
          (if joined
              (table-join joined (borrow-capability-fields token))
              (borrow-capability-fields token)))))
  (define (retain-entry entry type)
    (match (peel-ty type)
      [`(Record ,row)
       (define table (entry-table entry))
       (if (hash? table)
           (let ([retained
                  (for/hash ([field (in-list row)])
                    (define key (field-key (first field)))
                    (values key
                            (retain-entry
                             (capability-value
                              (hash-ref table key (only (set))))
                             (second field))))])
             (entry-with-parts
              (for/fold ([ws (set)]) ([field (in-hash-values retained)])
                (set-union ws (entry-ws field)))
              (for/fold ([views (set)]) ([field (in-hash-values retained)])
                (set-union views (entry-variants field)))
              retained))
           ;; 欄表のない値は、どの capability が除去欄由来か判別できない。
           entry)]
      [_ entry]))
  (match (peel-node c)
    [`(Borrow ,w) (only (set (cons (peel-node w) '())) (set) #t)]
    [`(BorrowMut ,w) (only (set (cons (peel-node w) '())) (set) #t)]
    [`(BorrowAt ,_ ,_ ,w) (only (set (cons (peel-node w) '())) (set) #t)]
    [`(BorrowMutAt ,_ ,_ ,w) (only (set (cons (peel-node w) '())) (set) #t)]
    [`(BorrowRef ,p ,fp ,_)
     (only (set (cons (peel-node p) fp)) (set) #t)]
    [`(BorrowMutRef ,p ,fp ,_)
     (only (set (cons (peel-node p) fp)) (set) #t)]
    [`(UVal ,value) (recur value locals 0)]
    [`(RVal ,_proof ,value) (recur value locals 0)]
    [`(Apply ,_function ,_arguments ...)
     (or (and apply-entry (apply-entry Λ c)) (only (set)))]
    [`(Reborrow ,c_1)
     (define entry (recur c_1 locals 0))
     (only (entry-ws entry) (entry-variants entry)
           (entry-borrowed-view? entry))]
    [`(ReborrowAt ,_ ,c_1)
     (define entry (recur c_1 locals 0))
     (only (entry-ws entry) (entry-variants entry)
           (entry-borrowed-view? entry))]
    [`(ProjBorrow ,c_1 ,label) (projborrow-entry c_1 label)]
    [`(ProjBorrowAt ,_ ,c_1 ,label) (projborrow-entry c_1 label)]
    [(? borrow-designator? w)
     (define designator (peel-node w))
     (define entry
       (cond
         [(hash-ref locals designator #f) => capability-value]
         [else
          (define token (hash-ref (region-ctx-tokens Λ) designator #f))
          (entry-with-parts
           (region-ctx-token Λ designator)
           (if (borrow-capability? token)
               (borrow-capability-variants token)
               (set))
           (region-ctx-field-table Λ designator)
           (and (borrow-capability? token)
                (borrow-capability-borrowed-view? token)))]))
     (define ws (entry-ws entry))
     (cond
       [(not (set-empty? ws))
        (entry-with-keys entry (capability-set ws))]
       [(and fail (not allow-empty-keys?))
        (fail 'unresolved-borrow-owner c)]
       [else (entry-with-keys entry (set))])]
    [`(Eliminate ,scrutinee ,brs)
     ;; scrutinee を辿るのは表と capability を得るためだけである。Eliminate
     ;; 全体の値は分岐の本体の値であって scrutinee の値ではないため、ws は
     ;; 合併しない。表が無ければ欄の位置を ws の path へ積む。
     (define entry_s
       (capability-of (enter-child Λ 0) scrutinee locals
                      #:apply-entry apply-entry))
     (define tbl_s (entry-table entry_s))
     (define ws_s (entry-ws entry_s))
     (define results
       (for/list ([br (in-list brs)] [branch-index (in-naturals 1)])
         (match-define `(,K (,parameters ...) -> ,body) (peel-branch br))
         (define binders (map peel-bind parameters))
         (define bindings
           (if (hash? tbl_s)
               (capability-branch-bindings
                tbl_s K binders
                (and (entry-borrowed-view? entry_s)
                     (variant-constructor? K))
                (entry-borrowed-view? entry_s)
                (set))
               (capability-projection-bindings
                ws_s binders
                (and (entry-borrowed-view? entry_s)
                     (variant-constructor? K))
                (entry-borrowed-view? entry_s)
                (entry-variants entry_s))))
         (define locals_branch
           (for/fold ([acc_l locals]) ([x (in-list binders)]
                                       [entry (in-list bindings)])
             (hash-set acc_l x entry)))
         (recur body locals_branch branch-index)))
     (if (null? results)
         (only (set))
         (for/fold ([acc (car results)]) ([r (in-list (cdr results))])
           (capability-entry-join (list acc r))))]
    [`(EliminateAt ,scrutinee ,brs)
     (define-values (plain-branches _regions)
       (peel-annotated-data-branches brs))
     (recur `(Eliminate ,scrutinee ,plain-branches) locals)]
    [`(UnionEliminate ,scrutinee ,branches)
     (define entry_s
       (capability-of (enter-child Λ 0) scrutinee locals
                      #:apply-entry apply-entry))
     (define tbl_s (entry-table entry_s))
     (define ws_s (entry-ws entry_s))
     (define results
       (for/list ([branch (in-list branches)]
                  [branch-index (in-naturals 1)])
         (define plain
           (match branch
             [(list (list '#:span _ _ _) _ ...) (peel-ubr branch)]
             [_ branch]))
         (match-define `(,member ,binder -> ,body) plain)
         (define binding
           (capability-union-binding tbl_s member ws_s
                                     (entry-borrowed-view? entry_s)
                                     #f
                                     (entry-borrowed-view? entry_s)
                                     (entry-variants entry_s)))
         (recur body (hash-set locals (peel-bind binder) binding)
                branch-index)))
     (if (null? results)
         (only (set))
         (for/fold ([acc (car results)]) ([r (in-list (cdr results))])
           (capability-entry-join (list acc r))))]
    [`(UnionEliminateAt ,scrutinee ,branches)
     (define-values (plain-branches _regions)
       (peel-annotated-union-branches branches))
     (recur `(UnionEliminate ,scrutinee ,plain-branches) locals)]
    [`(Scope ,_ ,body) (recur body locals 0)]
    [`(Proj ,c_1 ,label)
     (field-entry c_1 label)]
    [`(ProjOpt ,_ ,c_1 ,label)
     (define field (field-entry c_1 label))
     (entry-with-parts
      (entry-ws field) (entry-variants field) (hash (cons 'some 0) field))]
    [`(Suspend ,c_1)
     (define entry (recur c_1 locals 0))
     (only (entry-ws entry) (entry-variants entry)
           (entry-borrowed-view? entry))]
    [`(Yield ,_ ,c_next) (recur c_next locals 1)]
    [`(Handle ,_ ,handler ,body)
     (define flow (capability-flow-of Λ c locals #:apply-entry apply-entry))
     (or (capability-flow-normal flow) (only (set)))]
    [`(Read ,operand)
     (define operand-entry (recur operand locals 0))
     (define entries
       (for/list ([cap (in-set (entry-ws operand-entry))]
                  #:do [(define table (field-table-for-root (car cap)))]
                  #:when (hash? table)
                  #:do [(define selected
                          (capability-table-entry-at-path table (cdr cap)))]
                  #:when selected)
         selected))
     (or (and (pair? entries) (capability-entry-join entries))
         (only (set)))]
    [`(Rec (,fields ...))
     (define entries
       (for/list ([field (in-list fields)] [index (in-naturals)])
         (recur (third field) locals index)))
     (entry-with-parts
      (for/fold ([acc (set)]) ([entry (in-list entries)])
        (set-union acc (entry-ws entry)))
      (for/fold ([all (set)]) ([entry (in-list entries)])
        (set-union all (entry-variants entry)))
      (for/hash ([field (in-list fields)] [entry (in-list entries)])
        (values (field-key (first field)) entry)))]
    [`(Absent ,_) (only (set))]
    [`(Construct ,_ ,K ,fields ...)
     (define entries
       (for/list ([field (in-list fields)] [index (in-naturals)])
         (recur field locals index)))
     (entry-with-parts
      (for/fold ([acc (set)]) ([e (in-list entries)])
        (set-union acc (entry-ws e)))
      (for/fold ([all (set)]) ([e (in-list entries)])
        (set-union all (entry-variants e)))
      (for/hash ([e (in-list entries)] [i (in-naturals 0)])
        (values (cons K i) e)))]
    [`(UnionInject ,_ ,member-type ,payload)
     (define entry (recur payload locals 0))
     (entry-with-parts
      (entry-ws entry) (entry-variants entry)
      (hash (member-key member-type) entry))]
    [`(UnionVal ,_ ,member-type ,payload)
     (define entry (recur payload locals 0))
     (entry-with-parts
      (entry-ws entry) (entry-variants entry)
      (hash (member-key member-type) entry))]
    [`(RecRewriteOpen (,fields ...))
     (define entries
       (for/list ([field (in-list fields)] [index (in-naturals)])
         (recur (last field) locals index)))
     (entry-with-parts
      (for/fold ([acc (set)]) ([entry (in-list entries)])
        (set-union acc (entry-ws entry)))
      (for/fold ([all (set)]) ([entry (in-list entries)])
        (set-union all (entry-variants entry)))
      (for/hash ([field (in-list fields)] [entry (in-list entries)])
        (values (field-key (first field)) entry)))]
    [`(RecRewrite ,input ,entries)
     (define input-entry (recur input locals 0))
     (define input-ws (entry-ws input-entry))
     (define input-table (entry-table input-entry))
     ;; 非対象欄は入力 entry、対象欄は書換え後の entry を出力する。
     (define (source-entry label)
       (if (hash? input-table)
           (hash-ref input-table (field-key label) (only (set)))
           (only input-ws)))
     (define rewritten
       (for/list ([entry (in-list entries)] [entry-index (in-naturals 1)])
         (match entry
           [(list label binder _ _ _ body)
            (define source (source-entry label))
            (define name (peel-bind binder))
            (define result
              (if (eq? (peel-node body) name)
                  source
                  (recur body (hash-set locals name source) entry-index)))
           (list (field-key label) result
                  (not (eq? (peel-node body) name)))])))
     (define output-table
       (and (hash? input-table)
            (for/hash ([(key input-field) (in-hash input-table)])
              (values key
                      (or (for/first ([entry (in-list rewritten)]
                                      #:when (equal? (first entry) key))
                            (second entry))
                          input-field)))))
     (entry-with-parts
      (for/fold ([all input-ws]) ([entry (in-list rewritten)]
                                  #:when (third entry))
        (set-union all (entry-ws (second entry))))
      (if output-table
          (for/fold ([all (set)]) ([entry (in-hash-values output-table)])
            (set-union all (entry-variants entry)))
          (for/fold ([all (entry-variants input-entry)])
                    ([entry (in-list rewritten)] #:when (third entry))
            (set-union all (entry-variants (second entry)))))
      output-table)]
    ;; RegionLam は本体へ置き換わるので本体の表を通す。
    ;; RecurVal は関数値のままなので関数値自身の表を通す。
    [`(RegionApp ,f ,_)
     (define parts (region-lam-parts f))
     (define entry
       (cond
         [parts
          (capability-of (enter-child (enter-child Λ 0) 0)
                         (third parts) locals
                         #:apply-entry apply-entry)]
         [(match (peel-node f)
            [`(RecurVal ,_cid ,_f ,_xs ,_c_body) #t]
            [_ #f])
          (capability-of (enter-child Λ 0) f locals
                         #:apply-entry apply-entry)]
         [else (only (set))]))
     (entry-with-parts (set) (entry-variants entry) (entry-table entry))]
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
     (define bound-entry
       (if borrowed?
           (recur bound locals 0)
           (capability-of (enter-child Λ 0) bound locals
                          #:apply-entry apply-entry)))
     (define entry
       (if borrowed?
           bound-entry
           (entry-with-keys bound-entry (set))))
     (recur body (hash-set locals (peel-bind name) entry) 1)]
    [`(Discharge ,proof ,inner)
     (define entry (recur inner locals 0))
     (match (peel-node proof)
       [`(ProofRep ,_ (RemainderSafelyDropped ,_ ,expected))
        (retain-entry entry expected)]
       [_ entry])]
    [`(OwnLeaf ,payload) (recur payload locals 0)]
    [`(OwnedLeaf ,_ ,payload) (recur payload locals 0)]
    [`(OwnedTransit ,_ ,payload) (recur payload locals 0)]
    [`(Unsafe ,body) (recur body locals 0)]
    [`(Recur ,_ ,_ ,_ ,_ ,continuation)
     (recur continuation locals 1)]
    [_ (only (set))]))

(define (borrow-token-key Λ c [locals (hash)] #:fail [fail #f]
                         #:apply-entry [apply-entry #f])
  (entry-ws (capability-of Λ c locals #:fail fail
                           #:apply-entry apply-entry)))

(define (capability-field-entries Λ c [locals (hash)] #:fail [fail #f]
                                 #:apply-entry [apply-entry #f])
  (entry-table (capability-of Λ c locals #:fail fail
                              #:apply-entry apply-entry)))

(define (legacy-capability-table table)
  (and (hash? table)
       (for/hash ([(key raw-entry) (in-hash table)])
         (define entry (capability-value raw-entry))
         (values key
                 (cons (entry-ws entry)
                       (legacy-capability-table (entry-table entry)))))))

(define (capability-field-table Λ c [locals (hash)] #:fail [fail #f])
  (legacy-capability-table
   (entry-table (capability-of Λ c locals #:fail fail))))

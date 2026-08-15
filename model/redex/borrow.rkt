#lang racket

(require racket/match
         racket/set
         "region.rkt"
         "span-core.rkt")

(provide (struct-out region-ctx)
         empty-region-ctx
         enter-child
         region-ctx-add-owner region-ctx-owner
         region-ctx-add-token region-ctx-token
         (struct-out psi)
         empty-psi
         psi-join
         psi-suspend
         psi-exit
         check-region-annotation
         borrow-allowed?
         borrow-mut-allowed?
         use-allowed?
         psi-add-shared
         psi-add-mut
         borrow-typed?
         borrowed-type?
         borrow-token-key)

;; Λ（region 文脈）。spec §3.1。
;; 木を下る向きにだけ流れる不変の値である。parameterize を使わない。
;; ir は build-region-ir が返した region IR、point は現在の節点を指す point、
;; owners は designator から region 識別子への写像、tokens は借用の値を束縛した
;; 変数からその借用が指す designator の集合への写像である。
;; 集合にするのは Eliminate の分岐合流が 2 つ以上の所有者を返しうるためである。
;; 段 9 の Reborrow は集合の全要素を停止する。docs/specification/borrow.md §5。
(struct region-ctx (ir point owners tokens) #:transparent)

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

(define (region-ctx-add-token Λ x ws)
  (struct-copy region-ctx Λ
               [tokens (hash-set (region-ctx-tokens Λ) x ws)]))

(define (region-ctx-token Λ x)
  (hash-ref (region-ctx-tokens Λ) x (set)))

;; Ψ は評価順に流れる permission 状態である。Λ と違い、木を下る向きだけでは
;; 足りない。(Let (y τ) (Reborrow x) c_body) の c_body は (Reborrow x) の
;; 兄弟であり、c_1 で取った借用が c_2 へ届かなければ BOR-002 を判定できない。
(struct psi (shared mut suspended) #:transparent)

(define (empty-psi) (psi (set) (set) (set)))

;; 分岐の合流。どれか 1 つの経路で生きている借用を生きているものとして扱う。
(define (psi-join Ψ_1 Ψ_2)
  (psi (set-union (psi-shared Ψ_1) (psi-shared Ψ_2))
       (set-union (psi-mut Ψ_1) (psi-mut Ψ_2))
       (set-union (psi-suspended Ψ_1) (psi-suspended Ψ_2))))

;; Reborrow で親の可変借用を子 region の間だけ停止する。
;; mut に実在する項目だけを suspended へ退避する。自己 fallback で得た
;; designator は mut に無いので、退場時に項目を新規作成しない。
(define (psi-suspend Ψ w ρ_parent ρ_child)
  (define held? (set-member? (psi-mut Ψ) (list w ρ_parent)))
  (psi (set-add (psi-shared Ψ) (list w ρ_child))
       (if held?
           (set-remove (psi-mut Ψ) (list w ρ_parent))
           (psi-mut Ψ))
       (if held?
           (set-add (psi-suspended Ψ) (list w ρ_parent ρ_child))
           (psi-suspended Ψ))))

;; Scope の退場。exiting は regions-exiting-at が返す region の集合である。
;; suspended の親 capability は子 region の退場で復帰する。
(define (psi-exit Ψ exiting)
  (define (keep entries index)
    (for/set ([entry (in-set entries)]
              #:unless (set-member? exiting (list-ref entry index)))
      entry))
  (define restored
    (for/set ([entry (in-set (psi-suspended Ψ))]
              #:when (and (set-member? exiting (third entry))
                          (not (set-member? exiting (second entry)))))
      (list (first entry) (second entry))))
  (psi (keep (psi-shared Ψ) 1)
       (set-union (keep (psi-mut Ψ) 1) restored)
       (keep (psi-suspended Ψ) 2)))

;; 注釈済みの形の ρ は、走査位置の region と一致していなければならない。
;; 一致しない項は annotate-regions を通していない項か、別の ir で注釈した項である。
;; どちらも入力の誤りとして診断する。
(define (check-region-annotation Λ ρ node fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-region-mismatch node))
  (define expected (region->rho ir (region-at ir (region-ctx-point Λ))))
  (unless (equal? ρ expected) (fail 'borrow-region-mismatch node)))

;; permission map の key は w である。x と p を同じ空間で扱う。
;; 静的な core には x だけが、実行時の config には p だけが現れるため、
;; 両者が同じ Ψ に混在することは無い。
(define (conflicts? entries w ρ_borrow ir)
  (for/or ([entry (in-set entries)])
    (and (equal? (first entry) w)
         (regions-overlap? ir (second entry) ρ_borrow))))

;; [REQ: BOR-002] 共有借用どうしは許す。可変借用と重なるときだけ拒む。
(define (borrow-allowed? Ψ w ρ_borrow ir)
  (not (conflicts? (psi-mut Ψ) w ρ_borrow ir)))

;; [REQ: BOR-002] 可変借用は排他である。共有借用とも可変借用とも重なれない。
(define (borrow-mut-allowed? Ψ w ρ_borrow ir)
  (and (not (conflicts? (psi-mut Ψ) w ρ_borrow ir))
       (not (conflicts? (psi-shared Ψ) w ρ_borrow ir))))

;; Move と Drop は、その w について生きている借用が 1 つも無いときだけ許す。
;; suspended も見る。reborrow で停止した親は mut に無いため、
;; suspended を見なければ停止中の親を Move できてしまう。
(define (use-allowed? Ψ w)
  (define (holds? entries) (for/or ([e (in-set entries)]) (equal? (first e) w)))
  (not (or (holds? (psi-shared Ψ))
           (holds? (psi-mut Ψ))
           (holds? (psi-suspended Ψ)))))

(define (psi-add-shared Ψ w ρ)
  (struct-copy psi Ψ [shared (set-add (psi-shared Ψ) (list w ρ))]))

(define (psi-add-mut Ψ w ρ)
  (struct-copy psi Ψ [mut (set-add (psi-mut Ψ) (list w ρ))]))

(define (borrow-typed? type)
  (match type
    [`(Borrowed ,_ ,_) #t]
    [`(BorrowedMut ,_ ,_) #t]
    [_ #f]))

;; spec §14。型木のどこかに Borrowed または BorrowedMut が現れるかを返す。
;; 型構築子を列挙せずリストを盲目に降りるため、型文法の拡張に追従する。
(define (borrowed-type? type)
  (match type
    [`(Borrowed ,_ ,_) #t]
    [`(BorrowedMut ,_ ,_) #t]
    [(? list? ts) (ormap borrowed-type? ts)]
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
;; designator が locals にも Λ.tokens にも無いときは、その designator 自身を
;; 親 capability とみなす（borrow.md §5）。データへ格納された借用を分岐の
;; 束縛子で受けた形がこれに当たり、真の所有者は構造からは辿れない。
;; borrow-designator? は provide しない。この手続きの内部だけで使う。
(define (borrow-designator? w)
  (or (symbol? w) (exact-nonnegative-integer? w)))

(define (borrow-token-key Λ c [locals (hash)])
  (match (peel-node c)
    [`(Borrow ,w) (set (peel-node w))]
    [`(BorrowMut ,w) (set (peel-node w))]
    [`(BorrowAt ,_ ,w) (set (peel-node w))]
    [`(BorrowMutAt ,_ ,w) (set (peel-node w))]
    [`(BorrowRef ,p ,_) (set (peel-node p))]
    [`(BorrowMutRef ,p ,_) (set (peel-node p))]
    [`(Reborrow ,c_1) (borrow-token-key Λ c_1 locals)]
    [`(ReborrowAt ,_ ,c_1) (borrow-token-key Λ c_1 locals)]
    [(? borrow-designator? w)
     (define ws (hash-ref locals w (lambda () (region-ctx-token Λ w))))
     (if (set-empty? ws) (set w) ws)]
    [`(Eliminate ,_ ,brs)
     (for/fold ([acc (set)]) ([br (in-list brs)])
       (match-define `(,_ (,parameters ...) -> ,body) (peel-branch br))
       (define locals_branch
         (for/fold ([acc_l locals]) ([p (in-list parameters)])
           (hash-set acc_l (peel-bind p) (set))))
       (set-union acc (borrow-token-key Λ body locals_branch)))]
    [`(Scope ,_ ,body) (borrow-token-key Λ body locals)]
    [`(Proj ,c_1 ,_) (borrow-token-key Λ c_1 locals)]
    [`(Suspend ,c_1) (borrow-token-key Λ c_1 locals)]
    [`(Yield ,_ ,c_next) (borrow-token-key Λ c_next locals)]
    [`(Handle ,_ ,handler ,body)
     (match-define `(,name -> ,c_h) (peel-branch handler))
     (set-union (borrow-token-key Λ body locals)
                (borrow-token-key Λ c_h
                                  (hash-set locals (peel-bind name) (set))))]
    [`(Rec (,fields ...))
     (for/fold ([acc (set)]) ([field (in-list fields)])
       (set-union acc (borrow-token-key Λ (third field) locals)))]
    [`(Construct ,_ ,_ ,fields ...)
     (for/fold ([acc (set)]) ([field (in-list fields)])
       (set-union acc (borrow-token-key Λ field locals)))]
    ;; (,name ,rest ...) は bmode 付きの (x bmode τ) と G1 の (x τ) の両方に合う。
    ;; 宣言型はどちらの形でも最後の要素である。
    ;; 束縛子へ張る token は、宣言型が借用のときだけ bound から計算する。
    ;; place は非負整数であるため、borrow-designator? は place と整数リテラルを
    ;; 区別できない。非借用の束縛で bound を辿ると、(Let (y let Int) 1 y) の 1 が
    ;; designator の節へ落ち、自己 fallback によって y の token へ {1} を張る。
    ;; そのとき y 自身の token も {1} になり、y は自分を指す key を失う。
    ;; 宣言型で切ると、この取り違えが起きない。
    [`(Let (,name ,rest ...) ,bound ,body)
     ;; 非借用の束縛は Task 8 の回帰どおり空集合を張る。Reborrow の
     ;; operand になりうるのは宣言型が借用の束縛であり、その場合だけ
     ;; bound の token を body へ渡す。
     (define token
       (if (borrow-typed? (peel-ty (last rest)))
           (borrow-token-key Λ bound locals)
           (set)))
     (borrow-token-key Λ body (hash-set locals (peel-bind name) token))]
    [_ (set)]))

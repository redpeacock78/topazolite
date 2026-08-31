#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt"
         "../machine.rkt")

;; fixture は注釈前の形で書き、annotate-regions を 1 度だけ通す。
;; Let の宣言型の ρ は IR から引く。Task 8 と同じ引き方である。
(define (rho-at ir point) (region->rho ir (region-at ir point)))

;; 同じ起点を共有する借用 2 件が、point で区別されて別の σ へ置き換わる。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (a let (Borrowed Res ,ρ)) (Borrow 1)
                     (Scope () (Yield (Borrow 1) 0)))))
  (define ir (build-region-ir (make 0)))
  ;; 外側の Borrow は Let の子 0 で '(0 0)、内側は Yield の observed 側で
  ;; '(0 1 0 0) に居る。next を 0 に閉じ、内側の寿命を外へ流さない。
  (define annotated (annotate-regions (make (rho-at ir '(0 0))) ir))
  (define Λ (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))
  (match-define (list _type tbl cs _rs _ras _summaries)
    (typing-inference annotated (list (list 1 'Res)) '() '() Λ))
  (match-define (list 'ok σ) (typing-solve ir cs))
  (define out (materialize-regions ir annotated tbl σ))
  ;; 注釈欄はすべて natural である。RVar は残らない。
  (for ([point (in-list (core-points out))])
    (match (core-node out point)
      [`(BorrowAt ,ρ ,_ ,_) (check-true (exact-nonnegative-integer? ρ))]
      [`(BorrowMutAt ,ρ ,_ ,_) (check-true (exact-nonnegative-integer? ρ))]
      [`(ReborrowAt ,ρ ,_ ,_) (check-true (exact-nonnegative-integer? ρ))]
      [_ (void)]))
  ;; 2 件の注釈が別々に置き換わっている。
  (check-equal? (hash-count tbl) 2)
  ;; 鍵が point であることは、出力の 2 つの ρ が異なることで初めて確かめられる。
  ;; 数だけを見ると、両者が同じ ρ へ落ちても試験は通ってしまう。
  ;; 外側の Borrow は外の Scope の region、内側は内の Scope の region を得る。
  (define ρ-outer (match (core-node out '(0 0)) [`(BorrowAt ,ρ ,_ ,_) ρ]))
  (define ρ-inner (match (core-node out '(0 1 0 0)) [`(BorrowAt ,ρ ,_ ,_) ρ]))
  (check-not-equal? ρ-outer ρ-inner))

;; type-of の返す型に RVar が残らない。
(let ()
  (define core '(Scope (1) (Borrow 1)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (match-define (list 'ok (list type _row))
    (type-of/raw annotated (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (define (has-rvar? t)
    (match t
      [`(RVar ,_) #t]
      [(? list? ts) (ormap has-rvar? ts)]
      [_ #f]))
  (check-false (has-rvar? type)))

;; materialize した注釈を、機械が BorrowRef の ρ へそのまま運ぶ。
;; R-Borrow は BorrowAt の ρ を写すだけなので、両者は一致しなければならない。
(let ()
  (define core '(Scope (1) (Scope () (Borrow 1))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define Λ (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))
  (match-define (list 'ok _type out)
    (core-type-of/materialized annotated (list (list 1 'Res)) '() '() Λ))
  (define ρ-materialized
    (let walk ([t out])
      (match t
        [`(BorrowAt ,ρ ,_ ,_) ρ]
        [(? list? ts) (ormap walk ts)]
        [_ #f])))
  (check-true (exact-nonnegative-integer? ρ-materialized))
  (define config `(cfg ,out ((1 1)) ((1 Available)) () ()))
  (define next (raw-steps-g2 config))
  (check-equal? (length next) 1)
  (define ρ-machine
    (let walk ([t (first next)])
      (match t
        [`(BorrowRef ,_ ,_ ,ρ) ρ]
        [(? list? ts) (ormap walk ts)]
        [_ #f])))
  (check-equal? ρ-machine ρ-materialized))

;; materialize 後の core へ check-region-annotation を掛けると、寿命が
;; 起点より広がった借用では落ちる。この検査は起点との一致を見る道具であり、
;; 型付けの経路が二度掛けしていないことを、経路の側で保証する。

;; infer-eliminate は同じ分岐を infer と check-as の二度走査する。
;; 同じ point の alpha-table が後の alpha で上書きされても、両走査の
;; σ は同じ region を与え、materialize の結果は変わらないことを確認する。
(let ()
  (define core
    '(Scope (1)
       (Let (x let (Owned Res)) (resource 1)
         (Eliminate (Construct (Option Int) some 0)
           ((none () -> (Borrow x))
            (some (y) -> (Borrow x)))))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define Λ (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))
  (match-define (list 'ok _type out)
    (core-type-of/materialized annotated (list (list 1 'Res)) '() '() Λ))
  (define (borrow-at-rhos t)
    (match t
      [`(BorrowAt ,ρ ,_ ,_) (list ρ)]
      [(? list? ts) (apply append (map borrow-at-rhos ts))]
      [_ '()]))
  (define rhos (borrow-at-rhos out))
  (define branch-points '((0 1 1) (0 1 2)))
  (define expected-rhos
    (for/list ([point (in-list branch-points)])
      (region->rho ir (region-at ir point))))
  (check-equal? (length rhos) 2)
  (check-true (andmap exact-nonnegative-integer? rhos))
  (check-equal? rhos expected-rhos))

;; core-type-of/materialized が返す core は、入口の付け替えを通った項である。
;; 外と内で同じ名前の region 引数を束ねる項では、内側の束縛名が入力と変わる。
;; 付け替えを通していない項では名前が変わらないため、この差が renamed を
;; 使った証拠になる。
(let ()
  (define forall-callables
    '((g (ForallRegion (a) (NFn ((Borrowed Int (RParam a))) Int () ()) ))))
  (define core
    '(Scope ()
            (Yield (Scope () 0)
                   (RegionLam (a)
                     (RegionApp (RegionLam (a) (Lam User g (x) 1))
                                ((RParam a)))))))
  (define ir (build-region-ir core))
  (define Λ (region-ctx ir '() (hash) (hash)))
  (match-define (list 'ok _type out)
    (core-type-of/materialized core '() forall-callables '() Λ))
  (match-define
    `(Scope ()
            (Yield (Scope () 0)
                   (RegionLam (,outer)
                     (RegionApp (RegionLam (,inner) ,_) ((RParam ,argument))))))
    out)
  ;; 内側の束縛名が付け替わっている。
  (check-not-equal? inner outer)
  ;; 実引数は外側の束縛を指したままである。
  (check-equal? argument outer))

;; RegionApp の実引数も注釈欄と同じ σ で解く。
;; materialize-regions を直に呼ぶのは、この枝が alpha-table を引かず
;; σ だけを引くためである。table は空でよい。
(let ()
  (define core
    '(Scope () (RegionApp (RegionLam (a) 0) ((RVar 0)))))
  (define ir (build-region-ir core))
  (define σ (hash 0 (region-at ir '())))
  (define out (materialize-regions ir core (hash) σ))
  (match-define `(Scope () (RegionApp (RegionLam (a) 0) (,resolved))) out)
  (check-equal? resolved (region->rho ir (region-at ir '())))
  (check-true (exact-nonnegative-integer? resolved)))

;; (RVar k) でない実引数はそのまま通る。natural も (RParam rp) も
;; σ を引かない。
(let ()
  (define core
    '(Scope () (RegionApp (RegionLam (a) 0) (0 (RParam b)))))
  (define ir (build-region-ir core))
  (define out (materialize-regions ir core (hash) (hash)))
  (match-define `(Scope () (RegionApp (RegionLam (a) 0) ,ρs)) out)
  (check-equal? ρs '(0 (RParam b))))

;; R-RegionApp は包みを剥がすだけでなく、本体の型注釈の (RParam rp) を
;; 実引数へ置き換える。付け替えの結果だけを見る試験では、機械が実際に
;; 代入しているかを観測できない。
;; 束縛は a の 1 つだけであり、同じ名前を束ねる binder が本体に無い。
;; 未付け替えの項を機械へ直に渡しても捕獲は起きない。
(let ()
  (define c-body '(Let (x let (Borrowed Int (RParam a))) 1 x))
  (define config
    `(cfg (RegionApp (RegionLam (a) ,c-body) (3)) () () () ()))
  (define next (raw-steps-g2 config))
  (check-equal? (length next) 1)
  (match-define `(cfg ,after ,_H ,_Ω () ,_θ) (first next))
  (check-equal? after '(Let (x let (Borrowed Int 3)) 1 x))
  ;; spec 4.2.5 の 3 点目。還元の前後で point の構造を保つ。
  ;; G2m は span を持つ production を含まないため、機械の側で観測できるのは
  ;; point だけである。型注釈は `core-children` の子ではないので、
  ;; `(RParam a)` を実引数へ置き換えても節点の並びは変わらない。
  (check-equal? (core-points after) (core-points c-body)))

;; 実引数の数が束縛の数と合わない RegionApp では規則が発火しない。
;; 長さの不一致は region-app-arity が型検査で落とすため、還元では
;; 合わない形として詰まらせる。
(let ()
  (define c-body '(Let (x let (Borrowed Int (RParam a))) 1 x))
  (define config
    `(cfg (RegionApp (RegionLam (a) ,c-body) (3 4)) () () () ()))
  (check-equal? (raw-steps-g2 config) '()))

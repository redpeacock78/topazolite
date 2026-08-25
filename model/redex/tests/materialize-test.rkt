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
  (define config `(cfg ,out ((1 1)) ((1 Available)) ()))
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

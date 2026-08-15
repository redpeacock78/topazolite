#lang racket

(require racket/match
         racket/set
         "region.rkt")

(provide (struct-out region-ctx)
         empty-region-ctx
         enter-child
         region-ctx-add-owner region-ctx-owner
         region-ctx-add-token region-ctx-token
         (struct-out psi)
         empty-psi
         psi-join
         psi-exit
         check-region-annotation)

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

;; Scope の退場。exiting は regions-exiting-at が返す region の集合である。
;; suspended の復帰は段 9 で足す。本段では 3 欄すべてを同じ規則で削る。
(define (psi-exit Ψ exiting)
  (define (keep entries index)
    (for/set ([entry (in-set entries)]
              #:unless (set-member? exiting (list-ref entry index)))
      entry))
  (psi (keep (psi-shared Ψ) 1)
       (keep (psi-mut Ψ) 1)
       (keep (psi-suspended Ψ) 2)))

;; 注釈済みの形の ρ は、走査位置の region と一致していなければならない。
;; 一致しない項は annotate-regions を通していない項か、別の ir で注釈した項である。
;; どちらも入力の誤りとして診断する。
(define (check-region-annotation Λ ρ node fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-region-mismatch node))
  (define expected (region->rho ir (region-at ir (region-ctx-point Λ))))
  (unless (equal? ρ expected) (fail 'borrow-region-mismatch node)))

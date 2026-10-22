#lang racket

;; [REQ: BOR-001] 借用は所有者の region を超えて生きられない。

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; 内側 Scope の結果は外側 owner の生存中に消費できる。
;; borrow.md §9 が退けたのは内側の出口だけで拒否する案であり、
;; owner の Scope を越える借用の拒否は維持する。
(let ()
  (define core '(Scope (1) (Read (Scope () (Borrow 1)))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal?
   (first (type-of/raw annotated (list (list 1 'Res)) '() '()
                       (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'ok))

;; 内側 Scope が管理する所有値を借りて外へ返す形は弾く。
(let ()
  (define core '(Scope () (Scope (1) (Borrow 1))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define result
    (type-of/raw annotated (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '(0))) (hash))))
  (match result
    [(list 'fail 'borrow-escapes-owner node _)
     ;; key だけでなく、破れた outlives 制約の node が Borrow であることを確認する。
     (check-true (match node [`(BorrowAt ,_ ,_ 1) #t] [_ #f]))]
    [_ (fail (format "expected borrow-escapes-owner at Borrow node, got ~s" result))]))

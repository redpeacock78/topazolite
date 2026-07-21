#lang racket

(require rackunit redex/reduction-semantics "../schema.rkt" "../gen.rkt")

(check-equal? (constructor-schema 'Bool) '((true ()) (false ())))
(check-equal? (constructor-schema '(List Int))
              '((nil ()) (cons (Int (List Int)))))
(check-equal? (constructor-schema '(Option Int)) '((none ()) (some (Int))))
(check-equal? (constructor-schema '(Result Int Bool))
              '((ok (Int)) (ng (Bool))))
(check-equal? (constructor-schema 'Int) #f)

; drift 検知（one-way）: schema.rkt の各 constructor から代表 Construct 項を組み、
; gen.rkt の対応する G1gen nonterminal にマッチすることを照合する。schema が constructor を
; 追加すると、その代表項がどの nonterminal にもマッチせず失敗し、gen.rkt の手当てが要ると
; 気づく。constructor の削除と新規型の追加は検知しない一方向の gate（gen 側は静的文法のため）。

; schema 行の field 型に対する代表値（drift 照合用の最小 witness）。
(define (sample-value τ)
  (match τ
    ['Int 0]
    [`(List ,e) `(Construct nil (Types ,e))]
    [_ 0]))  ; G1 schema の field は Int／(List τ) のみ。未知型は不一致で fail-closed
; data-type の型引数（Bool → ()、(List Int) → (Int)）。
(define (type-args dt) (if (pair? dt) (cdr dt) '()))
; schema 行 (K (τ ...)) から代表 Construct 項 (Construct K (Types 型引数) 代表値 ...) を組む。
(define (sample-construct dt row)
  (match-define (list K field-τs) row)
  `(Construct ,K (Types ,@(type-args dt)) ,@(map sample-value field-τs)))

; Bool と List の全 constructor を schema から回す。nil/cons 固定と違い、List に
; constructor を追加すると代表項が ga-list にマッチせず fail し、List 追加も検出する。
(check-true (for/and ([row (in-list (constructor-schema 'Bool))])
              (redex-match? G1gen g-bool (sample-construct 'Bool row))))
(check-true (for/and ([row (in-list (constructor-schema '(List Int)))])
              (redex-match? G1gen ga-list (sample-construct '(List Int) row))))

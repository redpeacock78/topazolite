#lang racket/base

;; policy 層の読み込み時検査。所有モジュール 5 件を静的に require し、
;; 「行が宣言した操作」と「policy-wrap が登録した操作」の一致を確かめる。
;; policy.rkt 自身が所有モジュールを読むと循環するため、検査を分けている。
;; 動的な読み込みを使わないのは、読み込み順が実行環境に依存し、検査の失敗が
;; 「未登録」なのか「読めなかった」のか区別できなくなるためである。

(require racket/list
         racket/set
         "origins.rkt"
         "policy.rkt"
         ;; 所有モジュール。require の副作用として policy-wrap が登録を行う。
         "compat.rkt"
         "search.rkt"
         "type-equiv.rkt"
         "typing.rkt")

(provide declared-policy-operations
         policy-wrap-complete?
         policy-origins-ok?
         check-policy-layer!)

;; 行が宣言した (policy名 . 操作名) の全体。
(define (declared-policy-operations [rows policy-table])
  (for*/list ([row (in-list rows)]
              [op (in-list (policy-operations row))])
    (cons (policy-name row) op)))

(define (policy-wrap-complete? [rows policy-table])
  (set=? (list->set (declared-policy-operations rows))
         (list->set (registered-policy-operations))))

;; POL-001: 全行の origin が R0 の実値まで含めて正しいこと。
(define (policy-origins-ok? [r0 R0] [rows policy-table])
  (for/and ([row (in-list rows)])
    (policy-origin-ok? r0 row)))

(define (sorted-pairs pairs)
  (sort (map (lambda (p) (format "~a.~a" (car p) (cdr p))) pairs) string<?))

(define (check-policy-layer!)
  (unless (policy-origins-ok?)
    (error 'policy-check "a policy row has an invalid origin"))
  (unless (policy-wrap-complete?)
    (error 'policy-check
           "declared and wrapped policy operations differ:\n  declared: ~s\n  wrapped:  ~s"
           (sorted-pairs (declared-policy-operations))
           (sorted-pairs (registered-policy-operations)))))

(check-policy-layer!)

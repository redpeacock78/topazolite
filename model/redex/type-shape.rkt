#lang racket

(require racket/match
         "rows.rkt"
         "validators.rkt")

(provide type-shape-ok?)

;; 型の整形式性。record のラベル一意性に加えて、RFN-001 の Owned-free 制限を
;; Untrusted と Refined のペイロードへ課す。
(define (type-shape-ok? type)
  (match type
    [`(Record ,row)
     (and (field-row-unique? row)
          (for/and ([field (in-list row)])
            (type-shape-ok? (second field))))]
    [`(List ,element) (type-shape-ok? element)]
    [`(Option ,element) (type-shape-ok? element)]
    [`(Result ,ok-type ,error-type)
     (and (type-shape-ok? ok-type)
          (type-shape-ok? error-type))]
    [`(Owned ,inner) (type-shape-ok? inner)]
    [`(Untrusted ,inner)
     (and (owned-free? inner) (type-shape-ok? inner))]
    [`(Refined ,inner ,_)
     (and (owned-free? inner) (type-shape-ok? inner))]
    [`(NFn ,parameters ,return-type ,row ,_)
     (and (andmap type-shape-ok? parameters)
          (type-shape-ok? return-type)
          (for/and ([label (in-list row)])
            (match label
              [`(Return ,_ ,type) (type-shape-ok? type)]
              [`(Yield ,type) (type-shape-ok? type)]
              [_ #t])))]
    [_ #t]))

#lang racket

;; [REQ: BOR-006] 構築子の label ごとの capability 表。

(require rackunit
         racket/set
         "../borrow.rkt"
         "../diagnostic.rkt")

;; 表の値は (cons ws tbl) の組である。ws は capability の集合、tbl は
;; (cons K i) から同じ組への hash か #f である。

(test-case
 "region-ctx-field-table は fields 欄を出し入れする"
 (define tbl (hash (cons 'some 0) (cons (set '(1)) #f)))
 (define Λ (region-ctx-add-token (empty-region-ctx) 'o (set) #f #f tbl))
 (check-equal? (region-ctx-field-table Λ 'o) tbl)
 ;; 項目そのものが無い。
 (check-false (region-ctx-field-table (empty-region-ctx) 'o))
 ;; fields を渡さない既定の呼出し。
 (define Λ_plain (region-ctx-add-token (empty-region-ctx) 'b (set '(1))))
 (check-false (region-ctx-field-table Λ_plain 'b))
 ;; ws の側は既定の呼出しでも従来どおり読める。
 (check-equal? (region-ctx-token Λ_plain 'b) (set '(1))))

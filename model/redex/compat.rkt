#lang racket

(require racket/match
         "rows.rkt"
         "type-equiv.rkt")

(provide compat?)

(define (record-compatible? sub-row sup-row)
  (for/and ([field (in-list sup-row)])
    (match field
      [(list label sup-type sup-mutability)
       (match (field-row-lookup sub-row label)
         [(list sub-type sub-mutability)
          (and (eq? sub-mutability sup-mutability)
               (case sup-mutability
                 [(imm) (compat? sub-type sup-type)]
                 [(mut) (type-equiv? sub-type sup-type)]
                 [else #f]))]
         [_ #f])]
      [_ #f])))

(define (compat? sub sup)
  (match* (sub sup)
    [('Never _) #t]
    [(`(Record ,sub-row) `(Record ,sup-row))
     (record-compatible? sub-row sup-row)]
    [(`(Owned ,sub-type) `(Owned ,sup-type))
     (type-equiv? sub-type sup-type)]
    [(`(NFn ,_ ,_ ,_ ,_) `(NFn ,_ ,_ ,_ ,_))
     (type-equiv? sub sup)]
    [(_ _) (type-equiv? sub sup)]))

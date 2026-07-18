#lang racket

(require racket/match)

(provide row-equiv?
         type-equiv?)

(define (effect-equiv? left right)
  (match* (left right)
    [(`(Return ,left-boundary ,left-type)
      `(Return ,right-boundary ,right-type))
     (and (equal? left-boundary right-boundary)
          (type-equiv? left-type right-type))]
    [(`(Yield ,left-type) `(Yield ,right-type))
     (type-equiv? left-type right-type)]
    [(_ _) (equal? left right)]))

(define (row-equiv? left right)
  (and (for/and ([left-label (in-list left)])
         (for/or ([right-label (in-list right)])
           (effect-equiv? left-label right-label)))
       (for/and ([right-label (in-list right)])
         (for/or ([left-label (in-list left)])
           (effect-equiv? left-label right-label)))))

(define (types-equiv? left right)
  (and (= (length left) (length right))
       (for/and ([left-type (in-list left)]
                 [right-type (in-list right)])
         (type-equiv? left-type right-type))))

(define (type-equiv? left right)
  (match* (left right)
    [(`(List ,left-element) `(List ,right-element))
     (type-equiv? left-element right-element)]
    [(`(Option ,left-element) `(Option ,right-element))
     (type-equiv? left-element right-element)]
    [(`(Result ,left-ok ,left-error) `(Result ,right-ok ,right-error))
     (and (type-equiv? left-ok right-ok)
          (type-equiv? left-error right-error))]
    [(`(Owned ,left-inner) `(Owned ,right-inner))
     (type-equiv? left-inner right-inner)]
    [(`(NFn ,left-parameters ,left-return ,left-row ,left-obligations)
      `(NFn ,right-parameters ,right-return ,right-row ,right-obligations))
     (and (types-equiv? left-parameters right-parameters)
          (type-equiv? left-return right-return)
          (row-equiv? left-row right-row)
          (equal? left-obligations right-obligations))]
    [(`(TypeInfo ,left-kind) `(TypeInfo ,right-kind))
     (equal? left-kind right-kind)]
    [(`(Proof ,left-proposition) `(Proof ,right-proposition))
     (equal? left-proposition right-proposition)]
    ;; Future type-level computations remain opaque unless their syntax is
    ;; identical. G1 has no reducible type form beyond constructor specs.
    [(_ _) (equal? left right)]))

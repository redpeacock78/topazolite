#lang racket

(provide field-presence
         field-optional?
         field-with-type
         field-row-map-type
         field-row-lookup
         field-row-⊕
         field-row-residual
         field-row-equiv?
         field-row-intersection
         field-row-unique?)

(define (field-presence field)
  (match field
    [(list _ _ _) 'req]
    [(list _ _ _ 'opt) 'opt]))

(define (field-optional? field)
  (eq? (field-presence field) 'opt))

(define (field-with-type field type)
  (list* (first field) type (cddr field)))

(define (field-row-map-type row transform)
  (define fields
    (for/list ([field (in-list row)])
      (define type (transform (second field)))
      (and type (field-with-type field type))))
  (and (andmap values fields) fields))

(define (field-row-lookup row label)
  (match (assoc label row)
    [(list _ type mutability _ ...) (list type mutability)]
    [_ #f]))

(define (field-row-⊕ left right)
  (and (for/and ([field (in-list left)])
         (not (assoc (first field) right)))
       (append left right)))

(define (field-row-residual row removed)
  (filter (lambda (field)
            (not (assoc (first field) removed)))
          row))

(define (matching-field? field row type=?)
  (match field
    [(list label type mutability _ ...)
     (match (field-row-lookup row label)
       [(list other-type other-mutability)
        (and (eq? mutability other-mutability)
             (eq? (field-presence field)
                  (field-presence (assoc label row)))
             (type=? type other-type))]
       [_ #f])]
    [_ #f]))

(define (field-row-equiv? left right type=?)
  (and (= (length left) (length right))
       (andmap (lambda (field)
                 (matching-field? field right type=?))
               left)))

(define (field-row-intersection left right type=?)
  (filter (lambda (field)
            (matching-field? field right type=?))
          left))

(define (field-row-unique? row)
  (not (check-duplicates (map first row))))

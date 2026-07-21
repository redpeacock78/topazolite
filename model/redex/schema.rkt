#lang racket

(provide constructor-schema)

(define (constructor-schema type)
  (match type
    ['Bool '((true ()) (false ()))]
    [`(List ,element)
     `((nil ()) (cons (,element (List ,element))))]
    [`(Option ,element)
     `((none ()) (some (,element)))]
    [`(Result ,ok-type ,error-type)
     `((ok (,ok-type)) (ng (,error-type)))]
    [_ #f]))

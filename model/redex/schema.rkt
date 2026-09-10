#lang racket

(provide constructor-schema
         peel-eliminate-wrapper)

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

(define (peel-eliminate-wrapper data-type)
  ;; 借用と所有は data 型を包むだけで構成子を変えない。
  ;; 包みを剥がして schema を引き、包みごとに決まる rewrap を欄の型へ配る。
  ;; Borrowed と BorrowedMut は欄の型を同じ region と同じ mode で包み直す。
  ;; Owned は欄が宣言どおりの型を保つため rewrap は恒等である。
  (match data-type
    [`(Borrowed ,τ ,ρ) (values τ (lambda (t) `(Borrowed ,t ,ρ)))]
    [`(BorrowedMut ,τ ,ρ) (values τ (lambda (t) `(BorrowedMut ,t ,ρ)))]
    [`(Owned ,τ) (values τ values)]
    [_ (values data-type values)]))

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
  ;; Borrowed は欄の型を同じ region で包み直す。Owned は欄が宣言どおりの型を
  ;; 保つため rewrap は恒等である。
  ;; BorrowedMut は構成子の欄に mode が無く、可変の欄と不変の欄を区別できない
  ;; ため節を置かない。節が無ければ包みが剥がれず、constructor-schema が偽を
  ;; 返して non-data-eliminate で落ちる。
  (match data-type
    [`(Borrowed ,τ ,ρ) (values τ (lambda (t) `(Borrowed ,t ,ρ)))]
    [`(Owned ,τ) (values τ values)]
    [_ (values data-type values)]))

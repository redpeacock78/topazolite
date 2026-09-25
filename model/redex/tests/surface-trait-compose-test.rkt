#lang racket

;; SUR-009。trait と型の名前空間、および trait 合成の lowering の回帰である。

(require rackunit
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../traits.rkt"
         "../diagnostic.rkt")

(define (parse-src str) (parse (lex/string 'src str)))
(define (lower str [base canonical-trait-env]) (lower-surface (parse-src str) base))

;; str の中で n 番目（0 始まり）に現れる sub の span である。
(define (nth-span str sub [n 0])
  (define p (list-ref (regexp-match-positions* (regexp-quote sub) str) n))
  `(#:span src ,(car p) ,(cdr p)))

(define (check-diagnostic str id sub n [related '()])
  (define d (lower str))
  (check-true (diagnostic? d) (format "~s が Diagnostic になる" str))
  (check-equal? (diagnostic-id d) id)
  (check-equal? (diagnostic-primary-span d) (nth-span str sub n))
  (check-equal? (diagnostic-related d) related))

(test-case
 "SUR-009: trait 名を型の位置で使うと E-SUR-021 になる"
 (for ([c (in-list
           (list (list "trait R { }\n{ let x: R = 1\n x }" "R" 1)
                 (list "type N = Printable\n0" "Printable" 0)
                 (list "type N = Printable | Sizable\n0" "Printable" 0)
                 (list "type N = Int & Printable\n0" "Printable" 0)
                 (list "type N = { a: Printable }\n0" "Printable" 0)
                 (list "trait Q { f: Printable }\n0" "Printable" 0)
                 (list "trait R { }\nimpl R for Printable { }\n0" "Printable" 0)))])
   (check-diagnostic (first c) "E-SUR-021" (second c) (third c))))

(test-case
 "SUR-009: 未知の名前が trait 名より左にあれば E-SUR-008 になる"
 (check-diagnostic "type N = Foo & Printable\n0" "E-SUR-008" "Foo" 0))

(test-case
 "SUR-009: 型と trait の名前の衝突は宣言の順によらず型の側で E-SUR-023 になる"
 (define a "trait Foo { }\ntype Foo = Int\n0")
 (check-diagnostic a "E-SUR-023" "Foo" 1
                   (list (list 'trait-declaration (nth-span a "Foo" 0) "trait Foo の宣言")))
 (define b "type Foo = Int\ntrait Foo { }\n0")
 (check-diagnostic b "E-SUR-023" "Foo" 0
                   (list (list 'trait-declaration (nth-span b "Foo" 1) "trait Foo の宣言"))))

(test-case
 "SUR-009: 基底の trait 名の型と基本型名の trait は related を持たない E-SUR-023 になる"
 (check-diagnostic "type Printable = Int\n0" "E-SUR-023" "Printable" 0)
 (check-diagnostic "trait Int { }\n0" "E-SUR-023" "Int" 0))

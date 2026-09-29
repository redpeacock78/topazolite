#lang racket

(require rackunit
         racket/match
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../traits.rkt")

(define (lower str)
  (lower-surface (parse (lex/string 'src str)) canonical-trait-env))
(define (code str)
  (define r (lower str))
  (and (diagnostic? r) (diagnostic-id r)))
(define (primary str)
  (diagnostic-primary-span (lower str)))
(define (sp lo hi) `(#:span src ,lo ,hi))
(define (compile str) (compile-source/string 'src str))

;; lowering の結果の木に型 t が現れるかを見る。
(define (mentions? tree t)
  (or (equal? tree t)
      (and (pair? tree)
           (or (mentions? (car tree) t) (mentions? (cdr tree) t)))))

(test-case "型構成子の適用は UCore の型へ写る"
  (for ([src (in-list '("fn f(x: List<Int>) -> Int { 0 }\n0"
                        "fn f(x: Option<Int>) -> Int { 0 }\n0"
                        "fn f(x: Result<Int, String>) -> Int { 0 }\n0"
                        "fn f(x: Owned<Int>) -> Int { 0 }\n0"
                        "fn f(x: List<Option<Int>>) -> Int { 0 }\n0"))]
        [t (in-list '((List Int) (Option Int) (Result Int String)
                      (Owned Int) (List (Option Int))))])
    (define r (lower src))
    (check-true (lowered? r) (format "~a: ~s" src r))
    (check-true (mentions? (lowered-term r) t) src)))

(test-case "型適用を注釈に持つ関数は型付けできる"
  (for ([src (in-list '("fn f(x: Option<Int>) -> Option<Int> { x }\n0"
                        "fn f(x: Result<Int, String>) -> Result<Int, String> { x }\n0"
                        "type L = List<Int>\nfn f(x: L) -> L { x }\n0"))])
    (define r (compile src))
    (check-true (compiled? r) (format "~a: ~s" src r))))

(test-case "型構成子でない名前への型適用は全体の span で E-SUR-025 になる"
  (check-equal? (code "let x: Int<Int> = 0\n0") "E-SUR-025")
  (check-equal? (primary "let x: Int<Int> = 0\n0") (sp 7 15))
  (check-equal? (code "type A = Int\nlet x: A<Int> = 0\n0") "E-SUR-025")
  (check-equal? (primary "type A = Int\nlet x: A<Int> = 0\n0") (sp 20 26)))

(test-case "引数の個数の誤りは全体の span で E-SUR-025 になる"
  (check-equal? (code "let x: List<Int, Int> = 0\n0") "E-SUR-025")
  (check-equal? (primary "let x: List<Int, Int> = 0\n0") (sp 7 21))
  (check-equal? (code "let x: Result<Int> = 0\n0") "E-SUR-025"))

(test-case "型構成子の名前の単独使用はその名前の span で E-SUR-025 になる"
  (check-equal? (code "let x: List = 0\n0") "E-SUR-025")
  (check-equal? (primary "let x: List = 0\n0") (sp 7 11)))

(test-case "未知の頭の名前は頭の span で E-SUR-008 になる"
  (check-equal? (code "let x: Foo<Int> = 0\n0") "E-SUR-008")
  (check-equal? (primary "let x: Foo<Int> = 0\n0") (sp 7 10)))

(test-case "trait 宣言の外の Self の型適用は頭の span で E-SUR-008 になる"
  (check-equal? (code "let x: Self<Int> = 0\n0") "E-SUR-008")
  (check-equal? (primary "let x: Self<Int> = 0\n0") (sp 7 11)))

(test-case "trait 名の型適用は頭の span で E-SUR-021 になる"
  (check-equal? (code "let x: Sizable<Int> = 0\n0") "E-SUR-021")
  (check-equal? (primary "let x: Sizable<Int> = 0\n0") (sp 7 14)))

(test-case "展開中の別名の型適用は頭の span で E-SUR-010 になる"
  (check-equal? (code "type A = A<Int>\n0") "E-SUR-010")
  (check-equal? (primary "type A = A<Int>\n0") (sp 9 10)))

(test-case "型構成子の名前の型別名は宣言の名前で E-SUR-026 になる"
  (for ([name (in-list '("List" "Option" "Result" "Owned"))])
    (define src (format "type ~a = Int\n0" name))
    (check-equal? (code src) "E-SUR-026" src)
    (check-equal? (primary src) (sp 5 (+ 5 (string-length name))) src)))

(test-case "基本型の名前の型別名は従来どおり E-SUR-011 のままである"
  (check-equal? (code "type Int = Bool\n0") "E-SUR-011"))

(test-case "入れ子の内側の誤りは内側の型適用の span を指す"
  (check-equal? (code "let x: List<Int<Int>> = 0\n0") "E-SUR-025")
  (check-equal? (primary "let x: List<Int<Int>> = 0\n0") (sp 12 20)))

(test-case "引数の個数は引数の lowering より先に見る"
  (check-equal? (code "let x: List<Foo, Int> = 0\n0") "E-SUR-025")
  (check-equal? (primary "let x: List<Foo, Int> = 0\n0") (sp 7 21)))

(test-case "引数は左から lowering する"
  (check-equal? (code "let x: Result<Foo, Int<Int>> = 0\n0") "E-SUR-008")
  (check-equal? (primary "let x: Result<Foo, Int<Int>> = 0\n0") (sp 14 17)))

(test-case "& の葉の型適用は合成の候補にせず型の交差として落とす"
  (check-equal? (code "type X = List<Int> & Sizable\n0") "E-SUR-021")
  (check-equal? (primary "type X = List<Int> & Sizable\n0") (sp 21 28)))

(test-case "trait 宣言の中の Self の型適用は全体の span で E-SUR-025 になる"
  (define src "trait Foo { f: fn(Self<Int>) -> Int }\n0")
  (check-equal? (code src) "E-SUR-025")
  (check-equal? (primary src) (sp 18 27)))

(test-case "型構成子の名前の trait は宣言の名前で E-SUR-023 になる"
  (for ([name (in-list '("List" "Option" "Result" "Owned"))])
    (define src (format "trait ~a { f: fn(Self) -> Int }\n0" name))
    (check-equal? (code src) "E-SUR-023" src)
    (check-equal? (primary src) (sp 6 (+ 6 (string-length name))) src)))

(test-case "型構成子の適用への derive は host exception でなく E-SUR-019 になる"
  (for ([src (in-list '("derive Sizable for List<Int>\n0"
                        "type L = List<Int>\nderive Sizable for L\n0"
                        "derive Sizable for Option<Int>\n0"
                        "derive Sizable for { a: Int, b: List<Int> }\n0"
                        "derive Sizable for Int | Option<Int>\n0"))])
    (check-equal? (code src) "E-SUR-019" src))
  (check-equal? (primary "derive Sizable for List<Int>\n0") (sp 0 28)))

(test-case "impl の対象の型適用は別名を経由した同じ型と同じ行になる"
  (define (impl-target str)
    (impl-target-type (first (lowered-impl-rows (lower str)))))
  (define body "{ size: fn(x: List<Int>) -> Int { 0 } }")
  (check-equal? (impl-target (format "impl Sizable for List<Int> ~a\n0" body))
                (impl-target (format "type L = List<Int>\nimpl Sizable for L ~a\n0" body))))

#lang racket

;; SUR-008。戻り型を省略した関数を Surface の入力から driver まで通す。

(require rackunit
         "../diagnostic.rkt"
         "../driver.rkt")

(define (c str) (compile-source/string 'src str))

(define (code str)
  (define r (c str))
  (and (diagnostic? r) (diagnostic-id r)))

(test-case "SUR-008: 合成位置の省略した戻り型は本体の型になる"
  (for ([src (list "fn f(x: Int) { x }\nf(1)"
                   "{ let g = fn(x: Int) { x }\n g(2) }"
                   "fn f(b: Bool) { { a: b } }\nf(true).a")]
        [expected '(Int Int Bool)])
    (define r (c src))
    (check-true (compiled? r) src)
    (when (compiled? r)
      (check-equal? (compiled-type r) expected src))))

(test-case "SUR-008: 検査位置の省略した戻り型は期待型から決まる"
  (define src "fn ap(g: fn(Int) -> Int, x: Int) -> Int { g(x) }\nap(fn(y: Int) { y }, 4)")
  (check-true (compiled? (c src)) src))

(test-case "SUR-008: 本体が自身を参照する関数宣言は E-TYP-024 を返す"
  (check-equal? (code "fn f(x: Int) { f(x) }\nf(1)") "E-TYP-024"))

#lang racket

;; SUR-012。期待型から無名関数の仮引数型を補う経路を driver まで通す。

(require rackunit
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt")

(define (c str) (compile-source/string 'src str))
(define (code str)
  (define r (c str))
  (and (diagnostic? r) (diagnostic-id r)))
(define (type-of str) (compiled-type (c str)))
(define e-typ-025 (diagnostic-code-of 'elaborate 'parameter-type-not-inferable))

(test-case "SUR-012: 適用の実引数の位置で仮引数型を補う"
  (check-equal?
   (type-of "fn ap(g: fn(Int) -> Int, x: Int) -> Int { g(x) }\nap(y => y, 4)")
   'Int))

(test-case "SUR-012: 型注釈付きの束縛で仮引数型を補う"
  (check-equal? (type-of "{ let f: fn(Int) -> Int = x => x\n f(3) }") 'Int)
  (check-equal? (type-of "{ let f: fn(Int) -> Int = fn(x) { x }\n f(3) }") 'Int)
  (check-equal?
   (type-of "{ let f: fn(Int, Bool) -> Bool = fn(x: Int, b) => b\n f(1, true) }")
   'Bool))

(test-case "SUR-012: impl の要件へ期待型が届く（ホワイトペーパー §8.1）"
  (check-true
   (compiled?
    (c "type User = { name: String }\nimpl Printable for User { print: user => user.name }\n0"))))

(test-case "SUR-012: 合成位置の => は戻り型を本体から決める（ホワイトペーパー §3.3）"
  (check-equal? (type-of "const a = 1\n{ let f = fn() => a\n f() }") 'Int)
  (check-equal? (type-of "{ let f = fn(x: Int) => x\n f(2) }") 'Int))

;; P2i3b spec §7。閉包を返す関数宣言は、本体に自分の名前が無いので gate を通る。
(test-case "SUR-012: 閉包を返す fn 宣言は受理され 3 へ評価される"
  (define r (c "fn mk() -> fn(Int) -> Int { fn(y: Int) -> Int { y } }\nmk()(3)"))
  (check-true (compiled? r))
  (check-equal? (compiled-type r) 'Int)
  (call-with-trait-ledger
   (compiled-ledger r)
   (lambda ()
     (check-equal? (run (inject (erase-core (compiled-execution-core r))) 10000)
                   '(cfg 3 () () () ())))))

(test-case "SUR-012: 合成位置の仮引数省略は E-TYP-025、span は binder"
  (define r (c "{ let f = x => x\n f(1) }"))
  (check-equal? (diagnostic-id r) e-typ-025)
  (check-equal? (diagnostic-found r) 'no-expected-function)
  (check-equal? (diagnostic-primary-span r) '(#:span src 10 11)))

(test-case "SUR-012: 仮引数の数の不一致と関数型でない宣言型"
  (define r (c "{ let f: fn(Int, Int) -> Int = x => x\n f(1, 2) }"))
  (check-equal? (diagnostic-id r) e-typ-025)
  (check-equal? (diagnostic-found r) 'arity-mismatch)
  (check-equal? (code "{ let f: Int = x => x\n f }") e-typ-025))

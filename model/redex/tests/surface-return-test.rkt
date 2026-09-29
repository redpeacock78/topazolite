#lang racket

;; [REQ: SUR-015] Surface の return が関数宣言の境界へ届くことを確かめる。

(require rackunit
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt")

(define (c source) (compile-source/string 'src source))
(define (code source)
  (define result (c source))
  (and (diagnostic? result) (diagnostic-id result)))
(define (run-value result)
  (match (run-g2 (inject-g2m (erase-core (compiled-core result))) 10000)
    [`(cfg ,value () () () ()) value]
    [other (fail-check (format "純粋な整数値の終端状態を期待したが ~s" other))]))

(test-case "SUR-015: 関数宣言の return は受理され、早期に戻る"
  (define result (c "fn f(x: Int) -> Int { let a = return x\n 0 }\nf(7)"))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) 7)))

(test-case "SUR-015: 内側の関数の return は内側の呼出しだけから戻る"
  (define result
    (c "fn g(x: Int) -> Int { return x }\nfn f(x: Int) -> Int { let a = g(x)\n return 1 }\nf(7)"))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) 1)))

(test-case "SUR-015: return の値が戻り型と合わなければ拒否する"
  (check-equal? (code "fn f() -> Int { return \"a\" }\n0")
                (diagnostic-code-of 'elaborate 'type-mismatch)))

(test-case "SUR-015: 関数宣言の row に書いた Return は境界外である"
  (check-equal? (code "fn f() -> Int ! Return { 0 }\n0")
                (diagnostic-code-of 'elaborate 'return-label-outside-boundary)))

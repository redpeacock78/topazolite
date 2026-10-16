#lang racket

;; [REQ: SUR-015] Surface の return が関数宣言の境界へ届くことを確かめる。

(require rackunit
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt")

(define (c source) (compile-source/string 'src source))
(define (code source)
  (define result (c source))
  (and (diagnostic? result) (diagnostic-id result)))
(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value () () () ()) value]
       [other (fail-check (format "純粋な整数値の終端状態を期待したが ~s" other))]))))

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

(test-case "検査 Rec の bottom 余剰欄は関数を呼び出す前に return する"
  (define result
    (c "fn g(r: { a: Int }) -> Int { return r.a }\nfn f() -> Int { return g({ a: 1, b: return 2 }) }\nf()"))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) 2)))

(test-case "SUR-015: return の値が戻り型と合わなければ拒否する"
  (check-equal? (code "fn f() -> Int { return \"a\" }\n0")
                (diagnostic-code-of 'elaborate 'type-mismatch)))

(test-case "SUR-015: 関数宣言の row に書いた Return は境界外である"
  (check-equal? (code "fn f() -> Int ! Return { 0 }\n0")
                (diagnostic-code-of 'elaborate 'return-label-outside-boundary)))

(test-case "SUR-015: 戻り型省略の関数宣言と合成位置 Fn は明示注釈と一致する"
  (for ([pair (in-list
               '(("fn f(x: Int) { let a = return x\n 0 }\n0"
                 . "fn f(x: Int) -> Int { let a = return x\n 0 }\n0")
                 ("{ let f = fn(x: Int) { return x }\n0 }"
                  . "{ let f = fn(x: Int) -> Int { return x }\n0 }")))])
    (define inferred (c (car pair)))
    (define explicit (c (cdr pair)))
    (check-true (compiled? inferred))
    (check-true (compiled? explicit))
    (when (and (compiled? inferred) (compiled? explicit))
      (check-equal? (erase-core (compiled-core inferred))
                    (erase-core (compiled-core explicit)))
      (check-equal? (compiled-callables inferred)
                    (compiled-callables explicit)))))

(test-case "SUR-015: 束縛値の Return 後は異型の到達不能な本体を許す"
  (check-true (compiled? (c "fn f() { let a = return 1\n \"a\" }\n0"))))

(test-case "SUR-015: 候補が無ければ旧経路の E-TYP-024 になる"
  (check-equal? (code "fn f() { return y }\n0") "E-TYP-024")
  (check-equal? (code "{ let f = fn() { return y }\n0 }") "E-TYP-024"))

(test-case "SUR-015: 候補があれば後続 return payload の未束縛を報告する"
  (check-equal?
   (code "fn f() { let a = return 1\n return y }\n0")
   "E-VAR-002"))

(test-case "SUR-015: 戻り型省略の自己参照拒否は変わらない"
  (check-equal? (code "fn f() { let a = return 1\n f() }\n0")
                "E-TYP-024"))

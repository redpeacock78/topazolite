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

(define (run-source source)
  (define result (c source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "~s" result)))
  (and (compiled? result) (run-value result)))

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

(test-case "leave は式位置の if と when の値を関数へ返す"
  (for ([pair
         (in-list
          (list
           (cons "fn choose(b: Bool) -> Int {\n let x = if b { leave 11 } else { 22 }\n return x\n}\nchoose(true)" 11)
           (cons "fn choose(b: Bool) -> Int {\n let x = if b { leave 11 } else { 22 }\n return x\n}\nchoose(false)" 22)
           (cons "fn choose(b: Bool) -> Int {\n let x = when b { true => { leave 11 }\n false => 22 }\n return x\n}\nchoose(true)" 11)
           (cons "fn choose(b: Bool) -> Int {\n let x = when b { true => { leave 11 }\n false => 22 }\n return x\n}\nchoose(false)" 22)))])
    (define result (c (car pair)))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result)
                            (diagnostic-message result))
                    (format "~s" result)))
    (when (compiled? result)
      (check-equal? (compiled-type result) 'Int)
      (check-equal? (run-value result) (cdr pair)))))

(test-case "文位置 if の leave は外側 when の境界へ解決する"
  (define variable-source
    (string-append
     "fn choose(c: Bool, flag: Bool) -> Int {\n"
     " let x = when flag {\n"
     "  true => { if c { leave 1 }\n leave 2 }\n"
     "  false => 3\n"
     " }\n return x\n}\nchoose(true, true)"))
  (define call-source
    (string-append
     "fn get_flag() -> Bool { return true }\n"
     "fn choose(c: Bool) -> Int {\n"
     " let x = when get_flag() {\n"
     "  true => { if c { leave 1 }\n leave 2 }\n"
     "  false => 3\n"
     " }\n return x\n}\nchoose(true)"))
  (check-equal? (run-source variable-source) 1)
  (check-equal? (run-source call-source) 1)
  (check-equal?
   (run-source
    (string-append
     "fn choose(c: Bool, flag: Bool) -> Int {\n"
     " let x = when flag { true => { if c { leave 1 }\n leave 2 }\n"
     " false => 3 }\n return x\n}\nchoose(false, true)"))
   2))

(test-case "leave if は外側 when の境界で一度だけ返る"
  (for ([pair (in-list '((true . 1) (false . 2)))])
    (define source
      (format
       (string-append
        "fn choose(c: Bool, flag: Bool) -> Int {\n"
        " let x = when flag { true => { leave if c { 1 } else { 2 } }\n"
        " false => 3 }\n return x\n}\nchoose(~a, true)")
       (car pair)))
    (check-equal? (run-source source) (cdr pair))))

(test-case "式境界の外と内側関数の leave は E-RET-006 で拒否する"
  (check-equal? (code "fn f(c: Bool) -> Int { if c { leave 1 }\n 2 }\n0")
                "E-RET-006")
  (check-equal?
   (code "fn f(c: Bool) -> Int { let x = if c { let h = fn(y: Int) => { leave y }\n 1 } else { 2 }\n x }\n0")
   "E-RET-006")
  (check-equal? (code "fn f() -> Int { leave 1 }\n0") "E-RET-006"))

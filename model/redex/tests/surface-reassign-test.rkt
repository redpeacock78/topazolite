#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
       [other (fail-check (format "terminal config expected, got ~s" other))]))))

(define (run-source source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (and (compiled? result) (run-value result)))

(define (source-span source needle)
  (match (regexp-match-positions (regexp-quote needle) source)
    [(list (cons lo hi)) `(#:span src ,lo ,hi)]
    [_ (error 'source-span "substring not found: ~a" needle)]))

(define (assert-diagnostic source code needle #:whole? [whole? #f])
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" code result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) code source)
    (check-equal? (diagnostic-primary-span result)
                  (if whole?
                      (source-span source needle)
                      (let ([span (source-span source needle)])
                        (match span
                          [`(#:span src ,lo ,_hi) `(#:span src ,lo ,(add1 lo))])))
                  source)))

(define (relative-span source needle span)
  (define needle-start
    (match (source-span source needle)
      [`(#:span src ,start ,_) start]))
  (match span
    [`(#:span src ,lo ,hi)
     (list (- lo needle-start) (- hi needle-start))]
    [_ span]))

(test-case "SCP-001: Surface let mut variables can be reassigned"
  (check-equal?
   (run-source "let mut c = 0\nc = add(c, 1)\nc = add(c, 1)\nc")
   2)
  (check-equal?
   (run-source
    (string-append
     "fn f() -> Int ! Mutation {\n"
     "  let mut c = 0\n"
     "  c = add(c, 1)\n"
     "  c = add(c, 1)\n"
     "  return c\n"
     "}\nf()"))
   2))

(test-case "if の両方の scrutinee 形で代入枝と非代入枝を実行する"
  (for ([condition (in-list '("b" "yes(b)"))])
    (define prefix
      (if (string=? condition "b")
          ""
          "fn yes(b: Bool) -> Bool { return b }\n"))
    (define source
      (string-append
       prefix
       "fn f(b: Bool) -> Int ! Mutation {\n"
       "  let mut c = 0\n"
       "  if " condition " { c = 7 }\n"
       "  return c\n"
       "}\nf(true)"))
    (check-equal? (run-source source) 7)
    (check-equal?
     (run-source
      (string-append
       prefix
       "fn f(b: Bool) -> Int ! Mutation {\n"
       "  let mut c = 0\n"
       "  if " condition " { c = 7 }\n"
       "  return c\n"
       "}\nf(false)"))
     0)))

(test-case "Option、optional 欄、else の無い if を slot 型で検査する"
  (check-equal?
   (run-source
    (string-append
     "fn f(b: Bool) -> Option<Int> ! Mutation {\n"
     "  let mut r: Option<Int> = none\n"
     "  if b { r = some(1) } else { r = none }\n"
     "  return r\n"
     "}\nf(true)"))
   '(Construct (Option Int) some 1))
  (check-equal?
   (run-source
    (string-append
     "fn f() -> Option<Int> ! Mutation {\n"
     "  let mut r: { name: String, age?: Int } = { name: \"A\", age: 2 }\n"
     "  r = { name: \"B\" }\n"
     "  return r.age\n"
     "}\nf()"))
   '(Construct (Option Int) none))
  (check-equal?
   (run-source
    (string-append
     "fn f(b: Bool) -> Option<Int> ! Mutation {\n"
     "  let mut r: Option<Int> = none\n"
     "  r = if b { 3 }\n"
     "  return r\n"
     "}\nf(true)"))
   '(Construct (Option Int) some 3))
  (check-equal?
   (run-source
    (string-append
     "fn f(b: Bool) -> Option<Int> ! Mutation {\n"
     "  let mut r: Option<Int> = none\n"
     "  r = if b { 3 }\n"
     "  return r\n"
     "}\nf(false)"))
   '(Construct (Option Int) none)))

(test-case "Union slot の再代入は tag を付けて読み出せる"
  (check-equal?
   (run-source
    (string-append
     "fn f() -> String ! Mutation {\n"
     "  let mut v: Int | String = 0\n"
     "  v = \"changed\"\n"
     "  return when v {\n"
     "    (s: String) => s\n"
     "    (n: Int) => \"int\"\n"
     "  }\n"
     "}\nf()"))
   "changed"))

(test-case "同じ shape の Record slot を再代入する"
  (check-equal?
   (run-source
    (string-append
     "fn f() -> String ! Mutation {\n"
     "  let mut r: { name: String } = { name: \"A\" }\n"
     "  r = { name: \"B\" }\n"
     "  return r.name\n"
     "}\nf()"))
   "B"))

(test-case "再代入の束縛・型診断は source span を保つ"
  (assert-diagnostic "x = 1\n0"
                     "E-VAR-002" "x = 1" #:whole? #t)
  (assert-diagnostic "const x = 0\nx = 1\n0"
                     "E-VAR-011" "x = 1" #:whole? #t)
  (assert-diagnostic "let x = 0\nx = 1\n0"
                     "E-VAR-011" "x = 1" #:whole? #t)
  (assert-diagnostic "fn f(x: Int) -> Int ! Mutation { x = 1\n return x }\nf(0)"
                     "E-VAR-011" "x = 1" #:whole? #t)
  (assert-diagnostic
   (string-append
    "fn f() -> Int ! Mutation {\n"
    "  let mut x = 0\n"
    "  { let x = 2\n x = 3 }\n"
    "  return x\n"
    "}\nf()")
   "E-VAR-011" "x = 3" #:whole? #t)
  (assert-diagnostic "let mut x = 0\nx = true\n0"
                     "E-VAR-013" "x = true" #:whole? #t))

(test-case "右辺の型付け診断は再代入の型不一致へ置き換えない"
  (assert-diagnostic "let mut x = 0\nx = missing\n0"
                     "E-VAR-002" "missing" #:whole? #t))

(test-case "Mutation row と無名関数の期待 row を検査する"
  (check-equal?
   (run-source
    (string-append
     "fn f() -> Int ! Mutation {\n"
     "  let mut c = 0\n"
     "  let g: fn() -> Unit ! Mutation = fn() => { c = 1 }\n"
     "  g()\n"
     "  return c\n"
     "}\nf()"))
   1)
  (assert-diagnostic
   "fn f() -> Int ! Mutation { let mut c = 0\n let g = fn() => { c = 1 }\n return c }\nf()"
   "E-EFF-002" "fn() => { c = 1 }" #:whole? #t)
  (assert-diagnostic
   "fn f() -> Int { let mut c = 0\n c = 1\n return c }\nf()"
   "E-EFF-002" "fn f() -> Int { let mut c = 0\n c = 1\n return c }\nf()"
   #:whole? #t))

(test-case "TryBind を含む再代入 RHS は注釈付き let と同じ診断になる"
  (define rhs "{ let x ?= input\n some(x) }")
  (define reassign-source
    (string-append
     "fn f(input: Option<Int>) -> Option<Int> ! Mutation {\n"
     "  let mut out: Option<Int> = none\n"
     "  out = " rhs "\n"
     "  return out\n"
     "}\nf(none)"))
  (define annotated-source
    (string-append
     "fn f(input: Option<Int>) -> Option<Int> {\n"
     "  let out: Option<Int> = " rhs "\n"
     "  return out\n"
     "}\nf(none)"))
  (define reassign-result (compile reassign-source))
  (define annotated-result (compile annotated-source))
  (check-true (diagnostic? reassign-result))
  (check-true (diagnostic? annotated-result))
  (when (and (diagnostic? reassign-result) (diagnostic? annotated-result))
    (check-equal? (diagnostic-id reassign-result) (diagnostic-id annotated-result))
    (check-equal?
     (relative-span reassign-source rhs
                    (diagnostic-primary-span reassign-result))
     (relative-span annotated-source rhs
                    (diagnostic-primary-span annotated-result)))))

(test-case "Return を右辺に置いた再代入は Never のまま関数境界へ届く"
  (check-equal?
   (run-source
    (string-append
     "fn f() -> Int ! Mutation {\n"
     "  let mut x = 0\n"
     "  x = return 7\n"
     "}\nf()"))
   7))

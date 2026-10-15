#lang racket

(require rackunit
         racket/match
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../elaborate.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))
(define (code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))

(define (elab-code expression)
  (match (elab expression)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (run-main source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a" (diagnostic-id result))
                  "compiled result expected"))
  (and (compiled? result)
       (call-with-trait-ledger
        (compiled-ledger result)
       (lambda ()
          (match (run-g2
                  (inject-g2m
                   (erase-core (compiled-execution-core result)))
                  10000)
            [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
            [other (fail-check (format "terminal config expected, got ~s" other))])))))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 10000])
    (when (zero? fuel) (error 'trace-g2 "fuel exhausted at ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "expected one step, got ~s" steps)])))

(define (config-control configuration)
  (match configuration
    [`(cfg ,control ,_heap ,_states ,_tokens ,_events) control]))

(define (config-tokens configuration)
  (match configuration
    [`(cfg ,_control ,_heap ,_states ,tokens ,_events) tokens]))

(define (run-owned-place function inner-type value expected-value)
  (match-define (list function-core _function-type _row callables)
    (elab function))
  (define control-term
    `(Scope (0) (Apply ,(erase-core function-core) (Move 0))))
  (define typed (core-type-of control-term `((0 ,inner-type)) callables))
  (check-true (and (list? typed) (= (length typed) 2))
              (format "Owned argument の型検査が失敗した: ~s" typed))
  (when (and (list? typed) (= (length typed) 2))
    (define start
      `(cfg ,control-term
            ((0 ,value (declared (Owned ,inner-type))))
            ((0 Available)) () ()))
    (define-values (configs rules) (trace-g2 start))
    (check-config-trace configs callables (first typed))
    (check-not-false (member 'R-EliminateTransit rules))
    (check-equal? (config-control (last configs)) expected-value)
    configs))

(define (first-recur-call tree)
  (match tree
    [`(Apply (RecurVal ,_ ,name ,_ ,_) ,_ ...) name]
    [(? pair? parts)
     (or (first-recur-call (car parts))
         (first-recur-call (cdr parts)))]
    [_ #f]))

(define (check-config-trace configs callables expected)
  (define initial-row (runtime-row (first configs) callables expected))
  (check-not-false initial-row "initial config has a runtime row")
  (for ([cfg (in-list configs)] [index (in-naturals)])
    (define row (runtime-row cfg callables expected))
    (check-not-false row (format "config ~a has a runtime row" index))
    (when (and row initial-row)
      (check-true (row-subset? row initial-row)
                  (format "config ~a adds runtime effects" index))
      (check-true (config-ok? cfg callables expected row)
                  (format "config ~a is well typed: ~s" index cfg)))))

(define (trace-result result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (define start
       (inject-g2m (erase-core (compiled-execution-core result))))
     (define-values (configs rules) (trace-g2 start))
     (check-config-trace configs (compiled-callables result)
                         (compiled-type result))
     (values configs rules))))

(define (elaborated-trace expression)
  (match (elab expression)
    [(list core expected _row callables)
     (define-values (configs rules)
       (trace-g2 (inject-g2m (erase-core core))))
     (check-config-trace configs callables expected)
     (values core expected callables configs rules)]
    [other (fail-check (format "UCore の elaborate が失敗した: ~s" other))]))

(define (source-span source needle)
  (match (regexp-match-positions (regexp-quote needle) source)
    [(list (cons start end)) `(#:span src ,start ,end)]
    [_ (error 'source-span "substring not found: ~a" needle)]))

(define (source-span-last source needle)
  (match (last (regexp-match-positions* (regexp-quote needle) source))
    [(cons start end) `(#:span src ,start ,end)]
    [_ (error 'source-span-last "substring not found: ~a" needle)]))

(test-case "Option の ?= は成功で剥がし、失敗で none を返す"
  (define source
    (string-append
     "fn f(a: Option<Int>) -> Option<Int> {\n"
     "  let x ?= a\n"
     "  some(x)\n"
     "}\n"
     "f(some(1))"))
  (check-equal? (run-main source) '(Construct (Option Int) some 1))
  (check-equal? (run-main (regexp-replace #rx"some\\(1\\)" source "none"))
                '(Construct (Option Int) none)))

(test-case "Result の ?= は失敗の ng payload を保つ"
  (define source
    (string-append
     "fn f(a: Result<Int, Bool>) -> Result<Unit, Bool> {\n"
     "  let x ?= a\n"
     "  ok(())\n"
     "}\n"
     "f(ok(1))"))
  (check-equal? (run-main source)
                '(Construct (Result Unit Bool) ok unit))
  (check-equal? (run-main (regexp-replace #rx"ok\\(1\\)" source "ng(false)"))
                '(Construct (Result Unit Bool) ng (Construct Bool false))))

(test-case "when の枝の ?= は when へ返り、その後の関数本体を続ける"
  (define source
    (string-append
     "fn f(a: Option<Int>, b: Option<Int>, fallback: Option<Int>) -> Int {\n"
     "  let r: Option<Int> = when a {\n"
     "    some x => { let y ?= b\n let r2: Option<Int> = some(x)\n r2 }\n"
     "    none => fallback\n"
     "  }\n"
     "  when r { some value => 1\n none => 2 }\n"
     "}\n"
     "f(some(4), none, some(9))"))
  (check-equal? (run-main source) 2)
  (check-equal? (run-main (string-replace source "none, some(9)"
                                         "some(5), some(9)"))
                1))

(test-case "無名関数内の ?= は無名関数へ返る"
  (define source
    (string-append
     "fn outer(a: Option<Int>) -> Int {\n"
     "  let ignored = fn(x: Option<Int>) -> Option<Int> {\n"
     "    let y ?= x\n"
     "    some(y)\n"
     "  }(a)\n"
     "  7\n"
     "}\nouter(none)"))
  (check-equal? (run-main source) 7))

(test-case "最上位の ?= は return-outside-boundary になる"
  (check-equal?
   (elab-code '(TryBind x (Construct none (Types Int)) x))
   "E-RET-002"))

(test-case "戻り型推論は成功枝と利用者の Return だけを候補にする"
  (define success-only
    (compile (string-append
              "fn f(a: Option<Option<Int>>) {\n"
              "  let x ?= a\n"
              "  x\n}\n"
              "f(some(some(8)))")))
  (check-true (compiled? success-only) (format "success-only: ~s" success-only))
  (when (compiled? success-only)
    (check-equal? (compiled-type success-only) '(Option Int))
    (check-equal? (run-main
                   (string-append
                    "fn f(a: Option<Option<Int>>) {\n"
                    "  let x ?= a\n"
                    "  x\n}\n"
                    "f(some(some(8)))"))
                  '(Construct (Option Int) some 8)))
  (define user-return
    (compile (string-append
              "fn f(a: Option<Option<Int>>, out: Option<Bool>) {\n"
              "  let x ?= a\n"
              "  return out\n}\n"
              "f(none, some(true))")))
  (check-true (compiled? user-return) (format "user-return: ~s" user-return))
  (when (compiled? user-return)
    (check-equal? (third (second (first (compiled-callables user-return))))
                  '(Option Bool))
    (check-equal? (run-main (string-append
                             "fn f(a: Option<Option<Int>>, out: Option<Bool>) {\n"
                             "  let x ?= a\n"
                             "  return out\n}\n"
                             "f(none, some(true))"))
                  '(Construct (Option Bool) none))))

(test-case "?= の右辺が非 ADT か Union なら E-TYP-032"
  (check-equal?
   (code "fn f() -> Int { let x ?= 42\n 1 }\nf()")
   "E-TYP-032")
  (check-equal?
   (code "fn f(a: Int) -> Int { let x ?= a\n 1 }\nf(1)")
   "E-TYP-032")
  (check-equal?
   (code "fn f(value: Option<Int> | Result<Int, Bool>) -> Option<Int> { let x ?= value\n none }\nfn dummy() -> Int { 1 }\ndummy()")
   "E-TYP-032")
  (for ([source (in-list
                 '("fn f() -> Int { let x ?= 42\n 1 }\nf()"
                   "fn f(value: Option<Int> | Result<Int, Bool>) -> Option<Int> { let x ?= value\n none }\nfn dummy() -> Int { 1 }\ndummy()"))]
        [needle (in-list '("42" "value"))])
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-TYP-032")
      (check-false (diagnostic-expected result))
      (check-not-false (diagnostic-found result))
      (check-equal? (diagnostic-primary-span result)
                    (source-span-last source needle)))))

(test-case "?= の境界不一致は E-TYP-033 と primary / related span を持つ"
  (define function-source
    "fn f(a: Option<Int>) -> Int {\n  let x ?= a\n  1\n}\nf(none)")
  (define function-result (compile function-source))
  (check-true (diagnostic? function-result))
  (when (diagnostic? function-result)
    (check-equal? (diagnostic-id function-result) "E-TYP-033")
    (check-equal? (diagnostic-expected function-result) 'Int)
    (check-equal? (diagnostic-found function-result) '(Option Int))
    (check-equal? (diagnostic-primary-span function-result)
                  (source-span function-source "x ?= a"))
    (check-equal? (diagnostic-related function-result)
                  (list (list 'return-boundary
                              '(#:span src 0 56)
                              "失敗を受ける境界"))))
  (check-equal?
   (code "fn f(a: Option<Int>) -> Result<Int, Bool> { let x ?= a\n ok(1) }\nf(none)")
   "E-TYP-033")
  (check-equal?
   (code "fn f(a: Result<Int, Bool>) -> Result<Int, Int> { let x ?= a\n ok(1) }\nf(ok(1))")
   "E-TYP-033"))

(test-case "when と無名関数の境界 mismatch related は境界節点を指す"
  (define lambda-source
    "fn f(a: Option<Int>) -> Int { let g = fn(x: Option<Int>) -> Int { let y ?= x\n 1 }(a)\n 2 }\nf(none)")
  (define lambda-result (compile lambda-source))
  (check-true (diagnostic? lambda-result))
  (when (diagnostic? lambda-result)
    (check-equal? (diagnostic-id lambda-result) "E-TYP-033")
    (check-equal? (second (first (diagnostic-related lambda-result)))
                  (source-span lambda-source "fn(x: Option<Int>) -> Int { let y ?= x\n 1 }")))
  (define when-source
    "fn f(a: Option<Int>) -> Int { when true { true => { let y ?= a\n 1 }\n false => 0 } }\nf(none)")
  (define when-result (compile when-source))
  (check-true (diagnostic? when-result))
  (when (diagnostic? when-result)
    (check-equal? (diagnostic-id when-result) "E-TYP-033")
    (check-equal? (second (first (diagnostic-related when-result)))
                  (source-span when-source "true => { let y ?= a\n 1 }"))))

(test-case "Owned resource 変数の右辺は when と同じ E-OWN-010"
  (define try-source
    "fn f(a: Owned<Option<Int>>) -> Option<Int> { let x ?= a\n some(x) }\nf(none)")
  (define when-source
    "fn f(a: Owned<Option<Int>>) -> Option<Int> { when a { some x => some(x)\n none => none } }\nf(none)")
  (check-equal? (code try-source) "E-OWN-010")
  (check-equal? (code when-source) "E-OWN-010"))

(test-case "失敗枝だけでは戻り型も NarrativeExpr の期待型も推論できない"
  (define inferred-function
    '(Fn ((a (Option Int)) (loop (NFn () Never () ())))
         #:infer ()
       (TryBind x a (Apply loop))))
  (define narrative
    '(Fn ((a (Option Int)) (loop (NFn () Never () ())))
         Int ()
       (Let value
            (NarrativeExpr (TryBind x a (Apply loop)))
            1)))
  (check-equal? (elab-code inferred-function) "E-TYP-024")
  (check-equal? (elab-code narrative) "E-TYP-010"))

(test-case "TryBind の失敗枝は利用者の Return 候補を上書きしない"
  (define source
    (string-append
     "fn f(a: Option<Option<Int>>, out: Option<Bool>) {\n"
     "  let x ?= a\n"
     "  return out\n}\n"
     "f(none, some(true))"))
  (define result (compile source))
  (check-true (compiled? result) (format "user-return: ~s" result))
  (when (compiled? result)
    (check-equal? (third (second (first (compiled-callables result))))
                  '(Option Bool))))

(test-case "TryBind の成功枝が Never の NarrativeExpr は期待型を要する"
  (check-equal?
   (elab-code
    '(Fn ((a (Option Int)) (loop (NFn () Never () ())))
         Int ()
       (Let value
            (NarrativeExpr (TryBind x a (Apply loop)))
            1)))
   "E-TYP-010"))

(test-case "TryBind の右辺は一度だけ Core に現れる"
  (define result
    (compile
     (string-append
      "fn make() -> Option<Int> { some(9) }\n"
      "fn f() -> Option<Int> { let x ?= make()\n some(x) }\n"
      "f()")))
  (check-true (compiled? result) (format "TryBind compile: ~s" result))
  (when (compiled? result)
    (define (count-apply tree)
      (match tree
        [`(Apply ,callee ,args ...)
         (+ 1 (count-apply callee)
            (apply + (map count-apply args)))]
        [(? pair? parts)
         (+ (count-apply (car parts))
            (count-apply (cdr parts)))]
        [_ 0]))
    ;; main の f() と f 本体の make() がそれぞれ一つだけある。
    (check-equal? (count-apply (compiled-core result)) 2)))

(test-case "pipe の関数位置、左辺、残りの引数を順に評価する"
  (define source
    (string-append
     "fn h() { fn(a: Int, b: Int) -> Int { b } }\n"
     "fn g() -> Int { 10 }\n"
     "fn k() -> Int { 20 }\n"
     "g() |> h()(k())"))
  (define result (compile source))
  (check-true (compiled? result) (format "pipe compile: ~s" result))
  (when (compiled? result)
    (call-with-trait-ledger
     (compiled-ledger result)
     (lambda ()
       (define-values (configs rules)
         (trace-g2 (inject-g2m (erase-core (compiled-execution-core result)))))
       (check-config-trace configs (compiled-callables result)
                           (compiled-type result))
       (check-equal? (config-control (last configs)) 20)
       ;; h() の返す関数を先に得てから g() と k() の値を評価する。
       (define beta-indices
         (for/list ([rule (in-list rules)] [index (in-naturals)]
                    #:when (eq? rule 'R-Beta))
           index))
       (check-true (pair? beta-indices)
                   (format "h() の関数位置呼出しを trace する: ~s" rules))
       (define unfolded-call-names
         (for/list ([cfg (in-list configs)]
                    [rule (in-list rules)]
                    #:when (eq? rule 'R-RecurUnfold))
           (define name (first-recur-call (config-control cfg)))
           (and name
                (string->symbol
                 (regexp-replace #rx"⟨.*$" (symbol->string name) "")))))
       (check-equal? unfolded-call-names '(h g k))))))

(test-case "Owned 一時値は通常の Apply 引数として受理する"
  (define-values (_core expected _callables configs rules)
    (elaborated-trace
     '(Apply (Fn ((x (Owned Res))) Unit (Own) (Drop (Move x)))
             (Apply acquire 5))))
  (check-equal? expected 'Unit)
  (check-not-false (member 'R-Beta rules))
  (check-equal? (config-control (last configs)) 'unit))

(test-case "Owned Option と Result の ?= は marker を一度だけ移送する"
  (define option-function
    '(Fn ((p (Owned (Option Int)))) (Option Int) (Own)
         (TryBind x (Move p) (Construct some (Types Int) x))))
  (define option-some
    (run-owned-place option-function '(Option Int)
                     '(Construct (Option Int) some 4)
                     '(Construct (Option Int) some 4)))
  (define option-none
    (run-owned-place option-function '(Option Int)
                     '(Construct (Option Int) none)
                     '(Construct (Option Int) none)))
  (define result-function
    '(Fn ((p (Owned (Result Int Bool)))) (Result Unit Bool) (Own)
         (TryBind x (Move p) (Construct ok (Types Unit Bool) unit))))
  (define result-ng
    (run-owned-place result-function '(Result Int Bool)
                     '(Construct (Result Int Bool) ng (Construct Bool false))
                     '(Construct (Result Unit Bool) ng (Construct Bool false))))
  (define result-ok
    (run-owned-place result-function '(Result Int Bool)
                     '(Construct (Result Int Bool) ok 4)
                     '(Construct (Result Unit Bool) ok unit)))
  (check-true (and (pair? option-some) (pair? option-none)
                   (pair? result-ng) (pair? result-ok))))

(test-case "Owned payload の success と error は枝 encoding を通じて token を保つ"
  (define option
    '(Apply
      (Fn ((value (Option (Owned Res))))
          (Option (Owned Res)) (Own)
          (TryBind payload (Move value)
                   (Construct some (Types (Owned Res)) (Move payload))))
      (Construct some (Types (Owned Res)) (Apply acquire 17))))
  (define result
    '(Apply
      (Fn ((value (Result Int (Owned Res))))
          (Result Unit (Owned Res)) (Own)
          (TryBind payload (Move value)
                   (Construct ok (Types Unit (Owned Res)) unit)))
      (Construct ng (Types Int (Owned Res)) (Apply acquire 19))))
  (for ([expression (in-list (list option result))]
        [tag (in-list '(some ng))])
    (define-values (_core _expected _callables configs rules)
      (elaborated-trace expression))
    (check-not-false (member 'R-LetOwnedB rules)
                     (format "資源 payload の枝 encoding: ~s" rules))
    (check-not-false (member 'R-Move rules)
                     (format "資源 payload の消費: ~s" rules))
    (define terminal (last configs))
    (check-not-false (member tag (flatten (config-control terminal))))
    (check-equal? (length (collect-tokens (config-control terminal))) 1)
    (check-equal?
     (for/sum ([entry (in-list (config-tokens terminal))]
               #:when (eq? (second entry) 'Available))
       1)
     1)))

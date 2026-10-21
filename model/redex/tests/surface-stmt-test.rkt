#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lexer.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))
(define (compile-code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))

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
                  (format "~a: ~a" (diagnostic-id result) (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (and (compiled? result) (run-value result)))

(define (contains-form? tree wanted)
  (or (match tree [`(,head . ,_) (eq? head wanted)] [_ #f])
      (and (list? tree) (ormap (lambda (part) (contains-form? part wanted)) tree))))

(define (contains-value? tree wanted)
  (or (equal? tree wanted)
      (and (list? tree) (ormap (lambda (part) (contains-value? part wanted)) tree))))

(define (find-form tree wanted)
  (cond [(and (pair? tree) (eq? (car tree) wanted)) tree]
        [(pair? tree) (for/or ([child (in-list tree)]) (find-form child wanted))]
        [else #f]))

(define (lower source)
  (lower-surface (parse (lex/string 'src source)) (current-trait-env)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 10000])
    (when (zero? fuel) (error 'trace-g2 "fuel exhausted at ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "expected one step, got ~s" steps)])))

(define (config-control configuration)
  (match configuration [`(cfg ,control ,_heap ,_states ,_tokens ,_events) control]))

(define (config-tokens configuration)
  (match configuration [`(cfg ,_control ,_heap ,_states ,tokens ,_events) tokens]))

(define (trace-compiled result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (define callables (compiled-callables result))
     (define expected (compiled-type result))
     (define start (inject-g2m (erase-core (compiled-execution-core result))))
     (define-values (configs rules) (trace-g2 start))
     (for ([configuration (in-list configs)] [index (in-naturals)])
       (define runtime (runtime-row configuration callables expected))
       (check-not-false runtime (format "config ~a has runtime-row" index))
       (when runtime
         (check-true (config-ok? configuration callables expected runtime))))
     (values configs rules))))

(test-case "Unit 呼出しの式文後に明示した return を返す"
  (check-equal?
   (run-source
    (string-append
     "fn discard(x: Int) -> Unit { () }\n"
     "fn f() -> Int { discard(1)\n return 7 }\n"
     "f()"))
   7))

(test-case "Int の式文を捨て、明示した return を返す"
  (check-equal? (run-source "fn f() -> Int { 1\n return 2 }\nf()") 2))

(test-case "式文と束縛を交互に並べ、後続の束縛を末尾式から使う"
  (check-equal?
   (run-source
    (string-append
     "fn discard(x: Int) -> Unit { () }\n"
     "fn f() -> Int {\n"
     " let x = 2\n"
     " discard(x)\n"
     " let y = 3\n"
     " discard(y)\n"
     " return add(x, y)\n"
     "}\n"
     "f()"))
   5))

(test-case "式文の関数引数にある constructor は Construct になる"
  (define result
    (compile
     (string-append
      "fn take(o: Option<Int>) -> Unit { () }\n"
      "fn f() -> Int { take(some(1))\n return 0 }\n"
      "f()")))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result) (diagnostic-message result))
                  "compile failed"))
  (when (compiled? result)
    (check-equal? (run-value result) 0)
    (match (find-form (compiled-core result) 'Apply)
      [`(Apply ,_ ,_ (Construct ,_ (#:ty ,_ ,_) some ,_)) (void)]
      [other (fail-check (format "Construct を引数に持つ Apply を期待した: ~s" other))])))

(test-case "文位置の when は return を外側へ伝播し、通常の枝は後続へ進む"
  (define source
    (string-append
     "fn log(message: String) -> Unit { () }\n"
     "fn run(r: Result<Int, String>) -> Int {\n"
     " when r {\n"
     "  ok value => return mul(value, 2)\n"
     "  ng error => log(error)\n"
     " }\n"
     " return 0\n"
     "}\n"
     "run(ok(3))"))
  (check-equal? (run-source source) 6)
  (check-equal? (run-source (regexp-replace #rx"run\\(ok\\(3\\)\\)" source
                                           "run(ng(\"x\"))"))
                0))

(test-case "文位置 if は return、値位置 when は leave の宛先に従う"
  (define statement-source
    (string-append
     "fn choose(c: Bool) -> Int {\n"
     " if c { return 1 } else { () }\n"
     " return 2\n"
     "}\n"
     "choose(true)"))
  (check-equal? (run-source statement-source) 1)
  (define value-source
    (string-append
     "fn choose(c: Bool) -> Int {\n"
     " let ignored = when c { true => leave 1\n false => 2 }\n"
     " return 3\n"
     "}\n"
     "choose(true)"))
  (define value-result (compile value-source))
  (check-true (compiled? value-result))
  (when (compiled? value-result)
    (check-equal? (run-value value-result) 3)
    (check-true (contains-form? (compiled-core value-result) 'Handle))))

(test-case "入れ子の文位置 if の return も外側の関数へ伝播する"
  (define source
    (string-append
     "fn choose(a: Bool, b: Bool) -> Int {\n"
     " if a { if b { return 1 } else { () } } else { () }\n"
     " return 2\n"
     "}\n"
     "choose(true, true)"))
  (check-equal? (run-source source) 1)
  (check-equal? (run-source (regexp-replace #rx"choose\\(true, true\\)" source
                                           "choose(true, false)"))
                2))

(test-case "式文の引数、条件、scrutinee にある when の leave は各境界で止まる"
  (check-equal?
   (run-source
    (string-append
     "fn take(o: Option<Int>) -> Unit { () }\n"
     "fn f() -> Int {\n"
     " take(when true { true => leave none\n false => some(1) })\n"
     " return 2\n"
     "}\n"
     "f()"))
   2)
  (check-equal?
   (run-source
    (string-append
     "fn identity(x: Bool) -> Bool { return x }\n"
     "fn f() -> Int {\n"
     " if identity(when true { true => leave true\n false => false }) { () } else { () }\n"
     " return 2\n"
     "}\n"
     "f()"))
   2)
  (check-equal?
   (run-source
    (string-append
     "fn f() -> Int {\n"
     " when (when true { true => leave false\n false => true }) {\n"
     "  true => ()\n"
     "  false => ()\n"
     " }\n"
     " return 2\n"
     "}\n"
     "f()"))
   2))

(test-case "値位置 when の return は関数境界へ届く"
  (define source
    (string-append
     "fn take(o: Option<Int>) -> Unit { () }\n"
     "fn f(b: Bool) -> Option<Int> {\n"
     " take(when b { true => return none\n false => some(1) })\n"
     " return some(2)\n"
     "}\n"
     "f(true)"))
  (define result (compile source))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) '(Construct (Option Int) none)))
  (check-equal?
   (compile-code (string-append
                 "fn take(o: Option<Int>) -> Unit { () }\n"
                 "fn f() -> Int { take(when true { true => return none\n"
                 " false => some(1) })\n return 2 }\nf()"))
   "E-DAT-002"))

(test-case "文位置の非変数 scrutinee は葉を破棄する Eliminate に直接下ろす"
  (define source
    (string-append
     "fn get() -> Bool { return true }\n"
     "fn f() -> Int {\n"
     " when get() { true => ()\n false => () }\n"
     " return 1\n"
     "}\n"
     "f()"))
  (define result (lower source))
  (check-true (lowered? result))
  (when (lowered? result)
    (define (find-statement-eliminate tree)
      (match tree
        [`(Let ,_ ((#:bind %stmt ,_) const (#:ty Unit ,_))
               (Eliminate ,_ (Apply ,_ ,_) ,_) ,_) tree]
        [(? list? parts) (for/or ([part (in-list parts)])
                           (find-statement-eliminate part))]
        [_ #f]))
    (match (find-statement-eliminate (lowered-term result))
      [`(Let ,_ ((#:bind %stmt ,_) const (#:ty Unit ,_))
             (Eliminate ,_ (Apply ,_ ,_) ,_) ,_)
       (check-equal?
        (find-form (lowered-term result) 'Eliminate)
        '(Eliminate
          (#:span src 50 88)
          (Apply (#:span src 55 60) (#:var get (#:span src 55 58)))
          (((#:span src 63 73) true () ->
            (Let (#:span src 71 73) ((#:bind %stmt (#:span src 71 73)) const)
                 (#:lit unit (#:span src 71 73))
                 (#:lit unit (#:span src 71 73))))
           ((#:span src 75 86) false () ->
            (Let (#:span src 84 86) ((#:bind %stmt (#:span src 84 86)) const)
                 (#:lit unit (#:span src 84 86))
                 (#:lit unit (#:span src 84 86))))))
        "文位置の when は Unit 注釈の %stmt で結果を捨てる")]
      [other (fail-check (format "%stmt に包まれた Eliminate を期待した: ~s" other))])))

(test-case "[REQ: RET-001] 文位置の when は非 Unit の枝の値を捨てて後続へ進む"
  (define source
    (string-append
     "fn choose(flag: Bool) -> Int {\n"
     " when flag { true => 11\n false => 12 }\n"
     " return 3\n}\nchoose(true)"))
  (check-equal? (run-source source) 3))

(test-case "[REQ: RET-001] 文位置の非変数 when の全枝 return は関数境界へ届く"
  (define source
    (string-append
     "fn get_flag() -> Bool { return true }\n"
     "fn choose() -> Int {\n"
     " when get_flag() { true => return 11\n false => return 12 }\n"
     "}\nchoose()"))
  (check-equal? (run-source source) 11))

(test-case "Owned の式文の token は後続の実行中に Available で Scope 終了時に Dropped になる"
  (define result
    (compile
     (string-append
      "fn run() -> Int ! Own { acquire(1)\n return 0 }\n"
      "run()")))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result) (diagnostic-message result))
                  "compile failed"))
  (when (compiled? result)
    (check-equal? (run-value result) 0)
    (define-values (configs _rules) (trace-compiled result))
    (check-not-false
     (for/or ([configuration (in-list configs)])
       (and (equal? (config-tokens configuration) '(((tok 0) Available)))
            (contains-value? (config-control configuration) 0)))
     "後続式が実行される間、Owned token は Available である")
    (check-equal? (config-tokens (last configs)) '(((tok 0) Dropped)))))

(test-case "型が異なる枝と資源値を含む文位置の when は結果を合流しない"
  (check-equal?
   (run-source
    "fn f(c: Bool) -> Int { when c { true => 1\n false => () }\n return 0 }\nf(true)")
   0)
  (check-equal?
   (run-source
    (string-append
     "fn f(c: Bool) -> Int ! Own { when c { true => acquire(1)\n false => () }\n return 0 }\n"
     "f(true)"))
   0))

(test-case "文位置の when の本体 block は return で抜け、末尾値は捨てる"
  (define source
    (string-append
     "fn log(message: String) -> Unit { () }\n"
     "fn run(r: Result<Int, String>) -> Int {\n"
     " when r {\n"
     "  ok value => { return mul(value, 2) }\n"
     "  ng error => {\n"
     "   log(error)\n"
     "   99\n"
     "  }\n"
     " }\n"
     " return 0\n"
     "}\n"
     "run(ok(3))"))
  (check-equal? (run-source source) 6)
  (check-equal? (run-source (regexp-replace #rx"run\\(ok\\(3\\)\\)" source
                                           "run(ng(\"x\"))"))
                0))

(test-case "非変数 scrutinee の文位置 when で Owned 式文の token を破棄する"
  (define result
    (compile
     (string-append
      "fn get() -> Bool { return true }\n"
      "fn run() -> Int ! Own {\n"
      " when get() {\n"
      "  true => acquire(1)\n false => ()\n"
      " }\n"
      " return 0\n"
      "}\n"
      "run()")))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result) (diagnostic-message result))
                  "compile failed"))
  (when (compiled? result)
    (check-equal? (run-value result) 0)
    (define-values (configs rules) (trace-compiled result))
    (check-not-false (member 'R-Eliminate rules))
    (check-equal? (config-control (last configs)) 0)
    (check-equal? (config-tokens (last configs)) '(((tok 0) Dropped)))))

(test-case "資源型 scrutinee の文位置 when は Surface lowering と同じ形で token を破棄する"
  (define source
    (string-append
     "fn run(g: fn() -> Result<Owned<Int>, Int>) -> Int {\n"
     " when g() {\n"
     "  ok x => 1\n"
     "  ng y => 0\n"
     " }\n"
     " return 0\n"
     "}\n"
     "0"))
  (define compiled (compile source))
  (check-true (compiled? compiled)
              (if (diagnostic? compiled)
                  (format "~a: ~a" (diagnostic-id compiled)
                          (diagnostic-message compiled))
                  (format "unexpected result: ~s" compiled)))
  (define lowered (lower source))
  (check-true (lowered? lowered))
  (when (and (compiled? compiled) (lowered? lowered))
    (define erased (erase-surface (lowered-term lowered)))
    (define fn (find-form erased 'FnDecl))
    (define trace-expression
      (match fn
        [`(FnDecl run ,_ ,_ ,_
                   (BlockBody
                    (LexicalScope
                     (Let (%stmt const Unit)
                          (Eliminate (Apply g) ,arms)
                          ,_)))
                   ,_)
         (check-equal?
          arms
          '((ok (x) -> (Let (%stmt const) 1 unit))
            (ng (y) -> (Let (%stmt const) 0 unit)))
          "Surface lowering は SExprStmt と枝の葉の discard 形を保つ")
         `(Let (%stmt const Unit)
               (Eliminate
                (Construct ok (Types (Owned Res) Int) (Apply acquire 1))
                ,arms)
               0)]
        [other (fail-check (format "lowered function body の形が異なる: ~s" other))
               #f]))
    (when trace-expression
      (match (elab trace-expression)
        [(list core expected _row callables)
         (call-with-trait-ledger
          (current-trait-ledger)
          (lambda ()
            (define start (inject-g2m (erase-core core)))
            (define-values (configs _rules) (trace-g2 start))
            (for ([configuration (in-list configs)] [index (in-naturals)])
              (define runtime (runtime-row configuration callables expected))
              (check-not-false runtime
                               (format "config ~a has runtime-row" index))
              (when runtime
                (check-true
                 (config-ok? configuration callables expected runtime))))
            (define terminal (last configs))
            (check-equal? (config-control terminal) 0)
            (check-equal? (config-tokens terminal) '(((tok 0) Dropped))))) ]
        [other (fail-check
                (format "statement-mode resource scrutinee trace を elaborate できなかった: ~s"
                        other))]))))

(test-case "SFnDecl の本体は BlockBody として下ろす"
  (define result
    (lower "fn f() -> Unit { when true { true => ()\n false => () } }\nf()"))
  (check-true (lowered? result))
  (when (lowered? result)
    (check-not-false (find-form (lowered-term result) 'BlockBody))
    (check-false (find-form (lowered-term result) 'NarrativeExpr))))

(test-case "最上位の式文の後に末尾式を置き、最上位 return は E-RET-002 にする"
  (check-equal?
   (run-source
    (string-append
     "fn take(o: Option<Int>) -> Unit { () }\n"
     "take(some(1))\n"
     "0"))
   0)
  (define source "return 1\n0")
  (define result (compile source))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-RET-002")
    (check-equal? (diagnostic-primary-span result) '(#:span src 0 8))))

(test-case "同じ行の式列は従来どおり E-SUR-005 になる"
  (check-equal? (compile-code "fn f() -> Int { 1 2 }\nf()") "E-SUR-005"))

(test-case "Union member 枝の文位置 lowering は NarrativeExpr を持たない"
  (define result
    (lower
     (string-append
      "let value: Int | String = 42\n"
      "when value { (n: Int) => ()\n (s: String) => () }\n"
      "0")))
  (check-true (lowered? result))
  (when (lowered? result)
    (match (find-form (lowered-term result) 'Eliminate)
      [`(Eliminate ,_ ,_ ,branches)
       (check-false (contains-form? branches 'NarrativeExpr))]
      [other (fail-check (format "Eliminate を期待した: ~s" other))])))

#lang racket

(require rackunit
         racket/match
         racket/string
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../rows.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))
(define (code source)
  (match (compile source)
    [(? diagnostic? diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value () () () ()) value]
       [other (fail-check (format "終端状態を期待したが ~s" other))]))))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 10000])
    (when (zero? fuel) (error 'trace-g2 "燃料切れ: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _rule next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "1 ステップを期待したが ~s" steps)])))

(define (config-control configuration)
  (match configuration
    [`(cfg ,control ,_heap ,_states ,_tokens ,_events) control]))

(define (config-tokens configuration)
  (match configuration
    [`(cfg ,_control ,_heap ,_states ,tokens ,_events) tokens]))

(define (check-trace configs callables expected)
  (define initial-row (runtime-row (first configs) callables expected))
  (check-not-false initial-row)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row (format "configuration ~a の runtime row" index))
    (when (and row initial-row)
      (check-true (row-subset? row initial-row))
      (check-true (config-ok? configuration callables expected row)))))

(define (find-let-body expression name)
  (or (match expression
        [`(Let ,_ ,bindings ,_ ,body)
         (and (match bindings
                [`((#:bind ,bound-name ,_) . ,_)
                 (and (symbol? bound-name)
                      (string-prefix? (symbol->string bound-name)
                                      (symbol->string name)))]
                [_ #f])
              body)]
        [_ #f])
      (and (list? expression)
           (for/or ([part (in-list expression)])
             (find-let-body part name)))))

(test-case "実引数の Return で全経路を離れる本体を受理する"
  (define result
    (compile "fn id(x: Int) -> Int { return x }\nfn f() -> Int { id(return 1) }\nf()"))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 1)))

(test-case "constructor の欄の Return で全経路を離れる本体を受理する"
  (define result
    (compile (string-append
              "fn id(x: Option<Int>) -> Option<Int> { return x }\n"
              "fn f() -> Int { id(some(return 1)) }\nf()")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 1)))

(test-case "record の欄の Return を射影して返す本体を受理する"
  (define result
    (compile "fn f() -> Int { return ({ a: return 1 }).a }\nf()"))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 1)))

(test-case "record の欄の Return を束縛する本体を受理する"
  (check-equal? (code "fn f() -> Int { let r = { a: return 1 }\n return 2 }\nf()")
                'ok))

(test-case "文の位置の record の欄の Return を受理する"
  (check-equal? (code "fn f() -> Int { { a: return 1 }\n return 2 }\nf()")
                'ok))

(test-case "括弧つき射影の receiver の Return を受理する"
  (define result
    (compile "fn f(r: { a: Int }) -> Int { return (return 1).a }\nf({ a: 1 })"))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 1)))

(test-case "Never の呼び出しを束縛した後の when は正常型で検査する"
  (check-equal?
   (code (string-append
          "fn id(x: Option<Int>) -> Option<Int> { return x }\n"
          "fn f() -> Int { let x = id(some(return 1))\n"
          " return when x { some y => y\n none => 0 } }\nf()"))
   'ok))

(test-case "検査位置の E-Let-Never は到達しない none を期待型で検査する"
  (define result
    (compile (string-append
              "fn f(c: Bool) -> Option<Int> { return if c {"
              " let y = return some(1)\n none } else { none } }\n"
              "f(true)")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) '(Construct (Option Int) some 1))
    (check-match (find-let-body (compiled-core result) 'y)
                 `(Construct ,_ (#:ty (Option Int) ,_) none))))

(test-case "検査位置の E-Let-Never は不一致時に synth へ戻る"
  (define result
    (compile (string-append
              "fn f(c: Bool) -> Option<Int> { return if c {"
              " let y = return some(1)\n \"s\" } else { none } }\n"
              "f(true)")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) '(Construct (Option Int) some 1))
    (check-match (find-let-body (compiled-core result) 'y)
                 `(#:lit "s" ,_))))

(test-case "失敗した検査の TryBind 印を synth に持ち越さない"
  (define result
    (compile (string-append
              "fn id(x: Option<Int>) -> Option<Int> { return x }\n"
              "fn f(c: Bool) -> Option<Int> { return if c {"
              " let y = return some(1)\n"
              " let x ?= id(some(2))\n \"s\" } else { none } }\n"
              "f(true)")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) '(Construct (Option Int) some 1))))

(test-case "try-bind の右辺が直接の Return でも受理する"
  (define result
    (compile "fn f() -> Int { let x ?= return 3\n return x }\nf()"))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 3)))

(test-case "検査位置の TryBind bottom は期待型を先に試し、失敗時は synth へ戻る"
  (for ([tail (in-list '("none" "\"s\""))])
    (define result
      (compile (string-append
                "fn f(c: Bool) -> Option<Int> { return if c {"
                " let x ?= return some(1)\n " tail
                " } else { none } }\nf(true)")))
    (check-true (compiled? result) tail)
    (when (compiled? result)
      (check-equal? (run-value result) '(Construct (Option Int) some 1)))))

(test-case "try-bind の右辺の some の欄の Return を受理する"
  (check-equal?
   (code (string-append
          "fn id(x: Option<Int>) -> Option<Int> { return x }\n"
          "fn f() -> Option<Int> { let x ?= id(some(return none))\n"
          " return some(x) }\nf()"))
   'ok))

(test-case "try-bind の右辺の Result error 欄の Return を受理する"
  (check-equal?
   (code (string-append
          "fn id(x: Result<Int, String>) -> Result<Int, String> { return x }\n"
          "fn f() -> Result<Unit, String> { let x ?= id(ng(return ng(\"e\")))\n"
          " return ok(()) }\nf()"))
   'ok))

(test-case "if の枝の被演算子の Return は合流から除かれる"
  (check-equal?
   (code (string-append
          "fn id(x: Int) -> Int { return x }\n"
          "fn f(c: Bool) -> Int { return if c { id(return 1) } else { 2 } }\n"
          "f(true)"))
   'ok))

(test-case "Never の先にある被演算子の effect row も保持する"
  (define result
    (compile (string-append
              "fn takes(x: Int, y: Int) -> Int { return x }\n"
              "fn later() -> Int ! Own { acquire(2)\n return 0 }\n"
              "fn f() -> Int ! Own { takes(return 1, later()) }\nf()")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-not-false (member 'Own (compiled-row result)))
    (check-equal? (run-value result) 1)))

(test-case "Yield の bottom 観測は既存の ill-typed 診断で拒否する"
  ;; Yield は Surface の式ではなく、手書き UCore からだけ到達する。
  (match (elab '(Fn () Int ((Yield Int)) (Yield (Return 1) unit)))
    [`(err ,diagnostic) (check-equal? (diagnostic-id diagnostic) "E-TYP-001")]
    [other (fail-check (format "E-TYP-001 を期待したが ~s" other))]))

(test-case "TryBind の Known ADT 経路で Owned token を一度だけ返す"
  (define expression
    '(Apply
      (Fn ((payload (Owned Res))) (Option (Owned Res)) (Own)
        (TryBind x
          (Construct some (Types (Owned Res))
            (Return (Construct some (Types (Owned Res)) (Move payload))))
          (Construct some (Types (Owned Res)) (Move x))))
      (Apply acquire 7)))
  (match (elab expression)
    [(list core expected _row callables)
     (call-with-trait-ledger
      (current-trait-ledger)
      (lambda ()
        (define start (inject-g2m (erase-core core)))
        (define configs (trace-g2 start))
        (check-trace configs callables expected)
        (define terminal (last configs))
        (check-equal? (length (collect-tokens (config-control terminal))) 1)
        (check-equal? (config-tokens terminal)
                      '(((tok 0) Dropped) ((tok 1) Available)))))]
    [other (fail-check (format "Owned TryBind の Core を期待したが ~s" other))]))

(test-case "TryBind の直接 Return 経路で Owned token を一度だけ返す"
  (define expression
    '(Apply
      (Fn ((payload (Owned Res)) (fallback (Owned Res))) (Owned Res) (Own)
        (TryBind x (Return (Move payload)) (Move fallback)))
      (Apply acquire 9)
      (Apply acquire 10)))
  (match (elab expression)
    [(list core expected _row callables)
     (call-with-trait-ledger
      (current-trait-ledger)
      (lambda ()
        (define start (inject-g2m (erase-core core)))
        (define configs (trace-g2 start))
        (check-trace configs callables expected)
        (define terminal (last configs))
        (check-equal? (length (collect-tokens (config-control terminal))) 1)
        (check-equal? (config-tokens terminal)
                      '(((tok 0) Dropped)
                        ((tok 1) Dropped)
                        ((tok 2) Available)))))]
    [other (fail-check (format "Owned TryBind の Core を期待したが ~s" other))]))

#lang racket

;; P2m3a。when の式境界が return を局所化し、型を合成する。
(require rackunit
         racket/match
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

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
       [other (fail-check (format "実行結果の config を期待したが ~s" other))]))))

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

(define (contains-form? tree wanted)
  (or (match tree [`(,head . ,_) (eq? head wanted)] [_ #f])
      (and (list? tree) (ormap (lambda (part) (contains-form? part wanted)) tree))))

(define color "type Color =\n  | red\n  | green\n")

(test-case "枝の return は when の値になり関数の残りが実行される"
  (define result
    (compile (string-append
              "fn f(b: Bool) -> Int {\n"
              "  let ignored = when b {\n"
              "    true => return 1\n"
              "    false => 0\n"
              "  }\n"
              "  return 2\n"
              "}\n"
              "f(true)")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 2)))

(test-case "非変数 scrutinee の return は when の境界を越える"
  (define result
    (compile (string-append
              "fn identity(x: Bool) -> Bool { return x }\n"
              "fn f() -> Int {\n"
              "  let ignored = when identity(return 1) {\n"
              "    true => 3\n"
              "    false => 4\n"
              "  }\n"
              "  return 2\n"
              "}\n"
              "f()")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 1)))

(test-case "入れ子の when の return は内側の境界で止まる"
  (define result
    (compile (string-append
              "fn f() -> Int {\n"
              "  let outer = when true {\n"
              "    true => {\n"
              "      let inner = when true {\n"
              "        true => return 1\n"
              "        false => 0\n"
              "      }\n"
              "      2\n"
              "    }\n"
              "    false => 0\n"
              "  }\n"
              "  return outer\n"
              "}\n"
              "f()")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 2)))

(test-case "枝の無名関数の return はその関数の境界で止まる"
  (define result
    (compile (string-append
              "fn f() -> Int {\n"
              "  let ignored = when true {\n"
              "    true => fn(x: Int) -> Int { return x }(1)\n"
              "    false => 0\n"
              "  }\n"
              "  return 2\n"
              "}\n"
              "f()")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 2)))

(test-case "注釈の無い when は Handle と Scope を作って型を合成する"
  (define result
    (compile (string-append color
                            "let c = red\n"
                            "let n = when c {\n  red => 1\n  green => 2\n}\n"
                            "n")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (compiled-type result) 'Int)
    (check-true (contains-form? (compiled-core result) 'Handle))
    (check-true (contains-form? (compiled-core result) 'Scope))))

(test-case "Never の when は最初の return 候補の型を合成する"
  (define result
    (compile (string-append
              "fn f(b: Bool) -> Int {\n"
              "  let n = when b {\n"
              "    true => return 11\n"
              "    false => return 22\n"
              "  }\n"
              "  return n\n"
              "}\n"
              "f(true)")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) 11)))

(test-case "合成位置の非変数 when は従来の E-TYP-004 と span を保つ"
  (define diagnostic
    (compile "let n = when true {\n  true => some(1)\n  false => none\n}\nn"))
  (check-true (diagnostic? diagnostic))
  (when (diagnostic? diagnostic)
    (check-equal? (diagnostic-id diagnostic) "E-TYP-004")
    (check-equal? (diagnostic-primary-span diagnostic) '(#:span src 8 55))))

(test-case "Never で return 候補を合成できない NarrativeExpr は E-TYP-010 になる"
  (match (elab '(NarrativeExpr (Return (Construct none))))
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-TYP-010")]
    [other (fail-check (format "E-TYP-010 を期待したが ~s" other))]))

(test-case "Owned の when return は恒等 handler で受理する"
  (define result
    (elab '(Fn ((returned (Owned Res))) (Owned Res) (Own)
               (NarrativeExpr
                (Eliminate (Construct true (Types))
                  ((true () -> (Return (Move returned)))
                   (false () -> (Return (Move returned)))))))))
  (match result
    [(list core type _ _)
     (check-equal? type '(NFn ((Owned Res)) (Owned Res) () (Own) () User))
     (check-true (contains-form? core 'Handle))]
    [other (fail-check (format "Owned の when return を受理しなかった: ~s" other))]))

(test-case "資源型の非変数 scrutinee は枝の Scope で一度だけ破棄する"
  (define source
    (string-append
     "fn run(g: fn() -> Result<Owned<Int>, Int>) -> Int {\n"
     "  when g() {\n"
     "    ok x => 1\n"
     "    ng y => 0\n"
     "  }\n"
     "  return 0\n"
     "}\n"
     "0"))
  (define source-result (compile source))
  (check-true (compiled? source-result)
              (if (diagnostic? source-result)
                  (format "~a: ~a" (diagnostic-id source-result)
                          (diagnostic-message source-result))
                  (format "unexpected result: ~s" source-result)))
  (define expression
    '(Eliminate (Construct ok (Types (Owned Res) Int) (Apply acquire 1))
                ((ok (x) -> (NarrativeExpr 1))
                 (ng (y) -> (NarrativeExpr 0)))))
  (match (elab expression)
    [(list core expected row callables)
     (call-with-trait-ledger
      (current-trait-ledger)
      (lambda ()
        (define start (inject-g2m (erase-core core)))
        (define-values (configs rules) (trace-g2 start))
        (define initial-row (runtime-row start callables expected))
        (check-not-false initial-row "initial config has a runtime row")
        (for ([configuration (in-list configs)] [index (in-naturals)])
          (define runtime (runtime-row configuration callables expected))
          (check-not-false runtime (format "config ~a has a runtime row" index))
          (when (and runtime initial-row)
            (check-true (row-subset? runtime initial-row))
            (check-true (config-ok? configuration callables expected runtime))))
        (define terminal (last configs))
        (check-not-false (member 'R-LetOwnedB rules))
        (check-equal? (config-control terminal) 1)
        (check-equal? (config-tokens terminal) '(((tok 0) Dropped))))) ]
    [other (fail-check (format "資源型の scrutinee trace を elaboration できなかった: ~s"
                               other))]))

(test-case "Never scrutinee は E-DAT-003 と Never を保つ"
  (define result
    (compile "fn f() -> Int { return when (return 1) { true => 2\n false => 3 } }\nf()"))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-DAT-003")
    (check-equal? (diagnostic-found result) 'Never)))

(test-case "検査位置の非変数 scrutinee の when は期待型を受け取る"
  (define source
    (string-append
     "fn identity(x: Bool) -> Bool { return x }\n"
     "fn fromLet(b: Bool) -> Option<Int> {\n"
     "  let result: Option<Int> = when identity(b) {\n"
     "    true => some(1)\n"
     "    false => none\n"
     "  }\n"
     "  return result\n"
     "}\n"
     "fn fromReturn(b: Bool) -> Option<Int> {\n"
     "  return when identity(b) {\n"
     "    true => some(1)\n"
     "    false => none\n"
     "  }\n"
     "}\n"
     "fromLet(true)"))
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result))))

(test-case "Owned の非恒等 Return handler は E-OWN-032 で拒む"
  (define core
    '(Handle (Return boundary (Owned Res))
             (return-value -> (Move return-value))
             (Perform (Return boundary (Owned Res)) (resource 1))))
  (define result (core-type-of/diagnostic core '() '()))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-OWN-032")))

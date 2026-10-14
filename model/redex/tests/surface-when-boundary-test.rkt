#lang racket

;; P2m3a。when の式境界が return を局所化し、型を合成する。
(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../elaborate.rkt"
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
              "  2\n"
              "}\n"
              "f(true)")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 2)))

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
              "  outer\n"
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
              "  2\n"
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
              "  n\n"
              "}\n"
              "f(true)")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) 11)))

(test-case "期待型を要する when の枝は E-TYP-004 を保つ"
  (check-equal? (code "let n = when true {\n  true => some(1)\n  false => none\n}\nn")
                "E-TYP-004"))

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

(test-case "Owned の非恒等 Return handler は E-OWN-032 で拒む"
  (define core
    '(Handle (Return boundary (Owned Res))
             (return-value -> (Move return-value))
             (Perform (Return boundary (Owned Res)) (resource 1))))
  (define result (core-type-of/diagnostic core '() '()))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-OWN-032")))

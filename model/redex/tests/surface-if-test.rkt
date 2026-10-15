#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt")

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

(test-case "if は条件に応じて選んだ枝を評価する"
  (check-equal? (run-source "fn choose(b: Bool) -> Int { if b { 11 } else { 22 } }\nchoose(true)") 11)
  (check-equal? (run-source "fn choose(b: Bool) -> Int { if b { 11 } else { 22 } }\nchoose(false)") 22))

(test-case "選ばれない枝の return は実行されない"
  (check-equal?
   (run-source
    (string-append
     "fn choose(b: Bool) -> Int {\n"
     "  let ignored = if b { 7 } else { return 99 }\n"
     "  2\n"
     "}\nchoose(true)"))
   2))

(test-case "枝の return は if の値になって関数の残りが実行される"
  (check-equal?
   (run-source
    (string-append
     "fn choose(b: Bool) -> Int {\n"
     "  let result = if b { return 1 } else { 2 }\n"
     "  3\n"
     "}\nchoose(true)"))
   3))

(test-case "else if は内側の if として評価される"
  (check-equal?
   (run-source "fn choose(b: Bool) -> Int { if b { 1 } else if true { 2 } else { 3 } }\nchoose(false)")
   2))

(test-case "条件内の return は if の枝境界を越えて外側へ届く"
  (check-equal?
   (run-source
    (string-append
     "fn identity(x: Bool) -> Bool { x }\n"
     "fn f() -> Int {\n"
     "  let ignored = if identity(return 1) { true } else { false }\n"
     "  2\n"
     "}\nf()"))
   1))

(test-case "if の条件が Int なら全体の位置で expected Bool を診断する"
  (define source "if 1 { 1 } else { 2 }")
  (define result (compile source))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-012")
    (check-equal? (diagnostic-expected result) 'Bool)
    (check-equal? (diagnostic-found result) 'Int)
    (check-equal? (diagnostic-primary-span result)
                  `(#:span src 0 ,(string-length source)))))

(test-case "Union 条件の不適合成分も if 全体の位置で診断する"
  (define source
    "fn f(v: Int | Bool) -> Int { if v { 1 } else { 2 } }\nf(true)")
  (define result (compile source))
  (define if-start (string-length "fn f(v: Int | Bool) -> Int { "))
  (define if-end (+ if-start (string-length "if v { 1 } else { 2 }")))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-012")
    (check-equal? (diagnostic-expected result) 'Bool)
    (check-equal? (diagnostic-found result) 'Int)
    (check-equal? (diagnostic-primary-span result)
                  `( #:span src ,if-start ,if-end))))

(test-case "注釈付き Let と関数戻り型の期待型を if の両枝へ渡す"
  (define annotated
    (string-append
     "fn f(b: Bool) -> Option<Int> {\n"
     "  let value: Option<Int> = if b { some(1) } else { none }\n"
     "  value\n"
     "}\nf(true)"))
  (define returned
    (string-append
     "fn f(b: Bool) -> Option<Int> { if b { some(1) } else { none } }\nf(false)"))
  (for ([source (in-list (list annotated returned))])
    (define result (compile source))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result) (diagnostic-message result))
                    (format "unexpected result: ~s" result)))
    (when (compiled? result)
      (check-equal? (compiled-type result) '(Option Int)))))

(test-case "入れ子の if は各条件の束縛を取り違えない"
  (define source
    (string-append
     "fn choose(a: Bool, b: Bool) -> Int {\n"
     "  if a { if b { 1 } else { 2 } } else { 3 }\n"
     "}\nchoose(true, false)"))
  (check-equal? (run-source source) 2))

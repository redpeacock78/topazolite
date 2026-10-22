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
         "../region.rkt"
         "../typing.rkt")

(define (compile source)
  (compile-source/string 'src source))

(define (compile-accepted source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compiled source expected, got ~a at ~s"
                          (diagnostic-id result)
                          (diagnostic-primary-span result))
                  (format "unexpected result: ~s" result)))
  result)

(define (compile-rejected source expected-id)
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id))
  result)

(define (trace-compiled result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (define trace
       (bounded-trace-g2
        (inject-g2m (erase-core (compiled-execution-core result)))
        10000))
     (check-equal? (execution-outcome trace) 'terminal)
     (for ([config (in-list (execution-configs trace))]
           [index (in-naturals)])
       (define row
         (runtime-row config (compiled-callables result) (compiled-type result)))
       (check-not-false row (format "config ~a has runtime-row" index))
       (when row
         (check-true
          (config-ok? config (compiled-callables result) (compiled-type result) row)
          (format "config ~a passes config-ok?" index))))
     (execution-configs trace))))

(define (trace-value result)
  (match (last (trace-compiled result))
    [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
    [other (fail-check (format "terminal config expected, got ~s" other))]))

(define (core-failure core [places '()])
  (define ir (build-region-ir core))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
  (match (type-of/raw core places '() '()
                      (region-ctx ir '() owners (hash)))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(test-case "注釈付き Owned の let を実行できる"
  (for ([source (in-list
                 (list "let value: Owned<Int> = 1\n0"
                       "let value: Owned<{ n: Int }> = { n: 1 }\n0"
                       "let value: Owned<Option<Int>> = none()\n0"
                       "let values: Owned<List<Int>> = nil()\n0"))])
    (define result (compile-accepted source))
    (when (compiled? result)
      (check-equal? (compiled-type result) 'Int)
      (check-equal? (trace-value result) 0))))

(test-case "資源を含む Owned payload を注釈付き let で持ち上げて一度 fin する"
  (define result
    (compile-accepted "let value: Owned<Option<Owned<Res>>> = some(acquire(1))\n0"))
  (when (compiled? result)
    (define configs (trace-compiled result))
    (match (last configs)
      [`(cfg 0 ,_heap ,_states ,tokens ,events)
       (check-equal? (length tokens) 1)
       (check-equal? (second (first tokens)) 'Dropped)
       (define fin-leaves
         (filter (λ (event) (match event [`(finLeaf ,_place ,_) #t] [_ #f])) events))
       (check-equal? (length fin-leaves) 1)
       (check-equal? (length (filter (λ (event) (match event [`(fin ,_) #t] [_ #f]))
                                     events))
                     1)]
      [other (fail-check (format "trace terminal expected, got ~s" other))])))

(test-case "既に Owned を返す if・when・block の注釈を保つ"
  (for ([source
         (in-list
          (list
           (string-append
            "fn f(c: Bool) -> Int ! {Own, Partial} {\n"
            " let value: Owned<Res> = if c { acquire(1) } else { acquire(2) }\n"
            " return 0 }\nf(true)")
           (string-append
            "fn f(c: Bool) -> Int ! {Own, Partial} {\n"
            " let value: Owned<Res> = when c { true => acquire(1)\n"
            " false => acquire(2) }\n return 0 }\nf(true)")
           "let value: Owned<Res> = { acquire(3) }\n0"))])
    (define result (compile-accepted source))
    (when (compiled? result)
      (check-equal? (compiled-type result) 'Int)
      (check-equal? (trace-value result) 0))))

(test-case "Surface の Owned 局所値には Move 構文が無い"
  ;; Surface に Owned 局所値の Move 構文がないため、OwnedTransit の実行は Core の試験で担う。
  (compile-rejected "let x: Owned<Int> = 1\nlet y = x\n0" "E-OWN-010"))

(test-case "注釈付き let 以外では Owned lift しない"
  (compile-rejected
   "fn take(value: Owned<Int>) -> Int ! Own { return 7 }\ntake(1)"
   "E-TYP-012")
  (compile-rejected
   (string-append
    "fn choose(a: Bool, b: Bool, first: fn() -> Owned<Int> ! Own, "
    "second: fn() -> Owned<String> ! Own) -> Int ! Own {\n"
    " let ignored = if a { first() } else if b { second() }\n"
    " 0\n}\n0")
   "E-TYP-012"))

(test-case "資源値を別の Owned payload へ暗黙に持ち上げない"
  (compile-rejected
   "let value: Owned<Owned<Res>> = acquire(1)\n0"
   "E-TYP-012")
  (compile-rejected
   "let value: Owned<Option<Res>> = some(acquire(1))\n0"
   "E-DAT-002"))

(test-case "借用を含む Owned payload は Core と同じ key で拒否する"
  ;; Surface の借用構文は Task 5 で導入するため、UCore から先に Core の拒否を固定する。
  (match
      (elab
       '(LexicalScope
         (Let (x let (Owned Int)) 1
           (Let (borrow let (Borrowed Int Omitted)) (Borrow x)
             (Let (boxed let (Owned (Borrowed Int Omitted))) borrow 0)))))
    [(list core _type _row callables)
     (define result (core-type-of/regions core '() callables))
     (check-true (diagnostic? result))
     (when (diagnostic? result)
       (check-equal? (diagnostic-id result) "E-OWN-022"))]
    [other (fail-check (format "elaboration success を期待した: ~s" other))])
  (check-equal?
   (core-failure
    '(Scope (1)
       (Let (borrow let (BorrowedMut Int (RVar 0)))
            (BorrowMut 1)
         (Let (boxed let (Owned (BorrowedMut Int (RVar 0))))
              borrow
           0)))
    '((1 Int)))
   'own-binding-borrowed-payload))

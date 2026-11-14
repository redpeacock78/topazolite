#lang racket

(require rackunit
         racket/list
         racket/match
         "../borrow-oracle.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../region.rkt"
         "../typing.rkt")

(define (compile source)
  (compile-source/string 'src source))

(define (check-rejected source expected-id)
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)))

(define (compile-traced-value source)
  (define artifact (compile source))
  (check-true (compiled? artifact)
              (if (diagnostic? artifact)
                  (format "compile failed with ~a at ~s"
                          (diagnostic-id artifact)
                          (diagnostic-primary-span artifact))
                  (format "compiled result expected, got ~s" artifact)))
  (and (compiled? artifact)
       (let* ([core (compiled-core artifact)]
              [callables (compiled-callables artifact)]
              [ir (build-region-ir core)]
              [typed (core-type-of/regions core '() callables #:ir ir)])
         (check-true (region-typed? typed)
                     (format "Surface Core region typing: ~s" typed))
         (and (region-typed? typed)
              (call-with-trait-ledger
               (compiled-ledger artifact)
               (lambda ()
                 (define start
                   (inject-g2m (erase-core (region-execution-core typed))))
                 (define trace (bounded-trace-g2 start 10000))
                 (check-equal? (execution-outcome trace) 'terminal)
                 (for ([config (in-list (execution-configs trace))]
                       [index (in-naturals)])
                   (define row
                     (runtime-row config callables (region-typed-type typed)
                                  #:region-ir ir))
                   (check-not-false row
                                    (format "config ~a runtime-row: ~s"
                                            index config))
                   (when row
                     (check-true
                      (config-ok? config callables (region-typed-type typed)
                                  row #:region-ir ir)
                      (format "config ~a config-ok?: ~s" index config))))
                 (check-equal?
                  (check-borrow-execution start (region-typed-sidecar typed)
                                          ir 10000 (make-bcounters))
                  'ok
                  "trace borrow oracle")
                 (match (last (execution-configs trace))
                   [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
                   [other (fail-check (format "terminal config expected: ~s" other))])))))))

(test-case "for/?= binder から捕捉閉包を呼べる（全 trace は Task 2c で固定）"
  (define artifact
    (compile
     (string-append
      "fn outer<r>(p: &r Int) -> Option<Int> ! {Own, Partial} {\n"
      "  let xs: List<Int> = cons(1, nil)\n"
      "  let f ?= for x in xs {\n"
      "    leave fn(q: &r Int) -> Int { return deref(p) }\n"
      "  }\n"
      "  return some(f(p))\n"
      "}\n"
      "let owner: Owned<Int> = 75\n"
      "outer(&owner)")))
  (check-true (compiled? artifact)
              (if (diagnostic? artifact)
                  (format "static acceptance failed with ~a at ~s"
                          (diagnostic-id artifact)
                          (diagnostic-primary-span artifact))
                  (format "compiled result expected, got ~s" artifact))))

(test-case "Record/Proj 経由の捕捉閉包借用結果は静的に受理する"
  ;; 実行 trace は Task 2c で固定する。
  (define source
    (string-append
     "fn outer<r>(p: &r Int) -> Int ! {Own, Partial} {\n"
     "  let inner = fn(q: &r Int) -> &r Int { return p }\n"
     "  let holder = {callback: inner}\n"
     "  return deref(holder.callback(p))\n"
     "}\n"
     "let owner: Owned<Int> = 75\n"
     "outer(&owner)"))
  (define artifact (compile source))
  (check-true (compiled? artifact)
              (if (diagnostic? artifact)
                  (format "compile failed with ~a at ~s"
                          (diagnostic-id artifact)
                          (diagnostic-primary-span artifact))
                  (format "compiled result expected, got ~s" artifact)))
  (when (compiled? artifact)
    (define core (compiled-core artifact))
    (define typed
      (core-type-of/regions core '() (compiled-callables artifact)
                            #:ir (build-region-ir core)))
    (check-true (region-typed? typed)
                (format "Surface Core region typing: ~s" typed))))

(test-case "summary の無い高階 callee の非借用結果は引き続き受理する"
  (check-equal?
   (compile-traced-value
    (string-append
     "fn use(g: fn() -> fn(Int) -> Int) -> Int {\n"
     "  let f = g()\n"
     "  return f(7)\n"
     "}\n"
     "use(fn() => fn(x: Int) => x)"))
   7))

(test-case "owner Scope 内の return payload として捕捉閉包を運ぶと E-BOR-004"
  (check-rejected
   (string-append
    "fn outer<r>(p: &r Int) ! {Own, Partial} {\n"
    "  return fn(q: &r Int) -> Int { return deref(p) }\n"
    "}\n"
    "let closure = { let owner: Owned<Int> = 75\n"
    "  outer(&owner) }\n"
    "0")
   "E-BOR-004"))

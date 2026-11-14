#lang racket

(require rackunit
         "../diagnostic.rkt"
         "../driver.rkt")

(define (compile source)
  (compile-source/string 'src source))

(define (check-rejected source expected-id)
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)))

(test-case "既存の縮約 (Task 2c0b): for/?= binder の捕捉閉包呼出しは E-BOR-020"
  (check-rejected
   (string-append
    "fn outer<r>(p: &r Int) -> Option<Int> ! {Own, Partial} {\n"
    "  let xs: List<Int> = cons(1, nil)\n"
    "  let f ?= for x in xs {\n"
    "    leave fn(q: &r Int) -> Int { return deref(p) }\n"
    "  }\n"
    "  return some(f(p))\n"
    "}\n"
    "let owner: Owned<Int> = 75\n"
    "outer(&owner)")
   "E-BOR-020"))

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

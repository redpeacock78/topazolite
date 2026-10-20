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

(define (block-close-span source text)
  (match (regexp-match-positions (regexp (regexp-quote text)) source)
    [(list (cons _ end)) `(#:span src ,(sub1 end) ,end)]
    [_ (error 'block-close-span "block not found: ~a" text)]))

(define (check-accepted source type value)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (when (compiled? result)
    (check-equal? (compiled-type result) type)
    (check-equal? (run-value result) value)))

(define (check-rejected source id block-text)
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) id)
    (check-equal? (diagnostic-primary-span result)
                  (block-close-span source block-text))))

(test-case "明示ブロックの単一式は when と if の値になり、文を含むブロックは落ち抜ける"
  (for ([scrutinee (in-list '("flag" "get_flag()"))])
    (define prefix
      (if (equal? scrutinee "flag")
          ""
          "fn get_flag() -> Bool { return true }\n"))
    (define params (if (equal? scrutinee "flag") "flag: Bool" ""))
    (check-accepted
     (string-append prefix
                    "fn f(" params ") -> Int { return when " scrutinee " {\n"
                    " true => { 1 }\n false => { 2 }\n}\n}\n"
                    (if (equal? scrutinee "flag") "f(true)" "f()"))
     'Int 1)
    (check-rejected
     (string-append prefix
                    "fn f(" params ") -> Int { return when " scrutinee " {\n"
                    " true => { let x = 1\n x }\n false => { leave 2 }\n}\n}\n"
                    (if (equal? scrutinee "flag") "f(true)" "f()"))
     "E-RET-005" "true => { let x = 1\n x }"))
  (check-accepted
   "fn f(flag: Bool) -> Int { return if flag { 1 } else { 2 } }\nf(true)"
   'Int 1)
  (check-rejected
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool) -> Int { return if c { noop()\n 1 } else { 2 } }\nf(true)")
   "E-RET-005" "if c { noop()\n 1 }")
  (check-accepted
   "fn f(flag: Bool) -> Int { return when flag { true => { let x = 7\n leave x }\n false => { leave 2 } } }\nf(true)"
   'Int 7))

(test-case "[REQ: SUR-014] else if は式として lowering され、文を持つ分岐の leave が値になる"
  (check-accepted
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(a: Bool, b: Bool) -> Int { return if a { 1 } else if b { noop()\n leave 2 } else { 3 } }\n"
    "f(false, true)")
   'Int 2)
  (check-rejected
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(a: Bool, b: Bool) -> Int { return if a { 1 } else if b { let y = 2\n y } else { 3 } }\n"
    "f(false, true)")
   "E-RET-005" "if b { let y = 2\n y }"))

(test-case "合成位置の文を持つ if ブロックの落ち抜けは E-RET-005"
  (check-rejected
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool, d: Bool) -> Int { let a = if c { if d { leave 1 }\n noop() }\n return a }\n"
    "f(true, false)")
   "E-RET-005" "if c { if d { leave 1 }\n noop() }")
  (check-rejected
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool, d: Bool) -> Int { let a = if c { 1 } else if d { noop()\n 2 }\n return a }\n"
    "f(false, true)")
   "E-RET-005" "if d { noop()\n 2 }")
  (check-accepted
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool) -> Option<Unit> { let a = if c { noop()\n 1 }\n return a }\n"
    "f(true)")
   '(Option Unit) '(Construct (Option Unit) some unit)))

(test-case "値位置の if の落ち抜けは Unit payload となり、非 Unit payload と混ぜない"
  (check-accepted
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool) -> Option<Unit> { return if c { noop()\n 1 } }\n"
    "f(true)")
   '(Option Unit) '(Construct (Option Unit) some unit))
  (check-accepted
   (string-append
    "fn f(c: Bool) -> Option<Int> { return if c { leave 1 } }\n"
    "f(true)")
   '(Option Int) '(Construct (Option Int) some 1))
  (check-rejected
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool) -> Option<Int> { return if c { noop()\n noop() } }\n"
    "f(true)")
   "E-RET-005" "if c { noop()\n noop() }")
  (check-rejected
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool, d: Bool) -> Option<Int> { return if c { if d { leave 1 }\n noop() } }\n"
    "f(true, false)")
   "E-RET-005" "if c { if d { leave 1 }\n noop() }"))

(test-case "IfSome の下見と本検査は同じ型を選び、落ち抜けを外側へ漏らさない"
  (for ([annotation (in-list '("" ": Option<Int>"))])
    (check-accepted
     (string-append
      "fn noop() -> Unit { () }\n"
      "fn f(c: Bool) -> Option<Int> { let answer" annotation " = if c { noop()\n leave 1 }\n return answer }\n"
      "f(true)")
     '(Option Int) '(Construct (Option Int) some 1)))
  (check-accepted
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool, p: Bool) -> Int { return when p {\n"
    " true => { let u = if c { noop()\n noop() }\n leave 1 }\n"
    " false => { leave 2 }\n}\n}\nf(true, true)")
   'Int 1))

(test-case "文位置の if は枝の値を捨て、Unit 文脈の when と if は受理する"
  (check-accepted
   "fn f(c: Bool) -> Unit { if c { let x = 1\n x }\n () }\nf(true)"
   'Unit 'unit)
  (check-accepted
   (string-append
    "fn noop() -> Unit { () }\n"
    "fn f(c: Bool) -> Unit { if c { noop()\n () } else { () } }\nf(true)")
   'Unit 'unit)
  (check-accepted
   "fn f(c: Bool) -> Unit { return when c { true => { () }\n false => { () } } }\nf(true)"
   'Unit 'unit))

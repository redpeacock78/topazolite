#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt")

(define (compile source) (compile-source/string 'src source))
(define (code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))

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
                  (inject-g2m (erase-core (compiled-execution-core result)))
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

(define (first-recur-call tree)
  (match tree
    [`(Apply (RecurVal ,_ ,name ,_ ,_) ,_ ...) name]
    [(? pair? parts)
     (or (first-recur-call (car parts))
         (first-recur-call (cdr parts)))]
    [_ #f]))

(test-case
 "[REQ: SUR-002] SUR-002b: 穴の値を連結した文字列へ評価する"
 (check-equal? (run-main "let s = \"x\"\n\"a${s}b\"") "axb")
 (check-equal? (run-main "let s = \"x\"\n\"${s}\"") "x")
 (check-equal? (run-main "let a = \"p\"\nlet b = \"q\"\n\"${a}${b}\"") "pq")
 (check-equal? (run-main "\"\\${s}\"") "${s}"))

(test-case
 "SUR-002b: 入れ子の interpolation と穴の中の block を評価する"
 (check-equal? (run-main "let x = \"i\"\n\"o${\"m${x}\"}o\"") "omio")
 (check-equal? (run-main "let x = \"i\"\n\"${ {\n let y = x\n y\n} }\"") "i"))

(test-case
 "SUR-002b: String と互換でない穴は E-TYP-012 で、primary は穴の式である"
 (define source "\"a${1}\"")
 (define result (compile source))
 (check-equal? (diagnostic-id result) "E-TYP-012")
 (check-equal? (diagnostic-primary-span result) '(#:span src 4 5))
 (check-equal? (diagnostic-expected result) 'String)
 (check-equal? (diagnostic-found result) 'Int)
 ;; 括弧は節点を作らないので、primary は括弧の内側である。
 (check-equal? (diagnostic-primary-span (compile "\"a${(1)}\""))
               '(#:span src 5 6)))

(test-case
 "SUR-002b: Never の穴は受理し、穴の合成失敗はその診断のまま出る"
 (check-false (code "fn f() -> String { return \"a${return \"r\"}\" }\nf()"))
 (check-equal? (code "\"${x => x}\"") "E-TYP-025"))

(test-case
 "SUR-002b: 利用者の concat の束縛は組み替えに影響しない"
 (check-equal? (run-main "let concat = \"z\"\nlet s = \"x\"\n\"${s}${concat}\"") "xz"))

(test-case
 "SUR-002b: 穴の式の Effect は式全体の row に入る"
 (check-false
  (code "fn h(n: Int) -> String ! Partial { return h(n) }\nfn g() -> String ! Partial { return \"${h(1)}\" }\n0"))
 (check-equal?
  (code "fn h(n: Int) -> String ! Partial { return h(n) }\nfn g() -> String { return \"${h(1)}\" }\n0")
  (code "fn h(n: Int) -> String ! Partial { return h(n) }\nfn g() -> String { return h(1) }\n0")))

(test-case
 "SUR-002b: 穴の式は原文の左から右の順に評価する"
 (define source
   (string-append
    "fn f() -> String { return \"f\" }\n"
    "fn g() -> String { return \"g\" }\n"
    "\"${f()}${g()}\""))
 (define result (compile source))
 (check-true (compiled? result) (format "compile failed: ~s" result))
 (when (compiled? result)
   (call-with-trait-ledger
    (compiled-ledger result)
    (lambda ()
      (define-values (configs rules)
        (trace-g2 (inject-g2m (erase-core (compiled-execution-core result)))))
      (check-equal? (config-control (last configs))
                    "fg")
      ;; R-RecurUnfold が現れた構成の control から、先に f、次に g を観測する。
      (define unfolded-call-names
        (for/list ([cfg (in-list configs)]
                   [rule (in-list rules)]
                   #:when (eq? rule 'R-RecurUnfold))
          (define name (first-recur-call (config-control cfg)))
          (and name
               (string->symbol
                (regexp-replace #rx"⟨.*$" (symbol->string name) "")))))
      (check-equal? unfolded-call-names '(f g))
      (void rules)))))

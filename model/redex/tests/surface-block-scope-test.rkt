#lang racket

(require rackunit
         racket/list
         racket/match
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../elaborate.rkt"
         "../gen.rkt"
         "../lexer.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../parser.rkt"
         "../span-core.rkt"
         "../surface-lower.rkt"
         "../typing.rkt")

(define (lower-source source)
  (define result
    (lower-surface (parse (lex/string 'src source)) (current-trait-env)))
  (if (lowered? result) (lowered-term result) result))

(define (count-form term wanted)
  (+ (if (match term [`(,head . ,_) (eq? head wanted)] [_ #f]) 1 0)
     (if (list? term)
         (for/sum ([part (in-list term)]) (count-form part wanted))
         0)))

(define (find-form term wanted)
  (or (match term [`(,head . ,_) (and (eq? head wanted) term)] [_ #f])
      (and (list? term)
           (for/or ([part (in-list term)]) (find-form part wanted)))))

(define (compile source)
  (compile-source/string 'src source))

(define (config-tokens config)
  (match config [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (config-events config)
  (match config [`(cfg ,_ ,_ ,_ ,_ ,events) events]))

(define (span-of-fragment source fragment)
  (match (regexp-match-positions (regexp (regexp-quote fragment)) source)
    [(list (cons lo hi)) `(#:span src ,lo ,hi)]
    [_ (error 'span-of-fragment "fragment not found: ~a" fragment)]))

(define (close-span-of-fragment source fragment)
  (match (regexp-match-positions (regexp (regexp-quote fragment)) source)
    [(list (cons _ hi)) `(#:span src ,(sub1 hi) ,hi)]
    [_ (error 'close-span-of-fragment "fragment not found: ~a" fragment)]))

(define (fin-events config)
  (filter (λ (event) (match event [`(fin ,_) #t] [_ #f]))
          (config-events config)))

(define (trace-configs+rules result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (λ ()
     (define callables (compiled-callables result))
     (define expected (compiled-type result))
     (define start
       (inject-g2m (erase-core (compiled-execution-core result))))
     (let loop ([current start] [configs (list start)] [rules '()] [fuel 10000])
       (when (zero? fuel) (error 'trace-configs+rules "fuel exhausted at ~s" current))
       (match (raw-steps-g2/named current)
         ['() (values configs rules)]
         [(list (list rule next))
          (define row (runtime-row next callables expected))
          (check-not-false row)
          (when row (check-true (config-ok? next callables expected row)))
          (loop next (append configs (list next)) (append rules (list rule))
                (sub1 fuel))]
         [steps (error 'trace-configs+rules "expected one step, got ~s" steps)])))))

(define (trace-configs result)
  (define-values (configs _rules) (trace-configs+rules result))
  configs)

(define (token-state config token)
  (define entry (assoc token (config-tokens config)))
  (and entry (second entry)))

(define (check-dropped-once configs expected-count)
  (define terminal (last configs))
  (define tokens (config-tokens terminal))
  (check-equal? (length tokens) expected-count)
  (for ([entry (in-list tokens)])
    (define token (first entry))
    (check-equal? (second entry) 'Dropped)
    (define transitions
      (for/sum ([before (in-list configs)] [after (in-list (cdr configs))])
        (if (and (eq? (token-state before token) 'Available)
                 (eq? (token-state after token) 'Dropped))
            1
            0)))
    (check-equal? transitions 1 (format "~s is dropped once" token))))

(test-case "SBlock の全 lowering 経路が block ごとに LexicalScope を作る"
  (define examples
    (list
     (list "function body" "fn f() -> Unit { () }\n()" 1)
     (list "nested expression block with bindings"
           "fn f() -> Unit { let v = { let x = 1\n x }\n () }\n()" 2)
     (list "nested expression block without bindings"
           "fn f() -> Int { let v = { 1 }\n return v }\n0" 2)
     (list "nested statement block"
           "fn f() -> Unit { { let x = 1\n () }\n () }\n()" 2)
     (list "if branches and their generated block"
           "fn f(b: Bool) -> Unit { if b { () } else { () }\n () }\n()" 4)
     (list "when arms with and without bindings"
           (string-append
            "fn f(v: Option<Int>) -> Unit {\n"
            " when v { some n => { let x = n\n () }\n none => { () } }\n"
            " () }\n()")
           3)
     (list "for body"
           "fn f(xs: List<Int>) -> Unit { for x in xs { () }\n () }\n()" 2)
     (list "synthetic if-some block"
           "fn f(b: Bool) -> Unit { if b { () }\n () }\n()" 3)))
  (for ([example (in-list examples)])
    (define term (lower-source (second example)))
    (check-equal? (count-form term 'LexicalScope) (third example)
                  (first example))))

(test-case "入れ子 block の ScopeValue が次の block より前に fin を記録する"
  (define result
    (compile
     (string-append
      "fn f() -> Unit ! Own {\n"
      " { let first = acquire(1)\n () }\n"
      " let second = acquire(2)\n () }\n"
      "f()")))
  (check-true (compiled? result)
              (if (diagnostic? result) (diagnostic-id result)
                  "compiled result expected"))
  (when (compiled? result)
    (define-values (configs rules) (trace-configs+rules result))
    (check-dropped-once configs 2)
    (define first-token
      (first (first (config-tokens (findf
                                    (λ (config) (= (length (config-tokens config)) 1))
                                    configs)))))
    (check-not-false
     (for/or ([before (in-list configs)]
              [after (in-list (cdr configs))]
              [rule (in-list rules)])
       (and (eq? rule 'R-ScopeValue)
            (= (length (config-tokens before)) 1)
            (= (length (config-tokens after)) 1)
            (eq? (token-state before first-token) 'Dropped)
            (eq? (token-state after first-token) 'Dropped)
            (zero? (length (fin-events before)))
            (= (length (fin-events after)) 1)))
     "block Scope の R-ScopeValue が次の block の前に fin を記録する")
    (define after-second-acquire
      (findf (λ (config) (= (length (config-tokens config)) 2)) configs))
    (check-not-false after-second-acquire)
    (when after-second-acquire
      (define tokens (config-tokens after-second-acquire))
      (check-equal? (second (first tokens)) 'Dropped)
      (check-equal? (length (fin-events after-second-acquire)) 1))))

(test-case "block 内の return は資源を一度 drop する"
  (define result
    (compile
     (string-append
      "fn f() -> Int ! {Own, Partial} {\n"
      " { let x = acquire(3)\n return 7 }\n"
      " 0 }\n"
      "f()")))
  (check-true (compiled? result)
              (if (diagnostic? result) (diagnostic-id result)
                  "compiled result expected"))
  (when (compiled? result)
    (define configs (trace-configs result))
    (check-dropped-once configs 1)
    (match (last configs)
      [`(cfg 7 ,_ ,_ ,_ ,_) (void)]
      [other (fail-check (format "return terminal expected: ~s" other))])))

(test-case "for 本体からの leave で iterable を漏らさず二重 drop しない"
  (define result
    (compile
     (string-append
      "fn mk() -> List<Owned<Res>> ! Own {\n"
      " return cons(acquire(1), cons(acquire(2), nil())) }\n"
      "fn f() -> Option<Int> ! {Own, Partial} {\n"
      " return for x in mk() { leave 7 }\n}\n"
      "f()")))
  (check-true (compiled? result)
              (if (diagnostic? result) (diagnostic-id result)
                  "compiled result expected"))
  (when (compiled? result)
    (check-dropped-once (trace-configs result) 3)))

(test-case "Owned 仮引数の Scope の内側に関数 block の Scope がある"
  (define result
    (compile
     (string-append
      "fn f(x: Owned<Res>) -> Unit ! Own { { () }\n () }\n"
      "f(acquire(9))")))
  (check-true (compiled? result)
              (if (diagnostic? result) (diagnostic-id result)
                  "compiled result expected"))
  (when (compiled? result)
    (define body
      (match (compiled-execution-core result)
        [`(Recur ,_ ,_ ,_ ,body ,_) body]
        [_ #f]))
    (check-true
     (match body
       [`(Scope () (Let (,_ let (Owned Res)) ,_ (Scope () (Let ,_ ,_ ,_)))) #t]
       [_ #f]))
    (check-dropped-once (trace-configs result) 1)))

(test-case "if の枝内の Construct に期待型を渡す"
  (define source
    (string-append
     "fn f(b: Bool) -> Option<Int> {\n"
     " let value: Option<Int> = if b { some(1) } else { none }\n"
     " return value }\n"
     "f(true)"))
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result) (diagnostic-id result)
                  "compiled result expected"))
  (when (compiled? result)
    (check-equal? (compiled-type result) '(Option Int))))

(test-case "Eliminate 各枝の期待型不足の拒否を保つ"
  (define when-form
    (string-append
     "when v {\n"
     " some n => { some(1) }\n"
     " none => { some(2) }\n"
     " }"))
  (define source
    (string-append
     "fn f(v: Option<Int>) -> Option<Int> {\n"
     " let answer = " when-form "\n"
     " return answer }\n"
     "f(some(0))"))
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected E-TYP-004, got ~s" result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-004")
    (check-equal? (diagnostic-primary-span result)
                  (span-of-fragment source when-form))))

(test-case "全 Never の NarrativeExpr の Eliminate 拒否を保つ"
  (define raw
    '(Fn () Int ()
         (Let ignored
              (Eliminate (Construct true (Types))
                ((true () -> (LexicalScope (NarrativeExpr (Return 1))))
                 (false () -> (LexicalScope (NarrativeExpr (Return 2))))))
              (Return 0))))
  (define annotated (annotate-surface raw))
  (define eliminate (find-form annotated 'Eliminate))
  (define result (elab annotated))
  (check-true (match result [`(err ,_) #t] [_ #f])
              (format "expected E-TYP-010, got ~s" result))
  (when (match result [`(err ,_) #t] [_ #f])
    (define diagnostic (second result))
    (check-equal? (diagnostic-id diagnostic) "E-TYP-010")
    (check-equal? (diagnostic-primary-span diagnostic)
                  (span-of eliminate))))

(test-case "block scope 下の Eliminate を NarrativeExpr の試行で検出する"
  (define raw
    '(Fn () Int ()
         (Let ignored
              (NarrativeExpr
               (LexicalScope
                (Eliminate (Construct true (Types))
                  ((true () -> (Return 1))
                   (false () -> (Return 2))))))
              (Return 0))))
  (define annotated (annotate-surface raw))
  (define narrative (find-form annotated 'NarrativeExpr))
  (define result (elab annotated))
  (check-true (match result [`(err ,_) #t] [_ #f])
              (format "expected E-TYP-010, got ~s" result))
  (when (match result [`(err ,_) #t] [_ #f])
    (define diagnostic (second result))
    (check-equal? (diagnostic-id diagnostic) "E-TYP-010")
    (check-equal? (diagnostic-primary-span diagnostic)
                  (span-of narrative))))

(test-case "入れ子 when の fallthrough 診断を保つ"
  (define source
    (string-append
     "fn flag() -> Bool { return true }\n"
     "fn f() -> Int {\n"
     " return when flag() {\n"
     " true => { when flag() {\n"
     "  true => { let x = 1\n x }\n"
     "  false => { let y = 2\n y }\n"
     " } }\n"
     " false => { leave 3 }\n"
     " }\n"
     "}\n"
     "f()"))
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected E-RET-005, got ~s" result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-RET-005")
    (check-equal? (diagnostic-primary-span result)
                  (close-span-of-fragment source "true => { let x = 1\n x }"))))

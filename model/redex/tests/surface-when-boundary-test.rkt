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

(define (source-span source needle)
  (match (regexp-match-positions (regexp (regexp-quote needle)) source)
    [(list (cons start end)) `(#:span src ,start ,end)]
    [_ (error 'source-span "substring not found: ~a" needle)]))

(define (block-close-span source needle)
  (match-define `(#:span src ,_ ,end) (source-span source needle))
  `(#:span src ,(sub1 end) ,end))

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
              "      return 2\n"
              "    }\n"
              "    false => 0\n"
              "  }\n"
              "  return outer\n"
              "}\n"
              "f()")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 2)))

(test-case "式位置 when の本体ブロック arm は return の値を返す"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define source
      (string-append
       (if variable? "" "fn g() -> Bool { return true }\n")
       "fn choose(" (if variable? "a: Bool" "") ") -> Int {\n"
       "  return when " scrutinee " {\n"
       "    true => { return 1 }\n"
       "    false => { return 2 }\n"
       "  }\n}\n"
       (if variable? "choose(true)" "choose()")))
    (define result (compile source))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result)
                            (diagnostic-message result))
                    (format "unexpected result: ~s" result)))
    (when (compiled? result) (check-equal? (run-value result) 1))))

(test-case "when の本体ブロック arm の落ち抜けは閉じ波括弧を指す"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define source
      (string-append
       (if variable? "" "fn g() -> Bool { return true }\n")
       "fn choose(" (if variable? "a: Bool" "") ") -> Int {\n"
       "  return when " scrutinee " {\n"
       "    true => { 1 }\n"
       "    false => { return 2 }\n"
       "  }\n}\n"
       (if variable? "choose(true)" "choose()")))
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-RET-005")
      (check-equal? (diagnostic-primary-span result)
                    (block-close-span source "true => { 1 }")))))

(test-case "when の本体ブロックの部分 return は合成位置と検査位置で拒否する"
  (for* ([scrutinee (in-list '("a" "g()"))]
         [annotation (in-list '(#f #t))])
    (define variable? (equal? scrutinee "a"))
    (define source
      (string-append
       (if variable? "" "fn g() -> Bool { return false }\n")
       "fn choose(" (if variable? "a: Bool, " "") "b: Bool) -> Int {\n"
       (if annotation "  let result: Int = when " "  let result = when ")
       scrutinee " {\n"
       "    true => { if b { return 1 } }\n"
       "    false => { return 2 }\n"
       "  }\n  return result\n}\n"
       (if variable? "choose(true, false)" "choose(false)")))
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-RET-005")
      (check-equal? (diagnostic-primary-span result)
                    (block-close-span source "true => { if b { return 1 } }")))))

(test-case "Unit の when は落ち抜ける本体ブロック arm を受理する"
  (for* ([scrutinee (in-list '("a" "g()"))]
         [annotation (in-list '(#f #t))])
    (define variable? (equal? scrutinee "a"))
    (define source
      (string-append
       (if variable? "" "fn g() -> Bool { return false }\n")
       "fn choose(" (if variable? "a: Bool" "") ") -> Unit {\n"
       (if annotation "  let result: Unit = when " "  let result = when ")
       scrutinee " {\n"
       "    true => { 1 }\n"
       "    false => { 2 }\n"
       "  }\n"
       "  return result\n}\n"
       (if variable? "choose(true)" "choose()")))
    (define result (compile source))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result)
                            (diagnostic-message result))
                    (format "unexpected result: ~s" result)))))

(test-case "値 arm と本体ブロック arm の return 候補を合流する"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define source
      (string-append
       (if variable? "" "fn g() -> Bool { return false }\n")
       "fn choose(" (if variable? "a: Bool" "") ") -> Int | String {\n"
       "  let result = when " scrutinee " {\n"
       "    true => 1\n"
       "    false => { return \"s\" }\n"
       "  }\n  return result\n}\n"
       (if variable? "choose(true)" "choose()")))
    (define result (compile source))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result)
                            (diagnostic-message result))
                    (format "unexpected result: ~s" result)))
    (when (compiled? result)
      (check-equal? (compiled-type result) '(Union Int String))
      (match (run-value result)
        [`(UnionVal ,_ Int 1) #:when variable? (void)]
        [`(UnionVal ,_ String "s") #:when (not variable?) (void)]
        [other (fail-check (format "unexpected Union value: ~s" other))]))))

(test-case "入れ子 when の落ち抜け記録は境界を越えない"
  (define nested-statement
    (compile
     (string-append
      "fn f(a: Bool, b: Bool) -> Int {\n"
      "  let result = when a {\n"
      "    true => {\n"
      "      when b {\n"
      "        true => { 1 }\n"
      "        false => { 2 }\n"
      "      }\n"
      "      return 7\n"
      "    }\n"
      "    false => { return 9 }\n"
      "  }\n  return result\n}\nf(true, false)")))
  (check-true (compiled? nested-statement)
              (if (diagnostic? nested-statement)
                  (format "~a: ~a" (diagnostic-id nested-statement)
                          (diagnostic-message nested-statement))
                  (format "unexpected result: ~s" nested-statement)))
  (when (compiled? nested-statement)
    (check-equal? (run-value nested-statement) 7))
  (define nested-expression
    (compile
     (string-append
      "fn f(a: Bool, b: Bool) -> Int {\n"
      "  when a {\n"
      "    true => {\n"
      "      let inner = when b {\n"
      "        true => { return 1 }\n"
      "        false => { return 2 }\n"
      "      }\n"
      "      ()\n"
      "    }\n"
      "    false => { return 3 }\n"
      "  }\n  return 0\n}\nf(true, false)")))
  (check-true (compiled? nested-expression)
              (if (diagnostic? nested-expression)
                  (format "~a: ~a" (diagnostic-id nested-expression)
                          (diagnostic-message nested-expression))
                  (format "unexpected result: ~s" nested-expression)))
  (when (compiled? nested-expression)
    (check-equal? (run-value nested-expression) 0)))

(test-case "=> {} と => { a: 1 } は when の record 値を返す"
  (for ([source-and-type
         (in-list
          (list
           (list "let result = when true { true => {}\n false => {} }\nresult"
                 '(Record ()))
           (list "let result = when true { true => { a: 1 }\n false => { a: 2 } }\nresult"
                 '(Record ((a Int imm))))))])
    (define result (compile (first source-and-type)))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result)
                            (diagnostic-message result))
                    (format "unexpected result: ~s" result)))
    (when (compiled? result)
      (check-equal? (compiled-type result) (second source-and-type)))))

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

(test-case "when の正常経路と境界へ届く return 候補を合流する"
  (for ([source (in-list
                 (list
                  (string-append
                   "fn identity(x: String) -> String { return x }\n"
                   "fn choose(a: Bool) -> Int | String {\n"
                   " let answer = when a { true => 1\n"
                   "  false => identity(return \"s\") }\n"
                   " return answer\n}\nchoose(false)")
                  (string-append
                   "fn identity(x: String) -> String { return x }\n"
                   "fn flag() -> Bool { return false }\n"
                   "fn choose() -> Int | String {\n"
                   " let answer = when flag() { true => 1\n"
                   "  false => identity(return \"s\") }\n"
                   " return answer\n}\nchoose()")))])
    (define result (compile source))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result)
                            (diagnostic-message result))
                    (format "unexpected result: ~s" result)))
    (when (compiled? result)
      (check-equal? (compiled-type result) '(Union Int String))
      (match (run-value result)
        [`(UnionVal ,_ String "s") (void)]
        [other (fail-check (format "String member の UnionVal を期待したが ~s"
                                   other))]))))

(test-case "when の全 return 候補を合流し、同型候補はその型を保つ"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define different
      (compile
       (string-append
        (if variable? "" "fn g() -> Bool { return false }\n")
        "fn identityInt(x: Int) -> Int { return x }\n"
        "fn identityString(x: String) -> String { return x }\n"
        "fn choose(" (if variable? "a: Bool" "") ") -> Int | String {\n"
        " let answer = when " scrutinee " {\n"
        "  true => identityInt(return 1)\n"
        "  false => identityString(return \"s\")\n"
        " }\n return answer\n}\n"
        (if variable? "choose(true)" "choose()"))))
    (check-true (compiled? different)
                (if (diagnostic? different)
                    (format "~a: ~a" (diagnostic-id different)
                            (diagnostic-message different))
                    (format "unexpected result: ~s" different)))
    (when (compiled? different)
      (check-equal? (compiled-type different) '(Union Int String))
      (let ([value (run-value different)])
        (if variable?
            (match value
              [`(UnionVal ,_ Int 1) (void)]
              [other (fail-check (format "scrutinee ~a の UnionVal が不正: ~s"
                                         scrutinee other))])
            (match value
              [`(UnionVal ,_ String "s") (void)]
              [other (fail-check (format "scrutinee ~a の UnionVal が不正: ~s"
                                         scrutinee other))])))))
  (define same
    (compile
     (string-append
      "fn identity(x: Int) -> Int { return x }\n"
      "fn choose(a: Bool) -> Int {\n"
      " let answer = when a { true => 1\n"
      "  false => identity(return 2) }\n"
      " return answer\n}\nchoose(false)")))
  (check-true (compiled? same)
              (if (diagnostic? same)
                  (format "~a: ~a" (diagnostic-id same)
                          (diagnostic-message same))
                  (format "unexpected result: ~s" same)))
  (when (compiled? same)
    (check-equal? (compiled-type same) 'Int)
    (check-equal? (run-value same) 2)))

(test-case "when の record return 候補は ROW-005 で合流する"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define result
      (compile
       (string-append
        (if variable? "" "fn g() -> Bool { return false }\n")
        "fn choose(" (if variable? "a: Bool" "") ") {\n"
        " let answer = when " scrutinee " {\n"
        "  true => return { a: 1 }\n"
        "  false => return { a: 2, b: 3 }\n"
        " }\n return answer\n}\n"
        (if variable? "choose(false)" "choose()"))))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result)
                            (diagnostic-message result))
                    (format "unexpected result: ~s" result)))
    (when (compiled? result)
      (check-equal?
       (compiled-type result)
       (row005-join
        (list '(Record ((a Int imm))) '(Record ((a Int imm) (b Int imm)))))))))

(test-case "when の Owned 候補が直接の Owned Union を作る場合は拒否する"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define source
      (string-append
       (if variable? "" "fn g() -> Bool { return false }\n")
       "fn choose(" (if variable? "a: Bool, " "")
       "left: fn() -> Owned<Int> ! Own, right: fn() -> Owned<String> ! Own) ! Own {\n"
       " let answer = when " scrutinee " { true => return left()\n"
       "  false => return right() }\n return answer\n}\n0"))
    (define needle
      (string-append "when " scrutinee " { true => return left()\n"
                     "  false => return right() }"))
    (define result (compile source))
    (check-true (diagnostic? result) (format "unexpected result: ~s" result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-TYP-012")
      (check-equal? (diagnostic-primary-span result)
                    (source-span source needle)))))

(test-case "期待 Union で検査する when return は注入され実行できる"
  (define result
    (compile
     (string-append
      "fn choose(a: Bool) -> Int | String {\n"
      " return when a { true => return 1\n"
      "  false => return \"s\" }\n}\nchoose(false)")))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (when (compiled? result)
    (check-true
     (contains-form? (compiled-core result) 'UnionInject))
    (match (run-value result)
      [`(UnionVal ,_ String "s") (void)]
      [other (fail-check (format "String member の UnionVal を期待したが ~s"
                                 other))])))

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

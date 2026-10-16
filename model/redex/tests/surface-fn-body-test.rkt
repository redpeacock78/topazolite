#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lexer.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../ucore.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))
(define (code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))

(define (find-form tree wanted)
  (cond [(and (pair? tree) (eq? (car tree) wanted)) tree]
        [(pair? tree) (for/or ([part (in-list tree)]) (find-form part wanted))]
        [else #f]))

(define (contains-form? tree wanted)
  (and (find-form tree wanted) #t))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value () () () ()) value]
       [other (fail-check (format "終端状態を期待したが ~s" other))]))))

(define (source-span source pattern)
  (match (regexp-match-positions pattern source)
    [(list (cons start end)) `(#:span src ,start ,end)]
    [_ (error 'source-span "一致する式が無い: ~a" pattern)]))

(define (lower source)
  (lower-surface (parse (lex/string 'src source)) (current-trait-env)))

(test-case "1. 全枝の明示 return は関数境界へ届く"
  (for ([source+expected
         (in-list
          '(("fn f(b: Bool) -> Int { when b { true => return 11\n false => return 12 } }\nf(true)"
             . 11)
            ("fn f(b: Bool) -> Int { if b { return 21 } else { return 22 } }\nf(false)"
             . 22)))])
    (define result (compile (car source+expected)))
    (check-true (compiled? result))
    (when (compiled? result)
      (check-equal? (run-value result) (cdr source+expected)))))

(test-case "2. 非 Unit 関数の落ち抜けは閉じ波括弧を指す"
  (define source "fn f() -> Int { 1 }\nf()")
  (define result (compile source))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-RET-004")
    (check-equal? (diagnostic-primary-span result) (source-span source #px"\\}"))
    (check-equal? (diagnostic-related result)
                  (list (list 'return-type-annotation
                              (source-span source #px"Int")
                              "戻り型の注釈")))))

(test-case "3. else の無い if の fallthrough は返却保証にならない"
  (check-equal? (code "fn f(b: Bool) -> Int { if b { return 1 } }\nf(false)")
                "E-RET-004"))

(test-case "4. return 後の到達不能な式文も型検査し、返却値を保つ"
  (define result (compile "fn f() -> Int { return 1\n 0 }\nf()"))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 1)))

(test-case "5. 実引数の return で本体が正常完了しないことを受理する"
  (define result
    (compile "fn log(x: Int) -> Unit { () }\nfn f() -> Int { log(return 1) }\nf()"))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 1)))

(test-case "検査の record の余分な bottom 欄からの return を受理する"
  (define result
    (compile (string-append
              "fn g(r: { a: Int }) -> Int { return r.a }\n"
              "fn f() -> Int { return g({ a: 1, b: return 2 }) }\n"
              "f()")))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (run-value result) 2)))

(test-case "6. Unit 関数は落ち抜け、return、文位置 if を受理する"
  (for ([source (in-list
                 '("fn f() -> Unit { 1 }\nf()"
                   "fn f(b: Bool) -> Unit { if b { return () } else { () } }\nf(true)"
                   "fn f(b: Bool) -> Unit { if b { () } }\nf(false)"))])
    (define result (compile source))
    (check-true (compiled? result) source)
    (when (compiled? result) (check-equal? (run-value result) 'unit))))

(test-case "7. 省略した戻り型は fallthrough と return 候補から決まる"
  (for ([source+type (in-list
                      '(("fn f() { 1 }\nf()" Unit)
                        ("fn f() { return 7 }\nf()" Int)
                        ("{ let f = fn() { 1 }\n f() }" Unit)
                        ("{ let f = fn() { return 7 }\n f() }" Int)))])
    (define result (compile (first source+type)))
    (check-true (compiled? result) (first source+type))
    (when (compiled? result)
      (check-equal? (compiled-type result) (second source+type))))
  (for ([source (in-list
                 '("fn f(b: Bool) { if b { return 1 } else { () } }\nf(false)"
                   "{ let f = fn(b: Bool) { if b { return 1 } else { () } }\n f(false) }"))])
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-RET-004")
      (check-equal? (diagnostic-related result) '()))))

(test-case "8. 省略戻り型の候補は Union に合流し、後続を検査する"
  (define result
    (compile "fn f(b: Bool) { if b { return 1 } else { return \"x\" } }\nf(true)"))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (when (compiled? result)
    (check-equal? (compiled-type result) '(Union Int String))
    (match (run-value result)
      [`(UnionVal ,_ Int 1) (void)]
      [other (fail-check (format "Int member の UnionVal を期待したが ~s"
                                 other))])))

(test-case "9. when の局所境界で捕まる return は関数候補にならない"
  (define result
    (compile
     "fn f(b: Bool) { let ignored = when b { true => return 1\n false => return 2 }\n 0 }\nf(true)"))
  (check-true (compiled? result))
  (when (compiled? result) (check-equal? (compiled-type result) 'Unit)))

(test-case "10. arrow の block 本体だけを関数本体として扱う"
  (for ([source (in-list
                 '("fn apply(f: fn(Int) -> Int) -> Int { return f(3) }\napply(x => { return x })"
                   "fn apply(f: fn(Int) -> Int) -> Int { return f(3) }\napply(fn(x: Int) => { return x })"))])
    (define result (compile source))
    (check-true (compiled? result) source)
    (when (compiled? result) (check-equal? (run-value result) 3)))
  (check-equal?
   (code "fn apply(f: fn(Int) -> Int) -> Int { return f(3) }\napply(x => { x })")
   "E-RET-004")
  (for ([source (in-list '("x => {}" "x => { a: 1 }"))])
    (define parsed (parse (lex/string 'src source)))
    (match parsed
      [`(SProgram ,_ () (SFn ,_ ,_ #:none #:none ,expr ,body))
       (check-eq? expr 'expr)
       (check-false (contains-form? (lowered-term (lower source)) 'BlockBody))]
      [other (fail-check (format "arrow の expr 本体を期待したが ~s" other))])))

(test-case "11. 推論付き再帰 FnDecl は既存の自己参照診断を保つ"
  (define result
    (compile "fn f(x: Int) { f(x) }\nf(1)"))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-024")))

(test-case "12. Surface に無い候補無し Never の block body は E-TYP-024 になる"
  (define inferred
    '(Fn ((stop (NFn () Never () ()))) #:infer ()
         (BlockBody (Apply stop))))
  (define annotated
    '(Fn ((stop (NFn () Never () ()))) Int ()
         (BlockBody (Apply stop))))
  (match (elab inferred)
    [`(err ,diagnostic) (check-equal? (diagnostic-id diagnostic) "E-TYP-024")]
    [other (fail-check (format "候補無し Never の推論 Fn は拒否される: ~s" other))])
  (check-not-false (match (elab annotated) [(list _ _ _ _) #t] [_ #f])))

(test-case "13. when arm と関数本体以外の BlockBody は不変条件違反になる"
  (for ([term (in-list
               (list '(Let x (BlockBody 1) x)
                     '(NarrativeExpr
                       (BlockBody (#:span src 3 4)
                                  (Return (#:lit 1 (#:span src 3 4)))))))])
    (match (elab term)
      [`(err ,diagnostic)
       (check-equal? (diagnostic-id diagnostic) "E-SYN-003")]
      [other
       (fail-check (format "許可位置以外の BlockBody を拒否する: ~s" other))])))

(test-case "14. parser は arrow body の block と record を区別する"
  (for ([source-kind (in-list
                      '(("fn(x: Int) => { return x }" block)
                        ("x => { return x }" block)
                        ("x => x" expr)
                        ("x => {}" expr)))])
    (match (parse (lex/string 'src (first source-kind)))
      [`(SProgram ,_ () (SFn ,_ ,_ #:none #:none ,kind ,_))
       (check-eq? kind (second source-kind))]
      [other (fail-check (format "SFn body-kind を得られない: ~s" other))])))

(test-case "15. 下見で候補を得た後の到達不能 none は E-TYP-003 を保つ"
  (check-equal? (code "fn f() { return 1\n none }\nf()") "E-TYP-003")
  (check-equal? (code "fn f() { none }\nf()") "E-TYP-003"))

(test-case "16. block lambda の Owned capture は expr lambda と同じ制約を使う"
  (for ([body (in-list '((BlockBody (Drop o)) (Drop o)))])
    (define result
      (elab `(Fn ((o (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
                 (Fn () Unit (Own) ,body))))
    (check-true (match result [(list _ _ _ _) #t] [_ #f])))
  (for ([body (in-list '((BlockBody (Drop o)) (Drop o)))])
    (define result (elab `(Fn ((o (Owned Res))) (NFn () Unit () ()) ()
                             (Fn () Unit () ,body))))
    (check-true (match result [`(err ,_d) #t]
                  [_ #f]))))
  (check-equal?
   (diagnostic-id (second (elab '(Fn ((o (Owned Res))) (NFn () Unit () ()) ()
                                    (Fn () Unit () (Drop o))))))
   (diagnostic-id (second (elab '(Fn ((o (Owned Res))) (NFn () Unit () ()) ()
                                    (Fn () Unit () (BlockBody (Drop o))))))))

(test-case "17. BlockBody の annotate と erase は spanful と spanless を往復する"
  (define term
    '(Fn ((x Int)) Int () (BlockBody (#:span src 2 5) (Return 3))))
  (define lifted (annotate-surface (erase-surface term)))
  (check-equal? (erase-surface lifted) (erase-surface term))
  (check-true (redex-match? UCore+ e lifted)))

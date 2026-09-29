#lang racket

;; [REQ: SUR-003] Surface の Effect row を UCore と Typed Core へ通す回帰。

(require rackunit
         redex/reduction-semantics
         racket/match
         "../classify.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../lexer.rkt"
         "../origins.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../ucore.rkt")

(define (lowered-source source)
  (lower-surface (parse (lex/string 'src source)) (current-trait-env)))

(define (low source)
  (define result (lowered-source source))
  (if (lowered? result) (lowered-term result) result))

(define (compile source) (compile-source/string 'src source))

(define (binding-type source)
  (match (low source)
    [`(Let ,_ ((#:bind ,_ ,_) let (#:ty ,type ,_)) ,_ ,_) type]
    [other (fail-check (format "注釈付き Let の lowering を期待したが ~s" other))]))

(define (fn-effect-row term)
  (match term
    [`(Fn ,_ ,_ ,_ (#:ef ,labels ,span) ,_) (list labels span)]
    [other (fail-check (format "Fn と効果 row を期待したが ~s" other))]))

(define (decl-effect-row source)
  (match (low source)
    [`(Recur ,_ ,_ ,_ ,_ (#:ef ,labels ,span) ,_ ,_) (list labels span)]
    [other (fail-check (format "Recur と効果 row を期待したが ~s" other))]))

(define (source-span source needle)
  (define positions (regexp-match-positions (regexp-quote needle) source))
  (match positions
    [(list (cons lo hi)) `(#:span src ,lo ,hi)]
    [_ (error 'source-span "substring not found: ~a" needle)]))

(define (code result)
  (and (diagnostic? result) (diagnostic-id result)))

(define partial-int-fn '(NFn (Int) Int () (Partial) () User))
(define pure-int-fn '(NFn (Int) Int () () () User))

(define (check-signature-count result signature expected-count)
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal?
     (count (λ (entry) (equal? (second entry) signature))
            (compiled-callables result))
     expected-count)))

(test-case "SUR-003: row の省略形、括弧形、空形、重複と span"
  (define single (low "fn() ! Partial => 0"))
  (define braced (low "fn() ! {Partial} => 0"))
  (check-equal? (first (fn-effect-row single)) '(Partial))
  (check-equal? (first (fn-effect-row braced)) '(Partial))
  (check-equal? (first (fn-effect-row (low "fn() ! {} => 0"))) '())
  (check-equal? (first (fn-effect-row (low "fn() ! {Partial, Partial} => 0")))
                '(Partial Partial))
  (check-equal? (second (fn-effect-row single))
                (source-span "fn() ! Partial => 0" "! Partial"))
  (check-equal? (second (fn-effect-row braced))
                (source-span "fn() ! {Partial} => 0" "! {Partial}"))
  (check-equal? (first (fn-effect-row (low "fn() ! Yield<Int> { 0 }")))
                '((Yield Int)))
  (check-equal? (decl-effect-row "fn f() ! Partial { 0 }\n0")
                (list '(Partial) (source-span "fn f() ! Partial { 0 }\n0" "! Partial")))
  (check-equal? (decl-effect-row "fn f() { 0 }\n0")
                (list '() '(#:span src 0 12))))

(test-case "SUR-003: 関数型の row は最も内側の fn 型を閉じる"
  (check-equal?
   (binding-type "{ let f: fn(Int) -> Int | Bool ! Partial = 0\n f }")
   '(NFn (Int) (Union Int Bool) (Partial) ()))
  (check-equal?
   (binding-type "{ let f: fn(Int) -> Int ! Partial | Bool = 0\n f }")
   '(Union (NFn (Int) Int (Partial) ()) Bool))
  (check-equal?
   (binding-type "{ let f: fn(Int) -> fn(Int) -> Int ! Partial = 0\n f }")
   '(NFn (Int) (NFn (Int) Int (Partial) ()) () ())))

(test-case "SUR-003: 不正な label は左端の label span で E-SUR-024 になる"
  (define cases
    (list (cons "fn() ! State { 0 }" "State")
          (cons "fn() ! Yield { 0 }" "Yield")
          (cons "fn() ! Partial<Int> { 0 }" "Partial<Int>")
          (cons "{ let f: fn() -> Int ! Return = 0\n f }" "Return")))
  (for ([case (in-list cases)])
    (define source (car case))
    (define label (cdr case))
    (define result (low source))
    (check-equal? (code result) "E-SUR-024" source)
    (check-equal? (diagnostic-primary-span result) (source-span source label) source))
  (define multiple "fn() ! {State, Partial<Int>} { 0 }")
  (define first-error (low multiple))
  (check-equal? (code first-error) "E-SUR-024")
  (check-equal? (diagnostic-primary-span first-error) (source-span multiple "State"))
  (define unknown-type (low "fn() ! Yield<Unknown> { 0 }"))
  (check-equal? (diagnostic-id unknown-type)
                (diagnostic-code-of 'surface 'surface-unknown-type-name)))

(test-case "SUR-003: impl target の関数型 row も Surface lowering で検査する"
  (define source
    (string-append
     "trait Show { show: fn(Self) -> Int }\n"
     "impl Show for fn(Int) -> Int ! IO { show: fn(f) => 0 }\n0"))
  (define result (low source))
  (check-equal? (code result) "E-SUR-024")
  (check-equal? (diagnostic-primary-span result) (source-span source "IO")))

(test-case "SUR-003: 明示 Partial row の再帰は受理され、全体分類は Unknown になる"
  (define result (compile "fn loop(n: Int) -> Int ! Partial { loop(n) }\n0"))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal?
     (classify (erase-core (compiled-core result)) '() (compiled-callables result))
     'Unknown))
  (check-equal? (code (compile "fn loop(n: Int) -> Int { loop(n) }\n0"))
                "E-REC-002"))

(test-case "SUR-003: Return row は nearest boundary と SUR-008 に従う"
  (check-equal? (code (compile "fn f() -> Int ! Return { 0 }\n0")) "E-RET-001")
  (check-true
   (compiled?
    (compile "fn() -> Int { let g = fn() ! Return => 0\n 0 }")))
  (check-equal?
   (code (compile "fn() { let g = fn() ! Return => 0\n 0 }"))
   "E-TYP-024"))

(test-case "SUR-003: 明示 row は期待型に対して省略扱いにならない"
  (check-equal?
   (code (compile "fn ap(f: fn() -> Int) -> Int { f() }\nap(fn() ! Partial => 0)"))
   "E-TYP-012")
  (check-true
   (compiled?
    (compile "fn ap(f: fn() -> Int ! Partial) -> Int ! Partial { f() }\nap(fn() ! {} => 0)"))))

(test-case "SUR-003: 省略 row は検査位置で期待型から継承する"
  (define loop-decl "fn loop(n: Int) -> Int ! Partial { loop(n) }\n")
  (define let-arrow
    (compile (string-append loop-decl
                            "let f: fn(Int) -> Int ! Partial = x => loop(x)\nf(1)")))
  (check-signature-count let-arrow partial-int-fn 2)
  (define argument-arrow
    (compile (string-append loop-decl
                            "fn ap(g: fn(Int) -> Int ! Partial) -> Int ! Partial { g(1) }\n"
                            "ap(x => loop(x))")))
  (check-signature-count argument-arrow partial-int-fn 2)
  (define let-block
    (compile (string-append loop-decl
                            "let f: fn(Int) -> Int ! Partial = "
                            "fn(x: Int) -> Int { loop(x) }\nf(1)")))
  (check-signature-count let-block partial-int-fn 2)
  (define argument-block
    (compile (string-append loop-decl
                            "fn ap(g: fn(Int) -> Int ! Partial) -> Int ! Partial { g(1) }\n"
                            "ap(fn(x: Int) -> Int { loop(x) })")))
  (check-signature-count argument-block partial-int-fn 2))

(test-case "SUR-003: 合成位置の省略 row は空であり、非 NFn 期待型から継承しない"
  (define loop-decl "fn loop(n: Int) -> Int ! Partial { loop(n) }\n")
  (check-equal?
   (code (compile (string-append loop-decl
                                "let g = fn(x: Int) -> Int { loop(x) }\n0")))
   "E-EFF-002")
  (define union-expected
    (compile "{ let f: (fn(Int) -> Int ! Partial) | Bool = fn(x: Int) -> Int { x }\n0 }"))
  (check-signature-count union-expected pure-int-fn 1))

(test-case "SUR-003: 省略 row は関数 span を持ち、UCore+ と erase を往復する"
  (define lowered (low "fn(x: Int) => x"))
  (check-true (redex-match? UCore+ e lowered))
  (match lowered
    [`(Fn ,span ,_ ,_ (#:ef #:infer ,row-span) ,_)
     (check-equal? row-span span)]
    [other (fail-check (format "省略 row の印を期待したが ~s" other))])
  (define erased (erase-surface lowered))
  (check-true (redex-match? UCore e erased))
  (check-equal? erased '(Fn ((x Int)) #:infer #:infer x)))

(test-case "SUR-003: 検査位置の省略戻り型で Return row は囲む境界へ解決する"
  (check-true
   (compiled?
    (compile "let f: fn() -> Int = fn() {\n  let g = fn() ! Return => 0\n  1\n}\nf()"))))

(test-case "UCore の有効な declaration row は P2j でも elaborate できる"
  (define result (elab '(Fn () Unit ((Yield Int)) (Yield 1 unit))))
  (match result
    [`(err ,d) (fail-check (format "UCore row の elaboration に失敗した: ~s" d))]
    [(list _ type _ _)
     (check-equal? type '(NFn () Unit () ((Yield Int)) () User))]))

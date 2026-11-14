#lang racket

;; SUR-004b2a。名前付き region の解決と ForallRegion への lowering。

(require rackunit
         racket/list
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         (only-in "../origins.rkt" current-trait-env))

(define (compile source) (compile-source/string 'src source))

(define (source-span source needle [occurrence 0])
  (match (list-ref (regexp-match-positions*
                    (regexp (regexp-quote needle)) source)
                   occurrence)
    [(cons start end) `(#:span src ,start ,end)]))

(define (compile-accepted source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compiled source expected, got ~a at ~s"
                          (diagnostic-id result)
                          (diagnostic-primary-span result))
                  (format "unexpected result: ~s" result)))
  (when (compiled? result)
    (check-true (no-surface-region-name? result)
                "elaborate 後の Core に RName が残らない"))
  result)

(define (compile-rejected source expected-id [needle #f] [occurrence 0])
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)
    (when needle
      (check-equal? (diagnostic-primary-span result)
                    (source-span source needle occurrence))))
  result)

(define (contains-form? tree wanted)
  (or (and (pair? tree) (eq? (car tree) wanted))
      (and (pair? tree)
           (ormap (lambda (part) (contains-form? part wanted)) tree))))

(define (only-callable-type result)
  (match (compiled-callables result)
    [(list (list _ type)) type]
    [other (fail-check (format "callable が 1 件の形を期待した: ~s" other))]))

(define (no-surface-region-name? result)
  (and (not (contains-form? (compiled-core result) 'RName))
       (not (contains-form? (compiled-callables result) 'RName))))

(define nested-decl-span '(#:span src 0 1))

(define (nested-region-decl name)
  `(SFnDecl ,nested-decl-span
            (SName ,nested-decl-span inner)
            ((SName ,nested-decl-span ,name))
            ((SParam ,nested-decl-span
                     (SName ,nested-decl-span q)
                     (TBorrow ,nested-decl-span
                              (SName ,nested-decl-span ,name)
                              (TName ,nested-decl-span Int))))
            (TBorrow ,nested-decl-span
                     (SName ,nested-decl-span ,name)
                     (TName ,nested-decl-span Int))
            #:none
            (SBlock ,nested-decl-span ()
                    (SReturn ,nested-decl-span (SVar ,nested-decl-span q)))))

(define (lower-with-nested-decl source nested-decl)
  ;; The parser rejects block-local SFnDecl, so exercise this lowerer case directly.
  (define parsed (parse (lex/string 'src source)))
  (match parsed
    [`(SProgram ,program-span
        ((SFnDecl ,fn-span ,fn-name ,region-params ,parameters ,result ,row
                  (SBlock ,block-span ,bindings ,tail)))
        ,program-tail)
     (lower-surface
      `(SProgram ,program-span
         ((SFnDecl ,fn-span ,fn-name ,region-params ,parameters ,result ,row
                   (SBlock ,block-span ,(cons nested-decl bindings) ,tail)))
         ,program-tail)
      (current-trait-env))]
    [other (fail-check (format "注入対象の Surface FnDecl を期待した: ~s" other))]))

(test-case "choose の仮引数と戻りは一つの名前付き binder を共有する"
  (define result
    (compile-accepted
     "fn choose<r>(left: &r Int, right: &r Int, condition: Bool) -> &r Int { return left }\n0"))
  (match (only-callable-type result)
    [`(ForallRegion (,rp)
        (NFn ((Borrowed Int (RParam ,rp-left))
              (Borrowed Int (RParam ,rp-right))
              Bool)
             (Borrowed Int (RParam ,rp-result)) . ,_))
     (check-equal? (list rp-left rp-right rp-result) (list rp rp rp))]
    [other (fail-check (format "named ForallRegion を期待した: ~s" other))]))

(test-case "名前付きと省略の入力位置は別 binder で、戻りは名前付き位置を選ぶ"
  (define result
    (compile-accepted
     "fn f<r>(a: &r Int, b: &Int) -> &r Int { return a }\n0"))
  (match (only-callable-type result)
    [`(ForallRegion (,named ,elided)
        (NFn ((Borrowed Int (RParam ,named-arg))
              (Borrowed Int (RParam ,elided-arg)))
             (Borrowed Int (RParam ,named-result)) . ,_))
     (check-equal? (list named-arg elided-arg named-result)
                   (list named elided named))]
    [other (fail-check (format "混在した ForallRegion を期待した: ~s" other))]))

(test-case "内部名と同じ名前の利用者 binder も elision と衝突しない"
  (for ([name (in-list '(elided omitted))])
    (define source
      (format "fn f<~a>(a: &~a Int, b: &Int) -> &~a Int { return a }\n0"
              name name name))
    (define result (compile-accepted source))
    (check-equal? (length (match (only-callable-type result)
                            [`(ForallRegion (,binders ...) ,_) binders]
                            [_ '()]))
                  2)))

(test-case "let 注釈は囲む関数の named region を使う"
  (void
   (compile-accepted
    "fn f<r>(p: &r Int) -> &r Int { let q: &r Int = p\nreturn q }\n0")))

(test-case "入れ子の binder は外側を隠し、未宣言の内側 binder は外側を参照する"
  (void
   (compile-accepted
    "fn outer<r>(p: &r Int) -> Int ! {Own, Partial} { let g = fn<r>(q: &r Int) -> &r Int { return q }\nreturn 0 }\n0")
   (compile-accepted
    "fn outer<r>(p: &r Int) -> Int ! {Own, Partial} { let g = fn(q: &r Int) -> &r Int { return q }\nreturn 0 }\n0")))

(test-case "省略戻りは名前付きの入力位置一つへ結び付く"
  (void (compile-accepted "fn f<r>(p: &r Int) -> &Int { return p }\n0")))

(test-case "未宣言の region 名はその名前で E-SUR-008"
  (define source "fn f(p: &r Int) -> Int { return 0 }\n0")
  (void (compile-rejected source "E-SUR-008" "r")))

(test-case "関数の重複 binder は E-SUR-030 で二つ目を指す"
  (define source "fn f<r, r>(p: &r Int) -> Int { return 0 }\n0")
  (define diagnostic (compile-rejected source "E-SUR-030" "r" 1))
  (check-equal? (map second (diagnostic-related diagnostic))
                (list (source-span source "r" 0))))

(test-case "型位置でも使った binder は region 位置で E-SUR-008"
  (for ([source/index (in-list
                       (list (cons "fn f<r>(x: r, y: &r Int) -> Int { return 0 }\n0" 2)
                             (cons "fn f<r>(y: &r Int, x: r) -> Int { return 0 }\n0" 1)))])
    (compile-rejected (car source/index) "E-SUR-008" "r" (cdr source/index))))

(test-case "型 binder と未使用 binder は現行どおり E-SUR-005"
  (void
   (compile-rejected "fn f<T>(x: T) -> Int { return 0 }\n0" "E-SUR-005" "T")
   (compile-rejected "fn f<r>() -> Int { return 0 }\n0" "E-SUR-005" "r")))

(test-case "入力に無い named return region は E-BOR-020"
  (define diagnostic
    (compile-rejected "fn f<r>(p: &Int) -> &r Int { return p }\n0"
                      "E-BOR-020" "&r Int"))
  (check-equal? (diagnostic-found diagnostic)
                "戻りの借用に対応する入力の借用位置が無い"))

(test-case "省略戻りは named と omitted を含む複数入力位置で拒否する"
  (define diagnostic
    (compile-rejected
     "fn f<r>(a: &r Int, b: &Int) -> &Int { return a }\n0"
     "E-BOR-020" "&Int" 1))
  (check-equal? (diagnostic-found diagnostic)
                "入力の借用位置が複数あるため戻りの region を省略できない。明示の region を指定する"))

(test-case "入力に無い binder の let 注釈は E-BOR-020 で拒否する"
  (define diagnostic
    (compile-rejected
     "fn f<r>(p: &Int) -> Int { let q: &r Int = p\nreturn 0 }\n0"
     "E-BOR-020" "&r Int"))
  (check-equal? (diagnostic-found diagnostic)
                "region の束縛子に対応する入力の借用位置が無い"))

(test-case "E-SUR-008 と E-SUR-030 の title を拡張する"
  (define unknown
    (compile-rejected "fn f(p: &r Int) -> Int { return 0 }\n0" "E-SUR-008"))
  (define duplicate
    (compile-rejected "fn f<r, r>(p: &r Int) -> Int { return 0 }\n0"
                      "E-SUR-030"))
  (check-equal? (diagnostic-title unknown)
                "宣言の無い型または region の名前を参照した")
  (check-equal? (diagnostic-title duplicate)
                "data 型または関数の宣言で同じ束縛子を 2 度書いた"))

(test-case "入れ子の SFnDecl は独自の region binder を解決する"
  (define lowered
    (lower-with-nested-decl
     "fn outer(x: Int) -> Int { return 0 }\n0"
     (nested-region-decl 's)))
  (check-true (lowered? lowered)
              (format "nested SFnDecl lowers: ~s" lowered))
  (when (lowered? lowered)
    (check-true (contains-form? (lowered-term lowered) 'FnDecl))))

(test-case "入れ子の SFnDecl の同名 binder は外側の未使用判定を隠す"
  (define source "fn f<r>() -> Int { return 0 }\n0")
  (define lowered (lower-with-nested-decl source (nested-region-decl 'r)))
  (check-true (diagnostic? lowered))
  (when (diagnostic? lowered)
    (check-equal? (diagnostic-id lowered) "E-SUR-005")
    (check-equal? (diagnostic-primary-span lowered)
                  (source-span source "r"))))

(test-case "閉じた ForallRegion を E-BOR-020 と誤認せず callable 縮約で拒否する"
  (for ([source
         (in-list
          (list "fn mk() ! {Own, Partial} { return fn(p: &Int) -> Int { return 0 } }\n0"
                "let mk = fn() ! {Own, Partial} => fn(p: &Int) => 0\n0"))])
    (define diagnostic (compile-rejected source "E-TYP-018"))
    (check-equal? (diagnostic-title diagnostic) "callable 表の形が不正である")))

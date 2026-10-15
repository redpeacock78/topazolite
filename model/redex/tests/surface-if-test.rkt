#lang racket

(require rackunit
         racket/match
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))

(define (compile-code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
       [other (fail-check (format "terminal config expected, got ~s" other))]))))

(define (run-source source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (and (compiled? result) (run-value result)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 10000])
    (when (zero? fuel) (error 'trace-g2 "fuel exhausted at ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps (error 'trace-g2 "expected one step, got ~s" steps)])))

(define (config-control config)
  (match config [`(cfg ,control ,_heap ,_states ,_tokens ,_events) control]))

(define (config-tokens config)
  (match config [`(cfg ,_control ,_heap ,_states ,tokens ,_events) tokens]))

(define (core-forms predicate term)
  (define (walk value)
    (append (if (predicate value) (list value) '())
            (if (list? value) (append-map walk value) '())))
  (walk term))

(define (all-spans term)
  (append (if (match term [`(#:span ,_ ,_ ,_) #t] [_ #f]) (list term) '())
          (if (list? term) (append-map all-spans term) '())))

(define (source-span source pattern)
  (match (regexp-match-positions pattern source)
    [(list (cons lo hi)) `(#:span src ,lo ,hi)]
    [_ (error 'source-span "pattern not found: ~a" pattern)]))

(define (trace-elaborated expression)
  (call-with-trait-ledger
   (current-trait-ledger)
   (lambda ()
     (match (elab (annotate-surface expression))
      [(list core expected _row callables)
        (define start (inject-g2m (erase-core core)))
        (define-values (configs rules) (trace-g2 start))
        (check-equal? (core-type-of core '() callables)
                      (list expected _row))
        (for ([config (in-list configs)] [index (in-naturals)])
          (define runtime (runtime-row config callables expected))
          (check-not-false runtime (format "config ~a has runtime-row" index))
          (when runtime
            (check-true (config-ok? config callables expected runtime))))
        (values configs rules)]
       [other (fail-check (format "UCore を elaborate できなかった: ~s" other))]))))

(test-case "if は条件に応じて選んだ枝を評価する"
  (check-equal? (run-source "fn choose(b: Bool) -> Int { if b { 11 } else { 22 } }\nchoose(true)") 11)
  (check-equal? (run-source "fn choose(b: Bool) -> Int { if b { 11 } else { 22 } }\nchoose(false)") 22))

(test-case "選ばれない枝の return は実行されない"
  (check-equal?
   (run-source
    (string-append
     "fn choose(b: Bool) -> Int {\n"
     "  let ignored = if b { 7 } else { return 99 }\n"
     "  2\n"
     "}\nchoose(true)"))
   2))

(test-case "枝の return は if の値になって関数の残りが実行される"
  (check-equal?
   (run-source
    (string-append
     "fn choose(b: Bool) -> Int {\n"
     "  let result = if b { return 1 } else { 2 }\n"
     "  3\n"
     "}\nchoose(true)"))
   3))

(test-case "else if は内側の if として評価される"
  (check-equal?
   (run-source "fn choose(b: Bool) -> Int { if b { 1 } else if true { 2 } else { 3 } }\nchoose(false)")
   2))

(test-case "条件内の return は if の枝境界を越えて外側へ届く"
  (check-equal?
   (run-source
    (string-append
     "fn identity(x: Bool) -> Bool { x }\n"
     "fn f() -> Int {\n"
     "  let ignored = if identity(return 1) { true } else { false }\n"
     "  2\n"
     "}\nf()"))
   1))

(test-case "if の条件が Int なら全体の位置で expected Bool を診断する"
  (define source "if 1 { 1 } else { 2 }")
  (define result (compile source))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-012")
    (check-equal? (diagnostic-expected result) 'Bool)
    (check-equal? (diagnostic-found result) 'Int)
    (check-equal? (diagnostic-primary-span result)
                  `(#:span src 0 ,(string-length source)))))

(test-case "Union 条件の不適合成分も if 全体の位置で診断する"
  (define source
    "fn f(v: Int | Bool) -> Int { if v { 1 } else { 2 } }\nf(true)")
  (define result (compile source))
  (define if-start (string-length "fn f(v: Int | Bool) -> Int { "))
  (define if-end (+ if-start (string-length "if v { 1 } else { 2 }")))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-012")
    (check-equal? (diagnostic-expected result) 'Bool)
    (check-equal? (diagnostic-found result) 'Int)
    (check-equal? (diagnostic-primary-span result)
                  `( #:span src ,if-start ,if-end))))

(test-case "注釈付き Let と関数戻り型の期待型を if の両枝へ渡す"
  (define annotated
    (string-append
     "fn f(b: Bool) -> Option<Int> {\n"
     "  let value: Option<Int> = if b { some(1) } else { none }\n"
     "  value\n"
     "}\nf(true)"))
  (define returned
    (string-append
     "fn f(b: Bool) -> Option<Int> { if b { some(1) } else { none } }\nf(false)"))
  (for ([source (in-list (list annotated returned))])
    (define result (compile source))
    (check-true (compiled? result)
                (if (diagnostic? result)
                    (format "~a: ~a" (diagnostic-id result) (diagnostic-message result))
                    (format "unexpected result: ~s" result)))
    (when (compiled? result)
      (check-equal? (compiled-type result) '(Option Int)))))

(test-case "入れ子の if は各条件の束縛を取り違えない"
  (define source
    (string-append
     "fn choose(a: Bool, b: Bool) -> Int {\n"
     "  if a { if b { 1 } else { 2 } } else { 3 }\n"
     "}\nchoose(true, false)"))
  (check-equal? (run-source source) 2))

(test-case "else の無い if は then の型を Option に包む"
  (define true-source "let answer = if true { 42 }\nanswer")
  (define false-source "let answer = if false { 42 }\nanswer")
  (define true-result (compile true-source))
  (check-true (compiled? true-result))
  (when (compiled? true-result)
    (check-equal? (compiled-type true-result) '(Option Int))
    (check-equal? (run-value true-result) '(Construct (Option Int) some 42)))
  (check-equal? (run-source false-source)
                '(Construct (Option Int) none)))

(test-case "Option の注釈で check し、ほかの型では synth 結果と照合する"
  (check-equal? (run-source
                 "let answer: Option<Int> = if true { 42 }\nanswer")
                '(Construct (Option Int) some 42))
  (define wrong (compile "let answer: Int = if true { 42 }\n0"))
  (check-true (diagnostic? wrong))
  (when (diagnostic? wrong)
    (check-equal? (diagnostic-id wrong) "E-TYP-012")))

(test-case "Option then は平坦化せず、総称 constructor は期待型を要する"
  (check-equal?
   (run-source
    "let answer: Option<Option<Int>> = if true { some(1) }\nanswer")
   '(Construct (Option (Option Int)) some (Construct (Option Int) some 1)))
  (check-equal?
   (compile-code "let answer = if true { some(1) }\n0")
   "E-TYP-003")
  (check-equal?
   (run-source
    "fn f(c: Bool, option: Option<Int>) -> Option<Option<Int>> {\n let answer = if c { option }\n answer\n}\nf(true, some(9))")
   '(Construct (Option (Option Int)) some (Construct (Option Int) some 9))))

(test-case "最後まで else の無い連鎖は Option にし、枝の型を既存合流へ渡す"
  (define integer-source
    (string-append
     "fn choose(a: Bool, b: Bool) -> Option<Int> {\n"
     " let answer = if a { 1 } else if b { 2 }\n"
     " answer\n}\n"))
  (check-equal? (run-source (string-append integer-source "choose(true, false)"))
                '(Construct (Option Int) some 1))
  (check-equal? (run-source (string-append integer-source "choose(false, true)"))
                '(Construct (Option Int) some 2))
  (check-equal? (run-source (string-append integer-source "choose(false, false)"))
                '(Construct (Option Int) none))
  (define union-result
    (compile
     (string-append
      "fn choose(a: Bool, b: Bool) {\n"
      " let answer = if a { 1 } else if b { \"s\" }\n"
      " answer\n}\nchoose(false, true)")))
  (check-true (compiled? union-result))
  (when (compiled? union-result)
    (check-equal? (compiled-type union-result)
                  '(Option (Union Int String)))))

(test-case "明示 else の内側と then 内側の if は独立して合成する"
  (define explicit
    (compile "let answer = if true { 1 } else { if false { 2 } }\nanswer"))
  (check-true (compiled? explicit))
  (when (compiled? explicit)
    (check-equal? (compiled-type explicit)
                  '(Union (Option Int) Int)))
  (check-equal?
   (run-source "let answer = if true { if false { 1 } }\nanswer")
   '(Construct (Option (Option Int)) some
               (Construct (Option Int) none))))

(test-case "some と none を持たない型へ暗黙変換しない"
  (check-equal?
   (compile-code
    (string-append
     "type Maybe<T> =\n | just<T>\n | nothing\n"
     "let answer: Maybe<Int> = if true { 1 }\n0"))
   "E-TYP-012"))

(test-case "then の return は if の値となり、Option と不一致なら拒否する"
  (define source
    (string-append
     "fn empty() -> Option<Int> { none }\n"
     "fn choose(c: Bool) -> Option<Int> {\n"
     " let ignored = if c { return empty() }\n"
     " some(7)\n}\nchoose(true)"))
  (check-equal? (run-source source) '(Construct (Option Int) some 7))
  (check-equal?
   (compile-code
    "fn f(c: Bool) -> Option<Int> { let answer = if c { return 0 }\n answer }\n0")
   "E-TYP-012"))

(test-case "全ての then が Never の IfSome は候補と期待型で型を得る"
  (define no-candidate
    (elab
     '(FnDecl spin () Never (Partial)
        (Apply spin)
        (Let (flag const Bool)
          (Construct true (Types))
          (IfSome ((flag (Apply spin))))))))
  (match no-candidate
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-TYP-010")]
    [other (fail-check (format "E-TYP-010 を期待したが ~s" other))])
  (define expected
    (elab
     '(FnDecl f
        ((c Bool) (stop (NFn () Never (Partial) ())))
        (Option Int) (Partial)
        (Let (answer const (Option Int))
          (IfSome ((c (Apply stop))))
          answer)
        unit)))
  (check-false (match expected [`(err ,_) #t] [_ #f])))

(test-case "第2節の条件 return 候補は使い、第1節の条件候補は使わない"
  (define prefix
    '(FnDecl f
       ((a Bool) (b Bool) (option (Option Int))
        (stop (NFn () Never (Partial) ())))
       (Option Int) (Partial)
       (Let (answer const)
         (IfSome ((a (Apply stop)) ((Return option) (Apply stop))))
         answer)
       unit))
  (check-false (match (elab prefix) [`(err ,_) #t] [_ #f]))
  (define first-condition
    '(FnDecl f
       ((a Bool) (option (Option Int))
        (stop (NFn () Never (Partial) ())))
       (Option Int) (Partial)
       (Let (answer const)
         (IfSome (((Return option) (Apply stop))))
         answer)
       unit))
  (match (elab first-condition)
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-TYP-010")]
    [other (fail-check (format "c1 の候補を除外して E-TYP-010 を期待したが ~s" other))]))

(test-case "第2条件の return 候補で束縛する Surface IfSome を合成できる"
  (define source
    (string-append
     "fn identity(x: Bool) -> Bool { x }\n"
     "fn choose(a: Bool, option: Option<Int>) -> Option<Int> {\n"
     " let answer = if a { 1 } else if identity(return option) { 2 }\n"
     " answer\n}\nchoose(false, some(9))"))
  (check-equal? (run-source source) '(Construct (Option Int) some 9)))

(test-case "複数節の synthetic IfSome は展開後も妥当な span を持つ"
  (define source
    '(FnDecl f ((a Bool) (b Bool)) (Option Int) (Partial)
       (Let answer (IfSome ((a 1) (b 2))) answer)
       unit))
  (match (elab (annotate-surface source))
    [(list core _type _row _callables)
     (check-true (andmap span-ok? (all-spans core)))]
    [other (fail-check (format "IfSome の elaboration を期待したが ~s" other))]))

(test-case "Owned payload の IfSome は Surface の expected 経路を型検査する"
  (check-true
   (compiled?
    (compile
     (string-append
      "fn choose(c: Bool, make: fn() -> Owned<Int> ! Own) -> Int ! Own {\n"
      " let answer = if c { make() }\n 0\n}\n0")))))

(test-case "IfSome の Core は Owned を some へ移し、未選択なら Scope で drop する"
  (define (source condition)
    `(Apply
      (Fn ((flag Bool) (owned (Owned Res)))
          (Option (Owned Res)) (Own)
          (IfSome ((flag (Move owned)))))
      (Construct ,condition (Types))
      (Apply acquire 1)))
  (define-values (taken _taken-rules) (trace-elaborated (source 'true)))
  (define-values (skipped _skipped-rules) (trace-elaborated (source 'false)))
  (check-equal?
   (config-control (last taken))
   '(Construct (Option (Owned Res)) some
               (OwnedLeaf (tok 1) (resource 1))))
  (check-equal? (config-tokens (last taken))
                '(((tok 0) Dropped) ((tok 1) Available)))
  (check-equal? (config-tokens (last skipped)) '(((tok 0) Dropped)))
  (check-equal? (config-control (last skipped))
                '(Construct (Option (Owned Res)) none)))

(test-case "同じ空 span の UCore branch は IfSome の marker にならない"
  (define s '(#:span src 0 0))
  (match (elab
          `(Eliminate ,s
             (Construct ,s true (Types))
             ((,s true () -> (#:lit 1 ,s))
              (,s false () -> (#:lit unit ,s)))))
    [(list _ type _ _)
     (check-equal? type '(Union Int Unit))]
    [other (fail-check (format "Eliminate の結果を期待したが ~s" other))]))

(test-case "文位置の if は値を捨てて後続へ進む"
  (define source
    (string-append
     "fn log(message: String) -> Unit { () }\n"
     "fn choose(c: Bool) -> Int {\n"
     " if c { log(\"enabled\") }\n"
     " 7\n"
     "}\n"))
  (check-equal? (run-source (string-append source "choose(true)")) 7)
  (check-equal? (run-source (string-append source "choose(false)")) 7))

(test-case "文位置の if の明示 return は関数を抜ける"
  (define source
    (string-append
     "fn choose(c: Bool) -> Int {\n"
     " if c { return 1 }\n"
     " 2\n"
     "}\n"))
  (check-equal? (run-source (string-append source "choose(true)")) 1)
  (check-equal? (run-source (string-append source "choose(false)")) 2))

(test-case "文位置の else if 連鎖は Option の Construct を作らない"
  (define result
    (compile
     (string-append
      "fn choose(a: Bool, b: Bool) -> Int {\n"
      " if a { 1 } else if b { 2 }\n"
      " 3\n"
      "}\nchoose(false, false)")))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) 3)
    (check-false (member 'some (flatten (compiled-execution-core result))))
    (check-false (member 'none (flatten (compiled-execution-core result))))))

(test-case "値位置の末尾 if は Unit に暗黙変換せず、後続の式文なら受理する"
  (define source
    (string-append
     "fn log(message: String) -> Unit { () }\n"
     "fn f(c: Bool) -> Unit { if c { log(\"x\") } }\n"
     "fn g(c: Bool) -> Unit {\n"
     " if c { log(\"x\") }\n"
     " ()\n"
     "}\n0"))
  (define failed (compile source))
  (check-true (diagnostic? failed))
  (when (diagnostic? failed)
    (check-equal? (diagnostic-id failed) "E-TYP-012"))
  (define accepted
    (compile
     (string-append
      "fn log(message: String) -> Unit { () }\n"
      "fn g(c: Bool) -> Unit {\n"
      " if c { log(\"x\") }\n"
      " ()\n"
      "}\n0")))
  (check-true (compiled? accepted)))

(test-case "明示 else の Unit は式位置で値になる"
  (define result (compile "let answer = if true { () } else { () }\nanswer"))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (compiled-type result) 'Unit)))

(test-case "第2条件の return は先行する IfSome 境界へ届き、第1条件は関数へ届く"
  (define second-condition
    (string-append
     "fn identity(x: Bool) -> Bool { x }\n"
     "fn choose(a: Bool) -> Option<Int> {\n"
     " let answer: Option<Int> = if a { 1 } else if identity(return none) { 2 }\n"
     " some(9)\n"
     "}\nchoose(false)"))
  (check-equal?
   (run-source second-condition)
   '(Construct (Option Int) some 9))
  (define first-condition
    (string-append
     "fn identity(x: Bool) -> Bool { x }\n"
     "fn choose(b: Bool) -> Option<Int> {\n"
     " let answer = if identity(return none) { 1 } else if b { 2 }\n"
     " some(9)\n"
     "}\nchoose(true)"))
  (check-equal?
   (run-source first-condition)
   '(Construct (Option Int) none))
  (define explicit
    (string-append
     "fn identity(x: Bool) -> Bool { x }\n"
     "fn choose(a: Bool) -> Option<Int> {\n"
     " let answer: Option<Int> = if a { some(1) } else if identity(return none) { some(2) } else { none }\n"
     " some(9)\n"
     "}\nchoose(false)"))
  (check-equal?
   (run-source explicit)
   '(Construct (Option Int) some 9)))

(test-case "IfSome の明示形は節と then block の span を保つ"
  (define source
    (string-append
     "fn f(a: Bool, b: Bool) -> Option<Int> { let answer = if a { 1 } else if b { 2 }\n"
     " answer\n}\nf(false, true)"))
  (define result (compile source))
  (check-true (compiled? result))
  (when (compiled? result)
    (define core (compiled-core result))
    (define some-spans
      (map second
           (core-forms (λ (node)
                         (match node [`(Construct ,_ ,_ some ,_) #t] [_ #f]))
                       core)))
    (define none-spans
      (map second
           (core-forms (λ (node)
                         (match node [`(Construct ,_ ,_ none) #t] [_ #f]))
                       core)))
    (define true-branch-spans
      (map first
           (core-forms (λ (node)
                         (match node
                           [`((#:span ,_ ,_ ,_) true () -> ,_) #t]
                           [_ #f]))
                       core)))
    (define if-let-spans
      (map second
           (core-forms (λ (node)
                         (match node
                           [`(Let ,_ ((#:bind ,name ,_) const (#:ty Bool ,_)) ,_ ,_)
                            (and (symbol? name)
                                 (regexp-match? #rx"^%ifcond" (symbol->string name)))]
                           [_ #f]))
                       core)))
    (define then-spans
      (list (source-span source #rx"\\{ 1 \\}")
            (source-span source #rx"\\{ 2 \\}")))
    (define final-then-span (last then-spans))
    (define expected-none-span
      `(#:span src ,(fourth final-then-span) ,(fourth final-then-span)))
    (check-equal? some-spans then-spans)
    (check-equal? true-branch-spans then-spans)
    (check-equal? none-spans (list expected-none-span))
    (check-equal? if-let-spans
                  (list (source-span source #rx"if a \\{ 1 \\} else if b \\{ 2 \\}")
                        (source-span source #rx"if b \\{ 2 \\}")))))

(test-case "全 then が Never で Option 以外の return 候補は拒否する"
  (check-equal?
   (compile-code
    (string-append
     "fn f(a: Bool, b: Bool) -> Option<Int> {\n"
     " let answer = if a { return 1 } else if b { return 2 }\n"
     " answer\n}\nf(true, false)"))
   "E-TYP-012"))

(test-case "異なる Owned 型の then は合流できない"
  (check-equal?
   (compile-code
    (string-append
     "fn choose(a: Bool, b: Bool, first: fn() -> Owned<Int> ! Own, second: fn() -> Owned<String> ! Own) -> Int ! Own {\n"
     " let ignored = if a { first() } else if b { second() }\n"
     " 0\n"
     "}\n0"))
   "E-TYP-012"))

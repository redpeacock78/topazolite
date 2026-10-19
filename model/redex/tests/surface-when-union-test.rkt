#lang racket

(require rackunit
         racket/match
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../elaborate.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))
(define (check-compiled result)
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a (expected ~s, found ~s)"
                          (diagnostic-id result) (diagnostic-message result)
                          (diagnostic-expected result) (diagnostic-found result))
                  (format "unexpected result: ~s" result))))
(define (code . sources)
  (define result (compile (apply string-append sources)))
  (and (diagnostic? result) (diagnostic-id result)))
(define (core-code expression)
  (match (elab expression)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))
(define (ok? source) (compiled? (compile source)))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
       [other (fail-check (format "評価結果の config を期待したが ~s" other))]))))

(define (count-form tree wanted)
  (cond [(and (pair? tree) (eq? (car tree) wanted))
         (add1 (apply + (map (lambda (child) (count-form child wanted)) (cdr tree))))]
        [(pair? tree) (apply + (map (lambda (child) (count-form child wanted)) tree))]
        [else 0]))

(define (find-form tree wanted)
  (cond [(and (pair? tree) (eq? (car tree) wanted)) tree]
        [(pair? tree) (for/or ([child (in-list tree)]) (find-form child wanted))]
        [else #f]))

(define (source-span source needle)
  (match (regexp-match-positions (regexp-quote needle) source)
    [(list (cons start end)) `(#:span src ,start ,end)]
    [_ (error 'source-span "substring not found: ~a" needle)]))

(define (replace-binder-span tree name span)
  (match tree
    [`(#:bind ,actual ,_) #:when (eq? actual name) `(#:bind ,actual ,span)]
    [(list parts ...) (map (lambda (part) (replace-binder-span part name span))
                           parts)]
    [_ tree]))

(define (check-resource-core term)
  (match (elab term)
    [(list core type row callables)
     (define erased (erase-core core))
     (define actual (core-type-of erased '() callables))
     (define expected (list type row))
     (check-equal? actual expected
                   (if (equal? actual expected)
                       ""
                       (format "core typing diagnostic: ~s; core: ~s"
                               (core-type-of/diagnostic erased '() callables)
                               erased)))
     (check-true
      (config-ok? (inject-g2m (erase-core core)) callables type row))
     core]
    [(list 'err diagnostic)
     (fail-check
      (format "資源型 Union core の elaboration を期待したが ~a: ~a"
              (diagnostic-id diagnostic) (diagnostic-message diagnostic)))]))

(define (union-member-body core member-type)
  (match (find-form core 'UnionEliminate)
    [`(UnionEliminate ,_ ,_ ,branches)
     (for/first ([branch (in-list branches)]
                 #:when
                 (match branch
                   [`(,_ (#:ty ,type ,_) (#:bind ,_ ,_) -> ,_)
                    (equal? type member-type)]
                   [_ #f]))
       (match branch
         [`(,_ ,_ ,_ -> ,body) body]))]
    [_ #f]))

(define option-string
  "let option: Option<Int> = some(7)\nlet value: Option<Int> | String = option\n")

(test-case "Int | String の member pattern は tag ごとに枝を選ぶ"
  (for ([source+expected (in-list
                          (list (list "let value: Int | String = 42\n"
                                      42)
                                (list "let value: Int | String = \"text\"\n"
                                      0)))])
    (match-define (list prefix expected) source+expected)
    (define result
      (compile (string-append prefix
                              "let answer = when value {\n"
                              "  (n: Int) => n\n"
                              "  (s: String) => 0\n"
                              "}\nanswer")))
    (check-compiled result)
    (when (compiled? result) (check-equal? (run-value result) expected))))

(test-case "member 枝は source binder span を保つ"
  (define source
    (string-append
     "let value: Int | String = 42\n"
     "let answer = when value {\n"
     "  (n: Int) => n\n"
     "  (s: String) => 0\n"
     "}\nanswer"))
  (define result (compile source))
  (check-compiled result)
  (when (compiled? result)
    (define span (source-span source "n: Int"))
    (match-define `(#:span src ,start ,_) span)
    (match (find-form (compiled-core result) 'UnionEliminate)
      [`(UnionEliminate ,_ ,_ ,branches)
       (define branch
         (for/first ([branch (in-list branches)]
                     #:when (match branch
                              [`(,_ (#:ty Int ,_) (#:bind ,_ ,_) -> ,_) #t]
                              [_ #f]))
           branch))
       (match branch
         [`(,_ (#:ty Int ,_) (#:bind ,_ ,binder-span) -> ,_)
          (check-equal? binder-span `(#:span src ,start ,(add1 start)))]
         [_ (fail-check (format "Int member branch を期待した: ~s" branch))])]
      [other (fail-check (format "UnionEliminate を期待した: ~s" other))]))
  (define option-type '(Option (Owned Int)))
  (define alias-span '(#:span src 80 86))
  (define annotated
    (replace-binder-span
     (annotate-surface
      `(Fn ((value (Union ,option-type Int))) Unit (Own)
           (Eliminate (Move value)
                      ((,option-type option -> unit)
                       (Int number -> unit)))))
     'option alias-span))
  (define core (check-resource-core annotated))
  (check-match (union-member-body core option-type)
    `(Scope ,_ ()
            (Let ,_ ((#:bind ,_ ,alias-span) let (#:ty ,option-type ,_))
                 (#:var ,_ ,_)
                 ,_))))

(test-case "Union member の本体ブロック arm は leave の値を返す"
  (define source
    (string-append
     "fn choose(value: Int | String) -> Int | String {\n"
     "  return when value {\n"
     "    (x: Int) => { leave x }\n"
     "    (s: String) => { leave 0 }\n"
     "  }\n}\nchoose(1)"))
  (define result (compile source))
  (check-compiled result)
  (when (compiled? result)
    (match (run-value result)
      [`(UnionVal ,_ Int 1) (void)]
      [other (fail-check (format "Int member の UnionVal を期待した: ~s"
                                 other))])))

(test-case "Union member の単一式本体ブロック arm は式の値を返す"
  (define source
    (string-append
     "fn choose(value: Int | String) -> Int | String {\n"
     "  let answer = when value {\n"
     "    (x: Int) => { x }\n"
     "    (s: String) => { leave 0 }\n"
     "  }\n  return answer\n}\nchoose(1)"))
  (define result (compile source))
  (check-compiled result)
  (when (compiled? result)
    (check-match (run-value result) `(UnionVal ,_ Int 1))))

(test-case "Union member arm の文を持つブロックの落ち抜けは E-RET-005"
  (define source
    (string-append
     "fn choose(value: Int | String) -> Int {\n"
     "  let answer = when value {\n"
     "    (x: Int) => { let y = x\n y }\n"
     "    (s: String) => { leave 0 }\n"
     "  }\n  return answer\n}\nchoose(1)"))
  (define result (compile source))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-RET-005")
    (match-define `(#:span src ,_ ,end)
      (source-span source "(x: Int) => { let y = x\n y }"))
    (check-equal? (diagnostic-primary-span result)
                  `(#:span src ,(sub1 end) ,end))))

(test-case "Union の constructor group 内の落ち抜けを when の E-RET-005 へ伝える"
  (for ([scrutinee (in-list '("value" "g()"))])
    (define variable? (equal? scrutinee "value"))
    (define source
      (string-append
       (if variable?
           ""
           "fn g() -> Option<Int> | String { return \"s\" }\n")
       "fn noop() -> Unit { () }\n"
       "fn choose(" (if variable? "value: Option<Int> | String" "")
       ") -> Int {\n"
       "  let result = when " scrutinee " {\n"
       "    some x => { leave 0 }\n"
       "    none => { noop()\n () }\n"
       "    (s: String) => { leave 1 }\n"
       "  }\n  return result\n}\n"
       (if variable? "choose(none)" "choose()")))
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-RET-005")
      (match-define `(#:span src ,_ ,end)
        (source-span source "none => { noop()\n () }"))
      (check-equal? (diagnostic-primary-span result)
                    `(#:span src ,(sub1 end) ,end)))))

(test-case "constructor arm 内の文位置 when の落ち抜けは外側へ漏れない"
  (define source
    (string-append
     "fn f(value: Option<Int> | String, b: Bool) -> Int {\n"
     "  let result = when value {\n"
     "    some x => {\n"
     "      when b { true => { 1 }\n false => { 2 } }\n"
       "      leave x\n"
     "    }\n"
     "    none => { leave 0 }\n"
     "    (s: String) => { leave 3 }\n"
     "  }\n  return result\n}\n"
     "let option: Option<Int> = some(7)\nf(option, false)"))
  (define result (compile source))
  (check-compiled result)
  (when (compiled? result) (check-equal? (run-value result) 7)))

(test-case "Union member arm の if 式は本体ブロックではない"
  (for* ([scrutinee (in-list '("value" "g()"))]
         [position (in-list '(synth annotated return))])
    (define variable? (equal? scrutinee "value"))
    (define arms
      (string-append
       " {\n"
       "    (x: Int) => if b { x } else { 0 }\n"
       "    (s: String) => 5\n"
       "  }\n"))
    (define source
      (string-append
       (if variable? "" "fn g() -> Int | String { return 1 }\n")
       "fn f(" (if variable? "value: Int | String, " "") "b: Bool) -> Int {\n"
       (case position
         [(synth) (string-append "  let z = when " scrutinee arms "  return z\n")]
         [(annotated)
          (string-append "  let z: Int = when " scrutinee arms "  return z\n")]
         [(return) (string-append "  return when " scrutinee arms)])
       "}\n"
       (if variable? "f(1, true)" "f(true)")))
    (define result (compile source))
    (check-compiled result)
    (when (compiled? result) (check-equal? (run-value result) 1))))

(test-case "Option 成分と String 成分の constructor と member を混在できる"
  (define source
    (string-append
     option-string
     "let answer = when value {\n"
     "  some n => n\n"
     "  none => 0\n"
     "  (s: String) => 9\n"
     "}\nanswer"))
  (define result (compile source))
  (check-compiled result)
  (when (compiled? result)
    (check-equal? (run-value result) 7)
    (check-true (positive? (count-form (compiled-core result) 'UnionEliminate)))
    (check-true (positive? (count-form (compiled-core result) 'Eliminate)))))

(test-case "data 成分は member pattern でまとめられ、data だけの Union も除去できる"
  (check-true
   (ok? (string-append option-string
                       "let answer = when value {\n"
                       "  (o: Option<Int>) => 1\n"
                       "  (s: String) => 2\n"
                       "}\nanswer")))
  (define source
    (string-append
     "let result: Result<Int, String> = ok(7)\n"
     "let value: Option<Int> | Result<Int, String> = result\n"
     "let answer = when value {\n"
     "  some n => n\n"
     "  none => 0\n"
     "  ok n => n\n"
     "  ng message => 1\n"
     "}\nanswer"))
  (define result (compile source))
  (check-compiled result)
  (when (compiled? result)
    (check-equal? (run-value result) 7)
    (check-true (positive? (count-form (compiled-core result) 'UnionEliminate)))
    (check-true (positive? (count-form (compiled-core result) 'Eliminate)))))

(test-case "member 枝だけで使う外側の値を無名関数が capture する"
  (define result
    (compile
     (string-append
      "fn apply(value: Int | String, captured: Int) -> Int {\n"
      "  let f = when value {\n"
      "    (n: Int) => fn (x: Int) => captured\n"
      "    (s: String) => fn (x: Int) => captured\n"
      "  }\n"
      "  return f(0)\n"
      "}\napply(1, 37)")))
  (check-compiled result)
  (when (compiled? result) (check-equal? (run-value result) 37)))

(test-case "member の束縛子は同名 constructor を隠す"
  (define result
    (compile
     (string-append
      "let value: Option<Int> | String = \"kept\"\n"
      "let answer: String = when value {\n"
      "  some n => \"other\"\n"
      "  none => \"other\"\n"
      "  (none: String) => none\n"
      "}\nanswer")))
  (check-compiled result)
  (when (compiled? result) (check-equal? (run-value result) "kept")))

(test-case "member 枝の予約束縛子は constructor 枝と同じ診断で拒まれる"
  (check-equal? (core-code '(Eliminate value ((some (|x⟨1⟩|) -> 0))))
                "E-SYN-005")
  (check-equal? (core-code '(Eliminate value ((Int |x⟨1⟩| -> 0))))
                "E-SYN-005"))

(test-case "成分の不足、重複、不一致、曖昧さは E-DAT-004 になる"
  (define (program type arms)
    (string-append "fn f(value: " type ") -> Int {\n  when value {\n"
                   arms "\n  }\n}\n0"))
  (for ([arms (in-list
               (list "(n: Int) => n"
                     "(n: Int) => n\n(n2: Int) => n2\n(s: String) => 0"
                     "(b: Bool) => 0\n(s: String) => 0"
                     "(x: Int | Bool) => 0\n(s: String) => 0"
                     "(o: Option<Int>) => 0\nsome n => n\nnone => 0\n(s: String) => 0"
                     "missing => 0\n(s: String) => 0"))])
    (check-equal? (code (program "Int | String" arms)) "E-DAT-004"))
  (check-equal?
   (code (program "Option<Int> | Option<String>"
                  "some n => 0\nnone => 0"))
   "E-DAT-004"))

(test-case "scrutinee と枝の種類に応じた診断を優先する"
  (check-equal?
   (code "fn f(value: Int) -> Int { when value { (n: Int) => none } }\n0")
   "E-TYP-029")
  (check-equal?
   (code "fn f(value: Int) -> Int { when value { zero => 0 } }\n0")
   "E-DAT-003")
  (check-equal?
   (code "fn f(value: Owned<Int | String>) -> Int {\n"
         "  when value {\n    (n: Int) => n\n    (s: String) => 0\n  }\n}\n0")
   "E-OWN-010")
  (check-equal?
   (code "fn f(value: Owned<Option<Int> | String>) -> Int {\n"
         "  when value {\n    some n => n\n    none => 0\n    (s: String) => 1\n  }\n}\n0")
   "E-OWN-010")
  (check-equal?
   (core-code
    '(Fn ((value (Owned (Union Int String)))) Int (Own)
         (Eliminate (Move value) ((Int n -> n) (String s -> 0)))))
   #f)
  (check-equal?
   (core-code
    '(Fn ((value (Owned (Union (Option Int) (Result Int String))))) Int (Own)
         (Eliminate (Move value)
                    ((some (n) -> n) (none () -> 0)
                     (ok (n) -> n) (ng (message) -> 0)))))
   #f))

(test-case "member 型の未知名は E-SUR-008 になる"
  (check-equal?
   (code "fn f(value: Int | String) -> Int {\n"
         "  when value {\n    (n: Missing) => 0\n    (s: String) => 1\n  }\n}\n0")
   "E-SUR-008"))

(test-case "Owned 欄を持つ Record の member binder は資源 encoding を持つ"
  (define record-type '(Record ((a (Owned Int) imm))))
  (define core
    (check-resource-core
     `(Fn ((value (Union ,record-type Int))) Int (Own)
          (Eliminate
           (Move value)
           ((,record-type record -> 1)
            (Int number -> number))))))
  (check-match (union-member-body core record-type)
    `(Scope ,_ ()
            (Let ,_ ((#:bind ,_ ,_) let (#:ty ,record-type ,_))
                 (#:var ,_ ,_)
                 ,_))))

(test-case "Option<Owned<Int>> の member binder は資源 encoding を持つ"
  (define option-type '(Option (Owned Int)))
  (define core
    (check-resource-core
     `(Fn ((value (Union ,option-type Int))) Int (Own)
          (Eliminate
           (Move value)
           ((,option-type option -> 1)
            (Int number -> number))))))
  (check-match (union-member-body core option-type)
    `(Scope ,_ ()
            (Let ,_ ((#:bind ,_ ,_) let (#:ty ,option-type ,_))
                 (#:var ,_ ,_)
                 ,_))))

(test-case "resource data 枝は Move と未使用の両方を encoding する"
  (define option-type '(Option (Owned Int)))
  (for ([some-body (in-list '((Drop (Move item)) unit))])
    (define core
      (check-resource-core
       `(Fn ((value (Union ,option-type Int))) Unit (Own)
            (Eliminate
             (Move value)
             ((some (item) -> ,some-body)
              (none () -> unit)
              (Int number -> unit))))))
    (define option-body (union-member-body core option-type))
    (match option-body
      [`(Scope ,_ ()
               (Let ,_ ((#:bind ,alias ,_) let (#:ty ,option-type ,_))
                    (#:var ,_ ,_)
                    (Eliminate ,_ (Move ,_ (#:var ,same ,_)) ,_)))
       (check-equal? alias same)]
      [other (fail-check (format "resource data 枝の encoding が違う: ~s" other))])))

(test-case "resource Union の枝で Move と未使用を別々に合流する"
  (define option-type '(Option (Owned Int)))
  (define record-type '(Record ((a (Owned Int) imm))))
  (define core
    (check-resource-core
     `(Fn ((value (Union ,record-type ,option-type))) Unit (Own)
          (Eliminate
           (Move value)
           ((,record-type record -> (Drop (Proj (Move record) a)))
            (,option-type option -> unit))))))
  (for ([member (in-list (list record-type option-type))])
    (check-match (union-member-body core member)
      `(Scope ,_ ()
              (Let ,_ ((#:bind ,_ ,_) let (#:ty ,member ,_))
                   (#:var ,_ ,_)
                   ,_)))))

(test-case "注釈の無い Union when は合成される"
  (define result
    (compile (string-append
              "let value: Int | String = 23\n"
              "let answer = when value {\n  (n: Int) => n\n  (s: String) => 0\n}\n"
              "answer")))
  (check-compiled result)
  (when (compiled? result)
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) 23)))

;; SUR-014b2s。data の when と Union の when の入れ子を合成位置に置く。
(define (cross-program variable? scrutinee-type parameters return-type body arguments)
  (string-append
   (if variable? "" (string-append "fn g() -> " scrutinee-type " { return "
                                   (if (equal? scrutinee-type "Bool") "true" "1")
                                   " }\n"))
   "fn f(" parameters ") -> " return-type " {\n"
   "  let z = " body "\n"
   "  return z\n}\n"
   "f(" arguments ")"))

(test-case "合成位置の data when の枝の Union when を受理する"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define result
      (compile
       (cross-program
        variable? "Bool"
        (if variable? "a: Bool, u: Int | String" "u: Int | String")
        "Int"
        (string-append
         "when " scrutinee " {\n"
         "    true => when u {\n      (x: Int) => x\n      (s: String) => 0\n    }\n"
         "    false => 3\n  }")
        (if variable? "true, 5" "5"))))
    (check-compiled result)
    (when (compiled? result)
      (check-equal? (compiled-type result) 'Int)
      (check-equal? (run-value result) 5))))

(test-case "data when の中の Union when の葉の some と none は外側全体で E-TYP-004"
  (for ([scrutinee (in-list '("a" "g()"))])
    (define variable? (equal? scrutinee "a"))
    (define body
      (string-append
       "when " scrutinee " {\n"
       "    true => when u {\n      (x: Int) => some(x)\n      (s: String) => none\n    }\n"
       "    false => none\n  }"))
    (define source
      (cross-program variable? "Bool"
                     (if variable? "a: Bool, u: Int | String" "u: Int | String")
                     "Option<Int>" body (if variable? "true, 5" "5")))
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-TYP-004")
      (check-equal? (diagnostic-primary-span result) (source-span source body)))))

(test-case "Union when の中の data when の葉の some と none は内側全体で E-TYP-004"
  (for ([scrutinee (in-list '("u" "g()"))])
    (define variable? (equal? scrutinee "u"))
    (define inner "when b {\n      true => some(x)\n      false => none\n    }")
    (define source
      (cross-program variable? "Int | String"
                     (if variable? "u: Int | String, b: Bool" "b: Bool")
                     "Option<Int>"
                     (string-append
                      "when " scrutinee " {\n"
                      "    (x: Int) => " inner "\n"
                      "    (s: String) => none\n  }")
                     (if variable? "1, true" "true")))
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-TYP-004")
      (check-equal? (diagnostic-primary-span result) (source-span source inner)))))

(test-case "Union when の葉の型引数の無い constructor は E-TYP-003 で constructor を指す"
  (for ([scrutinee (in-list '("u" "g()"))])
    (define variable? (equal? scrutinee "u"))
    (define source
      (cross-program variable? "Int | String"
                     (if variable? "u: Int | String" "")
                     "Option<Int>"
                     (string-append
                      "when " scrutinee " {\n"
                      "    (x: Int) => some(x)\n"
                      "    (s: String) => none\n  }")
                     (if variable? "1" "")))
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-TYP-003")
      (check-equal? (diagnostic-primary-span result) (source-span source "some(x)")))))

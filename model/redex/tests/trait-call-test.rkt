#lang racket

(require rackunit
         racket/match
         racket/set
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../lexer.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../parser.rkt"
         "../search.rkt"
         "../surface-lower.rkt"
         "../traits.rkt")

(define (compile source) (compile-source/string 'src source))
(define (parse-source source) (parse (lex/string 'src source)))
(define (lower source) (lower-surface (parse-source source) canonical-trait-env))

(define (error-id result)
  (match result
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (run-value artifact)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (λ ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core artifact))) 10000)
       [`(cfg ,value () () () ()) value]
       [other (fail-check (format "unexpected result ~s" other))]))))

(define (elab-with artifact expression [providers (hasheq)])
  (call-with-trait-ledger
   (if artifact (compiled-ledger artifact) canonical-trait-ledger)
   (λ ()
     (parameterize ([current-trait-providers providers])
       (elab expression)))))

(define (trait-row artifact name)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (λ () (trait-row-by-name name (current-trait-env)))))

(define (provider-id artifact name)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (λ () (impl-oid (first (impl-rows-by-trait name (current-trait-env)))))))

(define (nth-span source text [index 0])
  (define positions (regexp-match-positions* (regexp (regexp-quote text)) source))
  (define position (list-ref positions index))
  `(#:span src ,(car position) ,(cdr position)))

(define (contains-form? tree head)
  (or (match tree [(list* (== head) _rest) #t] [_ #f])
      (and (pair? tree) (ormap (λ (child) (contains-form? child head)) tree))))

(define (contains-provider-call? tree)
  (define term (erase-origin-core (erase-core tree)))
  (define (find term)
    (or (match term
          [`(Apply (Proj ,provider print) ,_ ...)
           (eq? provider '%impl-rec-Printable-1)]
          [_ #f])
        (and (pair? term) (ormap find term))))
  (find term))

(test-case "T1 利用者の impl の欄を呼んで Apply-Proj へ消去し実行値を得る"
  (define source
    (string-append
     "type User = { name: String }\n"
     "impl Printable for User { print: fn(u: User) -> String { return u.name } }\n"
     "let u: User = { name: \"a\" }\n"
     "Printable.print(u)"))
  (define artifact (compile source))
  (check-true (compiled? artifact) (format "compile failed: ~s" artifact))
  (when (compiled? artifact)
    (check-false (contains-form? (compiled-execution-core artifact) 'TraitCall))
    (check-true (contains-provider-call? (compiled-execution-core artifact)))
    (check-equal? (run-value artifact) "a")))

(test-case "T2 derive の後の Sizable.size は recipe の葉の数を返す"
  (define artifact
    (compile (string-append
              "type Pair = { left: Int, right: Bool }\n"
              "derive Sizable for Pair\n"
              "let p: Pair = { left: 1, right: true }\n"
              "Sizable.size(p)")))
  (check-true (compiled? artifact) (format "compile failed: ~s" artifact))
  (when (compiled? artifact)
    (check-equal? (run-value artifact) 2)))

(test-case "T3 impl より前の関数は Absent、後の関数は Resolved"
  (define before
    (compile (string-append
              "fn before(x: Int) -> String { return Printable.print(x) }\n"
              "impl Printable for Int { print: fn(x: Int) -> String { return \"i\" } }\n"
              "before(1)")))
  (check-true (diagnostic? before))
  (when (diagnostic? before)
    (check-equal? (diagnostic-id before) "E-PRF-004"))
  (define after
    (compile (string-append
              "impl Printable for Int { print: fn(x: Int) -> String { return \"i\" } }\n"
              "fn after(x: Int) -> String { return Printable.print(x) }\n"
              "after(1)")))
  (check-true (compiled? after) (format "compile failed: ~s" after))
  (when (compiled? after) (check-equal? (run-value after) "i")))

(test-case "T4 合成 trait の呼出しは成分の実装値を呼ぶ"
  (define artifact
    (compile (string-append
              "type N = { n: Int }\n"
              "type PS = Printable & Sizable\n"
              "impl Printable for N { print: fn(x: N) -> String { return \"n\" } }\n"
              "derive Sizable for N\n"
              "let n: N = { n: 1 }\n"
              "PS.print(n)")))
  (check-true (compiled? artifact) (format "compile failed: ~s" artifact))
  (when (compiled? artifact) (check-equal? (run-value artifact) "n")))

(test-case "T5 trait 名の同綴り値を捕獲せず、非適用射影と pipe を区別する"
  (define call-artifact
    (compile (string-append
              "impl Printable for Int { print: fn(x: Int) -> String { return \"ok\" } }\n"
              "let Printable = 4\n"
              "Printable.print(1)")))
  (check-true (compiled? call-artifact)
              (format "trait call was captured by the value: ~s" call-artifact))
  (when (compiled? call-artifact)
    (check-equal? (run-value call-artifact) "ok"))
  (define projection (lower "let Printable = { print: 1 }\nPrintable.print"))
  (check-true (lowered? projection))
  (when (lowered? projection)
    (check-false (contains-form? (lowered-term projection) 'TraitCall)))
  (define pipe-artifact
    (compile (string-append
              "impl Printable for Int { print: fn(x: Int) -> String { return \"pipe\" } }\n"
              "1 |> Printable.print")))
  (check-true (compiled? pipe-artifact)
              (format "pipe trait call failed: ~s" pipe-artifact))
  (when (compiled? pipe-artifact) (check-equal? (run-value pipe-artifact) "pipe")))

(test-case "T6 Self が第 2 引数の欄は P1 を先に check し Self 引数を一度だけ合成する"
  (define artifact
    (compile (string-append
              "type User = { name: String }\n"
              "trait Select { select: fn(Int, Self) -> String }\n"
              "impl Select for User { select: fn(n: Int, u: User) -> String { return u.name } }\n"
              "let u: User = { name: \"second\" }\n"
              "Select.select(7, u)")))
  (check-true (compiled? artifact) (format "compile failed: ~s" artifact))
  (when (compiled? artifact) (check-equal? (run-value artifact) "second")))

(test-case "T7 Self を含む仮引数が Self より前にある欄は E-TYP-002"
  (define result
    (compile (string-append
              "trait Nested { f: fn(List<Self>, Self) -> Int }\n"
              "impl Nested for Int { f: fn(xs: List<Int>, x: Int) -> Int { return x } }\n"
              "Nested.f(nil(), 1)")))
  (check-true (diagnostic? result))
  (when (diagnostic? result) (check-equal? (diagnostic-id result) "E-TYP-002")))

(test-case "T8 label span、Self anchor、引数個数、未知 trait の診断"
  (define missing-label
    (string-append
     "trait Pick { get: fn(Self) -> Int }\n"
     "impl Pick for Int { get: fn(x: Int) -> Int { return x } }\n"
     "Pick.missing(1)"))
  (define label-error (compile missing-label))
  (check-true (diagnostic? label-error))
  (when (diagnostic? label-error)
    (check-equal? (diagnostic-id label-error) "E-RCD-004")
    (check-equal? (diagnostic-primary-span label-error)
                  (nth-span missing-label "missing")))
  (define no-self
    (compile (string-append
              "trait NoSelf { f: fn(Int) -> Int }\n"
              "impl NoSelf for Int { f: fn(x: Int) -> Int { return x } }\n"
              "NoSelf.f(1)")))
  (check-true (diagnostic? no-self))
  (when (diagnostic? no-self)
    (check-equal? (diagnostic-id no-self) "E-TYP-002"))
  (define arity-error (elab '(TraitCall Printable print ())))
  (check-equal? (error-id arity-error) "E-ARI-001")
  (define unknown-trait
    (elab-with #f '(TraitCall Ghost print (1))))
  (check-equal? (error-id unknown-trait) "E-SUR-015"))

(test-case "T9 UCore TraitCall は Absent と Ambiguous を E-PRF-004 にする"
  (check-equal? (error-id (elab '(TraitCall Printable print ("x"))))
                "E-PRF-004")
  (check-equal?
   (error-id (elab-with #f '(Let p (Rec ((print imm
                                            (Fn ((x String)) String () "one"))))
                                  (TraitCall Printable print ("x")))
                    (hasheq 'o-impl-printable-str-a 'missing)))
   "E-PRF-004")
  (define ambiguous
    (elab-with
     #f
     '(Let p1
        (Rec ((print imm (Fn ((x String)) String () "one"))))
        (Let p2
          (Rec ((print imm (Fn ((x String)) String () "two"))))
          (TraitCall Printable print ("x"))))
     (hasheq 'o-impl-printable-str-a 'p1
             'o-impl-printable-str-b 'p2)))
  (check-equal? (error-id ambiguous) "E-PRF-004"))

(test-case "T11 実引数は原文の左から右へ一度ずつ評価される"
  (define artifact
    (compile (string-append
              "trait Pair { pick: fn(Int, Self) -> Int }\n"
              "impl Pair for Int { pick: fn(a: Int, b: Int) -> Int { return b } }\n"
              "let mut state = 0\n"
              "Pair.pick({ state = 1\n 4 }, state)")))
  (check-true (compiled? artifact) (format "compile failed: ~s" artifact))
  (when (compiled? artifact)
    (define result
      (call-with-trait-ledger
       (compiled-ledger artifact)
       (λ ()
         (run-g2 (inject-g2m (erase-core (compiled-execution-core artifact))) 10000))))
    (match result
      [`(cfg 1 ,_ ,_ ,_ ,_) (void)]
      [_ (fail-check (format "unexpected result ~s" result))])))

(test-case "T12 Self anchor の後の実引数は特殊化した型で check する"
  (define accepted
    (compile (string-append
              "trait Same { same: fn(Self, Self) -> Int }\n"
              "impl Same for Int { same: fn(a: Int, b: Int) -> Int { return b } }\n"
              "Same.same(1, 2)")))
  (check-true (compiled? accepted) (format "compile failed: ~s" accepted))
  (when (compiled? accepted) (check-equal? (run-value accepted) 2))
  (define rejected
    (compile (string-append
              "trait Same { same: fn(Self, Self) -> Int }\n"
              "impl Same for Int { same: fn(a: Int, b: Int) -> Int { return b } }\n"
              "Same.same(1, \"x\")")))
  (check-true (diagnostic? rejected))
  (when (diagnostic? rejected)
    (check-equal? (diagnostic-id rejected) "E-TYP-012")))

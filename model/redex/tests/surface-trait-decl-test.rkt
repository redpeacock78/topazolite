#lang racket

;; SUR-010。trait と impl の宣言が行と項へ落ちることの回帰である。

(require rackunit
         racket/match
         redex/reduction-semantics
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../traits.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../typing.rkt")

(define (parse-src str) (parse (lex/string 'src str)))
(define (lower str [base canonical-trait-env]) (lower-surface (parse-src str) base))
(define (code str [base canonical-trait-env])
  (define r (lower str base))
  (and (diagnostic? r) (diagnostic-id r)))

;; 基底に行を足した環境である。基底の構築が失敗するのは試験の誤りである。
(define (base+ #:trait [trait-rows '()] #:impl [impl-rows '()])
  (make-trait-env
   #:trait (append (trait-env-trait-rows canonical-trait-env) trait-rows)
   #:impl (append (trait-env-impl-rows canonical-trait-env) impl-rows)
   #:intersect (trait-env-intersect-rows canonical-trait-env)
   #:scope (trait-env-scope-rows canonical-trait-env)
   #:fail (λ (r k key) (error 'test "bad base ~s ~s ~s" r k key))))

(define sizable-bool "impl Sizable for Bool { size: fn(x: Bool) -> Int { 0 } }\n")
(define user-sizable-bool '(o-impl-user-Sizable-1 impl-user-Sizable-1 impl Sizable Bool root))

(test-case
 "a trait declaration becomes a root trait row with a normalized field row"
 (define low (lower "trait Foo { b: Int, a: fn(Self) -> Int }\n0"))
 (check-equal? (lowered-trait-rows low)
               '((o-trait-user-Foo Foo root
                  ((a (NFn (Self) Int () () () User) imm) (b Int imm)))))
 (check-match (lowered-term low) `(#:lit 0 ,_)))

(test-case
 "record types inside a template are normalized too"
 (define low (lower "trait Foo { f: fn({ b: Int, a: Int }) -> Int }\n0"))
 (check-equal? (fourth (first (lowered-trait-rows low)))
               '((f (NFn ((Record ((a Int imm) (b Int imm)))) Int () () () User) imm))))

(test-case
 "an impl declaration becomes a row and a Let over an Apply of the primitive"
 (define low (lower (string-append sizable-bool "0")))
 (check-equal? (lowered-impl-rows low) (list user-sizable-bool))
 (match (lowered-term low)
   [`(Let ,_ ((#:bind %impl-Sizable-1 ,_) const)
          (Apply ,_ (#:var impl-user-Sizable-1 ,_) (Rec ,_ ,_))
          ,_)
    (void)]
   [other (fail (format "unexpected term ~s" other))]))

(test-case
 "an impl may precede the trait it names"
 (check-true
  (lowered? (lower "impl Foo for Int { f: 1 }\ntrait Foo { f: Int }\n0"))))

(test-case
 "impl numbering continues after the base's user impl rows"
 (define base (base+ #:impl (list user-sizable-bool)))
 (check-equal? (map first (lowered-impl-rows
                           (lower "impl Sizable for Unit { size: fn(x: Unit) -> Int { 0 } }\n0" base)))
               '(o-impl-user-Sizable-2)))

(test-case
 "impl numbering skips base suffixes that are not ASCII digit strings"
 (define base
   (base+ #:impl '((o-impl-user-Sizable-1/2 impl-user-Sizable-x impl Sizable Bool root))))
 (check-equal? (map first (lowered-impl-rows
                           (lower "impl Sizable for Unit { size: fn(x: Unit) -> Int { 0 } }\n0" base)))
               '(o-impl-user-Sizable-1)))

(test-case
 "lowering is deterministic"
 (define src (string-append "trait Foo { f: Int }\n" sizable-bool "impl Foo for Int { f: 1 }\n0"))
 (check-equal? (lower src) (lower src)))

(test-case
 "spans are keyed by trait-name, origin-id and primitive-name"
 (define src (string-append "trait Foo { f: Int }\n" sizable-bool "0"))
 (define low (lower src))
 (check-equal? (sort (map car (hash-keys (lowered-spans low))) symbol<?)
               '(origin-id origin-id primitive-name primitive-name trait-name))
 (match (parse-src src)
   [`(SProgram ,_ ((STraitDecl ,s_t (SName ,s_n ,_) ,_) (SImplDecl ,s_i ,_ ,_ ,_)) ,_)
    (check-equal? (hash-ref (lowered-spans low) '(trait-name . Foo)) s_n)
    (check-equal? (hash-ref (lowered-spans low) '(origin-id . o-trait-user-Foo)) s_t)
    (check-equal? (hash-ref (lowered-spans low) '(primitive-name . Foo-trait)) s_t)
    (check-equal? (hash-ref (lowered-spans low) '(primitive-name . impl-user-Sizable-1)) s_i)]))

(test-case
 "a Self label does not become the target type"
 (define low (lower "trait Foo { Self: Int }\nimpl Foo for Int { Self: 1 }\n0"))
 (check-true (lowered? low))
 (check-equal? (fourth (first (lowered-trait-rows low))) '((Self Int imm))))

(define (primary str [base canonical-trait-env])
  (diagnostic-primary-span (lower str base)))

(test-case
 "E-SUR-013 at the trait name, against the base and against earlier declarations"
 (define src "trait Printable { print: fn(Self) -> String }\n0")
 (check-equal? (code src) "E-SUR-013")
 (match (parse-src src)
   [`(SProgram ,_ ((STraitDecl ,_ (SName ,s_n ,_) ,_)) ,_)
    (check-equal? (primary src) s_n)])
 (check-equal? (code "trait Foo { f: Int }\ntrait Foo { g: Int }\n0") "E-SUR-013"))

(test-case
 "alias diagnostics precede trait declaration diagnostics"
 (check-equal? (code "type A = Missing\ntrait Foo { f: Int }\ntrait Foo { g: Int }\n0")
               "E-SUR-008"))

(test-case
 "E-SUR-015 at the trait name"
 (define src "impl Nope for Int { x: 1 }\n0")
 (check-equal? (code src) "E-SUR-015")
 (match (parse-src src)
   [`(SProgram ,_ ((SImplDecl ,_ (SName ,s_n ,_) ,_ ,_)) ,_)
    (check-equal? (primary src) s_n)]))

(test-case
 "E-SUR-018 at the trait name"
 (define src "impl PrintableSizable for Bool { print: fn(x: Bool) -> String { \"b\" }, size: fn(x: Bool) -> Int { 0 } }\n0")
 (check-equal? (code src) "E-SUR-018")
 (match (parse-src src)
   [`(SProgram ,_ ((SImplDecl ,_ (SName ,s_n ,_) ,_ ,_)) ,_)
    (check-equal? (primary src) s_n)]))

(test-case
 "E-SUR-017 compares the label set at the body; order does not matter"
 (define missing "trait Foo { a: Int, b: Int }\nimpl Foo for Int { a: 1 }\n0")
 (check-equal? (code missing) "E-SUR-017")
 (match (parse-src missing)
   [`(SProgram ,_ (,_ (SImplDecl ,_ ,_ ,_ (SRec ,s_b ,_))) ,_)
    (check-equal? (primary missing) s_b)])
 (check-true (lowered? (lower "trait Foo { a: Int, b: Int }\nimpl Foo for Int { b: 2, a: 1 }\n0")))
 (check-equal? (code "trait Foo { a: Int }\nimpl Foo for Int { a: 1, a: 2 }\n0") "E-SUR-017"))

(test-case
 "E-SUR-014 at the target type, against the canonical rows and the explicit base"
 (define src "impl Printable for Int { print: fn(x: Int) -> String { \"i\" } }\n0")
 (check-equal? (code src) "E-SUR-014")
 (match (parse-src src)
   [`(SProgram ,_ ((SImplDecl ,_ ,_ ,ty ,_)) ,_)
    (check-equal? (primary src) (second ty))])
 (define bool-src (string-append sizable-bool "0"))
 (check-true (lowered? (lower bool-src)))
 (check-equal? (code bool-src (base+ #:impl (list user-sizable-bool))) "E-SUR-014")
 (check-equal? (code (string-append sizable-bool sizable-bool "0")) "E-SUR-014"))

(test-case
 "E-SUR-016 when a new origin id collides with the base"
 (define src "trait Foo { f: Int }\n0")
 (define base (base+ #:trait '((o-trait-user-Foo Bar root ((f Int imm))))))
 (check-equal? (code src base) "E-SUR-016")
 (match (parse-src src)
   [`(SProgram ,_ ((STraitDecl ,s ,_ ,_)) ,_)
    (check-equal? (primary src base) s)]))

(test-case
 "E-SUR-016 when a new primitive name collides with the base"
 (define src "impl Sizable for Unit { size: fn(x: Unit) -> Int { 0 } }\n0")
 (define base (base+ #:impl '((o-x impl-user-Sizable-1 impl Sizable Bool root))))
 (check-equal? (code src base) "E-SUR-016")
 (match (parse-src src)
   [`(SProgram ,_ ((SImplDecl ,s ,_ ,_ ,_)) ,_)
    (check-equal? (primary src base) s)]))

(test-case
 "Self outside a trait is an unknown type name"
 (check-equal? (code "impl Sizable for Self { size: fn(x: Int) -> Int { 0 } }\n0") "E-SUR-008"))

(define showable-src
  (string-append
   "trait Showable { show: fn(Self) -> String }\n"
   "impl Showable for Int { show: fn(x: Int) -> String { \"i\" } }\n"
   "0"))

;; search-trait-integration-test.rkt の同名ヘルパーと同じ判定である。
(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) 40)
    [`(cfg ,result () () () ()) result]
    [other (fail-check (format "unexpected run-g2 result: ~s" other))]))

;; 宣言 1 つ分の Let が束縛する項、つまり impl primitive の適用を返す。
(define (bound-of core)
  (match core
    [`(Let ,_ ,bound ,_) bound]
    [other (fail-check (format "not a Let: ~s" other))]))

;; 停止した構成が、名前 name の impl primitive の適用を残しているか。
(define (stuck-at-impl? config name)
  (let walk ([t config])
    (match t
      [`(Apply (PrimVal ,_ ,(== name)) ,_) #t]
      [(cons a d) (or (walk a) (walk d))]
      [_ #f])))

;; 既定の表へ trait 行と impl 行を足した台帳。構築の失敗は試験の誤りなので例外にする。
(define (ledger-with #:trait [trait-rows '()] #:impl [impl-rows '()])
  (define (fail reason kind key)
    (error 'ledger-with "~s ~s ~s" reason kind key))
  (define env
    (make-trait-env
     #:trait (append (trait-env-trait-rows canonical-trait-env) trait-rows)
     #:impl (append (trait-env-impl-rows canonical-trait-env) impl-rows)
     #:intersect (trait-env-intersect-rows canonical-trait-env)
     #:scope (trait-env-scope-rows canonical-trait-env)
     #:fail fail))
  (make-trait-ledger env #:fail fail))

(define (compile-showable)
  (define r (compile-source/string 'src showable-src))
  (unless (compiled? r)
    (fail-check (format "compile failed: ~s" r)))
  r)

(test-case
 "a declared impl yields an Implements proof under the returned ledger"
 (define r (compile-showable))
 (define core (erase-core (compiled-core r)))
 (call-with-trait-ledger
  (compiled-ledger r)
  (λ ()
    (define row (impl-row-by-name 'impl-user-Showable-1 (current-trait-env)))
    (check-not-false row)
    (define proof (run-g2-core (bound-of core)))
    (check-equal? proof
                  `(ProofRep ,(impl-derived-origin row) (Implements Int Showable)))
    (check-equal? (term (verify-origins ,(current-R0) ,proof)) 'ok)
    (check-equal? (run-g2-core core) 0))))

(test-case
 "without the returned ledger the impl application is stuck"
 (define r (compile-showable))
 (define bound (bound-of (erase-core (compiled-core r))))
 (define result (run-g2 (inject-g2 bound) 40))
 (check-false (match result [`(cfg (ProofRep ,_ ,_) ,_ ...) #t] [_ #f]))
 (check-true (stuck-at-impl? result 'impl-user-Showable-1)))

(test-case
 "typing, configuration and search see the returned ledger"
 (define r (compile-showable))
 (define core (erase-core (compiled-core r)))
 (define callables (compiled-callables r))
 (define goal (make-goal '(Implements Int Showable)))
 (call-with-trait-ledger
  (compiled-ledger r)
  (λ ()
    (check-equal? (core-type-of core '() callables) (list 'Int '()))
    (check-true (config-ok? (inject-g2 core) callables 'Int '()))
    (check-false (null? (project-goal (current-Γ-pc0) '(root) goal)))))
 (check-equal? (core-type-of core '() callables) 'ill-typed)
 (check-equal? (project-goal (current-Γ-pc0) '(root) goal) '()))

(test-case
 "the base env is the outer ledger"
 (define r
   (call-with-trait-ledger
    (ledger-with #:trait '((o-trait-user-Legacy Legacy root ())))
    compile-showable))
 (define env (trait-ledger-env (compiled-ledger r)))
 (check-not-false (trait-row-by-name 'Legacy env))
 (check-not-false (trait-row-by-name 'Showable env))
 (check-not-false (trait-row-by-name 'Printable env)))

(test-case
 "a source without declarations keeps the outer ledger"
 (define r (compile-source/string 'src "0"))
 (check-true (compiled? r))
 (check-eq? (compiled-ledger r) canonical-trait-ledger)
 (define outer (ledger-with #:trait '((o-trait-user-Legacy Legacy root ()))))
 (define r2
   (call-with-trait-ledger
    outer
    (λ () (compile-source/string 'src "0"))))
 (check-eq? (compiled-ledger r2) outer))

(test-case
 "an origin-id collision with the base env is E-SUR-016 at the declaration"
 (define r
   (call-with-trait-ledger
    (ledger-with #:trait '((o-trait-user-Foo Legacy root ())))
    (λ () (compile-source/string 'src "trait Foo { }\n0"))))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-id r) "E-SUR-016")
 (check-equal? (diagnostic-primary-span r) '(#:span src 0 13)))

;; make-trait-env は通り、make-trait-ledger の Γ0 重複で落ちる衝突である。
(test-case
 "a trait constant colliding with a base impl primitive is E-SUR-016 at the declaration"
 (define r
   (call-with-trait-ledger
    (ledger-with #:impl '((o-x Foo-trait impl Sizable Bool root)))
    (λ () (compile-source/string 'src "trait Foo { }\n0"))))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-id r) "E-SUR-016")
 (check-equal? (diagnostic-primary-span r) '(#:span src 0 13)))

(test-case
 "a field type mismatch is left to typing, not E-SUR-017"
 (define r
   (compile-source/string
    'src
    (string-append
     "trait Showable { show: fn(Self) -> String }\n"
     "impl Showable for Int { show: fn(x: Int) -> Int { x } }\n"
     "0")))
 (check-true (diagnostic? r))
 (check-not-equal? (diagnostic-id r) "E-SUR-017"))

(test-case
 "record, function and nested function target types compile"
 (for ([impl (in-list
              (list
               "impl Named for { n: Int } { name: fn(r: { n: Int }) -> String { \"r\" } }\n"
               "impl Named for fn(Int) -> Int { name: fn(f: fn(Int) -> Int) -> String { \"f\" } }\n"
               (string-append
                "impl Named for { g: fn(Int) -> Int } "
                "{ name: fn(r: { g: fn(Int) -> Int }) -> String { \"g\" } }\n")))])
   (define r
     (compile-source/string
      'src (string-append "trait Named { name: fn(Self) -> String }\n" impl "0")))
   (check-true (compiled? r) (format "~a=> ~s" impl r))))

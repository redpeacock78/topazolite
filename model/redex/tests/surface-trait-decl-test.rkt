#lang racket

;; SUR-010。trait と impl の宣言が行と項へ落ちることの回帰である。

(require rackunit
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../traits.rkt"
         "../diagnostic.rkt")

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

(define sizable-bool "impl Sizable for Bool { size: fn(x: Bool) Int { 0 } }\n")
(define user-sizable-bool '(o-impl-user-Sizable-1 impl-user-Sizable-1 impl Sizable Bool root))

(test-case
 "a trait declaration becomes a root trait row with a normalized field row"
 (define low (lower "trait Foo { b: Int, a: fn(Self) Int }\n0"))
 (check-equal? (lowered-trait-rows low)
               '((o-trait-user-Foo Foo root
                  ((a (NFn (Self) Int () () () User) imm) (b Int imm)))))
 (check-match (lowered-term low) `(#:lit 0 ,_)))

(test-case
 "record types inside a template are normalized too"
 (define low (lower "trait Foo { f: fn({ b: Int, a: Int }) Int }\n0"))
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
                           (lower "impl Sizable for Unit { size: fn(x: Unit) Int { 0 } }\n0" base)))
               '(o-impl-user-Sizable-2)))

(test-case
 "impl numbering skips base suffixes that are not ASCII digit strings"
 (define base
   (base+ #:impl '((o-impl-user-Sizable-1/2 impl-user-Sizable-x impl Sizable Bool root))))
 (check-equal? (map first (lowered-impl-rows
                           (lower "impl Sizable for Unit { size: fn(x: Unit) Int { 0 } }\n0" base)))
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
 (define src "trait Printable { print: fn(Self) String }\n0")
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
 (define src "impl PrintableSizable for Bool { print: fn(x: Bool) String { \"b\" }, size: fn(x: Bool) Int { 0 } }\n0")
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
 (define src "impl Printable for Int { print: fn(x: Int) String { \"i\" } }\n0")
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
 (define src "impl Sizable for Unit { size: fn(x: Unit) Int { 0 } }\n0")
 (define base (base+ #:impl '((o-x impl-user-Sizable-1 impl Sizable Bool root))))
 (check-equal? (code src base) "E-SUR-016")
 (match (parse-src src)
   [`(SProgram ,_ ((SImplDecl ,s ,_ ,_ ,_)) ,_)
    (check-equal? (primary src base) s)]))

(test-case
 "Self outside a trait is an unknown type name"
 (check-equal? (code "impl Sizable for Self { size: fn(x: Int) Int { 0 } }\n0") "E-SUR-008"))

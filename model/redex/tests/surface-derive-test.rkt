#lang racket

;; SUR-005。derive 宣言が生成規則から impl と同じ行と項へ落ちることの回帰である。

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
         "../origins.rkt")

(define (parse-src str) (parse (lex/string 'src str)))
(define (lower str [base canonical-trait-env])
  (lower-surface (parse-src str) base))
(define (code str [base canonical-trait-env])
  (define r (lower str base))
  (and (diagnostic? r) (diagnostic-id r)))
(define (primary str [base canonical-trait-env])
  (diagnostic-primary-span (lower str base)))

(define (base+ #:trait [trait-rows '()] #:impl [impl-rows '()])
  (make-trait-env
   #:trait (append (trait-env-trait-rows canonical-trait-env) trait-rows)
   #:impl (append (trait-env-impl-rows canonical-trait-env) impl-rows)
   #:intersect (trait-env-intersect-rows canonical-trait-env)
   #:scope (trait-env-scope-rows canonical-trait-env)
   #:fail (λ (r k key) (error 'test "bad base ~s ~s ~s" r k key))))

(define (impl-sizable target value)
  (format "impl Sizable for ~a { size: fn(x: ~a) -> Int { ~a } }\n"
          target target value))

(define (derive-size src)
  (match (lowered-term (lower src))
    [`(Let ,_ ,_
           (Apply ,_ ,_ (Rec ,_ (((#:lbl size ,_) imm
                                  (Fn ,_ ,_ ,_ ,_ (#:lit ,n ,_))))))
           ,_)
     n]
    [other (fail-check (format "unexpected derive term ~s" other))]))

(test-case
 "SUR-005: Sizable の size は正規化した対象型の葉の数である"
 (check-equal? (derive-size "derive Sizable for Bool\n0") 1)
 (check-equal? (derive-size "derive Sizable for Unit\n0") 1)
 (check-equal? (derive-size "derive Sizable for fn(Int) -> Int\n0") 1)
 (check-equal? (derive-size "derive Sizable for {}\n0") 0)
 (check-equal? (derive-size "derive Sizable for { a: Int, b: { c: Bool, d: String } }\n0") 3)
 (check-equal? (derive-size "type P = { a: Int, b: Bool }\nderive Sizable for P\n0") 2))

(test-case
 "SUR-005: 欄の順序を入れ替えた record は同じ値と同じ行になる"
 (define ab "derive Sizable for { a: Int, b: String }\n0")
 (define ba "derive Sizable for { b: String, a: Int }\n0")
 (check-equal? (derive-size ab) 2)
 (check-equal? (derive-size ab) (derive-size ba))
 (check-equal? (impl-target-type (first (lowered-impl-rows (lower ab))))
               (impl-target-type (first (lowered-impl-rows (lower ba))))))

(test-case
 "SUR-005: derive の行と名前の span は宣言全体を指す"
 (define src "derive Sizable for Bool\n0")
 (define low (lower src))
 (check-equal? (lowered-impl-rows low)
               '((o-derive-user-Sizable-1 derive-user-Sizable-1 derive
                  Sizable Bool root)))
 (match (parse-src src)
   [`(SProgram ,_ ((SDeriveDecl ,s ,_ ,_)) ,_)
    (check-equal? (hash-ref (lowered-spans low)
                            '(origin-id . o-derive-user-Sizable-1))
                  s)
    (check-equal? (hash-ref (lowered-spans low)
                            '(primitive-name . derive-user-Sizable-1))
                  s)]))

(test-case
 "SUR-005: derive の Apply と生成 record は宣言 span を使う"
 (define src "derive Sizable for Bool\n0")
 (define low (lower src))
 (define-values (decl-span tail-span)
   (match (parse-src src)
     [`(SProgram ,_ ((SDeriveDecl ,s ,_ ,_)) (SInt ,s0 0)) (values s s0)]))
 (match (lowered-term low)
   [`(Let ,s_tail ((#:bind %derive-Sizable-1 ,binder-span) const)
          (Apply ,apply-span (#:var derive-user-Sizable-1 ,var-span)
                 (Rec ,rec-span (((#:lbl size ,label-span) imm
                                  (Fn ,fn-span
                                      (((#:bind %self ,self-span)
                                        (#:ty Bool ,self-type-span)))
                                      (#:ty Int ,result-span) (#:ef () ,effect-span)
                                      (#:lit 1 ,literal-span))))))
          (#:lit 0 ,tail-literal-span))
    (check-equal? s_tail (list '#:span 'src (third decl-span) (fourth tail-span)))
    (for ([span (in-list (list binder-span apply-span var-span rec-span label-span
                               fn-span self-span self-type-span result-span
                               effect-span literal-span))])
      (check-equal? span decl-span))
    (check-equal? tail-literal-span tail-span)]))

(define (derive-origin-collision)
  (base+ #:trait '((o-derive-user-Sizable-1 Other root ((size Int imm))))))

(define (derive-primitive-collision)
  (base+ #:impl '((o-impl-user-Sizable-9 derive-user-Sizable-1
                   derive Sizable Unit root))))

(test-case
 "SUR-005: derive の診断は spec §6.5 の順序と span を保つ"
 (define missing-trait "derive Nope for Nope2\n0")
 (check-equal? (code missing-trait) "E-SUR-015")
 (match (parse-src missing-trait)
   [`(SProgram ,_ ((SDeriveDecl ,_ (SName ,s_n Nope) ,_)) ,_)
    (check-equal? (primary missing-trait) s_n)])

 (define composite "derive PrintableSizable for Bool\n0")
 (check-equal? (code composite) "E-SUR-018")
 (match (parse-src composite)
   [`(SProgram ,_ ((SDeriveDecl ,_ (SName ,s_n PrintableSizable) ,_)) ,_)
    (check-equal? (primary composite) s_n)])

 (define unknown-type "derive Sizable for Nope\n0")
 (check-equal? (code unknown-type) "E-SUR-008")
 (match (parse-src unknown-type)
   [`(SProgram ,_ ((SDeriveDecl ,_ ,_ (TName ,s_t Nope))) ,_)
    (check-equal? (primary unknown-type) s_t)])

 (define no-recipe "derive Printable for Bool\n0")
 (check-equal? (code no-recipe) "E-SUR-019")
 (match (parse-src no-recipe)
   [`(SProgram ,_ ((SDeriveDecl ,s ,_ ,_)) ,_)
    (check-equal? (primary no-recipe) s)])

 (define duplicate "derive Sizable for { a: Int }\nderive Sizable for { a: Int }\n0")
 (check-equal? (code duplicate) "E-SUR-014")
 (match (parse-src duplicate)
   [`(SProgram ,_ (,_ (SDeriveDecl ,_ ,_ ,ty)) ,_)
    (check-equal? (primary duplicate) (second ty))])

 (define oid-collision "derive Sizable for Bool\n0")
 (check-equal? (code oid-collision
                     (derive-origin-collision))
               "E-SUR-016")
 (check-equal? (primary oid-collision
                        (derive-origin-collision))
               '(#:span src 0 23))

 (check-equal? (code oid-collision
                     (derive-primitive-collision))
               "E-SUR-016")
 (check-equal? (primary oid-collision
                        (derive-primitive-collision))
               '(#:span src 0 23)))

(test-case
 "SUR-005: derive は trait が無い誤りを対象型より先に報告する"
 (check-equal? (code "derive Nope for Nope2\n0") "E-SUR-015"))

(test-case
 "SUR-005: impl、derive、kernel の同じ対象型を重複として拒否する"
 (define derive-twice "derive Sizable for Bool\nderive Sizable for Bool\n0")
 (check-equal? (code derive-twice) "E-SUR-014")
 (check-equal? (code (string-append (impl-sizable "Bool" 0)
                                    "derive Sizable for Bool\n0"))
               "E-SUR-014")
 (check-equal? (code (string-append "derive Sizable for Bool\n"
                                    (impl-sizable "Bool" 0) "0"))
               "E-SUR-014")
 (check-equal? (code "derive Sizable for Int\n0") "E-SUR-014"))

(test-case
 "SUR-005: impl と derive は番号を独立に付ける"
 (define low (lower (string-append (impl-sizable "Bool" 0)
                                   "derive Sizable for Unit\n0")))
 (check-equal? (map impl-oid (lowered-impl-rows low))
               '(o-impl-user-Sizable-1 o-derive-user-Sizable-1)))

(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) 40)
    [`(cfg ,result () () () ()) result]
    [other (fail-check (format "unexpected run-g2 result: ~s" other))]))

(define (bound-of core)
  (match core
    [`(Let ,_ ,bound ,_) bound]
    [other (fail-check (format "not a Let: ~s" other))]))

(define (ledger-with #:trait [trait-rows '()] #:impl [impl-rows '()])
  (define (fail reason kind key) (error 'ledger-with "~s ~s ~s" reason kind key))
  (define env
    (make-trait-env
     #:trait (append (trait-env-trait-rows canonical-trait-env) trait-rows)
     #:impl (append (trait-env-impl-rows canonical-trait-env) impl-rows)
     #:intersect (trait-env-intersect-rows canonical-trait-env)
     #:scope (trait-env-scope-rows canonical-trait-env)
     #:fail fail))
  (make-trait-ledger env #:fail fail))

(test-case
 "SUR-005: derive の Proof は返された台帳の下で正規に検証される"
 (define src "derive Sizable for Bool\n0")
 (define r (compile-source/string 'src src))
 (check-true (compiled? r) (format "compile failed: ~s" r))
 (define core (erase-core (compiled-core r)))
 (call-with-trait-ledger
  (compiled-ledger r)
  (λ ()
    (define row (impl-row-by-name 'derive-user-Sizable-1 (current-trait-env)))
    (check-not-false row)
    (define proof (run-g2-core (bound-of core)))
    (check-equal? proof
                  `(ProofRep ,(impl-derived-origin row) (Implements Bool Sizable)))
    (check-equal? (term (verify-origins ,(current-R0) ,proof)) 'ok)
    (check-equal? (run-g2-core core) 0))))

(test-case
 "SUR-005: 同じ要求形の利用者 trait は Sizable の recipe を借りない"
 (check-equal? (code (string-append
                       "trait MySizable { size: fn(Self) -> Int }\n"
                       "derive MySizable for Bool\n0"))
               "E-SUR-019"))

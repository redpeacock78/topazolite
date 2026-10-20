#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../parser.rkt"
         "../span-core.rkt"
         "../surface.rkt"
         "../typing.rkt"
         "../lexer.rkt")

(define (compile source) (compile-source/string 'src source))
(define (compile-code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))
(define (compile-primary source)
  (diagnostic-primary-span (compile source)))
(define (run-source source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (and (compiled? result)
       (call-with-trait-ledger
        (compiled-ledger result)
        (lambda ()
          (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
            [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
            [other (fail-check (format "terminal config expected, got ~s" other))])))))
(define (p-expr source)
  (match (parse (lex/string 'src source))
    [`(SProgram ,_ ,_ ,expr) expr]
    [other other]))
(define (slo n) `(#:span src ,n ,(add1 n)))

(test-case "P1 結合と優先順位"
  (check-equal? (run-source "1 + 2 * 3") 7)
  (check-equal? (run-source "1 - 2 - 3") -4)
  (check-equal? (run-source "- - 3") 3)
  (check-equal? (run-source "not 1 < 2") '(Construct Bool false))
  (check-equal? (run-source "true and false or true") '(Construct Bool true)))

(test-case "P2 比較は結合しない"
  (check-equal? (compile-code "1 < 2 < 3") "E-SUR-005")
  (check-equal? (diagnostic-primary-span (compile "1 < 2 < 3")) '(#:span src 6 7))
  (check-equal? (compile-code "1 == 2 >= 3") "E-SUR-005"))

(test-case "P2b 空白を挟んだ > = は >= にならない"
  (check-equal? (compile-code "1 > = 2") "E-SUR-005")
  (check-equal? (run-source "2 >= 2") '(Construct Bool true)))

(test-case "P3 pipe と演算式"
  (check-match (p-expr "x + 1 |> f")
               `(SApply ,_ (SVar ,_ f)
                        ((SApply ,_ (SVar ,_ %op-add) ((SVar ,_ x) (SInt ,_ 1))))))
  (check-match (p-expr "x |> f + 1")
               `(SApply ,_ (SApply ,_ (SVar ,_ %op-add) ((SVar ,_ f) (SInt ,_ 1)))
                        ((SVar ,_ x))))
  (check-match (p-expr "x |> (f + 1)")
               `(SApply ,_ (SApply ,_ (SVar ,_ %op-add) ((SVar ,_ f) (SInt ,_ 1)))
                        ((SVar ,_ x))))
  (check-match (p-expr "x |> g(a) + 1")
               `(SApply ,_ (SApply ,_ (SVar ,_ %op-add)
                                      ((SApply ,_ (SVar ,_ g) ((SVar ,_ a))) (SInt ,_ 1)))
                        ((SVar ,_ x))))
  (check-match (p-expr "x |> not f")
               `(SApply ,_ (SBoolIf ,_ (SVar ,_ f) (SBool ,_ false) (SBool ,_ true))
                        ((SVar ,_ x)))))

(test-case "P4 括弧の無い既存の pipe は変わらない"
  (check-match (p-expr "x |> f") `(SApply ,_ (SVar ,_ f) ((SVar ,_ x))))
  (check-match (p-expr "x |> f(a)")
               `(SApply ,_ (SVar ,_ f) ((SVar ,_ x) (SVar ,_ a))))
  (check-match (p-expr "x |> g(1)(2)")
               `(SApply ,_ (SApply ,_ (SVar ,_ g) ((SInt ,_ 1)))
                        ((SVar ,_ x) (SInt ,_ 2))))
  (check-match (p-expr "x |> f |> g")
               `(SApply ,_ (SVar ,_ g) ((SApply ,_ (SVar ,_ f) ((SVar ,_ x)))))))

(test-case "P4b 括弧で包んだ右辺には差し込まない"
  (check-match (p-expr "x |> (g(a))")
               `(SApply ,_ (SApply ,_ (SVar ,_ g) ((SVar ,_ a))) ((SVar ,_ x))))
  (check-match (p-expr "x |> (y |> f)")
               `(SApply ,_ (SApply ,_ (SVar ,_ f) ((SVar ,_ y))) ((SVar ,_ x)))))

(test-case "P5 二項演算子の前後の改行"
  (check-equal? (compile-code "let a = 1 +\n2\na") "E-SUR-005")
  (check-equal? (run-source "let a = 5\na\n-a") -5))

(test-case "P6 条件と scrutinee の直後の {"
  (check-equal? (run-source "let a = 1\nlet b = 2\nif a < b { 10 } else { 20 }") 10)
  (check-equal? (run-source "let a = 2\nwhen a == 2 { true => 7\n false => 8 }") 7))

(test-case "K1 予約語 and or not は束縛名と欄の名前に使えない"
  (for ([source (in-list '("let not = 1\n0" "fn and() { 0 }\n0" "{ or: 1 }"))])
    (define result (parse (lex/string 'src source)))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-SUR-005")))
  (for ([word (in-list '(and or not))])
    (check-false (redex-match? Surface ident word))
    (check-false (redex-match? Surface label word))
    (check-false (surface-expr? `(SVar ,(slo 0) ,word)))
    (check-false (surface-expr? `(SProj ,(slo 0) (SVar ,(slo 0) x)
                                  (SLabel ,(slo 0) ,word))))))

(test-case "C1 同名の束縛は演算子を捕獲しない"
  (check-equal? (run-source "let add = 100\n1 + 2") 3)
  (check-equal? (run-source "fn lt(a: Int, b: Int) -> Bool { return false }\n1 < 2")
                '(Construct Bool true)))

(test-case "E1 > と >= は被演算子を原文の順に評価する"
  (check-equal? (run-source "fn f() -> Int { let ignored = (return 1) > (return 2)\n return 3 }\nf()") 1)
  (check-equal? (run-source "fn f() -> Int { let ignored = (return 1) >= (return 2)\n return 3 }\nf()") 1)
  (check-match (p-expr "left() > right()")
               `(SBlock ,_ ((SBind ,_ const (SName ,_ %cmp-l) #:none (SApply ,_ ,_ ()))
                            (SBind ,_ const (SName ,_ %cmp-r) #:none (SApply ,_ ,_ ())))
                        (SApply ,_ (SVar ,_ %op-lt)
                                 ((SVar ,_ %cmp-r) (SVar ,_ %cmp-l))))))

(test-case "S1 and と or は短絡する"
  (check-equal? (run-source "fn f() -> Int {\n let b = false and (return 1)\n return 2\n}\nf()") 2)
  (check-equal? (run-source "fn f() -> Int {\n let b = true or (return 1)\n return 2\n}\nf()") 2))

(test-case "S2 and の中の leave は外側の境界へ届く"
  (check-equal? (run-source
                 "fn f(c: Bool) -> Option<Bool> { let result = if c { true and leave false\n leave true }\n return result }\nf(true)")
                '(Construct (Option Bool) some (Construct Bool false))))

(test-case "T1 型の拒否"
  (check-equal? (compile-code "1 + true") "E-TYP-012")
  (check-equal? (compile-primary "1 + true") '(#:span src 4 8))
  (check-equal? (compile-code "true and 1") "E-TYP-012")
  (check-equal? (compile-primary "true and 1") '(#:span src 9 10))
  (check-equal? (compile-code "1 and true") "E-DAT-003")
  (check-equal? (compile-primary "1 and true") '(#:span src 0 10))
  (check-equal? (compile-code "\"a\" == \"a\"") "E-TYP-012")
  (check-equal? (compile-primary "\"a\" == \"a\"") '(#:span src 0 3)))

(test-case "V1 各演算子の値"
  (check-equal? (run-source "7 - 2") 5)
  (check-equal? (run-source "-7") -7)
  (check-equal? (run-source "3 * 4") 12)
  (check-equal? (run-source "1 == 1") '(Construct Bool true))
  (check-equal? (run-source "1 != 1") '(Construct Bool false))
  (check-equal? (run-source "1 != 2") '(Construct Bool true))
  (check-equal? (run-source "1 <= 1") '(Construct Bool true))
  (check-equal? (run-source "2 > 1") '(Construct Bool true))
  (check-equal? (run-source "1 >= 2") '(Construct Bool false))
  (check-equal? (run-source "not false") '(Construct Bool true)))

(test-case "I1 文字列補間の中の演算式"
  (check-true (compiled? (compile "let a = 1\n\"#{a + 1}\""))))

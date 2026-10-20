#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../diagnostic.rkt"
         "../traits.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt")

;; P2m3a。data 型の when の名前解決、lowering、elaborate である。
(define (lower str) (lower-surface (parse (lex/string 'src str)) canonical-trait-env))
(define (term str) (lowered-term (lower str)))
(define (find-form tree wanted)
  (cond [(and (pair? tree) (eq? (car tree) wanted)) tree]
        [(pair? tree) (for/or ([child (in-list tree)]) (find-form child wanted))]
        [else #f]))
(define (compile str) (compile-source/string 'src str))
(define (compile-code str)
  (define result (compile str))
  (and (diagnostic? result) (diagnostic-id result)))
(define (ok? str) (compiled? (compile str)))

(define (check-full-when-diagnostic-span prefix when-expression suffix code)
  (define result (compile (string-append prefix when-expression suffix)))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) code)
    (check-equal? (diagnostic-primary-span result)
                  `( #:span src ,(string-length prefix)
                     ,(+ (string-length prefix) (string-length when-expression))))))

(define color "type Color =\n  | red\n  | green\n  | leaf\n")
(define pair "type Pair<A> =\n  | pair<A, A>\n")
(define nat "type Nat =\n  | zero\n  | succ<Nat>\n")

(test-case "when は NarrativeExpr の Eliminate へ下りる"
  (check-match (term (string-append nat
                                   "when c {\n  zero => zero\n  succ m => m\n}"))
               `(NarrativeExpr ,_
                  (Eliminate ,_ (#:var c ,_)
                             ((,_ zero () -> (Construct ,_ zero (Types)))
                              (,_ succ ((#:bind m ,_)) -> (#:var m ,_)))))))
  ;; scrutinee、constructor の値、枝の本体を同じ resolver が走査する。
  (check-match (term (string-append nat
                                   "when succ(zero) {\n"
                                   "  zero => succ(zero)\n"
                                   "  succ m => m\n"
                                   "}"))
               `(Eliminate ,_
                           (Construct ,_ succ (Types) (Construct ,_ zero (Types)))
                           ((,_ zero () -> (NarrativeExpr ,_ (Construct ,_ succ (Types) (Construct ,_ zero (Types)))))
                            (,_ succ ((#:bind m ,_)) -> (NarrativeExpr ,_ (#:var m ,_))))))

(test-case "枝の束縛子は本体で同名 constructor を隠す"
  (check-match
   (find-form (term (string-append nat
                                   "fn f(n: Nat) -> Nat {\n"
                                   "  return when n {\n    zero => zero\n    succ zero => zero\n  }\n"
                                   "}\nf(zero)")) 'Eliminate)
   `(Eliminate ,_ ,_
               ((,_ zero () -> (Construct ,_ zero (Types)))
                (,_ succ ((#:bind zero ,_)) -> (#:var zero ,_))))))

(test-case "枝の頭は外側の束縛を無視して constructor として読む"
  (check-match
   (find-form (term (string-append color
                                   "fn f(c: Color) -> Int {\n"
                                   "  let red = 5\n"
                                   "  return when c {\n    red => red\n    green => 2\n    leaf => 3\n  }\n"
                                   "}\nf(red)")) 'Eliminate)
   `(Eliminate ,_ (#:var c ,_)
                ((,_ red () -> (#:var red ,_))
                (,_ green () -> (#:lit 2 ,_))
                (,_ leaf () -> (#:lit 3 ,_))))))

(test-case "単相、generic、再帰 data、Bool の when を受理する"
  (check-true (ok? (string-append color
                                  "fn f(c: Color) -> Int {\n"
                                  "  return when c {\n    red => 1\n    green => 2\n    leaf => 3\n  }\n"
                                  "}\nf(green)")))
  (check-true (ok? (string-append pair
                                  "fn fst(p: Pair<Int>) -> Int {\n"
                                  "  return when p { pair a b => a }\n"
                                  "}\nfst(pair(1, 2))")))
  (check-true (ok? (string-append nat
                                  "fn pred(n: Nat) -> Nat {\n"
                                  "  return when n {\n    zero => zero\n    succ m => m\n  }\n"
                                  "}\npred(succ(zero))")))
  (check-true (ok? "fn invert(b: Bool) -> Bool {\n  return when b {\n    true => false\n    false => true\n  }\n}\ninvert(true)")))

(test-case "注釈付き束縛は when を check し、注釈なし when は synth する"
  (check-true (ok? (string-append color
                                  "const c = green\n"
                                  "const n: Int = when c {\n  red => 1\n  green => 2\n  leaf => 3\n}\n"
                                  "n")))
  (define inferred
    (compile (string-append color
                            "const c = green\n"
                            "let n = when c {\n  red => 1\n  green => 2\n  leaf => 3\n}\n"
                            "n")))
  (check-true (compiled? inferred))
  (check-equal? (compiled-type inferred) 'Int))

(test-case "枝が期待型を要する注釈なし when は E-TYP-004 になる"
  ;; some/none の型引数を決める期待型がないため、synth の事前検査で拒否する。
  (check-equal? (compile-code "let n = when true {\n  true => some(1)\n  false => none\n}\nn")
                "E-TYP-004"))

(test-case "when の網羅性、枝の束縛子、scrutinee は既存診断を使う"
  (define (program arms)
    (string-append color
                   "fn f(c: Color) -> Int {\n"
                   "  when c {\n    " arms "\n  }\n"
                   "}\nf(red)"))
  (check-equal? (compile-code (program "red => 1\ngreen => 2")) "E-DAT-004")
  (check-equal? (compile-code (program "red => 1\nred => 1\ngreen => 2\nleaf => 3"))
                "E-DAT-004")
  (check-equal? (compile-code (program "red => 1\ngreen => 2\nnope => 3")) "E-DAT-004")
  (check-equal? (compile-code (program "_ => 1")) "E-DAT-004")
  (check-equal? (compile-code (program "red x => 1\ngreen => 2\nleaf => 3")) "E-SYN-002")
  (check-equal? (compile-code (string-append pair
                                             "fn g(p: Pair<Int>) -> Int {\n"
                                             "  when p { pair a a => a }\n"
                                             "}\ng(pair(1, 2))"))
                "E-SYN-002")
  (check-equal? (compile-code "fn h(n: Int) -> Int {\n  when n { zero => 0 }\n}\nh(1)")
                "E-DAT-003"))

(test-case "elaborate の when 診断は when 全体を primary span にする"
  (check-full-when-diagnostic-span
   "fn h(n: Int) -> Int {\n  "
   "when n {\n    zero => 0\n  }"
   "\n}\nh(1)"
   "E-DAT-003")
  (check-full-when-diagnostic-span
   (string-append color "fn f(c: Color) -> Int {\n  ")
   "when c {\n    red => 1\n  }"
   "\n}\nf(red)"
   "E-DAT-004")
  (check-full-when-diagnostic-span
   (string-append color "fn f(c: Color) -> Int {\n  ")
   "when c {\n    red x => 1\n    green => 2\n    leaf => 3\n  }"
   "\n}\nf(red)"
   "E-SYN-002")
  (check-full-when-diagnostic-span
   "let n = "
   "when true {\n  true => some(1)\n  false => none\n}"
   "\nn"
   "E-TYP-004"))

(test-case "when の評価結果を得る"
  (define result
    (compile (string-append color
                           "fn f(c: Color) -> Int {\n"
                           "  return when c {\n    red => 1\n    green => 2\n    leaf => 3\n  }\n"
                           "}\nf(green)")))
  (check-true (compiled? result))
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value ,_ ,_ ,_ ,_) (check-equal? value 2)]
       [other (fail-check (format "評価結果の config を期待したが ~s" other))]))))

#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../diagnostic.rkt"
         "../traits.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt")

;; P2m spec §6 と §7。data 型の match の名前解決、lowering、elaborate である。
(define (lower str) (lower-surface (parse (lex/string 'src str)) canonical-trait-env))
(define (term str) (lowered-term (lower str)))
(define (compile str) (compile-source/string 'src str))
(define (compile-code str)
  (define result (compile str))
  (and (diagnostic? result) (diagnostic-id result)))
(define (ok? str) (compiled? (compile str)))

(define color "type Color =\n  | red\n  | green\n  | leaf\n")
(define pair "type Pair<A> =\n  | pair<A, A>\n")
(define nat "type Nat =\n  | zero\n  | succ<Nat>\n")

(test-case "match は data constructor の Eliminate へ下りる"
  (check-match (term (string-append nat "match c { | zero => zero | succ(m) => m }"))
               `(Eliminate ,_ (#:var c ,_)
                           ((,_ zero () -> (Construct ,_ zero (Types)))
                            (,_ succ ((#:bind m ,_)) -> (#:var m ,_)))))
  ;; scrutinee、constructor の値、枝の本体を同じ resolver が走査する。
  (check-match (term (string-append nat "match succ(zero) { | zero => succ(zero) | succ(m) => m }"))
               `(Eliminate ,_ (Construct ,_ succ (Types) (Construct ,_ zero (Types)))
                           ((,_ zero () -> (Construct ,_ succ (Types) (Construct ,_ zero (Types))))
                            (,_ succ ((#:bind m ,_)) -> (#:var m ,_))))))

(test-case "枝の束縛子は本体で同名 constructor を隠す"
  (check-match (term (string-append nat
                                   "fn f(n: Nat) -> Nat {\n"
                                   "  match n { | zero => zero | succ(zero) => zero }\n"
                                   "}\nf(zero)"))
               `(FnDecl ,_ ,_ ,_ ,_ ,_
                        (Eliminate ,_ ,_
                                   ((,_ zero () -> (Construct ,_ zero (Types)))
                                    (,_ succ ((#:bind zero ,_)) -> (#:var zero ,_))))
                        ,_)))

(test-case "枝の頭は外側の束縛を無視して constructor として読む"
  (check-match (term (string-append color
                                   "fn f(c: Color) -> Int {\n"
                                   "  let red = 5\n"
                                   "  match c { | red => red | green => 2 | leaf => 3 }\n"
                                   "}\nf(red)"))
               `(FnDecl ,_ ,_ ,_ ,_ ,_
                        (Let ,_ ,_ (#:lit 5 ,_)
                             (Eliminate ,_ (#:var c ,_)
                                        ((,_ red () -> (#:var red ,_))
                                         (,_ green () -> (#:lit 2 ,_))
                                         (,_ leaf () -> (#:lit 3 ,_)))))
                        ,_)))

(test-case "単相、generic、再帰 data、Bool の match を受理する"
  (check-true (ok? (string-append color
                                  "fn f(c: Color) -> Int {\n"
                                  "  match c { | red => 1 | green => 2 | leaf => 3 }\n"
                                  "}\nf(green)")))
  (check-true (ok? (string-append pair
                                  "fn fst(p: Pair<Int>) -> Int {\n"
                                  "  match p { | pair(a, b) => a }\n"
                                  "}\nfst(pair(1, 2))")))
  (check-true (ok? (string-append nat
                                  "fn pred(n: Nat) -> Nat {\n"
                                  "  match n { | zero => zero | succ(m) => m }\n"
                                  "}\npred(succ(zero))")))
  (check-true (ok? "fn not(b: Bool) -> Bool {\n  match b { | true => false | false => true }\n}\nnot(true)")))

(test-case "注釈付き束縛は match を check し、省略注釈の束縛は E-TYP-004 になる"
  (check-true (ok? (string-append color
                                  "const c = green\n"
                                  "const n: Int = match c { | red => 1 | green => 2 | leaf => 3 }\n"
                                  "n")))
  (check-equal? (compile-code (string-append color
                                             "const c = green\n"
                                             "let n = match c { | red => 1 | green => 2 | leaf => 3 }\n"
                                             "n"))
                "E-TYP-004"))

(test-case "match の網羅性、枝の束縛子、scrutinee は既存診断を使う"
  (define (program arms)
    (string-append color
                   "fn f(c: Color) -> Int {\n"
                   "  match c { " arms " }\n"
                   "}\nf(red)"))
  (check-equal? (compile-code (program "| red => 1 | green => 2")) "E-DAT-004")
  (check-equal? (compile-code (program "| red => 1 | red => 1 | green => 2 | leaf => 3"))
                "E-DAT-004")
  (check-equal? (compile-code (program "| red => 1 | green => 2 | nope => 3")) "E-DAT-004")
  (check-equal? (compile-code (program "| _ => 1")) "E-DAT-004")
  (check-equal? (compile-code (program "| red(x) => 1 | green => 2 | leaf => 3")) "E-SYN-002")
  (check-equal? (compile-code (string-append pair
                                             "fn g(p: Pair<Int>) -> Int {\n"
                                             "  match p { | pair(a, a) => a }\n"
                                             "}\ng(pair(1, 2))"))
                "E-SYN-002")
  (check-equal? (compile-code "fn h(n: Int) -> Int {\n  match n { | zero => 0 }\n}\nh(1)")
                "E-DAT-003"))

(test-case "match の評価結果を得る"
  (define result
    (compile (string-append color
                           "fn f(c: Color) -> Int {\n"
                           "  match c { | red => 1 | green => 2 | leaf => 3 }\n"
                           "}\nf(green)")))
  (check-true (compiled? result))
  (match (run-g2 (inject-g2m (erase-core (compiled-core result))) 10000)
    [`(cfg ,value ,_ ,_ ,_ ,_) (check-equal? value 2)]
    [other (fail-check (format "評価結果の config を期待したが ~s" other))]))

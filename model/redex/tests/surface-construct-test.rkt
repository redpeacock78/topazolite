#lang racket

(require rackunit
         racket/match
         "../lexer.rkt"
         "../parser.rkt"
         "../surface.rkt"
         "../surface-lower.rkt"
         "../diagnostic.rkt"
         "../traits.rkt"
         "../driver.rkt")

;; P2l2b2 spec §12。constructor の式の名前解決と lowering である。
(define (lower str) (lower-surface (parse (lex/string 'src str)) canonical-trait-env))
(define (term str) (lowered-term (lower str)))
(define (compile str) (compile-source/string 'src str))
(define (compile-code str)
  (define r (compile str))
  (and (diagnostic? r) (diagnostic-id r)))
(define (ok? str) (not (diagnostic? (compile str))))

(define color "type Color =\n  | red\n  | green\n  | leaf\n")
(define pair "type Pair<A> =\n  | pair<A, A>\n")
(define nat "type Nat =\n  | zero\n  | succ<Nat>\n")
(define mk "type P =\n  | mk<Int>\n")

(test-case "型仮引数を持たない型の constructor は (Types) を持ち、期待型なしで合成できる"
  (check-match (term (string-append color "red"))
               `(Construct ,_ red (Types)))
  (check-true (ok? (string-append color "let c = red\nc")))
  (check-true (ok? (string-append mk "let p = mk(1)\np"))))

(test-case "leaf() は leaf と同じ 0 欄の構築である"
  ;; どちらも全体式の span が違うため、constructor の欄だけを比較する。
  (define (shape source)
    (match (term (string-append color source))
      [`(Construct ,_ ,parts ...) parts]))
  (check-equal? (shape "leaf()") (shape "leaf")))

(test-case "型仮引数を持つ型の constructor は期待型から型引数を決める"
  (check-match (term (string-append pair "pair(1, 2)"))
               `(Construct ,_ pair (#:lit 1 ,_) (#:lit 2 ,_)))
  (check-true (ok? (string-append pair "let p: Pair<Int> = pair(1, 2)\n0")))
  (check-equal? (compile-code (string-append pair "let p = pair(1, 2)\n0")) "E-TYP-003"))

(test-case "組み込みの constructor を式として適用できる"
  (check-true (ok? "let o: Option<Int> = some(1)\n0"))
  (check-true (ok? "let o: Option<Int> = none\n0"))
  (check-true (ok? "let l: List<Int> = cons(1, nil)\n0"))
  (check-true (ok? "let r: Result<Int, Unit> = ok(1)\n0"))
  (check-true (ok? "let r: Result<Int, Unit> = ng(())\n0"))
  (check-true (ok? "fn f(x: Option<Int>) -> Int { 0 }\nf(some(1))")))

(test-case "素の再帰欄を持つ型の値を入れ子の適用で作れる"
  (check-true (ok? (string-append nat "let n = succ(succ(zero))\nn"))))

(test-case "欄を持つ constructor の単独使用と個数の不一致は §9.3.7 の区分で拒否する"
  ;; 型仮引数を持たない型は期待型の有無にかかわらず arity-mismatch である。
  (check-equal? (compile-code (string-append mk "let p = mk\n0")) "E-ARI-001")
  (check-equal? (compile-code (string-append mk "let p: P = mk\n0")) "E-ARI-001")
  (check-equal? (compile-code (string-append color "let c = leaf(1)\n0")) "E-ARI-001")
  ;; 型仮引数を持つ型は期待型で分かれる。
  (check-equal? (compile-code (string-append pair "let p: Pair<Int> = pair\n0")) "E-ARI-001")
  (check-equal? (compile-code (string-append pair "let p = pair\n0")) "E-TYP-003")
  (check-equal? (compile-code (string-append pair "let p: Int = pair(1, 2)\n0")) "E-DAT-002")
  (check-equal? (compile-code "let o: Option<Int> | Int = some(1)\n0") "E-DAT-002")
  ;; 型仮引数を持たない型で欄の個数が合い、型が合わない場合は type-mismatch である。
  ;; elaborate の Construct-Types の check が返す type-mismatch である。
  (check-equal? (compile-code (string-append mk "let p: Int = mk(1)\n0")) "E-TYP-012"))

(test-case "局所の束縛子は constructor 名を隠し、let の右辺では隠さない"
  ;; 最上位の let の束縛子。
  (check-true (ok? (string-append color "let red = 1\nred")))
  (check-match (term (string-append color "let red = 1\nred"))
               `(Let ,_ ,_ ,_ (#:var red ,_)))
  ;; 右辺の red は constructor、継続の red は束縛子である。
  (check-match (term (string-append color "let red = red\nred"))
               `(Let ,_ ,_ (Construct ,_ red (Types)) (#:var red ,_)))
  ;; 組み込みの constructor と同名の最上位の let は E-SUR-032 にならない。
  (check-true (ok? "let some = 1\nsome"))
  ;; 関数の仮引数と => の仮引数は本体だけを隠す。
  (check-true (ok? (string-append color "fn f(red: Int) -> Int { red }\nf(1)")))
  (check-true (ok? (string-append color "let g = fn(red: Int) => red\ng(1)")))
  ;; block の中の let。
  (check-true (ok? (string-append color "{ let red = 1\n red }"))))

(test-case "局所の束縛子で隠した名前への適用は constructor にならない"
  (check-match (term (string-append color "fn f(red: fn(Int) -> Int) -> Int { red(1) }\n0"))
               `(FnDecl ,_ ,_ ,_ ,_ ,_ (Apply ,_ (#:var red ,_) ,_) ,_)))

(test-case "台帳に無い名前は constructor にならず、未束縛の変数の診断になる"
  (check-not-exn (λ () (compile "foo(1)")))
  (check-match (compile-code "foo(1)") (or "E-VAR-002" "E-VAR-006"))
  (check-match (compile-code "foo") (or "E-VAR-002" "E-VAR-006")))

(test-case "Absent は Surface の印ではなく通常の未束縛識別子である"
  (check-equal? (compile-code "Absent") "E-VAR-002"))

(test-case "関数の本体、impl の本体、record、射影の中の constructor を置き換える"
  (check-true (ok? (string-append color "fn f() -> Color { red }\nf()")))
  (check-true (ok? (string-append color "let r = { c: red }\nr.c")))
  (check-true (ok? (string-append color "impl Sizable for Color { size: fn(x: Color) -> Int { let c = red\n 0 } }\n0"))))

(test-case "索引に無い名前の SConstruct は host 例外を出さない"
  (define s '(#:span src 0 1))
  (define result
    (lower-surface `(SProgram ,s () (SConstruct ,s (SName ,s nope) ()))
                   canonical-trait-env))
  (check-true (lowered? result))
  (check-equal? (lowered-term result) `(Construct ,s nope)))

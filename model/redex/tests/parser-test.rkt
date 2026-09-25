#lang racket

(require rackunit
         redex/reduction-semantics
         "../surface.rkt"
         "../parser.rkt"
         "../lexer.rkt"
         "../diagnostic.rkt")

(define s0 '(#:span src 0 1))

(test-case
 "Surface の最小の program が言語に合う"
 (check-true
  (redex-match? Surface sprog
                `(SProgram ,s0 () (SInt ,s0 0)))))

(test-case
 "予約語は ident に合わない"
 (check-false (redex-match? Surface ident 'const))
 (check-false (redex-match? Surface ident 'fn))
 (check-false (redex-match? Surface ident 'trait))
 (check-false (redex-match? Surface ident 'impl))
 (check-false (redex-match? Surface ident 'for))
 (check-false (redex-match? Surface ident 'derive))
 (check-false (redex-match? Surface label 'derive))
 (check-true  (redex-match? Surface ident 'SInt))
 (check-true  (redex-match? Surface ident 'none)))

(test-case
 "source-id は Surface の literal と同じ綴りでもよい"
 ;; spec §5.4。Span の usid をそのまま継ぐと SInt が除外集合へ入って
 ;; 最初の 2 つが #f になる。3 つ目は上書きの前後で変わらない。
 (check-true (redex-match? Surface s '(#:span SInt 0 1)))
 (check-true (redex-match? Surface sexpr `(SInt (#:span SProgram 0 1) 0)))
 (check-true (redex-match? Surface s '(#:span #:synthetic 0 0))))

(test-case
 "注釈の無い束縛の sty-or-none は #:none である"
 (check-true
  (redex-match? Surface spitem
                `(SBind ,s0 let (SName ,s0 x) #:none (SInt ,s0 1)))))

(test-case
 "多 field 射影は Surface の言語に合う"
 (check-true
  (redex-match? Surface sexpr
                `(SProjRec ,s0 (SVar ,s0 r)
                           ((SLabel ,s0 a) (SLabel ,s0 b)))))
 ;; label 列が空でも言語には合う。非空の要求は parser の検査が持つ。
 (check-true
  (redex-match? Surface sexpr
                `(SProjRec ,s0 (SVar ,s0 r) ()))))

(define (p str) (parse (lex/string 'src str)))
(define (p-code str)
  (define r (p str))
  (and (diagnostic? r) (diagnostic-id r)))

(test-case
 "整数だけの program"
 (check-equal? (p "1")
               '(SProgram (#:span src 0 1) () (SInt (#:span src 0 1) 1))))

(test-case
 "true と false は構成子であり literal ではない"
 (check-equal? (p "true")
               '(SProgram (#:span src 0 4) () (SBool (#:span src 0 4) true))))

(test-case
 "後置は適用と射影を左結合で積む"
 (check-equal? (p "f(x).a")
               '(SProgram
                 (#:span src 0 6) ()
                 (SProj (#:span src 0 6)
                        (SApply (#:span src 0 4)
                                (SVar (#:span src 0 1) f)
                                ((SVar (#:span src 2 3) x)))
                        (SLabel (#:span src 5 6) a)))))

(test-case
 "多 field 射影は波括弧の中の label 列を順に持つ"
 (check-equal? (p "r.{a, b}")
               '(SProgram
                 (#:span src 0 8) ()
                 (SProjRec (#:span src 0 8)
                           (SVar (#:span src 0 1) r)
                           ((SLabel (#:span src 3 4) a)
                            (SLabel (#:span src 6 7) b))))))

(test-case
 "多 field 射影は後置として左結合で積める"
 (check-equal? (p "f(x).{a}")
               '(SProgram
                 (#:span src 0 8) ()
                 (SProjRec (#:span src 0 8)
                           (SApply (#:span src 0 4)
                                   (SVar (#:span src 0 1) f)
                                   ((SVar (#:span src 2 3) x)))
                           ((SLabel (#:span src 6 7) a))))))

(test-case
 "label 列の区切りは読点でも改行でもよく、末尾の読点を許す"
 (check-equal? (length (fourth (fourth (p "r.{a, b}")))) 2)
 (check-equal? (length (fourth (fourth (p "r.{a\n b}")))) 2)
 (check-equal? (length (fourth (fourth (p "r.{a, b,}")))) 2))

(test-case
 "空の label 列と重複した label は E-SUR-012 である"
 (check-equal? (p-code "r.{}") "E-SUR-012")
 (check-equal? (p-code "r.{a, a}") "E-SUR-012")
 ;; primary span は { から } までである。
 (check-equal? (diagnostic-primary-span (p "r.{}")) '(#:span src 2 4))
 (check-equal? (diagnostic-primary-span (p "r.{a, a}")) '(#:span src 2 8)))

(test-case
 "波括弧の中に式を書くと構文の誤りである"
 (check-equal? (p-code "r.{a: 1}") "E-SUR-005")
 (check-equal? (p-code "r.{1}") "E-SUR-005"))

(test-case
 "括弧で括った式は括弧の span を持たない"
 ;; spec §5.3。pitem が無いので SProgram の span は末尾の expr の span と
 ;; 一致する。括弧は span を持たないので、両端の ( と ) は含まれない。
 (check-equal? (p "(x)")
               '(SProgram (#:span src 1 2) () (SVar (#:span src 1 2) x))))

(test-case
 "空の波括弧は空の record である"
 (check-equal? (p "{}")
               '(SProgram (#:span src 0 2) () (SRec (#:span src 0 2) ()))))

(test-case
 "識別子と冒号が続けば record、そうでなければ block である"
 (check-equal? (p "{ a: 1 }")
               '(SProgram
                 (#:span src 0 8) ()
                 (SRec (#:span src 0 8)
                       ((SField (#:span src 2 6)
                                (SLabel (#:span src 2 3) a)
                                (SInt (#:span src 5 6) 1))))))
 (check-equal? (p "{ x }")
               '(SProgram
                 (#:span src 0 5) ()
                 (SBlock (#:span src 0 5) () (SVar (#:span src 2 3) x)))))

(test-case
 "record の区切りは読点でも改行でもよい"
 (check-equal? (length (third (fourth (p "{ a: 1\n b: 2 }")))) 2)
 (check-equal? (length (third (fourth (p "{ a: 1, b: 2 }")))) 2))

(test-case
 "block の中の束縛は改行で区切る"
 (check-equal? (p "{ let x = 1\n x }")
               '(SProgram
                 (#:span src 0 16) ()
                 (SBlock (#:span src 0 16)
                         ((SBind (#:span src 2 11) let
                                 (SName (#:span src 6 7) x)
                                 #:none
                                 (SInt (#:span src 10 11) 1)))
                         (SVar (#:span src 13 14) x)))))

(test-case
 "let mut は 2 つの kw から sbmode の mut へ正規化する"
 (check-equal? (second (first (third (fourth (p "{ let mut x = 1\n x }")))))
               '(#:span src 2 15))
 (check-equal? (third (first (third (fourth (p "{ let mut x = 1\n x }")))))
               'mut))

(test-case
 "無名関数は引数と返り値の型を取る"
 (check-equal? (p "fn(a: Int) -> Int { a }")
               '(SProgram
                 (#:span src 0 23) ()
                 (SFn (#:span src 0 23)
                      ((SParam (#:span src 3 9)
                               (SName (#:span src 3 4) a)
                               (TName (#:span src 6 9) Int)))
                      (TName (#:span src 14 17) Int)
                      (SBlock (#:span src 18 23) ()
                              (SVar (#:span src 20 21) a))))))

(test-case
 "出力は Surface の言語に合う"
 (for ([src (in-list (list "1" "true" "f(x).a" "{}" "{ a: 1 }"
                           "r.{a, b}"
                           "{ let x = 1\n x }"
                           "fn(a: Int) -> Int { a }"
                           "SInt" "TName" "none" "return"))])
   (check-true (redex-match? Surface sprog (p src))
               (format "~a の出力が Surface に合う" src))))

(test-case
 "provide する述語が言語の判定と一致する"
 (check-true  (surface-prog? `(SProgram ,s0 () (SInt ,s0 0))))
 (check-false (surface-prog? `(SInt ,s0 0)))
 (check-true  (surface-expr? `(SInt ,s0 0)))
 (check-false (surface-expr? `(SProgram ,s0 () (SInt ,s0 0)))))

(test-case
 "トップレベルの型宣言と関数宣言と束縛を受理する"
 (check-equal? (length (third (p "type A = Int\nconst x: A = 1\n1"))) 2)
 (check-true (redex-match? Surface sprog
                           (p "fn f(a: Int) -> Int { a }\nf(1)"))))

(test-case
 "trait and impl declarations parse"
 (define p (parse (lex/string 'src "trait Printable { print: fn(Self) -> String }\nimpl Printable for Int { print: fn(x: Int) -> String { \"i\" } }\n0")))
 (check-true (surface-prog? p))
 (match p
   [`(SProgram ,_ (,t ,i) ,_)
    (check-equal? (first t) 'STraitDecl)
    (check-equal? (first i) 'SImplDecl)
    (check-equal? (first (fifth i)) 'SRec)]))

(test-case
 "derive 宣言は SDeriveDecl になる"
 (define r (p "derive Sizable for Bool\n0"))
 (check-true (redex-match? Surface sprog r))
 (match r
   [`(SProgram ,_ ((SDeriveDecl ,s (SName ,s_n Sizable) (TName ,_ Bool))) ,_)
    (check-equal? s '(#:span src 0 23))
    (check-equal? s_n '(#:span src 7 14))]))

(test-case
 "derive 宣言は本体を持たず for を要する"
 (check-equal? (p-code "derive Sizable for Bool { size: 0 }\n0") "E-SUR-005")
 (check-equal? (diagnostic-primary-span (p "derive Sizable for Bool { size: 0 }\n0"))
               '(#:span src 24 25))
 (check-equal? (p-code "derive Sizable Bool\n0") "E-SUR-005")
 (check-equal? (diagnostic-primary-span (p "derive Sizable Bool\n0"))
               '(#:span src 15 19))
 (check-equal? (p-code "let derive = 0\n0") "E-SUR-005")
 (check-equal? (diagnostic-primary-span (p "let derive = 0\n0"))
               '(#:span src 4 10)))

(test-case
 "the three new keywords are no longer identifiers"
 (for ([src (in-list '("let trait = 0\n0" "let impl = 0\n0" "let for = 0\n0"))])
   (check-true (diagnostic? (parse (lex/string 'src src))))))

(test-case
 "declaration bodies must open with a brace"
 (for ([src (in-list '("trait P x: Int }\n0" "impl P for Int x: 0 }\n0"))])
   (check-true (diagnostic? (parse (lex/string 'src src))))))

(test-case
 "字句にならない記号は lexer の診断がそのまま返る"
 (check-equal? (p-code "List<Int>") "E-SUR-002")
 (check-equal? (p-code "1 + 2") "E-SUR-002")
 (check-equal? (p-code "x ?= y") "E-SUR-002")
 (check-equal? (p-code "x |> f") "E-SUR-002"))

(test-case
 "SUR-011: 戻り型は -> の後ろに書き、旧表記と省略は E-SUR-005 になる"
 (for ([src (in-list '("fn f() -> Int { 1 }\n0"
                       "fn(x: Int) -> Int { x }"
                       "let g: fn(Int) -> Int = fn(x: Int) -> Int { x }\n0"
                       "fn f() -> { a: Int } { 1 }\n0"))])
   (check-false (p-code src)))
 (for ([src (in-list '("fn f() Int { 1 }\n0"
                       "let g: fn(Int) Int = 0\n0"
                       "fn(x: Int) Int { x }"
                       "fn f() { 1 }\n0"
                       "fn(x: Int) { x }"))]
       [at  (in-list (list '(#:span src 7 10) '(#:span src 15 18) '(#:span src 11 14)
                           '(#:span src 7 8) '(#:span src 11 12)))])
   (check-equal? (p-code src) "E-SUR-005")
   (check-equal? (diagnostic-primary-span (p src)) at)))

(test-case
 "式の頭に置けない語は E-SUR-005 である"
 (check-equal? (p-code "if cond { 1 }") "E-SUR-005")
 (check-equal? (p-code "match e { 1 }") "E-SUR-005"))

(test-case
 "予約語 for は式の頭に置けず E-SUR-005 である"
 (check-equal? (p-code "for x { 1 }") "E-SUR-005")
 (check-equal? (diagnostic-primary-span (p "for x { 1 }"))
               '(#:span src 0 3)))

(test-case
 "単独の return は変数である"
 (check-equal? (p "return")
               '(SProgram (#:span src 0 6) () (SVar (#:span src 0 6) return))))

(test-case
 "let と mut の間の改行は束縛として受理しない"
 (check-equal? (p-code "{ let\nmut x = 1\n x }") "E-SUR-005"))

(test-case
 "空入力と宣言だけの入力は E-SUR-006 である"
 (check-equal? (p-code "") "E-SUR-006")
 (check-equal? (p-code "type A = Int\n") "E-SUR-006")
 (check-equal? (p-code "type A = Int") "E-SUR-006")
 (check-equal? (diagnostic-primary-span (p "")) '(#:span src 0 0)))

(test-case
 "途中で終わる入力は E-SUR-006 であり primary span は eof の span である"
 (check-equal? (p-code "f(") "E-SUR-006")
 (check-equal? (diagnostic-primary-span (p "f(")) '(#:span src 2 2)))

(test-case
 "lexer の診断はそのまま返り、構文の誤りへ読み替えない"
 (define r (parse (lex 'src (bytes 97 255 98))))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-id r) "E-SUR-001")
 (check-equal? (diagnostic-primary-span r) '(#:span src 1 2)))

;; spec §5.3 と §12。節点の span が子孫のすべての span を包含することを、個々
;; の形を並べずに構文木の走査で確かめる。Surface の節点はすべて (Ctor span ...)
;; の形であり、span は (#:span sid lo hi) の 4 要素である（spec §5.2）。
(define (span-term? x)
  (and (list? x) (= (length x) 4) (eq? (first x) '#:span)))

(define (node-term? x)
  (and (list? x) (>= (length x) 2) (symbol? (first x))
       (span-term? (second x))))

(define (all-nodes x)
  (cond
    [(node-term? x) (cons x (append-map all-nodes (cddr x)))]
    [(list? x) (append-map all-nodes x)]
    [else '()]))

(define (span-within? inner outer)
  (and (eq? (second inner) (second outer))
       (>= (third inner) (third outer))
       (<= (fourth inner) (fourth outer))))

(define (containment-violations t)
  (for*/list ([n (in-list (all-nodes t))]
              [c (in-list (append-map all-nodes (cddr n)))]
              #:unless (span-within? (second c) (second n)))
    (list (first n) (second n) (first c) (second c))))

(test-case
 "節点の span は子孫のすべての span を包含する"
 (for ([src (in-list (list "1"
                           "f(x).a"
                           "r.{a, b}"
                           "return"
                           "type A = Int\nconst x: A = 1\n1"
                           "fn f(a: Int) -> Int { a }\nf(1)"))])
   (define t (p src))
   (check-false (diagnostic? t) (format "~s が受理される" src))
   (check-equal? (containment-violations t) '()
                 (format "~s の span 包含" src))))

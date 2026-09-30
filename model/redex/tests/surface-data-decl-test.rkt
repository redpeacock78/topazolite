#lang racket

(require rackunit
         racket/match
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../diagnostic.rkt"
         "../traits.rkt")

;; P2l2b1 spec §12。Surface の data 型宣言の名前と欄の検査である。
;; 台帳を通る検査（regularity、positivity、基底の data）は driver-level で
;; Task 3 が足す。
(define (lower str)
  (lower-surface (parse (lex/string 'src str)) canonical-trait-env))
(define (code str)
  (define r (lower str))
  (and (diagnostic? r) (diagnostic-id r)))
(define (primary str) (diagnostic-primary-span (lower str)))
(define (related str) (diagnostic-related (lower str)))
(define (related-spans str) (map second (related str)))
(define (decls str) (lowered-data-decls (lower str)))
(define (sp lo hi) `(#:span src ,lo ,hi))

(test-case "data 型宣言は台帳の宣言の形へ写る"
  (check-equal? (decls "type Box<A> =\n  | box<A>\n0")
                '((Box (A) ((box ((Param A)))))))
  (check-equal? (decls "type Tree<A> =\n  | leaf\n  | node<Owned<Tree<A>>, A>\n0")
                '((Tree (A) ((leaf ()) (node ((Owned (Data Tree ((Param A)))) (Param A)))))))
  ;; 前方参照と相互参照。
  (check-equal? (decls "type A =\n  | a<B>\ntype B =\n  | b<A>\n0")
                '((A () ((a ((Data B ()))))) (B () ((b ((Data A ()))))))))

(test-case "型仮引数は型別名と組み込みの名前を欄の中で隠す"
  (check-equal? (decls "type X = Bool\ntype T<X> =\n  | k<X>\n0")
                '((T (X) ((k ((Param X)))))))
  (check-equal? (decls "type T<Int> =\n  | k<Int>\n0")
                '((T (Int) ((k ((Param Int))))))))

(test-case "型別名は後に現れる data 型を参照できる"
  (check-true (lowered? (lower "type X = Tree\ntype Tree =\n  | leaf\nfn f(x: X) -> Int { 0 }\n0"))))

(test-case "型仮引数は型別名の中へ漏れない"
  (check-equal? (code "type X = A\ntype T<A> =\n  | k<X>\n0") "E-SUR-008"))

(test-case "data 型と型別名の重なりはどちらの順でも E-SUR-031 である"
  (define s1 "type A = Int\ntype A =\n  | k\n0")
  (check-equal? (code s1) "E-SUR-031")
  (check-equal? (primary s1) (sp 18 19))
  (check-equal? (related-spans s1) (list (sp 5 6)))
  (check-equal? (map first (related s1)) '(type-alias-declaration))
  (define s2 "type A =\n  | k\ntype A = Int\n0")
  (check-equal? (code s2) "E-SUR-031")
  (check-equal? (primary s2) (sp 20 21))
  (check-equal? (related-spans s2) (list (sp 5 6)))
  (check-equal? (map first (related s2)) '(data-declaration)))

(test-case "data 型と trait の重なりはどちらの順でも E-SUR-023 である"
  (define s1 "trait A { f: Int }\ntype A =\n  | k\n0")
  (check-equal? (code s1) "E-SUR-023")
  (check-equal? (map first (related s1)) '(trait-declaration))
  (define s2 "type A =\n  | k\ntrait A { f: Int }\n0")
  (check-equal? (code s2) "E-SUR-023")
  (check-equal? (map first (related s2)) '(data-declaration)))

(test-case "Self と組み込みの型の名前は data 型の名前にできない"
  (check-equal? (code "type Self =\n  | k\n0") "E-SUR-008")
  (for ([name (in-list '("Int" "Never" "Res" "List" "Owned"))])
    (check-equal? (code (format "type ~a =\n  | k\n0" name)) "E-SUR-028" name)))

(test-case "data 型の重複は E-SUR-027 である"
  (define s "type A =\n  | k\ntype A =\n  | j\n0")
  (check-equal? (code s) "E-SUR-027")
  (check-equal? (related-spans s) (list (sp 5 6))))

(test-case "constructor の重なりは E-SUR-029 である"
  (define s "type A =\n  | k\ntype B =\n  | k\n0")
  (check-equal? (code s) "E-SUR-029")
  (check-equal? (primary s) (sp 28 29))
  (check-equal? (related-spans s) (list (sp 13 14)))
  (check-equal? (map first (related s)) '(constructor-declaration))
  ;; 組み込みの constructor は原文の span を持たないので related を持たない。
  (check-equal? (code "type A =\n  | none\n0") "E-SUR-029")
  (check-equal? (related "type A =\n  | none\n0") '())
  (check-equal? (code "type A =\n  | nil\n0") "E-SUR-029"))

(test-case "constructor と関数の名前の重なりはどちらの順でも E-SUR-032 である"
  (define s1 "fn k(x: Int) -> Int { x }\ntype A =\n  | k\n0")
  (check-equal? (code s1) "E-SUR-032")
  (check-equal? (map first (related s1)) '(function-declaration))
  (define s2 "type A =\n  | k\nfn k(x: Int) -> Int { x }\n0")
  (check-equal? (code s2) "E-SUR-032")
  (check-equal? (map first (related s2)) '(constructor-declaration))
  ;; kernel の Γ0 の鍵との重なりは constructor 名を primary とし、related を持たない。
  (check-equal? (code "type A =\n  | add\n0") "E-SUR-032")
  (check-equal? (primary "type A =\n  | add\n0") (sp 13 16))
  (check-equal? (related "type A =\n  | add\n0") '()))

(test-case "型仮引数の重複は E-SUR-030、Self は E-SUR-008 である"
  (define s "type T<A, A> =\n  | k\n0")
  (check-equal? (code s) "E-SUR-030")
  (check-equal? (primary s) (sp 10 11))
  (check-equal? (related-spans s) (list (sp 7 8)))
  (check-equal? (code "type T<Self> =\n  | k\n0") "E-SUR-008"))

(test-case "data 型への誤った型適用は E-SUR-025 で、宣言を related に添える"
  ;; 型仮引数への型適用は related を持たない。
  (check-equal? (code "type T<A> =\n  | k<A<Int>>\n0") "E-SUR-025")
  (check-equal? (related "type T<A> =\n  | k<A<Int>>\n0") '())
  (define arity "type T<A> =\n  | k\nfn f(x: T<Int, Int>) -> Int { 0 }\n0")
  (check-equal? (code arity) "E-SUR-025")
  (check-equal? (related-spans arity) (list (sp 5 6)))
  (define bare "type T<A> =\n  | k\nfn f(x: T) -> Int { 0 }\n0")
  (check-equal? (code bare) "E-SUR-025")
  (check-equal? (map first (related bare)) '(data-declaration)))

(test-case "欄の中の未知の名前は E-SUR-008 である"
  (check-equal? (code "type T =\n  | k<Missing>\n0") "E-SUR-008"))

(test-case "data 型への derive Sizable は E-SUR-019 である"
  (check-equal? (code "type T =\n  | k\nderive Sizable for T\n0") "E-SUR-019"))

;; spec §11。複数の違反は段の順で最初の 1 件を報告する。
(test-case "違反の報告は段の順である"
  ;; 段 1 の data 型の重複は、原文で先に現れる段 2 の nil より先である。
  (check-equal? (code "type T =\n  | nil\ntype T =\n  | a\n0") "E-SUR-027")
  ;; 段 2 の中では constructor の重複を値の名前との重なりより先に見る。
  (check-equal? (code "fn a(x: Int) -> Int { x }\ntype T =\n  | a\ntype U =\n  | b\n  | b\n0")
                "E-SUR-029")
  ;; 段 2 は段 3 より先である。
  (check-equal? (code "type T<A, A> =\n  | nil\n0") "E-SUR-029")
  ;; 段 3 は段 4 より先である。
  (check-equal? (code "type T<A> =\n  | a<Missing>\ntype U<B, B> =\n  | b\n0") "E-SUR-030")
  ;; 型別名の本体の誤りは段 2 より先である。
  (check-equal? (code "type X = Missing\ntype T =\n  | nil\n0") "E-SUR-008"))

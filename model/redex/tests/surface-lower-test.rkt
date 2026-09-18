#lang racket

;; SUR-001。Surface の式を UCore+ へ落とす部分の回帰である。
;; 束縛と宣言は surface-lower-test.rkt の後半（Task 7）が持つ。

(require rackunit
         redex/reduction-semantics
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../ucore.rkt"
         "../diagnostic.rkt")

(define (low str) (lower-surface (parse (lex/string 'src str))))

;; Surface の項を手で組む側の道具である。parser が SBlock を作る形
;; （SFn の本体）を、SBlock を落とせないこの段で確かめるために使う。
(define s0 '(#:span src 0 1))
(define (prog items e) `(SProgram ,s0 ,items ,e))

(test-case
 "literal は #:lit になる"
 (check-equal? (low "1") '(#:lit 1 (#:span src 0 1)))
 (check-equal? (lower-surface (prog '() `(SStr ,s0 "a")))
               `(#:lit "a" ,s0))
 (check-equal? (lower-surface (prog '() `(SUnit ,s0)))
               `(#:lit unit ,s0)))

(test-case
 "true と false は構成子であり literal ではない"
 (check-equal? (low "true") '(Construct (#:span src 0 4) true))
 (check-equal? (low "false") '(Construct (#:span src 0 5) false)))

(test-case
 "変数は #:var になる"
 (check-equal? (low "x") '(#:var x (#:span src 0 1))))

(test-case
 "適用と射影は span をそのまま継ぐ"
 ;; span の値は parser-test.rkt:53-60 と同じである。
 (check-equal? (low "f(x).a")
               '(Proj (#:span src 0 6)
                      (Apply (#:span src 0 4)
                             (#:var f (#:span src 0 1))
                             (#:var x (#:span src 2 3)))
                      (#:lbl a (#:span src 5 6)))))

(test-case
 "record の欄の可変性は imm に固定する"
 ;; span の値は parser-test.rkt:76-82 と同じである。
 (check-equal? (low "{ a: 1 }")
               '(Rec (#:span src 0 8)
                     (((#:lbl a (#:span src 2 3)) imm (#:lit 1 (#:span src 5 6)))))))

(test-case
 "record の重複した label は E-SUR-007 である"
 (define r (low "{ a: 1, a: 2 }"))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-id r) "E-SUR-007")
 ;; primary span は 2 つ目の SLabel である
 (check-equal? (diagnostic-primary-span r) '(#:span src 8 9)))

(test-case
 "空の record は空の行になる"
 (check-equal? (low "{}") '(Rec (#:span src 0 2) ())))

(test-case
 "Fn は引数と返り値の型注釈と空の効果行を持つ"
 ;; parser は Fn の本体を必ず SBlock にするので、Surface の項を手で組む。
 (define r
   (lower-surface
    (prog '() `(SFn ,s0 ((SParam ,s0 (SName ,s0 x) (TName ,s0 Int)))
                    (TName ,s0 Int)
                    (SVar ,s0 x)))))
 (check-equal? r
  `(Fn ,s0 (((#:bind x ,s0) (#:ty Int ,s0)))
       (#:ty Int ,s0)
       (#:ef () ,s0)
       (#:var x ,s0)))
 (check-true (redex-match? UCore+ e r)))

(test-case
 "落とした式は UCore+ の e に合う"
 (for ([src (in-list (list "1" "true" "x" "f(x).a" "{}" "{ a: 1 }"))])
   (define t (low src))
   (check-false (diagnostic? t) (format "~s が受理される" src))
   (check-true (redex-match? UCore+ e t) (format "~s の出力が UCore+ に合う" src))))

(test-case
 "注釈なしの束縛は 2 欄の Let になる"
 ;; spec §7.3。Let の span は尾部の span であり、束縛の始まりから
 ;; 末尾式の終わりまでである。
 (check-equal? (low "{ let x = 1\n x }")
               '(Let (#:span src 2 14)
                     ((#:bind x (#:span src 6 7)) let)
                     (#:lit 1 (#:span src 10 11))
                     (#:var x (#:span src 13 14)))))

(test-case
 "const と let mut も 2 欄の Let になる"
 (check-equal? (third (low "{ const x = 1\n x }")) '((#:bind x (#:span src 8 9)) const))
 (check-equal? (third (low "{ let mut x = 1\n x }")) '((#:bind x (#:span src 10 11)) mut)))

(test-case
 "注釈ありの束縛は 3 欄の Let になる"
 (check-equal? (third (low "{ let x: Int = 1\n x }"))
               '((#:bind x (#:span src 6 7)) let (#:ty Int (#:span src 9 12)))))

(test-case
 "複数の束縛は右へ入れ子にする"
 ;; spec §7.2。lower [b1 b2] e = L(b1, L(b2, lower e)) である。
 (define t (low "{ let x = 1\n let y = 2\n x }"))
 (check-equal? (first t) 'Let)
 (check-equal? (second (first (third t))) 'x)
 (check-equal? (first (fifth t)) 'Let)
 (check-equal? (second (first (third (fifth t)))) 'y))

(test-case
 "束縛の尾部 span は末尾式の終わりまで伸びる"
 ;; spec §7.3。2 つの Let の始まりは別だが、終わりは同じである。
 (define t (low "{ let x = 1\n let y = 2\n x }"))
 (check-equal? (second t) '(#:span src 2 25))
 (check-equal? (second (fifth t)) '(#:span src 13 25)))

(test-case
 "束縛の無い block は末尾式そのものになる"
 (check-equal? (low "{ x }") '(#:var x (#:span src 2 3))))

(test-case
 "型宣言は節点を作らない"
 (check-equal? (low "type A = Int\n1") '(#:lit 1 (#:span src 13 14))))

(test-case
 "トップレベルの束縛も Let になり、尾部は program の末尾式まで伸びる"
 ;; 型宣言を前に置くと、別名の展開と尾部 span の両方を一度に固定できる。
 ;; 注釈の #:ty は展開後の Int を持つが、span は使用箇所の A のままである。
 (check-equal? (low "type A = Int\nconst x: A = 1\nx")
               '(Let (#:span src 13 29)
                     ((#:bind x (#:span src 19 20)) const (#:ty Int (#:span src 22 23)))
                     (#:lit 1 (#:span src 26 27))
                     (#:var x (#:span src 28 29)))))

(test-case
 "関数宣言は Recur になる"
 (define t (low "fn f(a: Int) Int { a }\nf(1)"))
 (check-equal? (first t) 'Recur)
 (check-equal? (third t) '(#:bind f (#:span src 3 4)))
 (check-equal? (fourth t) '(((#:bind a (#:span src 5 6)) (#:ty Int (#:span src 8 11)))))
 (check-equal? (fifth t) '(#:ty Int (#:span src 13 16)))
 (check-equal? (sixth t) '(#:ef () (#:span src 0 22)))
 ;; 本体は束縛の無い block なので末尾式そのものである
 (check-equal? (seventh t) '(#:var a (#:span src 19 20)))
 ;; 尾部は program の末尾式まで伸びる
 (check-equal? (second t) '(#:span src 0 27)))

(test-case
 "落とした program は UCore+ の e に合う"
 (for ([src (in-list (list "{ let x = 1\n x }"
                           "{ let x: Int = 1\n x }"
                           "{ let mut x = 1\n x }"
                           "{ let x = 1\n let y = 2\n x }"
                           "type A = Int\nconst x: A = 1\nx"
                           "fn f(a: Int) Int { a }\nf(1)"))])
   (define t (low src))
   (check-false (diagnostic? t) (format "~s が受理される" src))
   (check-true (redex-match? UCore+ e t) (format "~s の出力が UCore+ に合う" src))))

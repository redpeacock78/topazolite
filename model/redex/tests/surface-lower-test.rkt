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

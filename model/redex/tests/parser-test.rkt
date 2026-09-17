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

(define (p str) (parse (lex/string 'src str)))

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
 (check-equal? (p "fn(a: Int) Int { a }")
               '(SProgram
                 (#:span src 0 20) ()
                 (SFn (#:span src 0 20)
                      ((SParam (#:span src 3 9)
                               (SName (#:span src 3 4) a)
                               (TName (#:span src 6 9) Int)))
                      (TName (#:span src 11 14) Int)
                      (SBlock (#:span src 15 20) ()
                              (SVar (#:span src 17 18) a))))))

(test-case
 "出力は Surface の言語に合う"
 (for ([src (in-list (list "1" "true" "f(x).a" "{}" "{ a: 1 }"
                           "{ let x = 1\n x }"
                           "fn(a: Int) Int { a }"
                           "SInt" "TName" "none" "return"))])
   (check-true (redex-match? Surface sprog (p src))
               (format "~a の出力が Surface に合う" src))))

(test-case
 "provide する述語が言語の判定と一致する"
 (check-true  (surface-prog? `(SProgram ,s0 () (SInt ,s0 0))))
 (check-false (surface-prog? `(SInt ,s0 0)))
 (check-true  (surface-expr? `(SInt ,s0 0)))
 (check-false (surface-expr? `(SProgram ,s0 () (SInt ,s0 0)))))

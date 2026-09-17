#lang racket

(require rackunit
         redex/reduction-semantics
         "../surface.rkt")

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

(test-case
 "provide する述語が言語の判定と一致する"
 (check-true  (surface-prog? `(SProgram ,s0 () (SInt ,s0 0))))
 (check-false (surface-prog? `(SInt ,s0 0)))
 (check-true  (surface-expr? `(SInt ,s0 0)))
 (check-false (surface-expr? `(SProgram ,s0 () (SInt ,s0 0)))))

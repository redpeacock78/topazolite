#lang racket

(require rackunit
         redex/reduction-semantics
         "../ucore.rkt"
         "../annotate.rkt")

;; spec §8。ホワイトペーパー 867-869 行の const と let と let mut は
;; 型注釈を持たない。注釈ありの 3 欄 (x bmode uτ) では落とす先が無いので、
;; 2 欄 (x bmode) の束縛子を持つ Let を足す。
(test-case
 "UCore は 2 欄の束縛子を持つ Let を受ける"
 (check-true (redex-match? UCore e '(Let (x let) 1 x)))
 (check-true (redex-match? UCore e '(Let (x const) 1 x)))
 (check-true (redex-match? UCore e '(Let (x mut) 1 x)))
 ;; 既存の 2 つの形は残る
 (check-true (redex-match? UCore e '(Let x 1 x)))
 (check-true (redex-match? UCore e '(Let (x let Int) 1 x))))

(define s0 '(#:span src 0 1))

(test-case
 "UCore+ は 2 欄の束縛子を持つ Let を受ける"
 (check-true
  (redex-match? UCore+ e
                `(Let ,s0 ((#:bind x ,s0) let) (#:lit 1 ,s0) (#:var x ,s0)))))

(test-case
 "annotate-surface は 2 欄の束縛子へ span を入れる"
 ;; spec §8。annotate-core と annotate-surface はどちらも provide して
 ;; おり、phase-span-test が annotate-core を直に呼ぶ。両方に節を足す。
 (define t (annotate-surface '(Let (x let) 1 x)))
 (check-true (redex-match? UCore+ e t))
 (match-define `(Let ,_ (,binder ,mode) ,_ ,_) t)
 (check-equal? mode 'let)
 (check-equal? (first binder) '#:bind)
 (check-equal? (second binder) 'x))

(test-case
 "annotate-core は 2 欄の束縛子へ span を入れる"
 (define t (annotate-core '(Let (x mut) 1 x)))
 (match-define `(Let ,_ (,binder ,mode) ,_ ,_) t)
 (check-equal? mode 'mut)
 (check-equal? (first binder) '#:bind))

(test-case
 "3 欄の Let は 2 欄の節へ落ちない"
 ;; 2 欄の節を 3 欄の節より前へ置くので、bmode の位置に uτ が来る形が
 ;; 誤って合わないことを確かめる。
 (define t (annotate-surface '(Let (x let Int) 1 x)))
 (match-define `(Let ,_ (,_ ,mode ,type-wrapper) ,_ ,_) t)
 (check-equal? mode 'let)
 (check-equal? (first type-wrapper) '#:ty))

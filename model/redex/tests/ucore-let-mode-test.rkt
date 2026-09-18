#lang racket

(require rackunit
         redex/reduction-semantics
         (prefix-in el: "../elaborate.rkt")
         "../ucore.rkt"
         "../annotate.rkt"
         "../diagnostic.rkt")

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

(define (elab-err? r) (and (pair? r) (eq? (first r) 'err)))

;; 拒否の code を見る回帰のための包み。owned-narrowing-test.rkt:24 と同じ形
;; である。
(define (code-of source)
  (define r (el:elab source))
  (if (elab-err? r) (diagnostic-id (second r)) 'ok))

;; spec §8。mode-only Let は束縛式から型を推論して、注釈ありの 3 欄の形へ
;; 直る。(#:ty uτ s) の s は束縛式の span である。#:synthetic は使わない。
(test-case
 "mode-only Let は束縛式の型を束縛型にする"
 (define r (el:elab '(Let (x let) 1 x)))
 (check-false (elab-err? r))
 (check-equal? (second r) 'Int)
 (match-define `(Let ,_ (,binder let (#:ty ,type ,type-span)) ,bound ,_)
   (first r))
 (check-equal? (first binder) '#:bind)
 (check-equal? type 'Int)
 ;; 型注釈の span は束縛式のものである。束縛式は (#:lit 1 s) なので
 ;; span は第 3 要素である。
 (check-equal? type-span (third bound)))

(test-case
 "mode-only の const と mut も通る"
 (check-false (elab-err? (el:elab '(Let (x const) 1 x))))
 (check-false (elab-err? (el:elab '(Let (x mut) 1 x)))))

(test-case
 "mode-only の let mut へは再代入できる"
 (check-false (elab-err? (el:elab '(Let (x mut) 1 (Reassign x 2))))))

(test-case
 "free-vars/erased は 2 欄の束縛子の名前を落とす"
 ;; spec §8。この節が無いと素の名前の節へ落ち、(p let) という list を
 ;; 1 つの名前として set-remove へ渡すので、p が自由変数のまま残る。
 ;; 自由変数の集合は捕捉の判定に使うので、外側に Owned の p を置き、
 ;; Recur の本体で mode-only Let が p を遮蔽する形を見る。
 ;; 名前が落ちなければ Recur が外側の Owned を捕捉したと見なし、
 ;; Recur の捕捉判定が owned-recur-capture すなわち E-OWN-008 で拒否する。
 ;; 診断の有無で観測できるので、素通りだけを見る回帰にしない。
 (check-equal?
  (code-of '(Fn ((p (Owned Res))) Unit (Partial)
                (Recur f () Int (Partial) (Let (p let) 1 p) unit)))
  'ok)
 ;; 遮蔽しなければ同じ形が実際に拒否されることを併せて固定する。
 ;; これが無いと、上の 'ok が捕捉の判定を素通りしただけでも通ってしまう。
 (check-equal?
  (code-of '(Fn ((p (Owned Res))) Unit (Partial)
                (Recur f () Int (Partial) (Let (q let) 1 p) unit)))
  "E-OWN-008"))

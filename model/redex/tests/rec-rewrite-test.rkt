#lang racket

(require rackunit
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt")

(define rewrite-a
  '(RecRewrite (Rec ((a imm 1) (b imm 2)))
               ((a x Int imm (Union Int Bool)
                 (UnionInject (Union Int Bool) Int x)))))

(test-case "RecRewrite は G2 と G2m の Core の項である"
  (check-true (redex-match? G2 c rewrite-a))
  (check-true (redex-match? G2m c rewrite-a)))

(test-case "評価文脈の穴は入力 e だけに置かれる"
  (define allowed (term (RecRewrite hole ((a x Int imm Int x)))))
  (define rejected
    (term (RecRewrite (Rec ((a imm 1))) ((a x Int imm Int hole)))))
  (check-true (redex-match? G2m F allowed))
  (check-true (redex-match? G2m E allowed))
  (check-true (redex-match? G2m G allowed))
  (check-false (redex-match? G2m F rejected))
  (check-false (redex-match? G2m E rejected))
  (check-false (redex-match? G2m G rejected)))

(test-case "子の順は e の後に各 entry の c で、再構成も一致する"
  (define core
    '(RecRewrite (Rec ((a imm 1)))
                 ((a x Int imm Int x)
                  (b y Bool imm Bool y))))
  (check-equal? (core-children core)
                '((Rec ((a imm 1))) x y))
  (check-equal? (core-with-children core '(input new-a new-b))
                '(RecRewrite input ((a x Int imm Int new-a)
                                    (b y Bool imm Bool new-b)))))

(test-case "entry の x は c だけを束縛し、外側の同名束縛と区別される"
  (define core
    '(Let (x Int) 5
       (RecRewrite x ((a x Int imm Int x)
                      (b y Int imm Int x)))))
  ;; input の x は外側の束縛、各 c の x はそれぞれの entry の束縛である。
  (check-equal? (core-free-vars core) (set))
  (check-equal?
   (core-free-vars '(RecRewrite x ((a x Int imm Int x))))
   (set 'x))
  ;; 先行 entry の binder は後続 entry の c へは届かない。
  (check-equal?
   (core-free-vars '(RecRewrite 0 ((a x Int imm Int x)
                                   (b y Int imm Int x))))
   (set 'x))
  (check-true
   (alpha-equivalent? G2
                      '(RecRewrite (Rec ((a imm 1))) ((a x Int imm Int x)))
                      '(RecRewrite (Rec ((a imm 1))) ((a y Int imm Int y)))))
  (check-false
   (alpha-equivalent? G2
                      '(RecRewrite (Rec ((a imm 1))) ((a x Int imm Int z)))
                      '(RecRewrite (Rec ((a imm 1))) ((a y Int imm Int w))))))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../span-core.rkt"
         "../span-subst.rkt")

(define s0 (term (#:span main.tz 0 4)))
(define s1 (term (#:span main.tz 5 9)))
(define s2 (term (#:span main.tz 10 14)))

(test-case "自由変数は出現順で重複なく返る"
  (check-equal? (span-free-vars (term (#:var x ,s0))) '(x))
  (check-equal? (span-free-vars (term (Apply ,s0 (#:var b ,s1) (#:var a ,s1) (#:var b ,s2))))
                '(b a))
  (check-equal? (span-free-vars (term (#:lit 1 ,s0))) '()))

(test-case "7 つの束縛形が束縛名を落とし、範囲の外は落とさない"
  ;; Lam
  (check-equal? (span-free-vars
                 (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var x ,s1))))
                '())
  (check-equal? (span-free-vars
                 (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var z ,s1))))
                '(z))
  ;; Let（型注釈だけの形）。c_1 は束縛の外である。
  (check-equal? (span-free-vars
                 (term (Let ,s0 ((#:bind x ,s1) (#:ty Int ,s1))
                            (#:var x ,s1) (#:var x ,s1))))
                '(x))
  ;; 分岐
  (check-equal? (span-free-vars
                 (term (Eliminate ,s0 (#:lit 1 ,s1)
                                  ((,s1 some ((#:bind x ,s1)) -> (#:var x ,s1))))))
                '())
  ;; ハンドラ
  (check-equal? (span-free-vars
                 (term (Handle ,s0 (Return b (#:ty Int ,s1))
                               (,s1 (#:bind x ,s1) -> (#:var x ,s1)) (#:var q ,s1))))
                '(q))
  ;; Recur。c_1 は f と x の両方を、c_2 は f だけを見る。
  (check-equal? (span-free-vars
                 (term (Recur ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                              (#:var x ,s1) (Apply ,s1 (#:var f ,s1) (#:var x ,s1)))))
                '(x))
  ;; RecurVal
  (check-equal? (span-free-vars
                 (term (RecurVal ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                                 (Apply ,s1 (#:var f ,s1) (#:var x ,s1)))))
                '())
  ;; bmode 付き Let（G2+）
  (check-equal? (span-free-vars
                 (term (Let ,s0 ((#:bind x ,s1) mut (#:ty Int ,s1))
                            (#:var x ,s1) (#:var x ,s1))))
                '(x)))

(test-case "origin の内側の値も走査する"
  ;; O は spanless である（span.md §4、span-core.rkt:102-106、origins.rkt:378-380）。
  ;; 走査が O の内側へ入っても落ちないことを固定する。
  (check-equal? (span-free-vars
                 (term (Lam ,s0 (Derived (Reserved o-mul) (Curry 2))
                            lam-id ((#:bind x ,s1)) (#:var x ,s1))))
                '())
  ;; spanless な分岐は spanful なハンドラと同じ 4 要素なので、
  ;; binder の包みを確認してから束縛形として扱う。
  (check-equal? (span-free-vars
                 (term (Lam ,s0
                            (Derived User
                                     (Curry
                                      (Lam User lam-id (g)
                                           (Eliminate g ((some (y) -> y))))))
                            lam-id ((#:bind x ,s1)) (#:var x ,s1))))
                '()))

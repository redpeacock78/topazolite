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

(test-case "置換の単位は (#:var x s) の節点全体である"
  ;; substitute は (#:var (#:lit 7 s) s) を作る（tests/span-binding-test.rkt:167）。
  ;; span-subst は節点ごと差し替える。
  (check-equal? (span-subst (term (#:var x ,s0))
                            (list (cons 'x (term (#:lit 7 ,s2)))))
                (term (#:lit 7 ,s2))))

(test-case "像は自分の span を持ち込み、出現位置の span を捨てる"
  (define out
    (span-subst (term (Apply ,s0 (#:var f ,s1) (#:var x ,s1)))
                (list (cons 'x (term (#:lit 7 ,s2))))))
  (check-equal? out (term (Apply ,s0 (#:var f ,s1) (#:lit 7 ,s2))))
  (check-true (redex-match? G2+ c out)))

(test-case "束縛された変数は置換されない"
  (check-equal?
   (span-subst (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var x ,s1)))
               (list (cons 'x (term (#:lit 7 ,s2)))))
   (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var x ,s1)))))

(test-case "置換は同時であり、像の中へは届かない"
  ;; x へ渡す像が自由な y を含む。逐次置換なら 2 番目の y の置換がその像へ届く。
  (define out
    (span-subst (term (Apply ,s0 (#:var x ,s1) (#:var y ,s1)))
                (list (cons 'x (term (#:var y ,s2)))
                      (cons 'y (term (#:lit 9 ,s2))))))
  (check-equal? out (term (Apply ,s0 (#:var y ,s2) (#:lit 9 ,s2)))))

(test-case "捕捉が起きる束縛子は改名される"
  (define out
    (span-subst (term (Lam ,s0 User lam-id ((#:bind y ,s1))
                           (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))
                (list (cons 'm (term (#:var y ,s2))))))
  (check-true (redex-match? G2+ c out))
  (match out
    [`(Lam ,_s ,_O ,_cid ((#:bind ,y* ,s_b)) (Apply ,_s1 ,arg (#:var ,used ,s_use)))
     ;; 束縛子は y から離れ、本体の参照はその新しい名前を指す。
     (check-not-equal? y* 'y)
     (check-equal? used y*)
     ;; 改名しても束縛子と出現位置の span は動かない。
     (check-equal? s_b s1)
     (check-equal? s_use s1)
     ;; 像は自分の span のまま入る。
     (check-equal? arg (term (#:var y ,s2)))]
    [_ (fail (format "形が違う: ~s" out))]))

(test-case "捕捉が起きない束縛子は改名されない"
  (check-equal?
   (span-subst (term (Lam ,s0 User lam-id ((#:bind y ,s1))
                          (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))
               (list (cons 'm (term (#:lit 9 ,s2)))))
   (term (Lam ,s0 User lam-id ((#:bind y ,s1))
               (Apply ,s1 (#:lit 9 ,s2) (#:var y ,s1))))))

(test-case "改名が兄弟の束縛子と衝突しない"
  ;; 本体に現れない兄弟 y1 がいる。改名先が y1 になると同名の束縛子が 2 つ並ぶ。
  (define out
    (span-subst (term (Lam ,s0 User lam-id ((#:bind y ,s1) (#:bind y1 ,s1))
                           (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))
                (list (cons 'm (term (#:var y ,s2))))))
  (check-true (redex-match? G2+ c out))
  (match out
    [`(Lam ,_s ,_O ,_cid ((#:bind ,y* ,_) (#:bind ,sib ,_)) ,_body)
     (check-not-equal? y* 'y)
     (check-not-equal? y* sib)]
    [_ (fail (format "形が違う: ~s" out))]))

(test-case "空の σ は項をそのまま返す"
  (define t (term (Apply ,s0 (#:var f ,s1) (#:var x ,s1))))
  (check-equal? (span-subst t '()) t))

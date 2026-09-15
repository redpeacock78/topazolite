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

;; 束縛形ごとの共通の検査。t の中の束縛名 y へ捕捉が起きる σ を掛け、
;; 4 点を見る。get-binder は結果から (#:bind y* s_b) を取り出す。
(define (check-binding-form label t get-binder)
  (define out (span-subst t (list (cons 'm (term (#:var y ,s2))))))
  (check-true (redex-match? G2+ c out) (format "~a: G2+ の c に属さない" label))
  (define b (get-binder out))
  (check-not-equal? (cadr b) 'y (format "~a: 束縛子が改名されていない" label))
  (check-equal? (caddr b) s1 (format "~a: 束縛子の span が動いた" label))
  ;; 本体の参照も改名後の名前を指す。束縛子だけ改名して本体を置き忘れる誤りを弾く。
  ;; 像が自分の span のまま引数位置へ入ることも同時に見る。
  (check-true (let loop ([u out])
                (cond [(equal? u (term (Apply ,s1 (#:var y ,s2)
                                              (#:var ,(cadr b) ,s1)))) #t]
                      [(list? u) (ormap loop u)]
                      [else #f]))
              (format "~a: 本体が (Apply s1 像 (#:var 改名後 s1)) になっていない" label)))

(test-case "7 つの束縛形で α 改名と span 保存が成り立つ"
  (check-binding-form
   "Lam"
   (term (Lam ,s0 User lam-id ((#:bind y ,s1))
               (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))
   (lambda (out) (match out [`(Lam ,_ ,_ ,_ (,b) ,_) b])))

  (check-binding-form
   "Let"
   (term (Let ,s0 ((#:bind y ,s1) (#:ty Int ,s1))
               (#:lit 1 ,s1)
               (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))
   (lambda (out) (match out [`(Let ,_ (,b ,_ty) ,_ ,_) b])))

  (check-binding-form
   "Let（bmode 付き）"
   (term (Let ,s0 ((#:bind y ,s1) mut (#:ty Int ,s1))
               (#:lit 1 ,s1)
               (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))
   (lambda (out) (match out [`(Let ,_ (,b ,_mode ,_ty) ,_ ,_) b])))

  (check-binding-form
   "分岐"
   (term (Eliminate ,s0 (#:lit 1 ,s1)
                    ((,s1 some ((#:bind y ,s1))
                          -> (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))))
   (lambda (out) (match out [`(Eliminate ,_ ,_ ((,_ ,_ (,b) -> ,_))) b])))

  (check-binding-form
   "ハンドラ"
   (term (Handle ,s0 (Return b (#:ty Int ,s1))
                 (,s1 (#:bind y ,s1) -> (Apply ,s1 (#:var m ,s1) (#:var y ,s1)))
                 (#:lit 1 ,s1)))
   (lambda (out) (match out [`(Handle ,_ ,_ (,_ ,b -> ,_) ,_) b])))

  ;; Recur は f と x ... で範囲が違う。x ... 側の捕捉を見る。
  (check-binding-form
   "Recur（引数側）"
   (term (Recur ,s0 recur-id (#:bind f ,s1) ((#:bind y ,s1))
                (Apply ,s1 (#:var m ,s1) (#:var y ,s1))
                (#:var f ,s1)))
   (lambda (out) (match out [`(Recur ,_ ,_ ,_ (,b) ,_ ,_) b])))

  (check-binding-form
   "RecurVal"
   (term (RecurVal ,s0 recur-id (#:bind f ,s1) ((#:bind y ,s1))
                   (Apply ,s1 (#:var m ,s1) (#:var y ,s1))))
   (lambda (out) (match out [`(RecurVal ,_ ,_ ,_ (,b) ,_) b])))

  ;; Recur の f 側。f への捕捉は c_1 と c_2 の双方を改名する。
  (let* ([t (term (Recur ,s0 recur-id (#:bind y ,s1) ((#:bind z ,s1))
                         (Apply ,s1 (#:var m ,s1) (#:var y ,s1))
                         (#:var y ,s1)))]
         [out (span-subst t (list (cons 'm (term (#:var y ,s2)))))])
    (check-true (redex-match? G2+ c out))
    (match out
      [`(Recur ,_s ,_cid (#:bind ,y* ,s_f) ,_binds
               (Apply ,_s1 ,arg (#:var ,u1 ,_)) (#:var ,u2 ,_))
       (check-not-equal? y* 'y)
       (check-equal? u1 y*)
       (check-equal? u2 y*)
       (check-equal? s_f s1)
       (check-equal? arg (term (#:var y ,s2)))]
      [_ (fail (format "Recur（f 側）の形が違う: ~s" out))])))

;; Redex の substitute を G2+ の上で呼ぶための包み。
;; tests/span-binding-test.rkt:12-20 と同じ形である。
(define-metafunction G2+
  sub+ : any x any -> any
  [(sub+ any_t x any_u) (substitute any_t x any_u)])

(test-case "substitute は spanful な項を壊し、span-subst は壊さない"
  (define t (term (#:var x ,s0)))
  (define u (term (#:lit 7 ,s2)))
  ;; substitute は (#:var x s) の第 2 要素を差し替えるため、
  ;; (#:var (#:lit 7 s2) s0) という G2+ に無い形になる。
  (define broken (term (sub+ ,t x ,u)))
  (check-false (redex-match? G2+ c broken))
  ;; span-subst は節点ごと差し替える。
  (define fixed (span-subst t (list (cons 'x u))))
  (check-true (redex-match? G2+ c fixed))
  (check-equal? fixed u))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../span.rkt"
         "../erase.rkt")

(define s0 (term (#:span main.tz 0 4)))
(define s1 (term (#:span main.tz 5 9)))

;; substitute は metafunction の中でしか使えないため、検査用の入口を置く。
;; codomain を any にするのは、壊れた結果も観測するためである。
(define-metafunction G2+
  sub+ : any x any -> any
  [(sub+ any_1 x any_2) (substitute any_1 x any_2)])

(define-metafunction G2
  sub : any x any -> any
  [(sub any_1 x any_2) (substitute any_1 x any_2)])

(test-case "#:refers-to は #:bind の内側の x を binder として解決する"
  ;; 束縛変数の付け替えは alpha 同値を保つ。
  (check-true
   (alpha-equivalent? G1+
                      (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var x ,s1)))
                      (term (Lam ,s0 User lam-id ((#:bind y ,s1)) (#:var y ,s1)))))
  ;; 自由変数の付け替えは alpha 同値を壊す。
  (check-false
   (alpha-equivalent? G1+
                      (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var z ,s1)))
                      (term (Lam ,s0 User lam-id ((#:bind y ,s1)) (#:var w ,s1)))))
  ;; 束縛の届かない位置は付け替えられない。
  (check-false
   (alpha-equivalent? G1+
                      (term (Apply ,s0 (#:var x ,s1) (#:var x ,s1)))
                      (term (Apply ,s0 (#:var y ,s1) (#:var y ,s1))))))

;; 束縛形ごとの直接 assertion。基底との比較だけでは、両辺がともに #f でも
;; 検査が通ってしまう。まず #t と #f を名指しで固定する。
;; car が束縛変数の付け替え（#t を要求）、cdr が自由変数の付け替え（#f を要求）。
(define binding-form-cases
  (list
   (cons (cons (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var x ,s1)))
               (term (Lam ,s0 User lam-id ((#:bind y ,s1)) (#:var y ,s1))))
         (cons (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var z ,s1)))
               (term (Lam ,s0 User lam-id ((#:bind y ,s1)) (#:var w ,s1)))))
   (cons (cons (term (Let ,s0 ((#:bind x ,s1) (#:ty Int ,s1))
                             (#:lit 1 ,s1) (#:var x ,s1)))
               (term (Let ,s0 ((#:bind y ,s1) (#:ty Int ,s1))
                             (#:lit 1 ,s1) (#:var y ,s1))))
         (cons (term (Let ,s0 ((#:bind x ,s1) (#:ty Int ,s1))
                             (#:lit 1 ,s1) (#:var z ,s1)))
               (term (Let ,s0 ((#:bind y ,s1) (#:ty Int ,s1))
                             (#:lit 1 ,s1) (#:var w ,s1)))))
   (cons (cons (term (Eliminate ,s0 (#:lit 1 ,s1)
                                ((,s1 some ((#:bind x ,s1)) -> (#:var x ,s1)))))
               (term (Eliminate ,s0 (#:lit 1 ,s1)
                                ((,s1 some ((#:bind y ,s1)) -> (#:var y ,s1))))))
         (cons (term (Eliminate ,s0 (#:lit 1 ,s1)
                                ((,s1 some ((#:bind x ,s1)) -> (#:var z ,s1)))))
               (term (Eliminate ,s0 (#:lit 1 ,s1)
                                ((,s1 some ((#:bind y ,s1)) -> (#:var w ,s1)))))))
   (cons (cons (term (Handle ,s0 (Return b (#:ty Int ,s1))
                             (,s1 (#:bind x ,s1) -> (#:var x ,s1)) (#:lit 1 ,s1)))
               (term (Handle ,s0 (Return b (#:ty Int ,s1))
                             (,s1 (#:bind y ,s1) -> (#:var y ,s1)) (#:lit 1 ,s1))))
         (cons (term (Handle ,s0 (Return b (#:ty Int ,s1))
                             (,s1 (#:bind x ,s1) -> (#:var z ,s1)) (#:lit 1 ,s1)))
               (term (Handle ,s0 (Return b (#:ty Int ,s1))
                             (,s1 (#:bind y ,s1) -> (#:var w ,s1)) (#:lit 1 ,s1)))))
   ;; Recur は c_1 が f と x の両方を、c_2 が f だけを見る。
   (cons (cons (term (Recur ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                            (#:var x ,s1) (Apply ,s1 (#:var f ,s1) (#:lit 0 ,s1))))
               (term (Recur ,s0 recur-id (#:bind g ,s1) ((#:bind y ,s1))
                            (#:var y ,s1) (Apply ,s1 (#:var g ,s1) (#:lit 0 ,s1)))))
         (cons (term (Recur ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                            (#:var z ,s1) (Apply ,s1 (#:var f ,s1) (#:lit 0 ,s1))))
               (term (Recur ,s0 recur-id (#:bind g ,s1) ((#:bind y ,s1))
                            (#:var w ,s1) (Apply ,s1 (#:var g ,s1) (#:lit 0 ,s1))))))
   (cons (cons (term (RecurVal ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                               (Apply ,s1 (#:var f ,s1) (#:var x ,s1))))
               (term (RecurVal ,s0 recur-id (#:bind g ,s1) ((#:bind y ,s1))
                               (Apply ,s1 (#:var g ,s1) (#:var y ,s1)))))
         (cons (term (RecurVal ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                               (Apply ,s1 (#:var f ,s1) (#:var z ,s1))))
               (term (RecurVal ,s0 recur-id (#:bind g ,s1) ((#:bind y ,s1))
                               (Apply ,s1 (#:var g ,s1) (#:var w ,s1))))))))

(test-case "G1+ の 6 つの束縛形で rename の可否が名指しで決まる"
  (for ([entry (in-list binding-form-cases)])
    (define bound (car entry))
    (define free (cdr entry))
    (check-true (alpha-equivalent? G1+ (car bound) (cdr bound))
                (format "束縛変数の付け替え: ~a" (car bound)))
    (check-false (alpha-equivalent? G1+ (car free) (cdr free))
                 (format "自由変数の付け替え: ~a" (car free)))))

(test-case "G2+ の bmode 付き Let でも rename の可否が名指しで決まる"
  (check-true
   (alpha-equivalent? G2+
                      (term (Let ,s0 ((#:bind x ,s1) const (#:ty Int ,s1))
                                 (#:lit 1 ,s1) (#:var x ,s1)))
                      (term (Let ,s0 ((#:bind y ,s1) const (#:ty Int ,s1))
                                 (#:lit 1 ,s1) (#:var y ,s1)))))
  (check-false
   (alpha-equivalent? G2+
                      (term (Let ,s0 ((#:bind x ,s1) const (#:ty Int ,s1))
                                 (#:lit 1 ,s1) (#:var z ,s1)))
                      (term (Let ,s0 ((#:bind y ,s1) const (#:ty Int ,s1))
                                 (#:lit 1 ,s1) (#:var w ,s1))))))

(test-case "alpha 同値の判定は基底の G1 と一致する"
  (define pairs
    (list (cons (term (Lam User lam-id (x) x)) (term (Lam User lam-id (y) y)))
          (cons (term (Let (x Int) 1 x)) (term (Let (y Int) 1 y)))
          (cons (term (Let (x Int) 1 z)) (term (Let (y Int) 1 w)))
          (cons (term (Recur recur-id f (x) x (Apply f 0)))
                (term (Recur recur-id g (y) y (Apply g 0))))
          (cons (term (Eliminate 1 ((some (x) -> x))))
                (term (Eliminate 1 ((some (y) -> y)))))
          (cons (term (Handle (Return b Int) (x -> x) 1))
                (term (Handle (Return b Int) (y -> y) 1)))))
  (define pairs+
    (list (cons (term (Lam ,s0 User lam-id ((#:bind x ,s1)) (#:var x ,s1)))
                (term (Lam ,s0 User lam-id ((#:bind y ,s1)) (#:var y ,s1))))
          (cons (term (Let ,s0 ((#:bind x ,s1) (#:ty Int ,s1)) (#:lit 1 ,s1)
                            (#:var x ,s1)))
                (term (Let ,s0 ((#:bind y ,s1) (#:ty Int ,s1)) (#:lit 1 ,s1)
                            (#:var y ,s1))))
          (cons (term (Let ,s0 ((#:bind x ,s1) (#:ty Int ,s1)) (#:lit 1 ,s1)
                            (#:var z ,s1)))
                (term (Let ,s0 ((#:bind y ,s1) (#:ty Int ,s1)) (#:lit 1 ,s1)
                            (#:var w ,s1))))
          (cons (term (Recur ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                             (#:var x ,s1) (Apply ,s1 (#:var f ,s1) (#:lit 0 ,s1))))
                (term (Recur ,s0 recur-id (#:bind g ,s1) ((#:bind y ,s1))
                             (#:var y ,s1) (Apply ,s1 (#:var g ,s1) (#:lit 0 ,s1)))))
          (cons (term (Eliminate ,s0 (#:lit 1 ,s1)
                                 ((,s1 some ((#:bind x ,s1)) -> (#:var x ,s1)))))
                (term (Eliminate ,s0 (#:lit 1 ,s1)
                                 ((,s1 some ((#:bind y ,s1)) -> (#:var y ,s1))))))
          (cons (term (Handle ,s0 (Return b (#:ty Int ,s1))
                              (,s1 (#:bind x ,s1) -> (#:var x ,s1)) (#:lit 1 ,s1)))
                (term (Handle ,s0 (Return b (#:ty Int ,s1))
                              (,s1 (#:bind y ,s1) -> (#:var y ,s1)) (#:lit 1 ,s1))))))
  (for ([base (in-list pairs)] [spanful (in-list pairs+)])
    (check-equal? (and (alpha-equivalent? G1+ (car spanful) (cdr spanful)) #t)
                  (and (alpha-equivalent? G1 (car base) (cdr base)) #t)
                  (format "~a" base))))

(test-case "substitute は erase-core の出力に対して G4b 以前と同じ結果を返す"
  (define core+
    (term (Let ,s0 ((#:bind y ,s1) (#:ty Int ,s1)) (#:var x ,s1) (#:var y ,s1))))
  (check-equal? (term (sub ,(erase-core core+) x 7))
                (term (sub (Let (y Int) x y) x 7))))

(test-case "spanful な項へ substitute を掛けると項が壊れる"
  ;; 置換項が (#:var x s) の x の位置へ入り、spanful な項として成立しない。
  ;; この結果があるため、spanful な項に substitute を掛けない契約が要る。
  (define broken (term (sub+ (#:var x ,s1) x (#:lit 7 ,s0))))
  (check-false (redex-match? G2+ c broken))
  (check-false (redex-match? G2+ vr broken)))

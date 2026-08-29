#lang racket

;; G5c5b2。Owned を捕捉する closure の生成を検査する。
(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../typing.rkt")

(define (elaboration-of source)
  (match (elab source)
    [(list core type row callables) (list core type row callables)]
    [other (error 'elaboration-of "elaboration failed: ~s" other)]))

(define (find-capture-let core)
  (cond
    [(and (pair? core)
          (eq? (car core) 'Let)
          (match (third core)
            [`(Curry (Lam User ,_ ,_ ,_) ,_) #t]
            [_ #f]))
     core]
    [(pair? core)
     (for/or ([item (in-list core)])
       (find-capture-let item))]
    [else #f]))

(define (find-lam-by-callable core callable)
  (cond
    [(and (pair? core)
          (eq? (car core) 'Lam)
          (equal? (fourth core) callable))
     core]
    [(pair? core)
     (for/or ([item (in-list core)])
       (find-lam-by-callable item callable))]
    [else #f]))

;; Owned を 1 件捕捉する closure。
(define capture-one-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Fn () Unit (Own) (Drop p))))

(test-case
 "Owned を 1 件捕捉する closure を elaborate でき、型が Owned<NFn> になる"
 (match-define (list core type row callables) (elaboration-of capture-one-surface))
 (check-equal? type '(NFn ((Owned Res)) (Owned (NFn () Unit (Own) ())) (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; Owned を 2 件捕捉する closure。
(define capture-two-surface
  '(Fn ((z (Owned Res)) (a (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Fn () Unit (Own) (Let r (Drop z) (Drop a)))))

(test-case
 "Owned を 2 件捕捉する closure を elaborate できる"
 (match-define (list core type row callables) (elaboration-of capture-two-surface))
 (check-equal? type '(NFn ((Owned Res) (Owned Res))
                          (Owned (NFn () Unit (Own) ())) (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; 捕捉が 0 件なら素の NFn を返す。
(define capture-none-surface
  '(Fn ((n Int)) (NFn () Int () ()) ()
       (Fn () Int () 1)))

(test-case
 "捕捉が 0 件の closure は素の NFn を返す"
 (match-define (list core type row callables) (elaboration-of capture-none-surface))
 (check-equal? type '(NFn (Int) (NFn () Int () ()) () ()))
 (check-equal? (core-type-of core '() callables) (list type row))
 (match (erase-core core)
   [`(Lam User ,_ ,_ ,_) (void)]
   [_ (fail "捕捉 0 件の closure が Lam でない")]))

(test-case
 "捕捉 1 件の closure は Let と Curry の連鎖へ脱糖される"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-one-surface))
 (match (find-capture-let (erase-core core))
   [`(Let (,place let ,let-type)
          (Curry (Lam User ,_ ,capture-binders ,_) (Move p))
          (Move ,same-place))
    (check-equal? let-type '(Owned (NFn () Unit (Own) ())))
    (check-equal? same-place place)
    (check-equal? (length capture-binders) 1)]
   [_ (fail "捕捉 1 件の Let/Curry 形が合わない")]))

(test-case
 "捕捉 formal の binder span は内側の Lam span と一致する"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-one-surface))
 (match (find-lam-by-callable core 'callable1)
   [`(Lam ,lam-span User ,_ ((#:bind ,_ ,binder-span)) ,_)
    (check-equal? binder-span lam-span)]
   [_ (fail "捕捉 formal の span を取り出せない")]))

(test-case
 "捕捉 2 件の Let と Curry は辞書順で並ぶ"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-two-surface))
 (match (find-capture-let (erase-core core))
   [`(Let (,first-place let ,first-type)
          (Curry (Lam User ,_ ,_ ,_) (Move a))
          (Let (,second-place let ,second-type)
               (Curry (Move ,moved-place) (Move z))
               (Move ,last-place)))
    (check-equal? first-type
                  '(Owned (NFn ((Owned Res)) Unit (Own) ())))
    (check-equal? second-type '(Owned (NFn () Unit (Own) ())))
    (check-equal? moved-place first-place)
    (check-equal? last-place second-place)]
   [_ (fail "捕捉 2 件の Let/Curry 順序が合わない")]))

(define capture-name-clash-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Fn () Unit (Own)
           (Let owned1
                (Apply acquire 1)
                (Let tmp (Drop p) (Drop owned1))))))

(test-case
 "捕捉 formal の生名は本体の surface 名と衝突しない"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-name-clash-surface))
 (match (find-lam-by-callable core 'callable1)
   [`(Lam ,_ User ,_ ((#:bind ,raw ,_)) ,_)
    (check-not-equal? raw 'owned1)]
   [_ (fail "捕捉 formal の生名を取り出せない")]))

(test-case
 "捕捉した closure の callable 署名は捕捉型を先頭へ持つ"
 (match-define (list _core _type _row callables)
   (elaboration-of capture-one-surface))
 (check-not-false
  (member '(callable1 (NFn ((Owned Res)) Unit (Own) ())) callables)))

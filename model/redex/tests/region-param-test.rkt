#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../region-param.rkt"
         "../type-equiv.rkt")

(define forall-a
  (term (ForallRegion (a) (NFn ((Borrowed Int (RParam a))) Int () ()))))
(define forall-b
  (term (ForallRegion (b) (NFn ((Borrowed Int (RParam b))) Int () ()))))

;; 文法。G2 と G2m の双方で region の型と項を受ける。
(test-case
 "region の形が G2 と G2m の両方に属する"
 (for ([language (in-list '(G2 G2m))]
       [c-match? (in-list (list (lambda (t) (redex-match? G2 c t))
                                (lambda (t) (redex-match? G2m c t))))]
       [v-match? (in-list (list (lambda (t) (redex-match? G2 v t))
                                (lambda (t) (redex-match? G2m v t))))]
       [τ-match? (in-list (list (lambda (t) (redex-match? G2 τ t))
                                (lambda (t) (redex-match? G2m τ t))))])
   (check-true (c-match? (term (RegionLam (a) x)))
               (format "~a: RegionLam が c" language))
   (check-true (v-match? (term (RegionLam (a) x)))
               (format "~a: RegionLam が v" language))
   (check-true (c-match? (term (RegionApp (RegionLam (a) x) ((RParam a)))))
               (format "~a: RegionApp が c" language))
   (check-true (τ-match? forall-a)
               (format "~a: ForallRegion が τ" language))))

;; core-children と core-with-children は RegionLam/RegionApp の形を往復する。
(test-case
 "core-children で取り出した子を core-with-children で戻すと同じ形になる"
 (for ([shape (in-list (list (term (RegionLam (a) x))
                             (term (RegionApp x ((RParam a))))))])
   (check-equal? (core-with-children shape (core-children shape)) shape)))

;; 束縛名と region 実引数を core の子に数えないため、free-vars に現れない。
(test-case
 "core-free-vars が rp を数えない"
 (check-equal? (core-free-vars (term (RegionLam (a) x))) (set 'x))
 (check-equal? (core-free-vars (term (RegionApp x ((RParam a))))) (set 'x)))

;; ForallRegion の束縛名を region-free-params から除く。
(test-case
 "region-free-params が束縛名を除く"
 (check-equal? (region-free-params forall-a) (set))
 (check-equal?
  (region-free-params
   (term (NFn ((Borrowed Int (RParam a))) Int () ())))
  (set 'a))
 (check-equal?
  (region-free-params
   (term (ForallRegion (a)
                       (NFn ((ForallRegion (a)
                                             (Borrowed Int (RParam a))))
                            Int () ()))))
  (set)))

;; 入れ子の同名束縛を外側の付け替えで捕獲しない。
(test-case
 "入れ子の同名の束縛が外側の付け替えで捕獲されない"
 (define renamed
   (call-with-region-params
    (lambda ()
      (alpha-rename-region-lam
       (term (RegionLam (a)
                        (RegionApp (RegionLam (a) (Borrow x)) ((RParam a)))))))))
 (match renamed
   [`(RegionLam (,outer) (RegionApp (RegionLam (,inner) ,_) ((RParam ,argument))))
    (check-not-equal? outer 'a)
    (check-equal? inner 'a)
    (check-equal? argument outer)]
   [other (fail (format "形が変わった: ~s" other))]))

;; spanful な RegionLam も同じ補助で扱う。
(test-case
 "spanful な RegionLam の束縛名を付け替える"
 (define span '(#:span src 10 20))
 (define inner-span '(#:span src 12 18))
 (define renamed
   (call-with-region-params
    (lambda ()
      (alpha-rename-region-lam
       `(RegionLam ,span (a)
                   (RegionApp ,inner-span
                              (RegionLam ,inner-span (a) (#:var x ,inner-span))
                              ((RParam a))))))))
 (match renamed
   [`(RegionLam ,kept (,outer)
                (RegionApp ,_ (RegionLam ,_ (,inner) ,_) ((RParam ,argument))))
    (check-equal? kept span)
    (check-not-equal? outer 'a)
    (check-equal? inner 'a)
    (check-equal? argument outer)]
   [other (fail (format "形が変わった: ~s" other))]))

;; 生成名が内側の束縛名と衝突しない。
(test-case
 "生成名が内側の束縛名と衝突しても捕獲されない"
 (define renamed
   (call-with-region-params
    (lambda ()
      (alpha-rename-region-lam
       (term (RegionLam (a)
                        (RegionLam (a.0) (Borrowed Int (RParam a)))))))))
 (match renamed
   [`(RegionLam (,outer) (RegionLam (,inner) (Borrowed Int (RParam ,used))))
    (check-not-equal? outer 'a)
    (check-not-equal? outer inner)
    (check-equal? inner 'a.0)
    (check-equal? used outer)]
   [other (fail (format "形が変わった: ~s" other))]))

;; 別々の RegionLam は同じ base でも異なる名前を得る。
(test-case
 "別々の RegionLam の同名が別の名前になる"
 (define-values (left right)
   (call-with-region-params
    (lambda ()
      (values (alpha-rename-region-lam (term (RegionLam (a) x)))
              (alpha-rename-region-lam (term (RegionLam (a) x)))))))
 (match* (left right)
   [(`(RegionLam (,left-name) ,_) `(RegionLam (,right-name) ,_))
    (check-not-equal? left-name right-name)]))

;; counter は文脈ごとに初期化される。
(test-case
 "付け替えが文脈ごとに決定的である"
 (define (rename-once)
   (call-with-region-params
    (lambda () (alpha-rename-region-lam (term (RegionLam (a) x))))))
 (check-equal? (rename-once) (rename-once))
 (check-exn exn:fail?
            (lambda () (alpha-rename-region-lam (term (RegionLam (a) x))))))

;; ForallRegion の束縛名は型同値で吸収する。
(test-case
 "type-equiv? が ForallRegion の束縛名を吸収する"
 (check-true (type-equiv? forall-a forall-b))
 (check-false (type-equiv? forall-a
                           (term (ForallRegion (a b)
                                               (NFn ((Borrowed Int (RParam a)))
                                                    Int () ())))))
 (check-false
  (type-equiv?
   (term (ForallRegion (b) (NFn ((Borrowed Int (RParam b))) Int () ())))
   (term (ForallRegion (a) (NFn ((Borrowed Int (RParam b))) Int () ())))))
 (check-true
  (type-equiv?
   (term (ForallRegion (a) (ForallRegion (a) (Borrowed Int (RParam a)))))
   (term (ForallRegion (b) (ForallRegion (c) (Borrowed Int (RParam c))))))))

;; Union の正規化も α 同値な ForallRegion を重複除去する。
(test-case
 "normalize-type が α 同値な ForallRegion を Union から重複除去する"
 (check-equal? (normalize-type (term (Union ,forall-a ,forall-b)))
               (normalize-type forall-a)))

;; normalize-type は宣言型に書いた binder 名を保存する。
(test-case
 "normalize-type が ForallRegion の束縛子名を保存する"
 (check-equal? (normalize-type forall-a) forall-a)
 (check-true (type-normal? forall-a))
 (check-true (type-normal? forall-b)))

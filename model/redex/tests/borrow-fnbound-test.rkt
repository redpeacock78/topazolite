#lang racket

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../region-param.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; [REQ: BOR-007] 関数境界の借用の受け渡し。
;; 判定は「借用型があれば違反」ではなく「region 欄が束縛された (RParam rp) で
;; なければ違反」である。

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; (a) 束縛された rp なら違反ではない。
(test-case
 "束縛された rp の借用は境界を越えられる"
 (check-false (unbound-borrowed-type? '(Borrowed Int (RParam a)) (set 'a)))
 (check-false (unbound-borrowed-type? '(BorrowedMut Int (RParam a)) (set 'a)))
 ;; 走査は型木のどこへでも入る。葉の判定だけが変わる。
 (check-false (unbound-borrowed-type?
               '(NFn ((Union (Borrowed Int (RParam a)) Int))
                     (Option (BorrowedMut Int (RParam a))) () ())
               (set 'a))))

;; (b) 束縛されていない rp は違反である。
(test-case
 "束縛されていない rp の借用は違反である"
 (check-true (unbound-borrowed-type? '(Borrowed Int (RParam a)) (set 'b)))
 (check-true (unbound-borrowed-type? '(Borrowed Int (RParam a)) (set)))
 ;; 混在。1 つでも束縛されていなければ違反である。
 (check-true
  (unbound-borrowed-type?
   '(NFn ((Borrowed Int (RParam a)) (Borrowed Int (RParam b))) Int () ())
   (set 'a))))

;; (c) 具体的な region の借用は、束縛の集合に何が入っていても違反である。
;; 呼出し側の region を関数の内側から名指す形は開かない。
(test-case
 "具体的な region の借用は境界を越えられない"
 (check-true (unbound-borrowed-type? '(Borrowed Int 0) (set 'a)))
 (check-true (unbound-borrowed-type? '(Borrowed Int (RVar 3)) (set 'a))))

;; (d) 借用でない型は違反ではない。既定の引数で今日と同じ判定になる。
(test-case
 "借用でない型は違反ではない"
 (check-false (unbound-borrowed-type? '(Union Int String)))
 (check-false (unbound-borrowed-type? '(NFn (Int Bool) (Option Int) () ())))
 (check-false (unbound-borrowed-type? '(Refined Int (Implements Int Tn)))))

;; (e) parameter の既定は空集合である。
;; 既定のままの呼び出しでは、あらゆる借用型が違反になる。
(test-case
 "bound-region-params の既定は空集合である"
 (check-equal? (bound-region-params) (set))
 (check-true (unbound-borrowed-type? '(Borrowed Int (RParam a))))
 (parameterize ([bound-region-params (set 'a)])
   (check-false (unbound-borrowed-type? '(Borrowed Int (RParam a))))))

;; (f) 既存の 3 つの key の発火位置は変わらない。
;; 束縛が空の文脈では、今日と同じ位置で同じ key が出る。
(test-case
 "既存の 3 つの key が同じ位置で出る"
 (define (boundary-key core signature)
   (define ir (build-region-ir core))
   (define rho (region->rho ir (region-at ir '())))
   (key-of (type-of/raw core '() (list (list 'f (signature rho))) '()
                        (region-ctx ir '() (hash) (hash)))))
 (check-equal?
  (boundary-key '(Scope () (Let (x let (Owned Res)) (resource 1) (Lam User f (a) 0)))
                (lambda (rho) `(NFn ((Borrowed Int ,rho)) Int () ())))
  'borrowed-function-parameter)
 (check-equal?
  (boundary-key '(Scope () (Lam User f (a) 0))
                (lambda (rho) `(NFn (Int) (Borrowed Int ,rho) () ())))
  'borrowed-function-result))

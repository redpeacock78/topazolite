#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../typing.rkt")

;; collector が無いときは何も起きない。
(check-equal? (collected-constraints) '())

;; 型の中の RVar それぞれに下限制約が立つ（spec §5.1）。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ (region-at ir '(0 0)))
  (define cs
    (with-lifetime-collector
      (lambda ()
        (collect-use-regions! '(Borrowed Int (RVar 0)) ir '(0 0))
        (collect-use-regions! 'Int ir '(0 0)))))
  (check-equal? cs (list (region-constraint 'contains '(RVar 0) ρ '(0 0) #f))))

;; 入れ子の型の中の RVar も拾う。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ (region-at ir '(0 0)))
  (define cs
    (with-lifetime-collector
      (lambda ()
        (collect-use-regions! '(Option (Borrowed Int (RVar 2))) ir '(0 0)))))
  (check-equal? cs (list (region-constraint 'contains '(RVar 2) ρ '(0 0) #f))))

;; 同じ α が 2 か所に現れると制約は 2 本立つ。並びは立てた順である。
(let ()
  (define core '(Scope () (Yield (Scope () 0) (Scope () 0))))
  (define ir (build-region-ir core))
  (define ρ1 (region-at ir '(0 0 0)))
  (define ρ2 (region-at ir '(0 1 0)))
  (define cs
    (with-lifetime-collector
      (lambda ()
        (collect-use-regions! '(Borrowed Int (RVar 0)) ir '(0 0 0))
        (collect-use-regions! '(Borrowed Int (RVar 0)) ir '(0 1 0)))))
  (check-equal? cs
                (list (region-constraint 'contains '(RVar 0) ρ1 '(0 0 0) #f)
                      (region-constraint 'contains '(RVar 0) ρ2 '(0 1 0) #f))))

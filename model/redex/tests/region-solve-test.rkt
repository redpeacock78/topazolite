#lang racket

(require rackunit
         racket/match
         racket/set
         "../region.rkt")

;; 空の制約集合は空の σ を返す。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (check-equal? (region-solve ir '()) (list 'ok (hash))))

;; 下限が 1 つのとき、α の解はその region である。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ-inner (region-at ir '(0 0)))
  (define cs (list (region-constraint 'contains '(RVar 0) ρ-inner '(0 0) #f)))
  (check-equal? (region-solve ir cs) (list 'ok (hash 0 ρ-inner))))

;; 下限が 2 つのとき、両方を含む極小の region が解である。
;; lexical adapter では最小共通祖先が唯一の極小解である。
(let ()
  (define core '(Scope () (Yield (Scope () 0) (Scope () 0))))
  (define ir (build-region-ir core))
  (define ρ-left (region-at ir '(0 0 0)))
  (define ρ-right (region-at ir '(0 1 0)))
  (define ρ-outer (region-at ir '(0)))
  (define cs (list (region-constraint 'contains '(RVar 0) ρ-left '(0 0 0) #f)
                   (region-constraint 'contains '(RVar 0) ρ-right '(0 1 0) #f)))
  (check-equal? (region-solve ir cs) (list 'ok (hash 0 ρ-outer))))

;; 上限制約は σ を代入してから検査する。満たすときは ok。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ-outer (region-at ir '()))
  (define ρ-inner (region-at ir '(0 0)))
  (define cs (list (region-constraint 'contains '(RVar 0) ρ-inner '(0 0) #f)
                   (region-constraint 'outlives ρ-outer '(RVar 0) '(0 0) #f)))
  (check-equal? (region-solve ir cs) (list 'ok (hash 0 ρ-inner))))

;; 上限制約が破れると error になり、破れた制約だけを並びで返す。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ-outer (region-at ir '()))
  (define ρ-inner (region-at ir '(0 0)))
  (define broken (region-constraint 'outlives ρ-inner '(RVar 0) '(0 0) #f))
  (define cs (list (region-constraint 'contains '(RVar 0) ρ-outer '() #f)
                   broken))
  (check-equal? (region-solve ir cs) (list 'error (list broken))))

;; 制約の並び順に依らず、同じ σ を返す。
(let ()
  (define core '(Scope () (Yield (Scope () 0) (Scope () 0))))
  (define ir (build-region-ir core))
  (define cs-forward
    (list (region-constraint 'contains '(RVar 0)
                             (region-at ir '(0 0 0)) '(0 0 0) #f)
          (region-constraint 'contains '(RVar 0)
                             (region-at ir '(0 1 0)) '(0 1 0) #f)))
  (define cs-reverse (reverse cs-forward))
  (match-define (list 'ok σ-forward) (region-solve ir cs-forward))
  (match-define (list 'ok σ-reverse) (region-solve ir cs-reverse))
  (check-equal? σ-forward σ-reverse))

;; 寿命項の判別。
(check-true (lifetime-var? '(RVar 3)))
(check-equal? (lifetime-var-index '(RVar 3)) 3)
(check-false (lifetime-var? (region 0)))

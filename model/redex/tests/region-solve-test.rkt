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

;; 複数の上限制約が破れたときも、発生順のまま返す。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ-outer (region-at ir '()))
  (define ρ-inner (region-at ir '(0 0)))
  (define lower-0
    (region-constraint 'contains '(RVar 0) ρ-outer '() #f))
  (define broken-0
    (region-constraint 'outlives ρ-inner '(RVar 0) '(0 0) 'first))
  (define lower-1
    (region-constraint 'contains '(RVar 1) ρ-outer '() #f))
  (define broken-1
    (region-constraint 'outlives ρ-inner '(RVar 1) '(0 0) 'second))
  (check-equal?
   (region-solve ir (list lower-0 broken-0 lower-1 broken-1))
   (list 'error (list broken-0 broken-1))))

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

;; 寿命変数を右辺に持つ contains は、その寿命の解を下限として伝播する。
;; 中間変数への下限より先に依存辺を読む順でも、固定点で同じ σ になる。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ (region-at ir '(0 0)))
  (define α3-lower
    (region-constraint 'contains '(RVar 3) '(RVar 1) '() #f))
  (define α1-lower
    (region-constraint 'contains '(RVar 1) ρ '() #f))
  (match-define
    (list 'ok σ-forward)
    (region-solve ir (list α3-lower α1-lower)))
  (match-define
    (list 'ok σ-reverse)
    (region-solve ir (list α1-lower α3-lower)))
  (check-equal? σ-forward (hash 1 ρ 3 ρ))
  (check-equal? σ-reverse σ-forward)
  (check-true (region-outlives? ir (hash-ref σ-forward 3) ρ)))

;; 具体下限を持つ依存サイクルも有限の固定点で解ける。
(let ()
  (define core '(Scope () (Scope () 0)))
  (define ir (build-region-ir core))
  (define ρ (region-at ir '(0 0)))
  (define cs
    (list (region-constraint 'contains '(RVar 0) '(RVar 1) '() #f)
          (region-constraint 'contains '(RVar 1) '(RVar 0) '() #f)
          (region-constraint 'contains '(RVar 0) ρ '() #f)))
  (check-equal? (region-solve ir cs)
                (list 'ok (hash 0 ρ 1 ρ))))

;; concrete 下限と寿命変数への依存が合流すると、lexical join が最小解になる。
(let ()
  (define core '(Scope () (Yield (Scope () 0) (Scope () 0))))
  (define ir (build-region-ir core))
  (define ρ-left (region-at ir '(0 0 0)))
  (define ρ-right (region-at ir '(0 1 0)))
  (define ρ-outer (region-at ir '(0)))
  (define cs
    (list (region-constraint 'contains '(RVar 1) ρ-left '() #f)
          (region-constraint 'contains '(RVar 0) '(RVar 1) '() #f)
          (region-constraint 'contains '(RVar 0) ρ-right '() #f)))
  (match-define (list 'ok σ) (region-solve ir cs))
  (check-equal? (hash-ref σ 1) ρ-left)
  (check-equal? (hash-ref σ 0) ρ-outer)
  (check-true (region-outlives? ir (hash-ref σ 0) ρ-right)))

;; 制約に lower-bound の無い右辺寿命変数が残る場合、solver は未解決の
;; contains を broken として返す。通常の型検査では各 fresh alpha が
;; 生成時に concrete lower bound を受けるため、この形は不変条件違反である。
(let ()
  (define core '(Scope () 0))
  (define ir (build-region-ir core))
  (define unresolved
    (region-constraint 'contains '(RVar 0) '(RVar 1) '() #f))
  (check-equal? (region-solve ir (list unresolved))
                (list 'error (list unresolved))))

;; 寿命項の判別。
(check-true (lifetime-var? '(RVar 3)))
(check-equal? (lifetime-var-index '(RVar 3)) 3)
(check-false (lifetime-var? (region 0)))

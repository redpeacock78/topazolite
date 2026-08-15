#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt"
         "../machine.rkt")

;; config に現れる借用値を実装から独立に拾う。
(define (live-borrow-refs config)
  (define (collect t)
    (match t
      [`(BorrowRef ,p ,ρ) (list (list p ρ))]
      [`(BorrowMutRef ,p ,ρ) (list (list p ρ))]
      [(? list?) (append* (map collect t))]
      [_ '()]))
  (match config
    [`(cfg ,c ,H ,_ ,_) (append (collect c) (collect H))]))

(define (omega-of config)
  (match config [`(cfg ,_ ,_ ,Ω ,_) Ω]))

(define (all-configs config fuel)
  (let loop ([frontier (list config)] [seen '()] [remaining fuel])
    (cond
      [(or (null? frontier) (zero? remaining)) (append seen frontier)]
      [else
       (define next (append* (map raw-steps-g2 frontier)))
       (loop next (append seen frontier) (sub1 remaining))])))

;; 借用の値は内側の non-owned Let で 0 へ消費し、owner Scope の外へ返さない。
;; region subsumption は未回収のため、13.2 の検査はこの範囲の fixture に限る。
(define stage-1-skeleton
  '(Scope ()
     (Let (x let (Owned Res)) (resource 1)
       (Scope ()
         (Let (y let (Borrowed Res 0)) (Borrow x) 0)))))

(define ir (build-region-ir stage-1-skeleton))
(define stage-1-rho (region->rho ir (region-at ir '(0 1 0 0))))
(define (fill-stage-1 t)
  (cond [(equal? t '(Borrowed Res 0)) `(Borrowed Res ,stage-1-rho)]
        [(pair? t) (cons (fill-stage-1 (car t))
                         (fill-stage-1 (cdr t)))]
        [else t]))
(define stage-1 (fill-stage-1 stage-1-skeleton))
(check-equal? (first (type-of/raw stage-1 '() '() '()
                                  (region-ctx ir '() (hash) (hash))))
              'ok)
(define stage-2 (annotate-regions stage-1 ir))
(define stage-3 (inject-g2m stage-2))

;; 型検査済み config の到達列では、生きている借用の place は Available である。
(let ()
  (define configs (all-configs stage-3 40))
  (define refs (append* (map live-borrow-refs configs)))
  (check-true (positive? (length refs)))
  (for ([config (in-list configs)])
    (for ([ref (in-list (live-borrow-refs config))])
      (check-equal? (match (assoc (first ref) (omega-of config))
                      [(list _ state) state]
                      [_ #f])
                    'Available))))

;; Moved の place からは BorrowRef を作らず Error へ落ちる。
(let ()
  (define n-root (region->rho ir (region-at ir '())))
  (define config `(cfg (Scope () (BorrowAt ,n-root 0))
                       ((0 1))
                       ((0 Moved))
                       ()))
  (define next (raw-steps-g2 config))
  (check-equal? (length next) 1)
  (check-equal? (live-borrow-refs (first next)) '())
  (check-equal? (first next)
                `(cfg (Scope () (Error 0)) ((0 1)) ((0 Moved)) ())))

;; 手組みの config は invariant を破るので、独立な抽出が検出する。
(let ()
  (define n-root (region->rho ir (region-at ir '())))
  (define config `(cfg (Scope () (BorrowRef 0 ,n-root))
                       ((0 1))
                       ((0 Moved))
                       ()))
  (define refs (live-borrow-refs config))
  (check-equal? (length refs) 1)
  (check-not-equal? (match (assoc (first (first refs)) (omega-of config))
                           [(list _ state) state]
                           [_ #f])
                   'Available))

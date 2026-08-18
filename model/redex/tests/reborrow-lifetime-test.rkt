#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; Let の宣言型の ρ は Task 8 と同じ引き方で IR から取る。
;; Reborrow の結果 region は Reborrow 節点自身の point の region であり、
;; 親の可変借用の region は BorrowMut 節点の point の region である。
;; typing.rkt の infer-reborrow が ρ_child を region-at (region-ctx-point Λ) で
;; 取っているのと同じ数え方である。
(define (rho-at ir point) (region->rho ir (region-at ir point)))

;; Reborrow は通る。親と子は BOR-002 を立てない。
;; operand は Let で束縛した変数であり、borrow-annotate-test.rkt の
;; (Reborrow (BorrowMut b)) と同じく Reborrow の子は core である。
(let ()
  (define (make ρ_p) `(Scope (1) (Let (p let (BorrowedMut Res ,ρ_p)) (BorrowMut 1)
                                      (Scope () (Reborrow p)))))
  (define ir (build-region-ir (make 0)))
  ;; BorrowMut は Let の子 0 に居る。
  (define annotated (annotate-regions (make (rho-at ir '(0 0))) ir))
  (check-equal?
   (first (type-of/raw annotated (list (list 1 'Res)) '() '()
                       (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'ok))

;; 停止中の親を Move すると拒む。
(let ()
  (define (make ρ_p ρ_q)
    `(Scope (1) (Let (p let (BorrowedMut Res ,ρ_p)) (BorrowMut 1)
                     (Let (q let (Borrowed Res ,ρ_q)) (Reborrow p)
                          (Move 1)))))
  (define ir (build-region-ir (make 0 0)))
  ;; BorrowMut は '(0 0)、Reborrow は内側 Let の子 0 で '(0 1 0) に居る。
  (define annotated
    (annotate-regions (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir))
  (check-equal?
   (key-of (type-of/raw annotated (list (list 1 'Res)) '() '()
                        (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'move-borrowed))

;; 親の借用ごと内側の Scope で尽きた後は Move を許す。
;; 停止は子の寿命の間だけであり、Scope を出た後まで残らない。
(let ()
  (define (make ρ_p ρ_q)
    `(Scope (1) (Let (r let Int)
                     (Scope () (Let (p let (BorrowedMut Res ,ρ_p)) (BorrowMut 1)
                                    (Let (q let (Borrowed Res ,ρ_q)) (Reborrow p)
                                         0)))
                     (Move 1))))
  (define ir (build-region-ir (make 0 0)))
  ;; BorrowMut は '(0 0 0 0)、Reborrow は '(0 0 0 1 0) に居る。
  (define annotated
    (annotate-regions (make (rho-at ir '(0 0 0 0)) (rho-at ir '(0 0 0 1 0))) ir))
  (check-equal?
   (first (type-of/raw annotated (list (list 1 'Res)) '() '()
                       (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'ok))

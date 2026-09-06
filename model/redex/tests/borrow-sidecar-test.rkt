#lang racket

(require rackunit
         racket/match
         "../borrow.rkt"
         "../region.rkt"
         "../typing.rkt")

;; 外側で所有値を束縛し、内側 Scope で共有借用を作って消費する骨格。
;; borrow-machine-test.rkt の stage-1-skeleton と同じ形を使う。
(define shared-skeleton
  '(Scope ()
     (Let (x let (Owned Res)) (resource 1)
       (Scope ()
         (Let (y let (Borrowed Res 0)) (Borrow x) 0)))))

(define shared-ir (build-region-ir shared-skeleton))
(define shared-rho
  (region->rho shared-ir (region-at shared-ir '(0 1 0 0))))

(define (fill-rho rho t)
  (cond [(equal? t '(Borrowed Res 0)) `(Borrowed Res ,rho)]
        [(pair? t) (cons (fill-rho rho (car t))
                         (fill-rho rho (cdr t)))]
        [else t]))

(define shared-term (fill-rho shared-rho shared-skeleton))

(define (sidecar-of term ir)
  (match (type-of/raw*+borrows term '() '() '()
                               (region-ctx ir '() (hash) (hash)))
    [(list 'ok (list _type _row _table _σ _renamed sidecar)) sidecar]
    [other other]))

(test-case "共有借用の項の sidecar は借用要求を 1 件持つ"
  (define sidecar (sidecar-of shared-term shared-ir))
  (check-true (borrow-sidecar? sidecar))
  (check-equal? (length (borrow-sidecar-requests sidecar)) 1)
  (check-equal? (borrow-request-mode
                 (first (borrow-sidecar-requests sidecar)))
                'shared))

(test-case "sidecar の alpha は未解決で、sigma が解ける"
  (define sidecar (sidecar-of shared-term shared-ir))
  (define request (first (borrow-sidecar-requests sidecar)))
  (define σ (borrow-sidecar-sigma sidecar))
  (check-true (hash? σ))
  (check-true (lifetime-var? (borrow-request-alpha request)))
  (check-true
   (hash-has-key? σ (lifetime-var-index (borrow-request-alpha request)))))

(test-case "型検査が落ちる項では既存 API と同じ失敗の形を返す"
  (define broken '(Scope () (Read 0)))
  (define broken-ir (build-region-ir broken))
  (match (type-of/raw*+borrows broken '() '() '()
                               (region-ctx broken-ir '() (hash) (hash)))
    [(list 'fail _key _node _details) (check-true #t)]
    [other (fail (format "unexpected result: ~e" other))]))

#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(define (run core ir)
  (typing-inference core '() '() '()
                    (region-ctx ir '() (hash) (hash))))

(define (alpha-table-of core ir) (second (run core ir)))
(define (constraints-of core ir) (third (run core ir)))
(define (borrow-rho-of core ir)
  (match (first (run core ir)) [`(Borrowed ,_ ,ρ) ρ]))

;; 借用の項 1 つにつき寿命変数が 1 つできる（spec §3.2）。
;; 借用が 2 つある形では α が 2 つ、採番は走査の順である。
(let ()
  (define core
    `(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Yield (Borrow x) (Borrow x)))))
  (define ir (build-region-ir core))
  (define table
    (alpha-table-of core ir))
  (check-equal? (hash-count table) 2)
  ;; 値は互いに異なる。
  (check-equal? (length (remove-duplicates (hash-values table))) 2))

;; 借用の起点で下限と上限が 1 本ずつ立つ。
(let ()
  (define core
    `(Scope () (Let (x let (Owned Res)) (resource 1) (Borrow x))))
  (define ir (build-region-ir core))
  (define cs (constraints-of core ir))
  (check-equal? (length (filter (lambda (c)
                                  (eq? (region-constraint-kind c) 'outlives))
                                cs))
                1)
  ;; 下限は起点の 1 本と、出口の収集が立てる 1 本以上である。
  (check-true (>= (length (filter (lambda (c)
                                    (eq? (region-constraint-kind c) 'contains))
                                  cs))
                  1)))

;; 借用の型の region 欄は寿命変数である。
(let ()
  (define core
    `(Scope () (Let (x let (Owned Res)) (resource 1) (Borrow x))))
  (define ir (build-region-ir core))
  (check-true (lifetime-var? (borrow-rho-of core ir))))

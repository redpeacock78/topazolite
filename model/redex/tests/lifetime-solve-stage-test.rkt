#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; region-ctx は borrow.rkt の側にある。region.rkt だけでは解決できない。

;; ir が無い形では σ は空である。
(check-equal? (typing-solve #f '()) (list 'ok (hash)))

;; 借用 1 件の形で σ が引ける。
(let ()
  (define core '(Scope (1) (Borrow 1)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (match-define (list _type tbl cs _rs _ras)
    (typing-inference annotated (list (list 1 'Res)) '() '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (match-define (list 'ok σ) (typing-solve ir cs))
  (define α (hash-ref tbl '(0)))
  (check-true (region? (sigma-ref σ α)))
  ;; 借用の値が外へ出ないので、解は起点の region である。
  (check-equal? (sigma-ref σ α) (region-at ir '(0))))

;; 具体的な region はそのまま返る。
(let ()
  (define core '(Scope (1) (Borrow 1)))
  (define ir (build-region-ir core))
  (define ρ (region-at ir '()))
  (check-equal? (sigma-ref (hash) ρ) ρ))

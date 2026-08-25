#lang racket

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; 借用は borrow-request を 1 件立てる。
;; fixture は注釈前の形で書き、annotate-regions を 1 度だけ通す。
;; 注釈済みの core を再び渡すと annotate-regions は error になる。
(let ()
  (define core '(Scope (1) (Borrow 1)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (match-define (list _type _tbl _cs rs _ras)
    (typing-inference annotated (list (list 1 'Res)) '() '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (length (filter borrow-request? rs)) 1)
  (define r (first (filter borrow-request? rs)))
  (check-equal? (borrow-request-w r) 1)
  (check-equal? (borrow-request-mode r) 'shared)
  (check-true (lifetime-var? (borrow-request-alpha r))))

;; Move は use-request を 1 件立てる。判定はまだ走らない。
;; Λ を省くと既定の empty-region-ctx になり、ir が #f なので emit-use-request! は
;; 何も記録しない。借用の fixture と同じく ir を作って Λ へ載せる。
;; 借用の節点が無いので annotate-regions は通さない。置き換える注釈欄が無いためである。
(let ()
  (define core '(Move x))
  (define ir (build-region-ir core))
  (match-define (list _type _tbl _cs rs _ras)
    (typing-inference core '() '() (list (list 'x '(Owned Int)))
                      (region-ctx ir '() (hash) (hash))))
  (check-equal? (length (filter use-request? rs)) 1)
  (check-equal? (use-request-w (first (filter use-request? rs))) 'x))

;; Ψ の項目は α を鍵に持つ。
(let ()
  (define alpha '(RVar 0))
  (define Ψ (psi-add-mut (empty-psi) 'x '() alpha))
  (check-equal? (psi-mut Ψ) (set (list 'x '() alpha))))

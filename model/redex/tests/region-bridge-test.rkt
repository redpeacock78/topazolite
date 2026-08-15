#lang racket

(require rackunit
         racket/set
         "../region.rkt")

(define core
  '(Scope ()
     (Let (x Int) 1
       (Scope () (Let (y Int) 2 y)))))

;; 1 本目: 往復。ir の全 region について rho->region が region->rho の逆になる。
(let ([ir (build-region-ir core)])
  (for ([ρ (in-set (region-ir-regions ir))])
    (check-equal? (rho->region ir (region->rho ir ρ)) ρ)))

;; 2 本目: fresh 性。同じ core から独立に 2 つ作った ir は、対応する位置の
;; region が一致しない。採番値の大小や連番は観測しない。
;; 一致しないことだけを見る。
(let ([ir1 (build-region-ir core)]
      [ir2 (build-region-ir core)])
  (check-equal? (set-count (set-intersect (region-ir-regions ir1)
                                          (region-ir-regions ir2)))
                0))

;; 3 本目: IR 間の非混同。一方の region と rho を他方の bridge へ渡すと error。
(let ([ir1 (build-region-ir core)]
      [ir2 (build-region-ir core)])
  (define ρ1 (region-at ir1 '()))
  (check-exn exn:fail? (lambda () (region->rho ir2 ρ1)))
  (check-exn exn:fail? (lambda () (rho->region ir2 (region->rho ir1 ρ1)))))

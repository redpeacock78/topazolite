#lang racket

(require rackunit
         racket/set
         "../borrow.rkt"
         "../region.rkt"
         "../typing.rkt")

(test-case "分解の退場は部分木の外の後続 point だけ"
  (define ir
    (build-region-ir
     '(Scope ()
        (Let (z let Unit)
             (Eliminate y ((none () -> unit) (some (v) -> unit)))
          unit))))
  (define E '(0 0))
  (check-true (point-after-decomposition? ir E '(0 1)))
  (check-false (point-after-decomposition? ir E '(0 0 1)))
  (check-false (point-after-decomposition? ir E '(0 0 2)))
  (check-false (point-after-decomposition? ir E '(0)))
  (check-false (point-after-decomposition? ir E E)))

(test-case "Handle の handler と本体をまたぐ分解の point は後続としない"
  (define ir
    (build-region-ir
     '(Scope ()
        (Handle (Return b Int)
          (k -> (Eliminate y ((none () -> unit) (some (v) -> unit))))
          unit))))
  (check-false (point-after-decomposition? ir '(0 0) '(0 1)))
)

(test-case "同じ枝の後続使用は分解の退場として除かれない"
  (define core
    '(Scope (1)
       (Eliminate (Construct Bool true)
         ((true () ->
                 (Let (b let (BorrowedMut Int (RVar 0))) (BorrowMut 1)
                   (Let (written let Unit) (Assign (BorrowMut 1) 2)
                     (Read b))))
          (false () -> 0)))))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw (annotate-regions core ir)
                 (list (list 1 'Int)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (second result) 'borrow-conflicting-alias))

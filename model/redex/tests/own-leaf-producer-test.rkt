#lang racket/base

;; G5c5b3b。値の内部の所有資源へ token を割り当てる producer 経路の回帰。
(require rackunit
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define (step config)
  (define results (apply-reduction-relation -->g1 config))
  (check-equal? (length results) 1
                (format "一手だけ進む: ~s" results))
  (car results))

(test-case "R-OwnLeaf は payload を OwnedLeaf へ置き換え Λtok へ Available を足す"
  (check-equal?
   (step (term (cfg (OwnLeaf (resource 1)) () () () ())))
   (term (cfg (OwnedLeaf (tok 0) (resource 1)) () () (((tok 0) Available)) ()))))

(test-case "R-OwnLeaf は Dropped の tombstone の番号を再利用しない"
  (check-equal?
   (step (term (cfg (OwnLeaf (resource 1)) () () (((tok 0) Dropped)) ())))
   (term (cfg (OwnedLeaf (tok 1) (resource 1)) () ()
              (((tok 0) Dropped) ((tok 1) Available)) ()))))

(test-case "R-OwnLeaf は Λtok に無い制御項の token も避ける"
  (check-equal?
   (step (term (cfg (Apply (OwnLeaf (resource 2))
                           (OwnedLeaf (tok 3) (resource 1)))
                    () () () ())))
   (term (cfg (Apply (OwnedLeaf (tok 4) (resource 2))
                     (OwnedLeaf (tok 3) (resource 1)))
              () () (((tok 4) Available)) ()))))

(test-case "producer 位置でない OwnLeaf は unexpected-ownleaf で落ちる"
  (check-equal? (core-type-of '(OwnLeaf 1) '() '()) 'ill-typed)
  (define diagnostic (core-type-of/diagnostic '(OwnLeaf 1) '() '()))
  (check-true (diagnostic? diagnostic))
  (check-equal? (diagnostic-id diagnostic)
                (diagnostic-code-of 'typing 'unexpected-ownleaf)))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../type-shape.rkt"
         "../typing.rkt"
         "../machine.rkt")

;; 試験 1: core-children と core-with-children が逆である。
;; Scope を 2 重にするのは試験 5 のためである。Scope が 1 つだと core の
;; どの点も同じ region になり、別の point の region を注釈へ置く形が作れない。
;; 枝は G2 の br、すなわち K (x ...) -> c の形で書く。-> を落とすと
;; core-children は last で本文を拾えても、文法としては Core でなくなる。
(define sample
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Scope ()
         (Eliminate (Move x)
           ((K1 (a) -> (Borrow a))
            (K2 (b) -> (Reborrow (BorrowMut b)))))))))

(define (round-trip-ok? t)
  (and (equal? t (core-with-children t (core-children t)))
       (for/and ([k (in-list (core-children t))]) (round-trip-ok? k))))

(check-true (round-trip-ok? sample))

;; 試験 2: annotate-regions が 3 形を置換し、ρ が region-at と一致する。
(define ir (build-region-ir sample))
(define annotated (annotate-regions sample ir))

(define (collect t point acc)
  (define acc2
    (match t
      [`(BorrowAt ,ρ ,_) (cons (list point ρ) acc)]
      [`(BorrowMutAt ,ρ ,_) (cons (list point ρ) acc)]
      [`(ReborrowAt ,ρ ,_) (cons (list point ρ) acc)]
      [_ acc]))
  (for/fold ([acc acc2]) ([k (in-list (core-children t))] [i (in-naturals)])
    (collect k (append point (list i)) acc)))

(define found (collect annotated '() '()))

(check-equal? (length found) 3)
(for ([entry (in-list found)])
  (check-equal? (second entry)
                (region->rho ir (region-at ir (first entry)))))

;; 注釈前の 3 形が残っていない。
(check-false (regexp-match? #rx"\\(Borrow " (format "~s" annotated)))
(check-false (regexp-match? #rx"\\(BorrowMut " (format "~s" annotated)))
(check-false (regexp-match? #rx"\\(Reborrow " (format "~s" annotated)))

;; 試験 3: 注釈済みの core を再び渡すと error になる。
(check-exn exn:fail? (lambda () (annotate-regions annotated ir)))

;; 試験 4: 注釈が一致すれば borrow-region-mismatch にならない。
;; Λ.owners は空なので、注釈検査を通った後に borrow-unknown-owner-region になる。
;; point '(0 1 0) は内側 Scope の中の Eliminate である。
;; '() の外側 Scope とは region が異なり、試験 5 の wrong-ρ が成り立つ。
(define Λ (region-ctx ir '(0 1 0) (hash) (hash)))
(define ok-node `(BorrowAt ,(region->rho ir (region-at ir '(0 1 0))) x))

(check-equal? (type-of/raw ok-node '() '() '((x (Owned Res))) Λ)
              (list 'fail 'borrow-unknown-owner-region ok-node '()))

;; 試験 5: 注釈が一致しなければ borrow-region-mismatch になる。
;; 別の point の region を注釈へ置く。
(define wrong-ρ (region->rho ir (region-at ir '())))
(define bad-node `(BorrowAt ,wrong-ρ x))

(check-not-equal? wrong-ρ (region->rho ir (region-at ir '(0 1 0))))
(check-equal? (type-of/raw bad-node '() '() '() Λ)
              (list 'fail 'borrow-region-mismatch bad-node '()))

;; entry 検査を通ること。ここが落ちると type-of/raw が診断へ届かない。
(check-true (core-types-normal? '(Borrow x)))
(check-true (core-types-normal? '(BorrowMut x)))
(check-true (core-types-normal? '(Reborrow (BorrowMut x))))
;; ρ は natural である（段 2、lang.rkt の (ρ ::= natural)）。
;; place も natural である（lang.rkt）。記号の ρ0 や p0 は文法に無い。
(check-true (core-types-normal? '(BorrowAt 1 x)))
(check-true (core-types-normal? '(BorrowMutAt 1 x)))
(check-true (core-types-normal? '(ReborrowAt 2 (BorrowMutAt 1 x))))
(check-true (core-types-normal? '(BorrowRef 0 1)))
(check-true (core-types-normal? '(BorrowMutRef 0 1)))

;; operand は辿る。正規でない型を内側に置くと偽になる。
;; (Union Int Int) が正規でないのは、normalize-type がこれを Int へ畳むためである。
;; 畳まれる型は正規形と一致しないので type-normal? は偽になる。
;; racket -e で確かめた結果は normalize=Int, type-normal?=#f である。
;; typing-span-test.rkt:184 も同じ型を non-normal-type の到達 fixture に使っている。
(check-false (core-types-normal? '(Reborrow (Let (y let (Union Int Int)) 1 y))))

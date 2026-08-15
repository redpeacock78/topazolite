#lang racket

(require rackunit racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; register-owner が実際に入れる値を直に固定する。
(let ()
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Scope () (Let (y let (Owned Int)) 2 (Borrow x))))))
  (define ir (build-region-ir core))
  (define (Λ-at point) (region-ctx ir point (hash) (hash)))
  (define Λ_x (register-owner (Λ-at '(0)) 'x '(Owned Int)))
  (check-equal? (region-ctx-owner Λ_x 'x) (region-at ir '(0)))
  (define Λ_y (register-owner (Λ-at '(0 1 0)) 'y '(Owned Int)))
  (check-equal? (region-ctx-owner Λ_y 'y) (region-at ir '(0 1 0)))
  (check-not-equal? (region-ctx-owner Λ_x 'x) (region-ctx-owner Λ_y 'y))
  (check-equal?
   (region-ctx-owner (register-owner (Λ-at '(0)) 'b '(Borrowed Int 0)) 'b)
   #f))

(define ok-core
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) (Borrow x))))
(define ok-ir (build-region-ir ok-core))
(define ok-ρ (region->rho ok-ir (region-at ok-ir '(0 1))))

(check-equal? (type-of/raw ok-core '() '() '() (Λ-of ok-ir))
              (list 'ok (list `(Borrowed Res ,ok-ρ) '())))

(define shared-twice
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) (Yield (Borrow x) (Borrow x)))))
(define shared-ir (build-region-ir shared-twice))
(check-equal? (first (type-of/raw shared-twice '() '() '() (Λ-of shared-ir)))
              'ok)

(define mut-twice
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) (Yield (BorrowMut x) (BorrowMut x)))))
(define mut-ir (build-region-ir mut-twice))
(check-equal? (key-of (type-of/raw mut-twice '() '() '() (Λ-of mut-ir)))
              'borrow-conflicting-alias)

(define mut-then-shared
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) (Yield (BorrowMut x) (Borrow x)))))
(define mts-ir (build-region-ir mut-then-shared))
(check-equal? (key-of (type-of/raw mut-then-shared '() '() '() (Λ-of mts-ir)))
              'borrow-conflicting-alias)

(define non-owned
  `(Scope ()
     (Let (x let Int) 1 (Borrow x))))
(define non-owned-ir (build-region-ir non-owned))
(check-equal? (key-of (type-of/raw non-owned '() '() '() (Λ-of non-owned-ir)))
              'borrow-non-owned)

(define bare `(Borrow x))
(define bare-ir (build-region-ir bare))
(check-equal? (key-of (type-of/raw bare '() '() '((x (Owned Int)))
                                   (Λ-of bare-ir)))
              'borrow-unknown-owner-region)

(define nested
  `(Scope () (Scope () 0)))
(define nested-ir (build-region-ir nested))
(define ρ-inner (region-at nested-ir '(0 0)))
(define ρ-root (region-at nested-ir '()))
(check-not-equal? ρ-inner ρ-root)
(check-false (region-outlives? nested-ir ρ-inner ρ-root))
(check-equal? (key-of (type-of/raw `(Borrow x) '() '() '((x (Owned Int)))
                                   (region-ctx nested-ir '()
                                               (hash 'x ρ-inner) (hash))))
              'borrow-escapes-owner)

(define move-while-borrowed
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) (Yield (Borrow x) (Move x)))))
(define mwb-ir (build-region-ir move-while-borrowed))
(define mwb-key
  (key-of (type-of/raw move-while-borrowed '() '() '() (Λ-of mwb-ir))))
(check-equal? mwb-key 'move-borrowed)
(check-not-equal? mwb-key 'move-non-owned)

(define drop-while-borrowed
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) (Yield (Borrow x) (Drop x)))))
(define dwb-ir (build-region-ir drop-while-borrowed))
(define dwb-key
  (key-of (type-of/raw drop-while-borrowed '() '() '() (Λ-of dwb-ir))))
(check-equal? dwb-key 'drop-borrowed)
(check-not-equal? dwb-key 'drop-non-owned)

(define borrow-then-move
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1)
       (Yield (Scope () (Borrow x)) (Move x)))))
(define btm-ir (build-region-ir borrow-then-move))
(check-equal? (first (type-of/raw borrow-then-move '() '() '() (Λ-of btm-ir)))
              'ok)

(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash))
                                `(BorrowMut x))
              (set 'x))
(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash 'y (set 'x)))
                                'y)
              (set 'x))
(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash)) 'y)
              (set 'y))
(check-equal? (borrow-token-key
               (region-ctx #f '() (hash) (hash))
               '(Let (y let (BorrowedMut Int 0)) (BorrowMut x) y))
              (set 'x))
(check-equal? (borrow-token-key
               (region-ctx #f '() (hash) (hash 'y (set 'x)))
               '(Let (y let (BorrowedMut Int 0)) (BorrowMut z) y))
              (set 'z))
(check-equal? (borrow-token-key
               (region-ctx #f '() (hash) (hash 'y (set 'x)))
               '(Let (y let Int) 1 y))
              (set 'y))
(check-equal? (borrow-token-key
               (region-ctx #f '() (hash) (hash))
               '(Eliminate 0 ((C1 (y) -> y))))
              (set 'y))
(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash 'y (set 3)))
                                'y)
              (set 3))
(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash)) 3)
              (set 3))
(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash 'y (set 'x 'z)))
                                'y)
              (set 'x 'z))

(define sp '(#:span #:synthetic 0 1))
(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash))
                                `(BorrowMut ,sp (#:var x ,sp)))
              (set 'x))
(check-equal? (borrow-token-key (region-ctx #f '() (hash) (hash 'y (set 'x)))
                                `(Let ,sp ((#:bind w ,sp) let (#:ty Int ,sp))
                                      (#:lit 1 ,sp)
                                      (#:var y ,sp)))
              (set 'x))

(check-equal? (borrow-token-key
               (region-ctx #f '() (hash) (hash))
               '(Eliminate 0 ((C1 () -> (BorrowMut x))
                              (C2 () -> (BorrowMut z)))))
              (set 'x 'z))

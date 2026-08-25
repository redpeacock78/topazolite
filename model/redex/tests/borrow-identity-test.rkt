#lang racket

;; [REQ: BOR-005] 関数境界を越える借用の受け渡しと identity forwarding。

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (place-types ids τ_place)
  (for/list ([id (in-list ids)]) (list id τ_place)))

(define (place-owners ir ids)
  (for/hash ([id (in-list ids)]) (values id (region-at ir '()))))

(define (status core ir τ_place callables #:places [ids '(1)])
  (first (type-of/raw (annotate-regions core ir)
                      (place-types ids τ_place) callables '()
                      (region-ctx ir '() (place-owners ir ids) (hash)))))

(define (failure core ir τ_place callables #:places [ids '(1)])
  (match (type-of/raw (annotate-regions core ir)
                      (place-types ids τ_place) callables '()
                      (region-ctx ir '() (place-owners ir ids) (hash)))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (use-sources core ir τ_place callables #:places [ids '(1)])
  (define inferred
    (typing-inference (annotate-regions core ir)
                      (place-types ids τ_place) callables '()
                      (region-ctx ir '() (place-owners ir ids) (hash))))
  (map use-request-source
       (filter use-request? (fourth inferred))))

(define (summaries core ir τ_place callables #:places [ids '(1)])
  (sixth (typing-inference (annotate-regions core ir)
                           (place-types ids τ_place) callables '()
                           (region-ctx ir '() (place-owners ir ids)
                                       (hash)))))

(define (call-alphas core ir τ_place callables #:places [ids '(1)])
  (define inferred
    (typing-inference (annotate-regions core ir)
                      (place-types ids τ_place) callables '()
                      (region-ctx ir '() (place-owners ir ids) (hash))))
  (map borrow-request-alpha
       (filter borrow-request? (fourth inferred))))

(define use-callables
  '((useb (ForallRegion (a)
            (NFn ((Borrowed Int (RParam a)))
                 Int
                 () ())))))

(define idf-callables
  '((idf (ForallRegion (a)
           (NFn ((BorrowedMut Int (RParam a)))
                (BorrowedMut Int (RParam a))
                () ())))))

(define lost-callables
  '((lost (ForallRegion (a b)
            (NFn ((BorrowedMut Int (RParam a)))
                 (BorrowedMut Int (RParam b))
                 () ())))))

(define plain-callables
  '((plain (ForallRegion (a)
             (NFn (Int)
                  (BorrowedMut Int (RParam a))
                  () ())))))

(define pair-callables
  '((pairb (ForallRegion (a)
             (NFn ((BorrowedMut Int (RParam a))
                   (BorrowedMut Int (RParam a)))
                  Int
                  () ())))
    (outer (ForallRegion (a)
             (NFn ((BorrowedMut Int (RParam a))
                   (BorrowedMut Int (RParam a)))
                  Int
                  () ())))))

(define (call-idf ρ)
  `(Scope (1)
          (Let (r let (BorrowedMut Int ,ρ))
               (Apply (RegionApp (RegionLam (a) (Lam User idf (x) x)) (,ρ))
                      (BorrowMut 1))
               (Assign r 7))))

(test-case
 "転送した借用への Assign が通る"
 (define ir (build-region-ir (call-idf 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (check-equal? (status (call-idf ρ) ir 'Int idf-callables) 'ok))

(test-case
 "転送した借用の使用の起点が実引数の α だけである"
 (define ir (build-region-ir (call-idf 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (define sources (use-sources (call-idf ρ) ir 'Int idf-callables))
 (define alphas (call-alphas (call-idf ρ) ir 'Int idf-callables))
 (check-equal? (length sources) 1)
 (check-equal? (length alphas) 1)
 (check-equal? (first sources) (set (first alphas))))

(test-case
 "対応しない結果の region を落とす"
 (define (core ρ ρ_other)
   `(Scope (1)
           (Scope ()
                  (Let (r let (BorrowedMut Int ,ρ))
                       (Apply (RegionApp (RegionLam (a b) (Lam User lost (x) x))
                                         (,ρ ,ρ_other))
                              (BorrowMut 1))
                       (Assign r 7)))))
 (define ir (build-region-ir (core 0 0)))
 (define ρ (region->rho ir (region-at ir '())))
 (define ρ_other (region->rho ir (region-at ir '(0 0))))
 (check-equal? (failure (core ρ ρ_other) ir 'Int lost-callables)
               'unresolved-borrow-owner))

(test-case
 "capability を運ばない実引数を落とす"
 (define (core ρ)
   `(Scope (1)
           (Let (r let (BorrowedMut Int ,ρ))
                (Apply (RegionApp
                        (RegionLam (a) (Lam User plain (x) (BorrowMut 1)))
                        (,ρ))
                       1)
                (Assign r 7))))
 (define ir (build-region-ir (core 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (check-equal? (failure (core ρ) ir 'Int plain-callables)
               'unresolved-borrow-owner))

(test-case
 "同名の仮引数を持つ入れ子の Lam が取り違えない"
 (define (core ρ)
   `(Scope (1)
           (Let (r let (BorrowedMut Int ,ρ))
                (Apply (RegionApp
                        (RegionLam (a)
                                   (Lam User idf (x)
                                        (Apply (RegionApp
                                                (RegionLam (a)
                                                           (Lam User idf (x) x))
                                                ((RParam a)))
                                               x)))
                        (,ρ))
                       (BorrowMut 1))
                (Assign r 7))))
 (define ir (build-region-ir (core 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (define sources (use-sources (core ρ) ir 'Int idf-callables))
 (define alphas (call-alphas (core ρ) ir 'Int idf-callables))
 (check-equal? (length sources) 1)
 (check-equal? (length alphas) 1)
 (check-equal? (first sources) (set (first alphas)))
 (define key-sets
   (for/list ([sm (in-list (summaries (core ρ) ir 'Int idf-callables))]
              #:when (positive? (hash-count
                                  (callable-summary-region-subst sm))))
     (list->set (filter values (callable-summary-formals sm)))))
 (check-equal? (length key-sets) 2)
 (check-equal? (set-count (apply set-union key-sets))
               (apply + (map set-count key-sets))))

(test-case
 "入れ子の呼出しで雛形が外側の実引数まで届く"
 (define (core ρ)
   `(Scope (1 2)
           (Apply (RegionApp
                   (RegionLam (a)
                              (Lam User outer (p q)
                                   (Apply (RegionApp
                                           (RegionLam (a)
                                                      (Lam User pairb (x y)
                                                           (Let (t let Int)
                                                                (Read (Reborrow x))
                                                                (Let (u let Unit)
                                                                     (Assign y 7)
                                                                     t))))
                                           ((RParam a)))
                                          p q)))
                   (,ρ))
                  (BorrowMut 1) (BorrowMut 2))))
 (define ir (build-region-ir (core 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (check-equal? (failure (core ρ) ir 'Int pair-callables #:places '(1 2)) 'ok))

(test-case
 "同じ借用を 2 つの仮引数へ渡す形を落とす"
 (define (core ρ)
   `(Scope (1)
           (Let (p let (BorrowedMut Int ,ρ))
                (BorrowMut 1)
                (Apply (RegionApp
                        (RegionLam (a)
                                   (Lam User pairb (x y)
                                        (Let (t let Int)
                                             (Read (Reborrow x))
                                             (Let (u let Unit)
                                                  (Assign y 7)
                                                  t))))
                        (,ρ))
                       p p))))
 (define ir (build-region-ir (core 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (check-not-equal? (failure (core ρ) ir 'Int pair-callables) 'ok))

(test-case
 "借用の仮引数を持つ署名の部分適用を落とす"
 (define (core ρ)
   `(Scope (1)
           (Curry (RegionApp (RegionLam (a) (Lam User idf (x) x)) (,ρ))
                  (BorrowMut 1))))
 (define ir (build-region-ir (core 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (check-equal? (failure (core ρ) ir 'Int idf-callables)
               'unresolved-borrow-owner))

(test-case
 "実引数の region が仮引数の region と一致しない呼出しを落とす"
 (define (core ρ ρ_other)
   `(Scope (1 2)
           (Scope ()
                  (Let (q let (BorrowedMut Int ,ρ_other))
                       (BorrowMut 2)
                       (Apply (RegionApp (RegionLam (a) (Lam User idf (x) x)) (,ρ)) q)))))
 (define ir (build-region-ir (core 0 0)))
 (define ρ (region->rho ir (region-at ir '())))
 (define ρ_other (region->rho ir (region-at ir '(0 0))))
 (define owners
   (hash 1 (region-at ir '())
         2 (region-at ir '(0 0))))
 (match (type-of/raw (annotate-regions (core ρ ρ_other) ir)
                     (place-types '(1 2) 'Int) idf-callables '()
                     (region-ctx ir '() owners (hash)))
   [(list 'fail key _node _details ...)
    (check-equal? key 'type-mismatch)]
   [(list 'ok _)
    (check-equal? 'ok 'type-mismatch)]))
(test-case
 "2 つの呼出しの実体化が別の α を採る"
 (define (core ρ)
   `(Scope (1)
           (Let (r let (BorrowedMut Int ,ρ))
                (BorrowMut 1)
                (Let (s let Int)
                     (Apply (RegionApp
                             (RegionLam (a) (Lam User useb (x) (Read x)))
                             (,ρ))
                            (Reborrow r))
                     (Apply (RegionApp
                             (RegionLam (a) (Lam User useb (x) (Read x)))
                             (,ρ))
                            (Reborrow r))))))
 (define ir (build-region-ir (core 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (define alphas (call-alphas (core ρ) ir 'Int use-callables))
 (check-equal? (length alphas) (length (remove-duplicates alphas))))

(test-case
 "実体化が節点の α の登録を潰さない"
 (define (core ρ)
   `(Scope (1)
           (Let (r let (BorrowedMut Int ,ρ))
                (BorrowMut 1)
                (Apply (RegionApp
                        (RegionLam (a) (Lam User useb (x) (Read x)))
                        (,ρ))
                       (Reborrow r)))))
 (define ir (build-region-ir (core 0)))
 (define ρ (region->rho ir (region-at ir '(0 0))))
 (define table
   (second (typing-inference (annotate-regions (core ρ) ir)
                             (list (list 1 'Int)) use-callables '()
                             (region-ctx ir '() (hash 1 (region-at ir '()))
                                         (hash)))))
 (check-true (hash-has-key? table '(0 1 1))))

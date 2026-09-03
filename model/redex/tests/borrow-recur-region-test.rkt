#lang racket

;; [REQ: BOR-005] region 多相な再帰関数の借用。形 i と形 ii。

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (raw-result core ir τ_place callables)
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ_place)) callables '()
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

(define (status core ir τ_place callables)
  (first (raw-result core ir τ_place callables)))

(define (failure-key result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; 外側の再帰関数の署名が結果型で (RParam a) に触れる。
;; 本体の内側の Lam は借用の仮引数を持つ。
;; 署名は入力側の自然な束縛名で書く。型検査入口の alpha-renaming 表が、
;; RegionLam の fresh 名との対応を解決する。
(define outer-callables
  '((outer (NFn (Int)
                (NFn ((BorrowedMut Int (RParam a))) Int () ())
                () ()))
    (innerb (NFn ((BorrowedMut Int (RParam a))) Int () ()))))

;; 1。署名が言及する region parameter を本体が引き継ぐ。
;; 空集合へ置き換える実装は、内側の Lam を borrowed-function-parameter で落とす。
(test-case
 "再帰の本体が署名の region parameter を引き継ぐ"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Recur outer f (n)
                             (Lam User innerb (y) (Read y))
                             0))))
 (define ir (build-region-ir core))
 (check-equal? (status core ir 'Int outer-callables) 'ok))

;; 2。署名が言及しない region parameter は引き継がない。
;; set-intersect を使わず外側をそのまま渡す実装は、この形を通してしまう。
(test-case
 "署名が言及しない region parameter は本体へ渡らない"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Recur plain f (n)
                             (Lam User innerb (y) (Read y))
                             0))))
 (define ir (build-region-ir core))
 (check-equal?
  (failure-key
   (raw-result core ir 'Int
               (cons '(plain (NFn (Int)
                                  (NFn (Int) Int () ())
                                  () ()))
                     outer-callables)))
  'borrowed-function-parameter))

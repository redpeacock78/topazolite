#lang racket

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; [REQ: BOR-001] 関数境界で借用の型を禁じる。

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; 定義位置の仮引数型。
(let ()
  (define core '(Scope () (Let (x let (Owned Res)) (resource 1) (Lam User f (a) 0))))
  (define ir (build-region-ir core))
  (define rho (region->rho ir (region-at ir '())))
  (define callables
    (list (list 'f `(NFn ((Borrowed Int ,rho)) Int () ()))))
  (define result (type-of/raw core '() callables '()
                              (region-ctx ir '() (hash) (hash))))
  (check-equal? (key-of result) 'borrowed-function-parameter)
  (check-not-equal? (key-of result) 'owned-function-parameter))

;; 定義位置の結果型。
(let ()
  (define core '(Scope () (Lam User f (a) 0)))
  (define ir (build-region-ir core))
  (define rho (region->rho ir (region-at ir '())))
  (define callables
    (list (list 'f `(NFn (Int) (Borrowed Int ,rho) () ()))))
  (check-equal? (key-of (type-of/raw core '() callables '()
                                       (region-ctx ir '() (hash) (hash))))
                'borrowed-function-result))

;; 定義位置の捕捉。
(let ()
  (define core '(Scope () (Lam User f (a) y)))
  (define ir (build-region-ir core))
  (define rho (region->rho ir (region-at ir '())))
  (define environment (list (list 'y `(Borrowed Int ,rho))))
  (define callables (list (list 'f '(NFn (Int) Int () ()))))
  (define result
    (type-of/raw core '() callables environment
                 (region-ctx ir '() (hash) (hash))))
  (check-equal? (key-of result) 'borrowed-function-capture)
  (check-not-equal? (key-of result) 'unbound-variable))

;; 仮引数が外側の同名 Borrowed を遮蔽する場合は捕捉ではない。
(let ()
  (define core '(Scope () (Lam User f (x) x)))
  (define ir (build-region-ir core))
  (define rho (region->rho ir (region-at ir '())))
  (define environment (list (list 'x `(Borrowed Int ,rho))))
  (define callables (list (list 'f '(NFn (Int) Int () ()))))
  (check-equal? (first (type-of/raw core '() callables environment
                                     (region-ctx ir '() (hash) (hash))))
                'ok))

;; RecurVal の関数名も外側の同名 Borrowed を遮蔽する。
(let ()
  (define core '(RecurVal f f (x) x))
  (define ir (build-region-ir core))
  (define rho (region->rho ir (region-at ir '())))
  (define environment (list (list 'f `(Borrowed Int ,rho))))
  (define callables (list (list 'f '(NFn (Int) Int () ()))))
  (check-equal? (first (type-of/raw core '() callables environment
                                     (region-ctx ir '() (hash) (hash))))
                'ok))

;; 本体で使わない借用は境界を越えない。
(let ()
  (define core '(Scope () (Lam User f (a) 0)))
  (define ir (build-region-ir core))
  (define rho (region->rho ir (region-at ir '())))
  (define environment (list (list 'y `(Borrowed Int ,rho))))
  (define callables (list (list 'f '(NFn (Int) Int () ()))))
  (check-equal? (first (type-of/raw core '() callables environment
                                     (region-ctx ir '() (hash) (hash))))
                'ok))

;; 型木を再帰的に走査する。
(check-true (unbound-borrowed-type? '(Union (Borrowed Int 0) Int)))
(check-true (unbound-borrowed-type? '(Option (BorrowedMut Int 0))))
(check-true (unbound-borrowed-type? '(Result Int (List (Borrowed Int 0)))))
(check-true (unbound-borrowed-type? '(NFn (Int) (NFn ((Borrowed Int 0)) Int () ()) () ())))
(check-true (unbound-borrowed-type? '(List (Option (Borrowed Int 0)))))
(check-false (unbound-borrowed-type? '(Union Int String)))
(check-false (unbound-borrowed-type? '(NFn (Int Bool) (Option Int) () ())))
(check-false (unbound-borrowed-type? '(Refined Int (FieldType a Int))))
(check-false (unbound-borrowed-type? '(Refined Int (Implements Int Tn))))

;; 環境由来の署名を Apply で拒む。
(define bad-environment
  (list (list 'f '(NFn ((Union (Borrowed Int 0) Int)) Int () ()))
        (list 'g '(NFn (Int) (Borrowed Int 0) () ()))))
(check-equal? (key-of (type-of/raw '(Apply f 1) '() '() bad-environment
                                  (empty-region-ctx)))
              'borrowed-function-parameter)
(check-equal? (key-of (type-of/raw '(Apply g 1) '() '() bad-environment
                                  (empty-region-ctx)))
              'borrowed-function-result)

;; 仮引数列の 2 番目。
(let ()
  (define core '(Scope () (Lam User f (a b) 0)))
  (define callables (list (list 'f '(NFn (Int (Borrowed Int 0)) Int () ()))))
  (check-equal? (key-of (type-of/raw core '() callables '()
                                       (empty-region-ctx)))
                'borrowed-function-parameter))

;; 仮引数の Union の中。
(let ()
  (define core '(Scope () (Lam User f (a) 0)))
  (define callables
    (list (list 'f '(NFn ((Union (Borrowed Int 0) Int)) Int () ()))))
  (check-equal? (key-of (type-of/raw core '() callables '()
                                       (empty-region-ctx)))
                'borrowed-function-parameter))

;; 結果型が入れ子の NFn。
(let ()
  (define core '(Scope () (Lam User f (a) 0)))
  (define callables
    (list (list 'f '(NFn (Int) (NFn ((Borrowed Int 0)) Int () ()) () ()))))
  (check-equal? (key-of (type-of/raw core '() callables '()
                                       (empty-region-ctx)))
                'borrowed-function-result))

;; Q の欄。定義位置と使用位置をそれぞれ押さえる。
(let ()
  (define core '(Scope () (Lam User f (a) 0)))
  (define callables
    (list (list 'f '(NFn (Int) Int () ((Implements (Borrowed Int 0) Tn))))))
  (check-equal? (key-of (type-of/raw core '() callables '()
                                       (empty-region-ctx)))
                'borrowed-function-result))
(check-equal? (key-of
               (type-of/raw '(Apply h 1) '() '()
                            (list (list 'h '(NFn (Int) Int ()
                                                   ((FieldType a (BorrowedMut Int 0))))))
                            (empty-region-ctx)))
              'borrowed-function-result)

;; Curry の残余仮引数。
(check-equal?
 (key-of
  (type-of/raw '(Curry g 1) '() '()
               (list (list 'g '(NFn (Int (Borrowed Int 0)) Int () ())))
               (empty-region-ctx)))
 'borrowed-function-parameter)

;; Curry の残余結果型。
(check-equal?
 (key-of
  (type-of/raw '(Curry g 1) '() '()
               (list (list 'g '(NFn (Int) (Borrowed Int 0) () ())))
               (empty-region-ctx)))
 'borrowed-function-result)

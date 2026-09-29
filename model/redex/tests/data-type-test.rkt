#lang racket
(require rackunit
         racket/match
         "../compat.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../origins.rkt"
         "../schema.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         "../type-shape.rkt")

(define (no-fail reason kind key) (error 'test "~s ~s ~s" reason kind key))
(define ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((Pair (A B) ((mkpair ((Param A) (Param B)))))
            (Nat () ((zero ()) (succ ((Data Nat ())))))
            (Wrap (A) ((wrap ((Untrusted (Param A))))))
            (Outer (A) ((outer ((Data Wrap ((Param A)))))))
            (Phantom (A) ((ph ()))) )
   #:fail no-fail))
(define-syntax-rule (with-data body ...)
  (call-with-trait-ledger ledger (lambda () body ...)))

;; elaborate の成功結果から型を取り、失敗時は診断 code を返す。
(define (elaborated-type source)
  (match (elab source)
    [(list _ type _ _) type]
    [`(err ,diagnostic) (diagnostic-id diagnostic)]))

(test-case "schema は台帳から置換して引く"
  (with-data
    (check-equal? (constructor-schema '(Data Pair (Int Bool)))
                  '((mkpair (Int Bool))))
    (check-false (constructor-schema '(Data Pair (Int))))
    (check-false (constructor-schema '(Data Missing ())))))

(test-case "組み込みの schema は変わらない"
  (with-data
    (check-equal? (constructor-schema '(Option Int)) '((none ()) (some (Int))))))

(test-case "形の検査は台帳と個数と引数を見る"
  (with-data
    (check-true (type-shape-ok? '(Data Pair (Int (Data Nat ())))))
    (check-false (type-shape-ok? '(Data Pair (Int))))
    (check-false (type-shape-ok? '(Data Missing ()))))
  (check-false (type-shape-ok? '(Data Nat ()))))

(test-case "形の検査は具体化した欄を見る"
  (with-data
    (check-true (type-shape-ok? '(Data Wrap (Int))))
    (check-false (type-shape-ok? '(Untrusted (Owned Int))))
    (check-false (type-shape-ok? '(Data Wrap ((Owned Int)))))
    (check-false (type-shape-ok? '(Data Pair ((Data Wrap ((Owned Int))) Int))))
    ;; 宣言時の Param→Int 近似では通り、入れ子の具体化で拒否される。
    (check-true (type-shape-ok? '(Data Outer (Int))))
    (check-false (type-shape-ok? '(Data Outer ((Owned Int)))))
    ;; 型引数の形は欄とは別に検査する。
    (check-true (type-shape-ok? '(Data Phantom (Int))))
    (check-false (type-shape-ok? '(Data Phantom ((Untrusted (Owned Int))))))))

(test-case "等価は名前と引数ごとの等価で決まる"
  (with-data
    (check-true (type-equiv? '(Data Pair (Int (Union Int Int))) '(Data Pair (Int Int))))
    (check-false (type-equiv? '(Data Pair (Int Bool)) '(Data Pair (Bool Int))))
    (check-false (compat? '(Data Pair (Int Int)) '(Data Pair (String Int))))))

(test-case "UCore の注釈と constructor が Data を返す"
  (with-data
    (check-equal? (elaborated-type '(Construct mkpair (Types Int Bool) 1 (Construct true)))
                  '(Data Pair (Int Bool)))
    (check-equal? (elaborated-type '(Construct succ (Types) (Construct zero (Types))))
                  '(Data Nat ()))
    (check-equal? (elaborated-type '(Let (n const (Data Nat ()))
                                      (Construct succ (Types)
                                                 (Construct zero))
                                      n))
                  '(Data Nat ()))))

(test-case "UCore の Fn 戻り型注釈で Data を解決する"
  (with-data
    (check-equal? (elaborated-type '(Fn () (Data Nat ()) () (Construct zero (Types))))
                  '(NFn () (Data Nat ()) () () () User))))

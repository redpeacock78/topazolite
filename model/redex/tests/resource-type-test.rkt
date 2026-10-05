#lang racket/base

(require rackunit
         "../resource-type.rkt"
         "../origins.rkt"
         "../traits.rkt")

(define (test-fail reason kind key)
  (error 'resource-type-test "~s ~s ~s" reason kind key))

(define resource-test-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data
   '((Pair (A B) ((mkpair ((Param A) (Param B)))))
     (Nat () ((zero ()) (succ ((Data Nat ())))))
     (Chain () ((cnil ()) (ccons (Int (Owned (Data Chain ())))))))
   #:fail test-fail))

(define-syntax-rule (with-data body ...)
  (call-with-trait-ledger resource-test-ledger (lambda () body ...)))

(test-case "schema の無い Data は型付け用では資源あり、実行用では error になる"
  (define type '(Data Unknown ()))
  (check-true (resource-type? type))
  (check-exn #rx"runtime-resource-type\\?"
             (lambda () (runtime-resource-type? type))))

(test-case "台帳の下では schema に従い、二つの述語が同じ値を返す"
  (with-data
    (check-false (resource-type? '(Data Nat ())))
    (check-false (runtime-resource-type? '(Data Nat ())))
    (check-true (resource-type? '(Data Chain ())))
    (check-true (runtime-resource-type? '(Data Chain ())))))

(test-case "台帳の外では資源を持たない Data も実行用の述語で error になる"
  (check-exn #rx"runtime-resource-type\\?"
             (lambda () (runtime-resource-type? '(Data Nat ())))))

(test-case "Owned を含む集約型は両方の述語で資源ありになる"
  (for ([type (in-list '((Option (Owned Int))
                         (Record ((a (Owned Int) imm) (b Int imm)))))])
    (check-true (resource-type? type))
    (check-true (runtime-resource-type? type))))

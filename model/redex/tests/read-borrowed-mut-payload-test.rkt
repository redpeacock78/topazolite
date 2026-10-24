#lang racket

(require rackunit
         "../region.rkt"
         "../borrow.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../typing.rkt")

(define read-payload-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((ReadPayload (A) ((pack ((Param A))))))
   #:fail (lambda (reason kind key)
            (error 'read-borrowed-mut-payload-test "~s ~s ~s" reason kind key))))

(define (with-data thunk)
  (call-with-trait-ledger read-payload-ledger thunk))

(define (type-read core place-type)
  (define ir (build-region-ir core))
  (with-data
   (lambda ()
     (type-of/raw (annotate-regions core ir)
                  (list (list 1 place-type))
                  '()
                  '()
                  (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))))

(define mut-borrow '(BorrowedMut Int (RVar 0)))
(define (mut-payload-results place-type)
  (for/list ([mode (in-list '(Borrow BorrowMut))])
    (define result
      (type-read `(Scope (1) (Read (,mode 1))) place-type))
    (list (first result) (second result))))

(define mut-payload-rejections
  '((fail read-uncopyable-payload) (fail read-uncopyable-payload)))

(test-case "Record の直下の BorrowedMut を含む payload は両方の借用で拒否する"
  (check-equal? (mut-payload-results `(Record ((field ,mut-borrow mut))))
                mut-payload-rejections))

(test-case "入れ子 Record の BorrowedMut を含む payload は両方の借用で拒否する"
  (check-equal? (mut-payload-results
                 `(Record ((outer (Record ((inner ,mut-borrow mut))) imm))))
                mut-payload-rejections))

(test-case "data payload の BorrowedMut を含む値は両方の借用で拒否する"
  (check-equal? (mut-payload-results `(Data ReadPayload (,mut-borrow)))
                mut-payload-rejections))

(test-case "Union member の BorrowedMut を含む値は両方の借用で拒否する"
  (check-equal? (mut-payload-results `(Union ,mut-borrow Bool))
                mut-payload-rejections))

(test-case "共有借用だけを含む Record payload は Read できる"
  (define core '(Scope (1)
                 (Read (Proj (Read (Borrow 1)) field))))
  (define shared-type '(Record ((field (Borrowed Int (RVar 0)) imm))))
  (define result (type-read core shared-type))
  (check-equal? (first result) 'ok (format "~s" result)))

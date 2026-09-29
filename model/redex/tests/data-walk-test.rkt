#lang racket
(require rackunit
         racket/set
         "../borrow.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../type-shape.rkt"
         "../validators.rkt"
         (only-in "../typing.rkt" forall-region-free? borrow-payload-borrow-free?))

(define (no-fail reason kind key) (error 'test "~s ~s ~s" reason kind key))
(define poly-field
  '(ForallRegion (r) (NFn ((Borrowed Int (RParam r))) Int () () () User)))
(define ledger
  (make-trait-ledger
   canonical-trait-env
   #:data `((Nat () ((zero ()) (succ ((Data Nat ())))))
            (Even (A) ((enil ()) (econs ((Param A) (Data Odd ((Param A)))))))
            (Odd (B) ((ocons ((Param B) (Data Even ((Param B)))))))
            (Box () ((box ((Owned Int)))))
            (Held () ((held ((RawPtr Int Const NonNull (Align 1)
                                             (AddrSpace native) (Prov owned))))))
            (Poly () ((poly (,poly-field))))
            (Nested () ((nested
                         ((ForallRegion (r)
                           (NFn ((Borrowed (Borrowed Int (RParam r))
                                           (RParam r)))
                                Int () () () User)))))))
   #:fail no-fail))
(define-syntax-rule (with-data body ...)
  (call-with-trait-ledger ledger (lambda () body ...)))

(test-case "再帰する data 型でも走査が停止する"
  (with-data
    (for ([type (in-list '((Data Nat ())
                          (Data Even (Int))
                          (Data Odd ((Data Nat ())))))])
      (check-true (storage-ok? type))
      (check-true (owned-free? type))
      (check-equal? (copy-out-scan type) '())
      (check-false (leaks-rawptr? type))
      (check-false (type-carries-capability? type))
      (check-true (forall-region-free? type))
      (check-true (borrow-payload-borrow-free? type))
      (check-false (unbound-borrowed-type? type (set))))))

(test-case "欄にしか無い性質を見落とさない"
  (with-data
    (check-false (owned-free? '(Data Box ())))
    (check-equal? (copy-out-scan '(Data Box ())) (copy-out-scan '(Owned Int)))
    (check-false (type-shape-ok? '(Untrusted (Data Box ()))))
    (check-true (leaks-rawptr? '(Data Held ())))
    (check-false (forall-region-free? '(Data Poly ())))
    (check-true (type-carries-capability? '(Data Poly ())))
    (check-true (borrow-payload-borrow-free? '(Data Poly ())))
    (check-false (borrow-payload-borrow-free? '(Data Nested ())))
    (check-equal? (unbound-borrowed-type? '(Data Poly ()) (set))
                  (unbound-borrowed-type? poly-field (set)))))

(test-case "組み込みの型は以前と同じ答えを返す"
  (for ([type (in-list '((List Int) (Option (Owned Int))
                         (Result Int (List Int))))])
    (check-equal? (with-data (storage-ok? type)) (storage-ok? type))
    (check-equal? (with-data (owned-free? type)) (owned-free? type))
    (check-equal? (with-data (copy-out-scan type)) (copy-out-scan type))))

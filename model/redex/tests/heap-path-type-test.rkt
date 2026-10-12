#lang racket

(require rackunit
         "../machine.rkt"
         "../typing.rkt")

(define (one-place value declared-type)
  (list (list 0 value `(declared ,declared-type))))

(test-case "heap-path-type は Record の label の型を返す"
  (define root-type '(Record ((a Int imm))))
  (define heap (one-place '(Rec ((a imm 7))) root-type))
  (check-equal? (heap-path-type heap 0 root-type '(a)) 'Int))

(test-case "heap-path-type は Construct の欄の型を schema から返す"
  (define root-type '(Option Int))
  (define heap (one-place '(Construct (Option Int) some 7) root-type))
  (check-equal? (heap-path-type heap 0 root-type '(0)) 'Int))

(test-case "heap-path-type は UnionVal の Payload の型を返す"
  (define root-type '(Union Int Bool))
  (define heap (one-place '(UnionVal (Union Int Bool) Int 7) root-type))
  (check-equal? (heap-path-type heap 0 root-type '((Payload))) 'Int))

(test-case "heap-path-type は Absent と不正な path を拒否する"
  (check-false
   (heap-path-type (one-place '(Rec ((a imm (Absent Int))))
                             '(Record ((a Int imm))))
                   0 '(Record ((a Int imm))) '(a)))
  (check-false
   (heap-path-type (one-place '(Rec ((a imm 7)))
                             '(Record ((a Int imm))))
                   0 '(Record ((a Int imm))) '(missing)))
  (check-false
   (heap-path-type (one-place '(Construct (Option Int) some 7) '(Option Int))
                   0 '(Option Int) '(1)))
  (check-false
   (heap-path-type (one-place '(Construct (Option Bool) some #t) '(Option Bool))
                   0 '(Option Int) '(0))))

(test-case "heap-path-type は place state に依存しない"
  (define heap (one-place 7 'Int))
  (define states '((0 Moved)))
  (check-equal? (assoc 0 states) '(0 Moved))
  (check-equal? (procedure-arity heap-path-type) 4)
  (check-equal? (heap-path-type heap 0 'Int '()) 'Int))

(test-case "place-root-type は宣言型の根の Owned だけを外す"
  (define heap (append (one-place 7 '(Owned Int))
                       (list (list 1 7 '(declared Int))
                             (list 2 7))))
  (check-equal? (place-root-type heap 0) 'Int)
  (check-equal? (place-root-type heap 1) 'Int)
  (check-false (place-root-type heap 2)))

(test-case "place を作る三規則は heap に宣言型を記録する"
  (define cases
    (list
     (list 'R-LetOwned
           '(cfg (Scope () (Let (x (Owned Int)) 7 (Move x))) () () () ())
           '(Owned Int) 7)
     (list 'R-LetOwnedB
           '(cfg (Scope () (Let (x let (Owned Int)) 7 (Move x))) () () () ())
           '(Owned Int) 7)
     (list 'R-LetMutB
           '(cfg (Scope () (Let (x mut Int) 7 unit)) () () () ())
           'Int 7)))
  (for ([case-data (in-list cases)])
    (match-define (list expected-rule start declared-type expected-value)
      case-data)
    (match (raw-steps-g2/named start)
      [(list (list rule next))
       (check-eq? rule expected-rule)
       (match next
         [`(cfg ,_ ,heap ,states ,_ ,_)
          (define place (first (first states)))
          (check-equal? (assoc place heap)
                        (list place expected-value `(declared ,declared-type)))
          (check-eq? (second (assoc place states)) 'Available)
          (check-equal? (place-root-type heap place)
                        (match declared-type
                          [`(Owned ,payload) payload]
                          [_ declared-type]))])]
      [steps (error 'heap-path-type-test
                    "~a の一意な一歩を期待した: ~s" expected-rule steps)])))

(test-case "Owned wrapper の path は変更前の recover と同じ境界を保つ"
  (define root-type '(Record ((a Int imm))))
  (define record-value '(Rec ((a imm 7))))
  (define wrappers
    (list (list 'OwnedTransit 0 record-value)
          (list 'OwnedLeaf '(tok 1) record-value)))
  (for ([wrapper (in-list wrappers)])
    (define heap (one-place wrapper root-type))
    (define root-borrow '(BorrowRef 0 () 1))
    (define child-borrow '(BorrowRef 0 (a) 1))
    (check-equal? (heap-path-type heap 0 root-type '()) root-type)
    (check-false (heap-path-type heap 0 root-type '(a)))
    (define recovered
      (recover-runtime-borrow-types
       root-borrow heap '((0 Available)) `((0 ,root-type))))
    (check-equal? (hash-count recovered) 1)
    (check-equal? (hash-ref recovered root-borrow #f)
                  `(Borrowed ,root-type 1))
    (check-false (recover-runtime-borrow-types
                  child-borrow heap '((0 Available)) `((0 ,root-type)))))
  (define absent-value '(Rec ((a imm (Absent Int)))))
  (define absent-wrappers
    (list (list 'OwnedTransit 0 absent-value)
          (list 'OwnedLeaf '(tok 1) absent-value)))
  (for ([wrapper (in-list absent-wrappers)])
    (define heap (one-place wrapper root-type))
    (check-false (heap-path-type heap 0 root-type '(a)))
    (check-false (recover-runtime-borrow-types
                  '(BorrowRef 0 (a) 1) heap '((0 Available))
                  `((0 ,root-type))))))

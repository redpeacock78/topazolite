#lang racket

(require rackunit
         "../compat.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../ownership.rkt"
         "../traits.rkt"
         "../validators.rkt")

(define (always-compatible _actual _expected) #t)

(define borrow-wide
  '(Record ((name String imm) (hidden (Borrowed Int ρ) imm))))
(define borrow-narrow '(Record ((name String imm))))
(define borrow-value
  '(Rec ((name imm "A") (hidden imm (BorrowRef 1 () ρ)))))

(test-case "借用を含む型は borrow-free? が偽になる"
  (check-false (borrow-free? '(Borrowed Int ρ)))
  (check-false (borrow-free? '(BorrowedMut Int ρ)))
  (check-false (borrow-free? '(Record ((name String imm)
                                      (b (Borrowed Int ρ) imm)))))
  (check-true (borrow-free? '(Record ((name String imm) (id Int imm)))))
  (for ([type (in-list '((Owned (Borrowed Int ρ))
                         (Option (Borrowed Int ρ))
                         (List (Borrowed Int ρ))
                         (Result Int (Borrowed Int ρ))
                         (Untrusted (Borrowed Int ρ))
                         (Refined (Borrowed Int ρ) (Prop P))
                         (Union Int (Borrowed Int ρ))
                         (Intersection Int (Borrowed Int ρ))
                         (ForallRegion (r) (Borrowed Int (RParam r)))))])
    (check-false (borrow-free? type)))
  (check-true (borrow-free? '(NFn () (Borrowed Int ρ) () () () User)))
  (check-true (borrow-free? '(RawPtr (Borrowed Int ρ) Const NonNull
                                     (Align 4) (AddrSpace native)
                                     (Prov owned))))
  (check-false (borrow-free? '(SomeFutureType Int))))

(test-case "再帰する Data の schema を visited で一度だけ辿る"
  (define (no-fail reason kind key)
    (error 'borrow-hiding-test "~s ~s ~s" reason kind key))
  (define ledger
    (make-trait-ledger
     canonical-trait-env
     #:data '((Nat () ((zero ()) (succ ((Data Nat ())))))
              (BorrowBox () ((box ((ForallRegion (r)
                                    (Borrowed Int (RParam r)))
                                   (Data BorrowBox ()))))))
     #:fail no-fail))
  (call-with-trait-ledger
   ledger
   (lambda ()
     (check-true (borrow-free? '(Data Nat ())))
     (check-false (borrow-free? '(Data BorrowBox ()))
                  "Data schema の借用を見落とさない")
     (check-false (borrow-free? '(Data Missing ()))))))

(test-case "最上位の借用残余を RSD の義務として返す"
  (check-equal? (borrow-hiding-kind borrow-wide borrow-narrow compat?)
                `(drop-obligation ,borrow-wide ,borrow-narrow)))

(test-case "mut から imm の共通欄の入れ子も借用残余を落とす"
  (define actual
    '(Record ((inner
                     (Record ((name String imm)
                              (b (Borrowed Int ρ) imm)))
                     mut))))
  (define expected
    '(Record ((inner (Record ((name String imm))) imm))))
  (define shape (remainder-removal-shape actual expected))
  (check-equal? shape
                '((inner nested #f ((b drop #f)))))
  (check-equal? (remainder-target-type actual expected) expected)
  (check-true (rsd-proof-pair-ok? actual expected compat?)))

(test-case "Owned と借用の余剰を一つの shape で取り除く"
  (define actual
    '(Record ((name String imm)
              (owned (Owned Res) imm)
              (hidden (Borrowed Int ρ) imm))))
  (define expected '(Record ((name String imm))))
  (check-equal? (remainder-removal-shape actual expected)
                '((owned drop #f) (hidden drop #f)))
  (check-equal?
   (strip-remainder
    actual expected
    '(Rec ((name imm "A")
           (owned imm 7)
           (hidden imm (BorrowRef 1 () ρ)))))
   (list '(Rec ((name imm "A")))
         '(7 (BorrowRef 1 () ρ)))))

(test-case "RSD は借用残余を値から実際に取り除く"
  (check-equal? (remainder-removal-shape borrow-wide borrow-narrow)
                '((hidden drop #f)))
  (check-equal?
   (strip-remainder borrow-wide borrow-narrow borrow-value)
   (list '(Rec ((name imm "A"))) '((BorrowRef 1 () ρ)))))

(test-case "Union と Owned の payload 内側の隠れる借用は拒否する"
  (define wide '(Record ((name String imm) (b (Borrowed Int ρ) imm))))
  (define narrow '(Record ((name String imm))))
  (define wide2 '(Record ((name String imm) (b (Borrowed Bool ρ) imm))))
  (define narrow2 '(Record ((name String imm) (id Int imm))))
  (check-equal?
   (borrow-hiding-kind `(Union ,wide ,wide2) `(Union ,narrow ,narrow2)
                       always-compatible)
   'reject)
  (check-equal?
   (borrow-hiding-kind `(Owned ,wide) `(Owned ,narrow) always-compatible)
   'reject))

(test-case "NFn と wrapper の内側の隠れる借用は互換時も拒否する"
  (define wide '(Record ((name String imm) (b (Borrowed Int ρ) imm))))
  (define narrow '(Record ((name String imm))))
  (define pairs
    (list (list `(NFn () ,wide () () () User)
                `(NFn () ,narrow () () () User))
          (list `(NFn (,narrow) Int () () () User)
                `(NFn (,wide) Int () () () User))
          (list `(Untrusted ,wide) `(Untrusted ,narrow))
          (list `(Refined ,wide (Prop P))
                `(Refined ,narrow (Prop P)))))
  (for ([pair (in-list pairs)])
    (check-true (compat? (first pair) (second pair)))
    (check-equal? (borrow-hiding-kind (first pair) (second pair)
                                      compat?)
                  'reject)))

(test-case "Borrowed<Record> の capability view は許可する"
  (check-equal? (borrow-hiding-kind `(Borrowed ,borrow-wide ρ)
                                    `(Borrowed ,borrow-narrow ρ)
                                    compat?)
                'ok))

(test-case "RSD の後にも NFn 返り値に借用が隠れる Proof を拒否する"
  (define wide-nfn `(NFn () ,borrow-wide () () () User))
  (define narrow-nfn `(NFn () ,borrow-narrow () () () User))
  (define actual `(Record ((name String imm) (f ,wide-nfn imm))))
  (define expected `(Record ((name String imm) (f ,narrow-nfn imm))))
  (check-true (compat? actual expected))
  (check-equal? (remainder-target-type actual expected) actual)
  (check-equal? (borrow-hiding-kind actual expected compat?) 'reject)
  (check-false (rsd-proof-pair-ok? actual expected compat?)))

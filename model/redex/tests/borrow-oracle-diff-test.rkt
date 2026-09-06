#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../borrow-oracle.rkt"
         "../lang.rkt"
         "../machine.rkt")

;; R-Borrow の遷移。制御項の差分は BorrowAt の位置ひとつである。
(define borrow-pre
  (term (cfg (Scope () (BorrowAt (RVar 0) (Own 0 ()) 0))
             ((0 1)) ((0 Available)) () ())))

(test-case "raw-steps-g2/named は規則名と後続 config を返す"
  (define steps (raw-steps-g2/named borrow-pre))
  (check-equal? (length steps) 1)
  (check-equal? (first (first steps)) 'R-Borrow))

(test-case "control-diff は R-Borrow の redex と contractum を返す"
  (define post (second (first (raw-steps-g2/named borrow-pre))))
  (match-define (cons redex contractum)
    (control-diff (second borrow-pre) (second post)))
  (check-equal? redex '(BorrowAt (RVar 0) (Own 0 ()) 0))
  (check-equal? contractum '(BorrowRef 0 () (RVar 0))))

(test-case "borrow-form-candidates は R-Borrow を根の共有借用と分類する"
  (define post (second (first (raw-steps-g2/named borrow-pre))))
  (match-define (cons redex contractum)
    (control-diff (second borrow-pre) (second post)))
  (check-equal? (borrow-form-candidates redex contractum)
                (list (list 'root 'shared 0 '() '(RVar 0) 0))))

(test-case "borrow-form-candidates は R-BorrowMut を根の可変借用と分類する"
  (check-equal?
   (borrow-form-candidates
    '(BorrowMutAt 0 (Own 3 ()) w)
    '(BorrowMutRef 3 () 0))
   (list (list 'root 'mut 3 '() 0 'w))))

(test-case "借用を含まない遷移の候補は 0 件である"
  (check-equal? (borrow-form-candidates '(Read 7) '7) '()))

(test-case "承認済みの形へ照合できない借用値の出現は unverified になる"
  ;; contractum にだけ現れる借用値で、redex がどの承認済みの形でもない。
  (check-equal? (borrow-form-candidates '(Foo 1)
                                        '(BorrowRef 0 () (RVar 0)))
                (list (list 'unverified))))

(test-case "制御項が変わらない遷移では control-diff が #f を返す"
  (check-equal? (control-diff '(Scope () unit) '(Scope () unit)) #f))

(test-case "子が 2 つ以上異なるときは根が最小の位置になる"
  (check-equal? (control-diff '(Pair (Read a) (Read b))
                              '(Pair (Read c) (Read d)))
                (cons '(Pair (Read a) (Read b))
                      '(Pair (Read c) (Read d)))))

(test-case "散らばった差分で借用値がなければ非借用遷移とみなす"
  (check-equal? (borrow-form-candidates '(Pair (Read a) (Read b))
                                        '(Pair (Read c) (Read d)))
                '()))

(test-case "ProjBorrowAt は可変から共有への降格を分類する"
  (check-equal?
   (borrow-form-candidates
    '(ProjBorrowAt 0 (Own 3 (0 fld))
                   (BorrowMutRef 3 (0) 0) fld)
    '(BorrowRef 3 (0 fld) 0))
   (list (list 'derived 'shared 3 '(0 fld) 0
               3 '(0) 0))))

(test-case "ProjBorrowAt の共有から可変への昇格は未検証になる"
  (check-equal?
   (borrow-form-candidates
    '(ProjBorrowAt 0 (Own 3 (0 fld))
                   (BorrowRef 3 (0) 0) fld)
    '(BorrowMutRef 3 (0 fld) 0))
   (list (list 'unverified))))

(test-case "ReborrowAt は親付きの共有借用を分類する"
  (check-equal?
   (borrow-form-candidates
    '(ReborrowAt 0 (Own 3 ())
                 (BorrowMutRef 3 () 1))
    '(BorrowRef 3 () 0))
   (list (list 'reborrow 3 '() 0 1))))

(test-case "Eliminate は一段深い借用を派生として分類する"
  (check-equal?
   (borrow-form-candidates
    '(Eliminate (BorrowRef 3 (0) 0) branch)
    '(BorrowRef 3 (0 1) 0))
   (list (list 'derived 'shared 3 '(0 1) 0
               3 '(0) 0))))

(test-case "Read は共有借用の使用を分類する"
  (check-equal?
   (borrow-form-candidates
    '(Read (BorrowRef 3 () 0))
    'unit)
   (list (list 'use 'shared 3 '() 0))))

(test-case "Assign は可変借用の使用を分類する"
  (check-equal?
   (borrow-form-candidates
    '(Assign (BorrowMutRef 3 () 0) 1)
    'unit)
   (list (list 'use 'mut 3 '() 0))))

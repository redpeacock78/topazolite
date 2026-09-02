#lang racket

;; [REQ: BOR-004] 入れ子の借用の複製。copy-out-scan の走査。

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../validators.rkt"
         "../typing.rkt"
         "../machine.rkt")

(test-case "copy-out-scan は借用を含まない型に対して空の列を返す"
  (check-equal? (copy-out-scan 'Int) '())
  (check-equal? (copy-out-scan '(List Int)) '())
  (check-equal? (copy-out-scan '(Record ((f Int const)))) '()))

(test-case "copy-out-scan は所有値を含む型を拒否する"
  (check-false (copy-out-scan '(Owned Int)))
  (check-false (copy-out-scan '(List (Owned Int))))
  (check-false (copy-out-scan '(Record ((f (Owned Int) const))))))

(test-case "copy-out-scan は借用の lifetime を出現順に集める"
  (check-equal? (copy-out-scan '(Borrowed Int a1)) '(a1))
  (check-equal? (copy-out-scan '(BorrowedMut Int a2)) '(a2))
  (check-equal? (copy-out-scan '(Record ((f (Borrowed Int a1) const)
                                         (g (BorrowedMut Int a2) mut))))
                '(a1 a2))
  (check-equal? (copy-out-scan '(List (Borrowed Int a3))) '(a3)))

(test-case "copy-out-scan は借用の payload の中まで降りない"
  (check-equal? (copy-out-scan '(Borrowed (Owned Int) a1)) '(a1)))

(test-case "copy-out-scan は未知の型構成子を拒否する"
  (check-false (copy-out-scan '(Mystery Int))))

(test-case "effect-copy-out-scan は型を運ぶ Effect だけを走査する"
  (check-equal? (effect-copy-out-scan '(Return b (Borrowed Int a1))) '(a1))
  (check-equal? (effect-copy-out-scan '(Yield (Borrowed Int a2))) '(a2))
  (check-equal? (effect-copy-out-scan 'Suspend) '())
  (check-false (effect-copy-out-scan '(Return b (Owned Int)))))

(test-case "copy-out-ok? の意味は変わらない"
  (check-true (copy-out-ok? 'Int))
  (check-false (copy-out-ok? '(Owned Int)))
  (check-false (copy-out-ok? '(Borrowed Int a1)))
  (check-false (copy-out-ok? '(Record ((f (Borrowed Int a1) const))))))

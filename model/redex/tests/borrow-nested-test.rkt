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

(test-case "copy-out-scan は NFn の順に lifetime を集める"
  (check-equal?
   (copy-out-scan
    '(NFn ((Borrowed Int a1)) (Borrowed Int a2)
          ((Yield (Borrowed Int a3))) ()))
   '(a1 a2 a3)))

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

(define nested-read-core '(Scope (1) (Read (Borrow 1))))
(define nested-read-ir (build-region-ir nested-read-core))
(define nested-read-Λ
  (region-ctx nested-read-ir
              '()
              (hash 1 (region-at nested-read-ir '()))
              (hash)))
(define nested-read-type
  '(Record ((f (Borrowed Int (RVar 0)) imm))))

(test-case "所有者を追える借用を含む payload の複製は通る"
  (define result
    (type-of/raw (annotate-regions nested-read-core nested-read-ir)
                 (list (list 1 nested-read-type))
                 '()
                 '()
                 nested-read-Λ))
  (check-equal? (first result) 'ok))

(define fnbound-read-type
  '(Record ((f (Borrowed Int (RVar 1)) imm))))

(test-case "所有者を引けない借用を含む payload は拒否される"
  (define result
    (type-of/raw (annotate-regions nested-read-core nested-read-ir)
                 (list (list 1 fnbound-read-type))
                 '()
                 '()
                 nested-read-Λ))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'borrow-unknown-owner-region))

(define owned-read-type
  '(Record ((f (Owned Res) imm))))

(test-case "所有値を含む payload は従来どおり拒否される"
  (define result
    (type-of/raw (annotate-regions nested-read-core nested-read-ir)
                 (list (list 1 owned-read-type))
                 '()
                 '()
                 nested-read-Λ))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'read-uncopyable-payload))

(define nested-borrow-read-type
  '(Record ((f (Borrowed (BorrowedMut Res (RVar 1)) (RVar 0)) imm))))

(test-case "借用の payload に別の借用がある型は複製を拒否される"
  (define result
    (type-of/raw (annotate-regions nested-read-core nested-read-ir)
                 (list (list 1 nested-borrow-read-type))
                 '()
                 '()
                 nested-read-Λ))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'read-uncopyable-payload))

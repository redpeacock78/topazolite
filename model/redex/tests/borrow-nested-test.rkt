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

(define nested-read-constraint-core
  '(Scope (1)
     (Let (b let (Borrowed (Record ((f (Borrowed Int (RVar 0)) imm)))
                           (RVar 0)))
          (Borrow 1)
          (Read (Borrow 1)))))
(define nested-read-constraint-ir
  (build-region-ir nested-read-constraint-core))
(define nested-read-constraint-Λ
  (region-ctx nested-read-constraint-ir
              '()
              (hash 1 (region-at nested-read-constraint-ir '()))
              (hash)))

(test-case "読み出しは view と payload の lifetime 間に outlives を出す"
  (define inference
    (typing-inference
     (annotate-regions nested-read-constraint-core nested-read-constraint-ir)
     (list (list 1 nested-read-type))
     '()
     '()
     nested-read-constraint-Λ))
  (define alpha-table (second inference))
  (define view-alpha (hash-ref alpha-table '(0 1 0)))
  (define payload-alpha (hash-ref alpha-table '(0 0)))
  (define outlives-pairs
    (for/list ([c (in-list (third inference))]
               #:when (eq? (region-constraint-kind c) 'outlives))
      (cons (region-constraint-left c) (region-constraint-right c))))
  (check-not-false (member (cons view-alpha payload-alpha) outlives-pairs)))

(define escaping-view-core
  '(Scope (1)
     (Let (b let (Borrowed (Record ((f (Borrowed Int (RVar 0)) imm)))
                           (RVar 0)))
          (Borrow 1)
          (Scope (2) (Read (Borrow 2))))))
(define escaping-view-ir (build-region-ir escaping-view-core))
(define escaping-view-Λ
  (region-ctx escaping-view-ir
              '()
              (hash 1 (region-at escaping-view-ir '())
                    2 (region-at escaping-view-ir '(0 1)))
              (hash)))

(test-case "view の region を超えて出る借用は拒否される"
  (define result
    (type-of/raw (annotate-regions escaping-view-core escaping-view-ir)
                 (list (list 1 nested-read-type)
                       (list 2 nested-read-type))
                 '()
                 '()
                 escaping-view-Λ))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'borrow-escapes-owner))

;; place 2 の中身を mutable view として借り、place 1 由来の借用を欄へ書く。
(define nested-assign-core
  '(Scope (1 2)
     (Let (b let (Borrowed Int (RVar 0)))
          (Borrow 1)
          (Assign (BorrowMut 2) b))))
(define nested-assign-ir (build-region-ir nested-assign-core))
(define nested-assign-Λ
  (region-ctx nested-assign-ir
              '()
              (hash 1 (region-at nested-assign-ir '())
                    2 (region-at nested-assign-ir '()))
              (hash)))
(define nested-assign-places
  (list (list 1 'Int)
        (list 2 '(Borrowed Int (RVar 0)))))

(test-case "代入は値の lifetime が target より長いことを制約にする"
  (define inference
    (typing-inference
     (annotate-regions nested-assign-core nested-assign-ir)
     nested-assign-places
     '()
     '()
     nested-assign-Λ))
  (define alpha-table (second inference))
  (define value-alpha (hash-ref alpha-table '(0 0)))
  (define target-alpha (hash-ref alpha-table '(0 1 0)))
  (define outlives-pairs
    (for/list ([c (in-list (third inference))]
               #:when (eq? (region-constraint-kind c) 'outlives))
      (cons (region-constraint-left c) (region-constraint-right c))))
  (check-not-false (member (cons value-alpha target-alpha) outlives-pairs)))

;; 外側で作った target view へ、内側で作った短い借用を書き込む。
(define short-assign-core
  '(Scope (2)
     (Let (t let (BorrowedMut (Borrowed Int (RVar 1)) (RVar 0)))
          (BorrowMut 2)
          (Scope (3)
            (Let (b let (Borrowed Int (RVar 1)))
                 (Borrow 3)
                 (Assign t b))))))
(define short-assign-ir (build-region-ir short-assign-core))
(define short-assign-Λ
  (region-ctx short-assign-ir
              '()
              (hash 2 (region-at short-assign-ir '())
                    3 (region-at short-assign-ir '(0 1)))
              (hash)))
(define short-assign-places
  (list (list 2 '(Borrowed Int (RVar 1)))
        (list 3 'Int)))

(test-case "target view より短い借用の代入は拒否される"
  (define result
    (type-of/raw (annotate-regions short-assign-core short-assign-ir)
                 short-assign-places
                 '()
                 '()
                 short-assign-Λ))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'borrow-escapes-owner))

(define owned-assign-core '(Scope (1) (Assign (BorrowMut 1) 7)))
(define owned-assign-ir (build-region-ir owned-assign-core))
(define owned-assign-Λ
  (region-ctx owned-assign-ir
              '()
              (hash 1 (region-at owned-assign-ir '()))
              (hash)))

(test-case "所有値を含む代入は assign-owned-payload で拒否される"
  (define result
    (type-of/raw (annotate-regions owned-assign-core owned-assign-ir)
                 (list (list 1 '(Owned Res)))
                 '()
                 '()
                 owned-assign-Λ))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-owned-payload))

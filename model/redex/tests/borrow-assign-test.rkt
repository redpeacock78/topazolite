#lang racket

;; [REQ: BOR-004] Assign の型付けと受理条件。

(require rackunit
         redex/reduction-semantics
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt"
         "../machine.rkt")

(define (run core τ-place)
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ-place))
               '()
               '()
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

;; Assign は可変借用 capability を通じた書き換えだけを受け入れる。
(let ()
  (define result (run '(Scope (1) (Assign (BorrowMut 1) 7)) 'Int))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

(let ()
  (define result
    (run '(Scope (1) (Assign (ProjBorrow (BorrowMut 1) a) 7))
         '(Record ((a Int mut)))))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

;; shared capability と非借用値は代入できない。
(let ()
  (define result (run '(Scope (1) (Assign (Borrow 1) 7)) 'Int))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-through-shared))

(let ()
  (define result (run '(Scope (1) (Assign 1 7)) 'Int))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-non-borrow))

(let ()
  (define result
    (run '(Scope (1) (Assign (ProjBorrow (Borrow 1) a) 7))
         '(Record ((a Int imm)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-through-shared))

;; 可変借用から imm field を射影すると共有 capability へ落ちるため、
;; field mode 単独でも Assign を拒む。
(let ()
  (define result
    (run '(Scope (1) (Assign (ProjBorrow (BorrowMut 1) a) 7))
         '(Record ((a Int imm)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-through-shared))

;; target の payload に Owned を含める書き換えと、Union の一成分だけに
;; compat? する書き換えは拒む。
(let ()
  (define result (run '(Scope (1) (Assign (BorrowMut 1) 7)) '(Owned Res)))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-owned-payload))

(let ()
  (define result
    (run '(Scope (1) (Assign (BorrowMut 1) 7)) '(Union Bool Int)))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-union-variant))

(define assign-heap
  '((1 (Rec ((a mut 0) (b imm 0))))))
(define assign-omega '((1 Available)))

;; 根 capability への Assign は H の値だけを差し替え、Ω と θ は変えない。
(let ()
  (define conf
    (term (cfg (Assign (BorrowMutRef 1 () 0) 9)
               ((1 5))
               ((1 Available))
               ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg unit ((1 9)) ((1 Available)) ())))))

;; field path の Assign は根の record を関数的に更新する。
(let ()
  (define conf
    (term (cfg (Assign (BorrowMutRef 1 (a) 0) 9)
               ,assign-heap
               ,assign-omega
               ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list
    (term
     (cfg unit
          ((1 (Rec ((a mut 9) (b imm 0)))))
          ((1 Available))
          ())))))

;; Moved の place は Assign の対象にできず、規則は stuck する。
(let ()
  (define conf
    (term (cfg (Assign (BorrowMutRef 1 () 0) 9)
               ((1 5))
               ((1 Moved))
               ())))
  (check-equal? (apply-reduction-relation -->g2 conf) '()))

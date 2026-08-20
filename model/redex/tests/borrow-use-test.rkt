#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (rho-at ir point) (region->rho ir (region-at ir point)))
(define (status core ir τ_place)
  (first (type-of/raw (annotate-regions core ir)
                      (list (list 1 τ_place)) '() '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))))

(define (use-sources core ir τ_place)
  (define inferred
    (typing-inference (annotate-regions core ir)
                      (list (list 1 τ_place)) '() '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (map use-request-source
       (filter use-request? (fourth inferred))))

(define REC2 '(Record ((a Int mut) (b Int mut))))
(define INNER '(Record ((x Int mut))))
(define NEST `(Record ((a ,INNER mut))))

;; 1。Borrowed を通した Read。
(let ()
  (define core '(Scope (1) (Read (Borrow 1))))
  (check-equal? (status core (build-region-ir core) 'Int) 'ok))

;; 2。BorrowedMut を通した Read。
(let ()
  (define core '(Scope (1) (Read (BorrowMut 1))))
  (check-equal? (status core (build-region-ir core) 'Int) 'ok))

;; 3。BorrowedMut を通した Assign。
(let ()
  (define core '(Scope (1) (Assign (BorrowMut 1) 7)))
  (check-equal? (status core (build-region-ir core) 'Int) 'ok))

;; 4。mut の field の ProjBorrow。
(let ()
  (define core '(Scope (1) (ProjBorrow (BorrowMut 1) a)))
  (check-equal? (status core (build-region-ir core) REC2) 'ok))

;; 5。共有借用が 2 つ生きているとき、片方を通した Read が通る。
(let ()
  (define (make ρ1 ρ2)
    `(Scope (1)
            (Let (b1 let (Borrowed Int ,ρ1)) (Borrow 1)
                 (Let (b2 let (Borrowed Int ,ρ2)) (Borrow 1)
                      (Read b1)))))
  (define ir (build-region-ir (make 0 0)))
  (check-equal? (status (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir 'Int)
                'ok))

;; 6。所有者側の Move は重なる借用に阻まれる。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Borrow 1) (Move 1))))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0))) ir 'Res) 'fail))

;; 7。兄弟 field は重ならない。
(let ()
  (define (make ρ_b ρ_a)
    `(Scope (1)
            (Let (b let (BorrowedMut ,REC2 ,ρ_b)) (BorrowMut 1)
                 (Let (ba let (BorrowedMut Int ,ρ_a)) (ProjBorrow b a)
                      (Read (ProjBorrow b b))))))
  (define ir (build-region-ir (make 0 0)))
  (check-equal? (status (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir REC2)
                'ok))

;; 8。射影は新しい α を採らないため、同じ根から派生した親 field の
;; capability と子 field の使用は競合しない。ProjBorrow が新しい α を
;; 採る実装へ変われば、この回帰が fail へ転ぶ。
(let ()
  (define (make ρ_b ρ_a)
    `(Scope (1)
            (Let (b let (BorrowedMut ,NEST ,ρ_b)) (BorrowMut 1)
                 (Let (ba let (BorrowedMut ,INNER ,ρ_a)) (ProjBorrow b a)
                      (Read (ProjBorrow (ProjBorrow b a) x))))))
  (define ir (build-region-ir (make 0 0)))
  (check-equal? (status (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir NEST)
                'ok))

;; 9。子が生きているあいだ、親を通した Read を拒む。
(let ()
  (define (make ρ_b ρ_c)
    `(Scope (1)
            (Let (b let (BorrowedMut Int ,ρ_b)) (BorrowMut 1)
                 (Let (c let (Borrowed Int ,ρ_c)) (Reborrow b)
                      (Read b)))))
  (define ir (build-region-ir (make 0 0)))
  (check-equal? (status (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir 'Int)
                'fail))

;; 10。親を通した Assign も拒む。
(let ()
  (define (make ρ_b ρ_c)
    `(Scope (1)
            (Let (b let (BorrowedMut Int ,ρ_b)) (BorrowMut 1)
                 (Let (c let (Borrowed Int ,ρ_c)) (Reborrow b)
                      (Assign b 7)))))
  (define ir (build-region-ir (make 0 0)))
  (check-equal? (status (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir 'Int)
                'fail))

;; 11。親を通した ProjBorrow も拒む。
(let ()
  (define (make ρ_b ρ_c)
    `(Scope (1)
            (Let (b let (BorrowedMut ,REC2 ,ρ_b)) (BorrowMut 1)
                 (Let (c let (Borrowed ,REC2 ,ρ_c)) (Reborrow b)
                      (ProjBorrow b a)))))
  (define ir (build-region-ir (make 0 0)))
  (check-equal? (status (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir REC2)
                'fail))

;; 12。子を通した Read は通る。
(let ()
  (define (make ρ_b ρ_c)
    `(Scope (1)
            (Let (b let (BorrowedMut Int ,ρ_b)) (BorrowMut 1)
                 (Let (c let (Borrowed Int ,ρ_c)) (Reborrow b)
                      (Read c)))))
  (define ir (build-region-ir (make 0 0)))
  (check-equal? (status (make (rho-at ir '(0 0)) (rho-at ir '(0 1 0))) ir 'Int)
                'ok))

;; 13。両分岐で作った借用を合流した capability の source は、2 つの葉へ
;; 展開され、合流 alpha 自身を残さない。
(let ()
  (define (make ρ)
    `(Scope (1)
            (Let (b let (Borrowed Int ,ρ))
                 (Eliminate (Construct Bool true)
                            ((true () -> (Borrow 1))
                             (false () -> (Borrow 1))))
                 (Read b))))
  (define ir (build-region-ir (make 0)))
  (define sources (use-sources (make (rho-at ir '(0 0))) ir 'Int))
  (check-equal? (length sources) 1)
  (check-equal? (set-count (first sources)) 2)
  (check-true (for/and ([α (in-set (first sources))])
                (lifetime-var? α))))

;; 14。入れ子の合流も葉まで展開し、3 つの葉を source へ残す。
(let ()
  (define (make ρ)
    `(Scope (1)
            (Let (b let (Borrowed Int ,ρ))
                 (Eliminate (Construct Bool true)
                            ((true () -> (Eliminate (Construct Bool true)
                                                    ((true () -> (Borrow 1))
                                                     (false () -> (Borrow 1)))))
                             (false () -> (Borrow 1))))
                 (Read b))))
  (define ir (build-region-ir (make 0)))
  (define sources (use-sources (make (rho-at ir '(0 0))) ir 'Int))
  (check-equal? (length sources) 1)
  (check-equal? (set-count (first sources)) 3)
  (check-true (for/and ([α (in-set (first sources))])
                (lifetime-var? α))))

;; 15。実体化を経ても source は解の前に保存したものを使う。
(let ()
  (define (make ρ_b)
    `(Scope (1)
            (Let (b let (BorrowedMut ,REC2 ,ρ_b)) (BorrowMut 1)
                 (Assign (ProjBorrow b a) 7))))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0))) ir REC2) 'ok))

;; 16。同じ root/path の共有借用でも、source は型の alpha ごとに別々に
;; 保存される。source を項の形から推し量る実装は 2 本を同一視して誤る。
;; 停止を絡めた同時共存は、Reborrow が可変借用だけを受け、同じ場所の
;; 可変と共有が BOR-002 で共存しないため書けない。
(let ()
  (define core
    `(Scope (1)
            (Let (b1 let (Borrowed Int 0)) (Borrow 1)
                 (Let (b2 let (Borrowed Int 0)) (Borrow 1)
                      (Yield (Read b1) (Read b2))))))
  (define ir (build-region-ir core))
  (define inferred
    (typing-inference (annotate-regions core ir)
                      (list (list 1 'Int)) '() '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (define read-sources
    (map use-request-source
         (filter use-request? (fourth inferred))))
  (check-equal? (length read-sources) 2)
  (check-not-equal? (first read-sources) (second read-sources)))

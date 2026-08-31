#lang racket

;; [REQ: BOR-004] Read の型付けと copy-out-ok?。

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../validators.rkt"
         "../typing.rkt"
         "../machine.rkt")

;; spec §6.2。所有値も借用も複製できない。
(check-false (copy-out-ok? '(Owned Res)))
(check-false (copy-out-ok? '(Borrowed Res 0)))
(check-false (copy-out-ok? '(BorrowedMut Res 0)))
;; 包む型は payload へ再帰する。
(check-false (copy-out-ok? '(List (Owned Res))))
(check-false (copy-out-ok? '(Option (BorrowedMut Res 0))))
(check-false (copy-out-ok? '(Untrusted (Borrowed Res 0))))
(check-false (copy-out-ok? '(Record ((a (Owned Res) imm)))))
(check-false (copy-out-ok? '(Record ((a (BorrowedMut Res 0) mut)))))
;; Result / Union / Intersection / Refined も payload を再帰する。
(check-false (copy-out-ok? '(Result Int (Borrowed Res 0))))
(check-false (copy-out-ok? '(Union Int (Owned Res))))
(check-false
 (copy-out-ok? '(Intersection (Record ((a Int imm)))
                             (Record ((b (BorrowedMut Res 0) mut))))))
(check-false (copy-out-ok? '(Refined (Owned Res) (Prop P))))
;; NFn は引数、戻り値、effect の payload まで辿る。
(check-false
 (copy-out-ok? '(NFn (Int) Int ((Yield (BorrowedMut Res 0))) ())))
;; 複製してよい型。
(check-true (copy-out-ok? 'Int))
(check-true (copy-out-ok? '(Record ((a Int imm) (b Bool mut)))))
(check-true (copy-out-ok? '(List Int)))
(check-true (copy-out-ok? '(Result Int Bool)))
(check-true (copy-out-ok? '(Union Int Bool)))
(check-true
 (copy-out-ok? '(Intersection (Record ((a Int imm)))
                             (Record ((b Bool mut))))))
(check-true (copy-out-ok? '(Refined Int (Prop P))))

;; owned-free? は変えない。可変借用は今までどおり素通りする。
;; この 1 件が、2 つの述語を分けた理由（spec §6.2）を固定する。
(check-true (owned-free? '(BorrowedMut Res 0)))

(define (run core ir τ_place)
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ_place)) '() '()
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

;; 受理。共有借用から読み出すと payload の型が返る。
(let ()
  (define core '(Scope (1) (Read (Borrow 1))))
  (define ir (build-region-ir core))
  (define result (run core ir 'Int))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Int))

;; 可変借用から読み出しても結果は同じ型である。
(let ()
  (define core '(Scope (1) (Read (BorrowMut 1))))
  (define ir (build-region-ir core))
  (define result (run core ir 'Int))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Int))

;; 射影した借用から読み出す。Task 3 の path が乗った借用でも通る。
(let ()
  (define core '(Scope (1) (Read (ProjBorrow (Borrow 1) a))))
  (define ir (build-region-ir core))
  (define result (run core ir '(Record ((a Int imm)))))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Int))

;; 拒否 1。借用でない値を読む。
(let ()
  (define core '(Scope (1) (Read 0)))
  (define ir (build-region-ir core))
  (define result (run core ir 'Int))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'read-non-borrow))

;; 拒否 2。payload が所有値を含む。
(let ()
  (define core '(Scope (1) (Read (Borrow 1))))
  (define ir (build-region-ir core))
  (define result (run core ir '(Record ((a (Owned Res) imm)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'read-uncopyable-payload))

(define read-heap
  '((1 42)
    (2 (Rec ((a imm 7))))))
(define read-omega '((1 Available) (2 Available)))
(define moved-omega '((1 Moved) (2 Available)))

;; 共有借用の読み出しは H の値を返す。H、Ω、θ は変わらない（spec §6.3）。
(let ()
  (define conf
    (term (cfg (Read (BorrowRef 1 () 0)) ,read-heap ,read-omega () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg 42 ,read-heap ,read-omega () ())))))

;; 可変借用の読み出しも同じ値を返す。
(let ()
  (define conf
    (term (cfg (Read (BorrowMutRef 1 () 0)) ,read-heap ,read-omega () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg 42 ,read-heap ,read-omega () ())))))

;; path を持つ借用は fp を辿った先を返す。
(let ()
  (define conf
    (term (cfg (Read (BorrowRef 2 (a) 0)) ,read-heap ,read-omega () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg 7 ,read-heap ,read-omega () ())))))

;; Moved の place は読めない。規則が当たらず 1 歩も進まない（spec §6.3）。
(let ()
  (define conf
    (term (cfg (Read (BorrowRef 1 () 0)) ,read-heap ,moved-omega () ())))
  (check-equal? (length (apply-reduction-relation -->g2 conf)) 0))

;; 拒否 2 の 2 件目。payload が可変借用を含む。
;; owned-free? を流用していれば通ってしまう形である。
(let ()
  (define core '(Scope (1) (Read (Borrow 1))))
  (define ir (build-region-ir core))
  (define result
    (run core ir '(Record ((a (BorrowedMut Res 0) mut)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'read-uncopyable-payload))

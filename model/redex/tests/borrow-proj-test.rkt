#lang racket

;; [REQ: BOR-005] ProjBorrow の型付けと mode の表。

(require rackunit
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../type-shape.rkt"
         "../typing.rkt"
         "../machine.rkt")

;; spec §5.2 の表。親が共有ならば field の可変性によらず子は共有。
(check-equal? (proj-borrow-mode 'Borrowed 'imm) 'Borrowed)
(check-equal? (proj-borrow-mode 'Borrowed 'mut) 'Borrowed)
;; 親が可変で field が mut のときだけ子が可変になる。
(check-equal? (proj-borrow-mode 'BorrowedMut 'mut) 'BorrowedMut)
(check-equal? (proj-borrow-mode 'BorrowedMut 'imm) 'Borrowed)

;; 注釈は親の own の末尾へ label を足す（spec §4.2、§5.1）。
(let ()
  (define core '(Scope (1) (ProjBorrow (Borrow 1) a)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal?
   (match annotated
     [`(Scope (1) (ProjBorrowAt ,_ ,own ,_ ,_)) own]
     [_ 'no-match])
   '(Own 1 (a))))

;; 2 段の射影で path が 2 要素になる。
(let ()
  (define core '(Scope (1) (ProjBorrow (ProjBorrow (Borrow 1) a) b)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal?
   (match annotated
     [`(Scope (1) (ProjBorrowAt ,_ ,own ,_ ,_)) own]
     [_ 'no-match])
   '(Own 1 (a b))))

;; borrow-token-key は子の capability を返す。親のものではない。
(let ()
  (define core '(Scope (1) (ProjBorrow (Borrow 1) a)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define inner (match annotated [`(Scope (1) ,c) c]))
  (check-equal? (borrow-token-key (empty-region-ctx) inner)
                (set (cons 1 '(a)))))

;; 補助。1 番の place に record 型を与えて型付けする。
(define rec-τ '(Record ((a Int mut) (b Bool imm))))
(define (proj-heap)
  '((1 (Rec ((a mut 0) (b imm 1))))))
(define (proj-omega)
  '((1 Available)))

(define (run core ir [τ_place rec-τ])
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ_place)) '() '()
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

;; 受理。可変借用から mut の field を射影すると可変借用が返る。
(let ()
  (define core '(Scope (1) (ProjBorrow (BorrowMut 1) a)))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (check-equal? (first result) 'ok)
  (check-equal? (match (first (second result)) [`(BorrowedMut ,τ ,_) τ] [_ 'no-match])
                'Int))

;; 可変借用から imm の field を射影すると共有借用へ落ちる（spec §5.2）。
(let ()
  (define core '(Scope (1) (ProjBorrow (BorrowMut 1) b)))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (check-equal? (first result) 'ok)
  (check-equal? (match (first (second result)) [`(Borrowed ,τ ,_) τ] [_ 'no-match])
                'Bool))

;; 射影の結果の region は親と同じである。新しい α を採らない（spec §5.1）。
(let ()
  (define core '(Scope (1) (ProjBorrow (BorrowMut 1) a)))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (define α_child (match (first (second result)) [`(BorrowedMut ,_ ,α) α]))
  ;; 同じ IR の operand point と比べる。別の IR は region 識別子の採番が
  ;; 独立なので、同値な region でも natural が一致するとは限らない。
  (define α_parent
    (region->rho ir (region-at ir '(0 0))))
  (check-equal? α_child α_parent))

;; 所有値を内側に含む field の射影は通る（spec §5.4）。
(let ()
  (define nested '(Record ((c (Owned Res) imm))))
  (define core '(Scope (1) (ProjBorrow (BorrowMut 1) a)))
  (define ir (build-region-ir core))
  (define result (run core ir `(Record ((a ,nested mut)))))
  (check-equal? (first result) 'ok)
  (check-equal? (match (first (second result)) [`(BorrowedMut ,τ ,_) τ] [_ 'no-match])
                nested))

;; 拒否 0。field の型が直接の Owned のときは borrow.md §2 が禁じる形になる。
(let ()
  (define core '(Scope (1) (ProjBorrow (BorrowMut 1) a)))
  (define ir (build-region-ir core))
  (define result (run core ir '(Record ((a (Owned Res) mut)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'borrowed-owned-payload))

;; 拒否 1。record でない借用を射影する。
(let ()
  (define core '(Scope (1) (ProjBorrow (Borrow 1) a)))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw (annotate-regions core ir)
                 (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'projborrow-non-record))

;; 機械は射影で H と Ω を変更しない（spec §5.3）。
(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (Own 1 (a))
                             (BorrowRef 1 () 1) a)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg (BorrowRef 1 (a) 0)
                    ,(proj-heap) ,(proj-omega) () ())))))

(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (Own 1 (a))
                             (BorrowMutRef 1 () 1) a)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg (BorrowMutRef 1 (a) 0)
                    ,(proj-heap) ,(proj-omega) () ())))))

(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (Own 1 (b))
                             (BorrowMutRef 1 () 1) b)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg (BorrowRef 1 (b) 0)
                    ,(proj-heap) ,(proj-omega) () ())))))

;; own の root だけが射影結果と食い違う configuration は stuck にする。
(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (Own 2 (a))
                             (BorrowRef 1 () 1) a)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal? (apply-reduction-relation -->g2 conf) '()))

;; own の path だけが射影結果と食い違う configuration は stuck にする。
(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (Own 1 (wrong))
                             (BorrowRef 1 () 1) a)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal? (apply-reduction-relation -->g2 conf) '()))

;; 可変借用の射影も own の root を検査し、proj-borrow-mut より先に stuck にする。
(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (Own 2 (a))
                             (BorrowMutRef 1 () 1) a)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal? (apply-reduction-relation -->g2 conf) '()))

;; 拒否 2。row に無い label を射影する。
(let ()
  (define core '(Scope (1) (ProjBorrow (Borrow 1) z)))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'projborrow-unknown-field))

;; 借用でない operand には capability が無いため、冗長な own 欄を
;; fail-closed で拒む。
(let ()
  (define core '(Scope (1) (ProjBorrowAt 0 (Own 1 (a))
                                         (Rec ((a mut 0))) a)))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw core (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (second result) 'own-designator-mismatch))

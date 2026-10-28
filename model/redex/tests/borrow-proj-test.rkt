#lang racket

;; [REQ: BOR-005] ProjBorrow の型付けと mode の表。

(require rackunit
         racket/set
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../type-shape.rkt"
         "../typing.rkt"
         "../machine.rkt")

;; spec §5.2 の表。親が共有ならば field の可変性によらず子は共有。
(test-case "BOR-005: projected borrow mode follows parent and field mutability"
  (check-equal? (proj-borrow-mode 'Borrowed 'imm) 'Borrowed)
  (check-equal? (proj-borrow-mode 'Borrowed 'mut) 'Borrowed)
  ;; 親が可変で field が mut のときだけ子が可変になる。
  (check-equal? (proj-borrow-mode 'BorrowedMut 'mut) 'BorrowedMut)
  (check-equal? (proj-borrow-mode 'BorrowedMut 'imm) 'Borrowed))

;; 射影は own 欄を持たず、親の capability から path を導く。
(let ()
  (define core '(Scope (1) (ProjBorrow (Borrow 1) a)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal?
   (match annotated
     [`(Scope (1) (ProjBorrowAt ,_ (BorrowAt ,_ (Own 1 ()) 1) a)) #t]
     [_ #f])
   #t))

;; 2 段の射影で path が 2 要素になる。
(let ()
  (define core '(Scope (1) (ProjBorrow (ProjBorrow (Borrow 1) a) b)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal? annotated
                '(Scope (1)
                   (ProjBorrowAt 3
                     (ProjBorrowAt 3 (BorrowAt 3 (Own 1 ()) 1) a)
                     b))))

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
  `((1 (Rec ((a mut 0) (b imm 1))) (declared ,rec-τ))))
(define (proj-omega)
  '((1 Available)))

(define (run core ir [τ_place rec-τ])
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ_place)) '() '()
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

;; mut field の射影結果は可変借用として代入に使える。
(let ()
  (define core '(Assign (ProjBorrow (BorrowMut 1) a) 2))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (check-equal? result '(ok (Unit (Mutation)))))

;; 可変借用から imm の field を射影すると共有借用へ落ちる（spec §5.2）。
(let ()
  (define core '(Read (ProjBorrow (BorrowMut 1) b)))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Bool))

;; imm field の射影結果は共有借用であり、代入先にはできない。
(let ()
  (define core '(Assign (ProjBorrow (BorrowMut 1) b) true))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-through-shared))

;; 同じ lexical Scope にある parent/child は region 解決後に同じ場所を指す。
(test-case "一時型付けで解決した親と射影の region が同じ場合がある"
  (define core '(ProjBorrow (BorrowMut 1) a))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (define α_child
    (match (first (second result)) [`(BorrowedMut ,_ ,α) α]))
  (define annotated (annotate-regions core ir))
  (define α_parent
    (match annotated
      [`(ProjBorrowAt ,_ (BorrowMutAt ,ρ ,_ ,_) ,_) ρ]))
  (check-equal? α_child α_parent))

(test-case "同じ Scope の ProjBorrow も親と別の alpha を採る"
  (define core
    '(Scope ()
       (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
         (Let (p let (BorrowedMut (Record ((n Int mut)))
                                   (RParam %omitted)))
              (BorrowMut x)
           (Let (c let (BorrowedMut Int (RParam %omitted)))
                (ProjBorrow p n)
             unit)))))
  (define typed (core-type-of/regions core '() '()))
  (check-true (region-typed? typed) (format "region 型付け: ~s" typed))
  (when (region-typed? typed)
    (define alpha-table (region-typed-table typed))
    (define parent-alpha (hash-ref alpha-table '(0 1 0)))
    (define child-alpha (hash-ref alpha-table '(0 1 1 0)))
    (check-not-equal? parent-alpha child-alpha)
    (check-equal? (hash-ref (region-typed-σ typed) 0)
                  (hash-ref (region-typed-σ typed) 1))))

;; 所有値を内側に含む field の射影は通る（spec §5.4）。
(let ()
  (define nested '(Record ((c (Owned Res) imm))))
  (define core '(ProjBorrow (BorrowMut 1) a))
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
    (term (cfg (ProjBorrowAt 0 (BorrowRef 1 () 1) a)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg (BorrowRef 1 (a) 1)
                    ,(proj-heap) ,(proj-omega) () ())))))

(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (BorrowMutRef 1 () 1) a)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg (BorrowMutRef 1 (a) 0)
                    ,(proj-heap) ,(proj-omega) () ())))))

(let ()
  (define conf
    (term (cfg (ProjBorrowAt 0 (BorrowMutRef 1 () 1) b)
               ,(proj-heap) ,(proj-omega) () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg (BorrowRef 1 (b) 0)
                    ,(proj-heap) ,(proj-omega) () ())))))

(test-case "可変親からの ProjBorrowAt は注釈の region を結果に使う"
  (for ([annotation (in-list '(0 1 7))])
    (define conf
      (term (cfg (ProjBorrowAt ,annotation (BorrowMutRef 1 () 1) a)
                 ,(proj-heap) ,(proj-omega) () ())))
    (check-equal?
     (apply-reduction-relation -->g2 conf)
     (list (term (cfg (BorrowMutRef 1 (a) ,annotation)
                      ,(proj-heap) ,(proj-omega) () ()))))))

;; 拒否 2。row に無い label を射影する。
(let ()
  (define core '(Scope (1) (ProjBorrow (Borrow 1) z)))
  (define ir (build-region-ir core))
  (define result (run core ir))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'projborrow-unknown-field))

;; 借用でない operand は ProjBorrowAt の型規則で拒む。
(let ()
  (define core '(Scope (1) (ProjBorrowAt 0 (Rec ((a mut 0))) a)))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw core (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (second result) 'projborrow-non-record))

(test-case "借用の path は label だけを受理する"
  (check-true (record-path? (term (a b))))
  (check-false (record-path? (term (a 0))))
  (check-true (owner-path? (term (a 0))))
  (check-true (path-wf? (term (a 0))))
  (check-false (path-wf? (term (a (b))))))

(test-case "record でない値への射影は例外でなく #f になる"
  (check-false (heap-walk-path (term (resource 1)) (term (a)))))

(test-case "natural を含む path の借用は簡約できない"
  (define config
    (term (cfg (Read (BorrowRef 0 (a 0) 0))
               ((0 (Rec ((a imm (resource 1))))))
               ((0 Available))
               ()
               ())))
  (check-equal? (apply-reduction-relation -->g2 config) '()))

(test-case "optional field の ProjBorrow は専用診断で拒否する"
  (define opt-rec-τ '(Record ((a Int imm) (b Int imm opt))))
  (define core '(Scope (1) (ProjBorrow (Borrow 1) b)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define result
    (core-type-of/diagnostic
     annotated
     (list (list 1 opt-rec-τ))
     '() '()
     (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (and (diagnostic? result) (diagnostic-id result))
                "E-BOR-026"))

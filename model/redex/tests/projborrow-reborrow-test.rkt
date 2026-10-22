#lang racket

(require rackunit
         "../annotate.rkt"
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../region.rkt"
         "../typing.rkt")

(define owner-type '(Record ((a Int mut) (b Int mut))))

(define (field-reborrow body)
  `(Scope ()
     (Let (x let (Owned ,owner-type)) (Rec ((a mut 1) (b mut 2)))
       (Let (root let (BorrowedMut ,owner-type (RParam %omitted)))
            (BorrowMut x)
         (Let (field let (BorrowedMut Int (RParam %omitted)))
              (ProjBorrow root a)
           (Let (child let (Borrowed Int (RParam %omitted)))
                (Reborrow field)
             ,body)))))
)

(define (type-result body)
  (core-type-of/regions (field-reborrow body) '() '()))

(define (raw-result body)
  (define core (field-reborrow body))
  (define ir (build-region-ir core))
  (type-of/raw*+borrows
   (annotate-regions core ir) '() '() '()
   (region-ctx ir '() (hash) (hash))))

(define (check-rejected result expected-id)
  (check-true (diagnostic? result) (format "診断を期待: ~s" result))
  (check-equal? (diagnostic-id result) expected-id))

(test-case "射影した可変借用を再借用して読み出せる"
  (define result (type-result '(Read child)))
  (check-true (region-typed? result)
              (format "region 型付け: ~s; raw: ~s"
                      result (raw-result '(Read child))))
  (check-equal? (region-typed-type result) 'Int))

(test-case "再借用の生存中は親の同じ欄への書込みを拒否する"
  (check-rejected
   (type-result
    '(Let (ignored let Unit) (Assign (ProjBorrow root a) 3) (Read child)))
   "E-BOR-025"))

(test-case "再借用の生存中は親の別の欄へ書き込める"
  (define result
    (type-result
     '(Let (ignored let Unit) (Assign (ProjBorrow root b) 3) (Read child))))
  (check-true (region-typed? result) (format "region 型付け: ~s" result))
  (check-equal? (region-typed-type result) 'Int))

(test-case "再借用の生存中は親全体への書込みを拒否する"
  (check-rejected
   (type-result
    `(Let (ignored let Unit)
          (Assign root (Rec ((a mut 3) (b mut 4))))
          (Read child)))
   "E-BOR-025"))

(test-case "再借用の生存中は root の所有者を move できない"
  (check-rejected
   (type-result
    `(Let (moved let (Owned ,owner-type)) (Move x) (Read child)))
   "E-BOR-008"))

(test-case "再借用の子が死んだ後は親の同じ欄へ書き込める"
  (define core
    `(Scope ()
       (Let (x let (Owned ,owner-type)) (Rec ((a mut 1) (b mut 2)))
         (Let (root let (BorrowedMut ,owner-type (RParam %omitted)))
              (BorrowMut x)
           (Let (field let (BorrowedMut Int (RParam %omitted)))
                (ProjBorrow root a)
             (Let (ignored let Int) (Scope ()
                            (Let (child let (Borrowed Int (RParam %omitted)))
                                 (Reborrow field)
                              (Read child)))
               (Assign (ProjBorrow root a) 3)))))))
  (define result (core-type-of/regions core '() '()))
  (check-true (region-typed? result) (format "region 型付け: ~s" result)))

(test-case "Loop の借用仮引数は E-BOR-012 で止まり再借用を次反復へ持ち越せない"
  (define source
    `(Fn ((p (Owned ,owner-type))) Int (Partial Mutation Own)
       (LexicalScope
        (Let (x let (Owned ,owner-type)) (Move p)
          (Let (root let (BorrowedMut ,owner-type Omitted)) (BorrowMut x)
            (Let (child let (Borrowed Int Omitted)) (Reborrow (Proj root a))
                (Loop loop ((next (Borrowed Int Omitted))) Int
                  (Partial Mutation Own)
                  (Let (ignored let Unit)
                       (Assign (Proj root a) 3)
                    (Let (again let (Borrowed Int Omitted))
                         (Reborrow (Proj root a))
                      (Apply loop next)))
                  (child))))))))
  (define result (elab (annotate-surface source)))
  (define diagnostic
    (match result
      [`(err ,diagnostic) diagnostic]
      [(list core _type _row callables)
       (core-type-of/regions core '() callables)]
      [_ (fail (format "予期しない elab 結果: ~s" result))]))
  (check-true (diagnostic? diagnostic)
              (format "診断を期待: ~s" diagnostic))
  (check-equal? (diagnostic-id diagnostic) "E-BOR-012"))

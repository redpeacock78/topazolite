#lang racket

(require rackunit
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../typing.rkt")

(define (function-with body)
  `(Fn ((p (Owned Int))) Int (Own Mutation)
       (LexicalScope
        (Let (x let (Owned Int)) (Move p)
          (Let (b let (BorrowedMut Int Omitted)) (BorrowMut x)
            ,body)))))

(define (compile-and-type body)
  (match (elab (function-with body))
    [(list core _type _row callables)
     (values core callables (core-type-of/regions core '() callables))]
    [`(err ,diagnostic)
     (fail (format "elaboration を期待したが ~s" diagnostic))]))

(test-case "関数本体の再借用結果を読める"
  (define-values (_core _callables typed)
    (compile-and-type
     '(Let (child let (Borrowed Int Omitted)) (Reborrow b)
        (Read child))))
  (check-true (region-typed? typed) (format "region 型付け: ~s" typed)))

(test-case "子の生存中は関数本体の親を書けない"
  (define-values (_core _callables result)
    (compile-and-type
     '(Let (child let (Borrowed Int Omitted)) (Reborrow b)
        (Let ignored (Assign b 18) (Read child)))))
  (check-true (diagnostic? result) (format "診断を期待: ~s" result))
  (check-equal? (diagnostic-id result) "E-BOR-025"))

(test-case "子が死んだ後は関数本体の親を書ける"
  (define-values (_core _callables typed)
    (compile-and-type
     '(Let ignored
          (LexicalScope
           (Let (child let (Borrowed Int Omitted)) (Reborrow b)
             (Read child)))
        (Let assigned (Assign b 18) 0))))
  (check-true (region-typed? typed) (format "region 型付け: ~s" typed)))

(test-case "ProjBorrow の欄を読んだ後も関数本体の親を書ける"
  (define expression
    '(Fn ((p (Owned (Record ((n Int mut)))))) Unit (Own Mutation)
         (LexicalScope
          (Let (x let (Owned (Record ((n Int mut))))) (Move p)
            (Let (b let (BorrowedMut (Record ((n Int mut))) Omitted))
                 (BorrowMut x)
              (Let (field let (BorrowedMut Int Omitted)) (Proj b n)
                (Let ignored (Read field) (Assign b (Rec ((n mut 1)))))))))))
  (match (elab expression)
    [(list core _type _row callables)
     (define result (core-type-of/regions core '() callables))
     (check-true (region-typed? result) (format "region 型付け: ~s" result))]
    [`(err ,diagnostic) (fail (format "elaboration: ~s" diagnostic))]))

(test-case "合流した可変借用を再借用して関数本体で読める"
  (define expression
    '(Fn ((p (Owned Int)) (q (Owned Int)) (condition Bool)) Int (Own Mutation)
         (LexicalScope
          (Let (x let (Owned Int)) (Move p)
            (Let (y let (Owned Int)) (Move q)
              (Let (left let (BorrowedMut Int Omitted)) (BorrowMut x)
                (Let (right let (BorrowedMut Int Omitted)) (BorrowMut y)
                  (Let (b let (BorrowedMut Int Omitted))
                       (Eliminate condition
                         ((true () -> left) (false () -> right)))
                    (Let (child let (Borrowed Int Omitted)) (Reborrow b)
                      (Read child))))))))))
  (match (elab expression)
    [(list core _type _row callables)
     (define typed (core-type-of/regions core '() callables))
     (check-true (region-typed? typed) (format "region 型付け: ~s" typed))]
    [`(err ,diagnostic) (fail (format "elaboration: ~s" diagnostic))]))

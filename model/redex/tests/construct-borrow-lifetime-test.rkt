#lang racket

(require rackunit
         racket/match
         racket/set
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../origins.rkt"
         "../region-param.rkt"
         "../traits.rkt"
         "../typing.rkt")

(define data-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((BorrowBox (A) ((box ((Param A)))))
            (BorrowPair (A) ((pair ((Param A) (Param A)))))
            (MutablePair (A) ((mpair ((Param A) (Param A)))))
            (MutableInvariantPair
             (A) ((mutable-invariant-pair
                   ((ForallRegion (r)
                      (BorrowedMut (Param A) (RParam r)))
                    (ForallRegion (r)
                      (BorrowedMut (Param A) (RParam r))))))))
   #:fail (lambda (reason kind key)
            (error 'construct-borrow-lifetime-test "~s ~s ~s" reason kind key))))

(define core-borrow '(Borrowed Int (RParam %omitted)))
(define ucore-borrow '(Borrowed Int Omitted))
(define core-mut-borrow '(BorrowedMut Int (RParam %omitted)))
(define ucore-mut-borrow '(BorrowedMut Int Omitted))
(define (box-type payload) `(Data BorrowBox (,payload)))
(define (pair-type payload) `(Data BorrowPair (,payload)))
(define (mutable-pair-type payload) `(Data MutablePair (,payload)))
(define union-type `(Union ,core-borrow String))
(define ucore-union-type `(Union ,ucore-borrow String))
(define mut-union-type `(Union ,core-mut-borrow String))
(define mut-ucore-union-type `(Union ,ucore-mut-borrow String))

(define (with-data thunk)
  (call-with-trait-ledger data-ledger thunk))

(define (core-type core [callables '()])
  (with-data (lambda () (core-type-of/regions core '() callables))))

(define (core-type/env core environment bound-params)
  (with-data
   (lambda ()
     (parameterize ([bound-region-params (list->set bound-params)])
       (core-type-of/regions core '() '() environment)))))

(define (core-type/places core places)
  (with-data
   (lambda () (core-type-of/regions core places '()))))

(define (elaborated-type source)
  (with-data
   (lambda ()
     (match (elab source)
       [(list core _type _row callables)
        (core-type-of/regions core '() callables)]
       [`(err ,diagnostic) diagnostic]
       [other (error 'elaborated-type "unexpected elaboration result: ~s" other)]))))

(define (check-accepted result)
  (check-true (region-typed? result) (format "型付け結果: ~s" result)))

(define (check-rejected result id)
  (check-true (diagnostic? result) (format "診断結果: ~s" result))
  (check-equal? (diagnostic-id result) id (format "diagnostic: ~s" result)))

(define (core-option-escape)
  `(Scope ()
     (Let (container let (Option ,core-borrow))
          (Scope ()
            (Let (x let (Owned Int)) 1
              (Construct (Option ,core-borrow) some (Borrow x))))
       (Eliminate container
         ((none () -> 0) (some (value) -> (Read value)))))))

(define (core-box-escape)
  `(Scope ()
     (Let (container let ,(box-type core-borrow))
          (Scope ()
            (Let (x let (Owned Int)) 1
              (Construct ,(box-type core-borrow) box (Borrow x))))
       (Eliminate container ((box (value) -> (Read value)))))))

(define (core-union-escape)
  `(Scope ()
     (Let (value let ,union-type)
          (Scope ()
            (Let (x let (Owned Int)) 1
              (UnionInject ,union-type ,core-borrow (Borrow x))))
       (UnionEliminate value
         ((,core-borrow borrowed -> (Read borrowed))
          (String text -> 0))))))

(define (core-option-read)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (container let (Option ,core-borrow))
            (Construct (Option ,core-borrow) some (Borrow x))
         (Eliminate container
           ((none () -> 0) (some (value) -> (Read value))))))))

(define (core-box-read)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (container let ,(box-type core-borrow))
            (Construct ,(box-type core-borrow) box (Borrow x))
         (Eliminate container ((box (value) -> (Read value))))))))

(define (core-list-read)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (items let (List ,core-borrow))
            (Construct (List ,core-borrow) cons
                       (Borrow x)
                       (Construct (List ,core-borrow) nil))
         (Eliminate items
           ((nil () -> 0)
            (cons (head tail) -> (Read head))))))))

(define (core-union-read)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (value let ,union-type)
            (UnionInject ,union-type ,core-borrow (Borrow x))
         (UnionEliminate value
           ((,core-borrow borrowed -> (Read borrowed))
            (String text -> 0)))))))

(define (ucore-option-escape)
  `(Fn ((p (Owned Int))) Int (Own)
     (LexicalScope
       (Let (container let (Option ,ucore-borrow))
            (LexicalScope
             (Let (x let (Owned Int)) (Move p)
               (Construct some (Types ,ucore-borrow) (Borrow x))))
         (Eliminate container
           ((none () -> 0) (some (value) -> (Read value))))))))

(define (ucore-box-escape)
  `(Fn ((p (Owned Int))) Int (Own)
     (LexicalScope
       (Let (container let ,(box-type ucore-borrow))
          (LexicalScope
           (Let (x let (Owned Int)) (Move p)
             (Construct box (Types ,ucore-borrow) (Borrow x))))
         (Eliminate container ((box (value) -> (Read value))))))))

(define (ucore-union-escape)
  `(Fn ((p (Owned Int))) Int (Own)
     (LexicalScope
       (Let (value let ,ucore-union-type)
            (LexicalScope
             (Let (x let (Owned Int)) (Move p) (Borrow x)))
         (Eliminate value
           ((,ucore-borrow borrowed -> (Read borrowed))
            (String text -> 0)))))))

(define (ucore-option-read)
  (define branches '((none () -> 0) (some (value) -> (Read value))))
  (define construction `(Construct some (Types ,ucore-borrow) (Borrow x)))
  (define option-let
    `(Let (container let (Option ,ucore-borrow)) ,construction
       (Eliminate container ,branches)))
  (define x-let `(Let (x let (Owned Int)) (Move p) ,option-let))
  `(Fn ((p (Owned Int))) Int (Own) (LexicalScope ,x-let)))

(define (ucore-option-mut-move)
  `(Fn ((p (Owned Int))) Unit (Own)
     (LexicalScope
       (Let (x let (Owned Int)) (Move p)
         (Let (container let (Option ,ucore-mut-borrow))
              (Construct some (Types ,ucore-mut-borrow) (BorrowMut x))
           (Let (moved let (Owned Int)) (Move x)
             (Eliminate container
               ((none () -> unit) (some (value) -> unit)))))))))

(define (ucore-box-read)
  (define branches '((box (value) -> (Read value))))
  (define construction `(Construct box (Types ,ucore-borrow) (Borrow x)))
  (define box-let
    `(Let (container let ,(box-type ucore-borrow)) ,construction
       (Eliminate container ,branches)))
  (define x-let `(Let (x let (Owned Int)) (Move p) ,box-let))
  `(Fn ((p (Owned Int))) Int (Own) (LexicalScope ,x-let)))

(define (ucore-box-mut-move)
  (define construction `(Construct box (Types ,ucore-mut-borrow) (BorrowMut x)))
  (define box-let
    `(Let (container let ,(box-type ucore-mut-borrow)) ,construction
       (Let (moved let (Owned Int)) (Move x)
         (Eliminate container ((box (value) -> unit))))))
  (define x-let `(Let (x let (Owned Int)) (Move p) ,box-let))
  `(Fn ((p (Owned Int))) Unit (Own) (LexicalScope ,x-let)))

(define (ucore-list-read)
  (define item-type `(List ,ucore-borrow))
  (define branches '((nil () -> 0) (cons (head tail) -> (Read head))))
  (define construction
    `(Construct cons (Types ,ucore-borrow)
                (Borrow x)
                (Construct nil (Types ,ucore-borrow))))
  (define items-let `(Let (items let ,item-type) ,construction
                          (Eliminate items ,branches)))
  (define x-let `(Let (x let (Owned Int)) (Move p) ,items-let))
  `(Fn ((p (Owned Int))) Int (Own) (LexicalScope ,x-let)))

(define (ucore-union-read)
  (define branches
    (list (list ucore-borrow 'borrowed '-> '(Read borrowed))
          '(String text -> 0)))
  (define value-let
    `(Let (value let ,ucore-union-type) (Borrow x)
       (Eliminate value ,branches)))
  (define x-let `(Let (x let (Owned Int)) (Move p) ,value-let))
  `(Fn ((p (Owned Int))) Int (Own) (LexicalScope ,x-let)))

(define (ucore-union-mut-move)
  (define value-let
    `(Let (value let ,mut-ucore-union-type) (BorrowMut x)
       (Let (moved let (Owned Int)) (Move x)
         (Eliminate value
           ((,ucore-mut-borrow borrowed -> unit)
            (String text -> unit))))))
  `(Fn ((p (Owned Int))) Unit (Own) (LexicalScope
       (Let (x let (Owned Int)) (Move p) ,value-let))))

(define (core-option-mut-move)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (container let (Option ,core-mut-borrow))
            (Construct (Option ,core-mut-borrow) some (BorrowMut x))
         (Let (moved let (Owned Int)) (Move x)
           (Eliminate container ((none () -> unit) (some (value) -> unit))))))))

(define (core-box-mut-move)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (container let ,(box-type core-mut-borrow))
            (Construct ,(box-type core-mut-borrow) box (BorrowMut x))
         (Let (moved let (Owned Int)) (Move x)
           (Eliminate container ((box (value) -> unit))))))))

(define (core-union-mut-move)
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (value let ,mut-union-type)
            (UnionInject ,mut-union-type ,core-mut-borrow (BorrowMut x))
         (Let (moved let (Owned Int)) (Move x)
           (UnionEliminate value
            ((,core-mut-borrow borrowed -> unit)
              (String text -> unit))))))))

(define (core-option-branch-merge-read)
  (define option-body
    `(Let (option let (Option ,core-borrow))
          (Eliminate flag
            ((true () ->
               (Construct (Option ,core-borrow) some (Borrow x)))
             (false () ->
               (Construct (Option ,core-borrow) some (Borrow y)))))
       (Eliminate option
         ((none () -> 0) (some (value) -> (Read value))))))
  (define flag-body
    `(Let (flag let Bool) (Construct Bool true) ,option-body))
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Scope ()
         (Let (y let (Owned Int)) 2 ,flag-body)))))

(define (core-option-branch-merge-escape)
  (define option-branch
    `(Eliminate flag
       ((true () ->
          (Construct (Option ,core-borrow) some (Borrow x)))
        (false () ->
          (Construct (Option ,core-borrow) some (Borrow y))))))
  (define flag-let `(Let (flag let Bool) (Construct Bool true) ,option-branch))
  (define scoped-option `(Scope () (Let (y let (Owned Int)) 2 ,flag-let)))
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (option let (Option ,core-borrow)) ,scoped-option
         (Eliminate option
           ((none () -> 0) (some (value) -> (Read value))))))))

(define (ucore-option-branch-merge-read)
  (define branch-value
    `(Eliminate flag
        ((true () -> (Construct some (Types ,ucore-borrow) (Borrow x)))
        (false () -> (Construct some (Types ,ucore-borrow) (Borrow y))))))
  (define flag-let `(Let (flag let Bool) (Construct true (Types)) ,branch-value))
  (define option-let
    `(Let (option let (Option ,ucore-borrow)) ,flag-let
       (Eliminate option
         ((none () -> 0) (some (value) -> (Read value))))))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Int (Own)
     (LexicalScope
       (Let (x let (Owned Int)) (Move p)
         (LexicalScope (Let (y let (Owned Int)) (Move q) ,option-let))))))

(define (ucore-option-branch-merge-escape)
  (define branch-value
    `(Eliminate flag
       ((true () -> (Construct some (Types ,ucore-borrow) (Borrow x)))
        (false () -> (Construct some (Types ,ucore-borrow) (Borrow y))))))
  (define flag-let `(Let (flag let Bool) (Construct true (Types)) ,branch-value))
  (define scoped-value
    `(LexicalScope (Let (y let (Owned Int)) (Move q) ,flag-let)))
  (define option-let
    `(Let (option let (Option ,ucore-borrow)) ,scoped-value
       (Eliminate option
         ((none () -> 0) (some (value) -> (Read value))))))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Int (Own)
     (LexicalScope (Let (x let (Owned Int)) (Move p) ,option-let))))

(define (core-borrowed-union-read)
  '(Scope (1)
     (UnionEliminate (Borrow 1)
       ((Int value -> (Read value)) (String text -> 0)))))

(define (core-borrowed-union-move)
  '(Scope (1)
     (UnionEliminate (Borrow 1)
       ((Int value ->
          (Let (moved let (Owned (Union Int String))) (Move 1) unit))
        (String text -> unit)))))

(test-case "Option Core の Construct は借用の escape を E-BOR-004 で拒否する"
  (check-rejected (core-type (core-option-escape)) "E-BOR-004"))

(test-case "Option Core の Construct payload は some で読める"
  (check-accepted (core-type (core-option-read))))

(test-case "Option Core の可変借用 payload の生存中は owner を Move できない"
  (check-rejected (core-type (core-option-mut-move)) "E-BOR-008"))

(test-case "BorrowBox Core の Construct は借用の escape を E-BOR-004 で拒否する"
  (check-rejected (core-type (core-box-escape)) "E-BOR-004"))

(test-case "BorrowBox Core の Construct payload は読める"
  (check-accepted (core-type (core-box-read))))

(test-case "List cons は空の tail の Omitted を無視して head の借用を読める"
  (check-accepted (core-type (core-list-read))))

(test-case "BorrowBox Core の可変借用 payload の生存中は owner を Move できない"
  (check-rejected (core-type (core-box-mut-move)) "E-BOR-008"))

(test-case "UnionInject Core は借用 member の escape を E-BOR-004 で拒否する"
  (check-rejected (core-type (core-union-escape)) "E-BOR-004"))

(test-case "UnionInject Core は選んだ borrow member を読める"
  (check-accepted (core-type (core-union-read))))

(test-case "UnionInject Core の可変借用 member の生存中は owner を Move できない"
  (check-rejected (core-type (core-union-mut-move)) "E-BOR-008"))

(test-case "Option payload の Eliminate 合流は両 owner の scope 内で読める"
  (check-accepted (core-type (core-option-branch-merge-read))))

(test-case "Option payload の Eliminate 合流は短い owner の外へ escape しない"
  (check-rejected (core-type (core-option-branch-merge-escape)) "E-BOR-004"))

(test-case "Option UCore の Eliminate 合流は両 owner の scope 内で読める"
  (check-accepted (elaborated-type (ucore-option-branch-merge-read))))

(test-case "Option UCore の Eliminate 合流は短い owner の外へ escape しない"
  (check-rejected (elaborated-type (ucore-option-branch-merge-escape)) "E-BOR-004"))

(test-case "借用 UnionEliminate の member を読め、owner Move は E-BOR-008"
  (define places '((1 (Union Int String))))
  (check-accepted (core-type/places (core-borrowed-union-read) places))
  (check-rejected (core-type/places (core-borrowed-union-move) places)
                  "E-BOR-008"))

(test-case "Option UCore の注釈付き Construct は escape を拒否し payload を読める"
  (check-rejected (elaborated-type (ucore-option-escape)) "E-BOR-004")
  (check-accepted (elaborated-type (ucore-option-read)))
  (check-rejected (elaborated-type (ucore-option-mut-move)) "E-BOR-008"))

(test-case "BorrowBox UCore の注釈付き Construct は escape を拒否し payload を読める"
  (check-rejected (elaborated-type (ucore-box-escape)) "E-BOR-004")
  (check-accepted (elaborated-type (ucore-box-read)))
  (check-rejected (elaborated-type (ucore-box-mut-move)) "E-BOR-008"))

(test-case "List cons UCore は空の tail の Omitted を無視して head の借用を読める"
  (check-accepted (elaborated-type (ucore-list-read))))

(test-case "UnionInject UCore の注釈付き let は escape を拒否し member を読める"
  (check-rejected (elaborated-type (ucore-union-escape)) "E-BOR-004")
  (check-accepted (elaborated-type (ucore-union-read)))
  (check-rejected (elaborated-type (ucore-union-mut-move)) "E-BOR-008"))

(define (core-pair-read)
  (define type (pair-type core-borrow))
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Scope ()
         (Let (y let (Owned Int)) 2
           (Let (pair let ,type)
                (Construct ,type pair (Borrow x) (Borrow y))
             (Eliminate pair
               ((pair (left right)
                  -> (Let (read-left let Int) (Read left) (Read right)))))))))))

(define (core-pair-escape)
  (define type (pair-type core-borrow))
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (pair let ,type)
            (Scope ()
              (Let (y let (Owned Int)) 2
                (Construct ,type pair (Borrow x) (Borrow y))))
         (Eliminate pair ((pair (left right) -> (Read left))))))))

(define (ucore-pair-read)
  (define type `(Data BorrowPair (,ucore-borrow)))
  (define branches
    (list (list 'pair '(left right) '->
                '(Let (read-left let Int) (Read left) (Read right)))))
  (define elimination `(Eliminate pair ,branches))
  (define construction
    `(Construct pair (Types ,ucore-borrow) (Borrow x) (Borrow y)))
  (define pair-let `(Let (pair let ,type) ,construction ,elimination))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Int (Own)
     (LexicalScope
       (Let (x let (Owned Int)) (Move p)
         (LexicalScope
           (Let (y let (Owned Int)) (Move q) ,pair-let))))))

(define (ucore-pair-escape)
  (define type `(Data BorrowPair (,ucore-borrow)))
  (define construct
    `(Construct pair (Types ,ucore-borrow) (Borrow x) (Borrow y)))
  (define y-let `(Let (y let (Owned Int)) (Move q) ,construct))
  (define inner `(LexicalScope ,y-let))
  (define elimination
    '(Eliminate pair ((pair (left right) -> (Read left)))))
  (define pair-let `(Let (pair let ,type) ,inner ,elimination))
  (define x-let `(Let (x let (Owned Int)) (Move p) ,pair-let))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Int (Own)
     (LexicalScope ,x-let)))

(define (ucore-mut-pair-mismatch)
  (define type `(Data MutablePair (,ucore-mut-borrow)))
  (define construct
    `(Construct mpair (Types ,ucore-mut-borrow) bx (BorrowMut y)))
  (define y-let
    `(Let (y let (Owned Int)) (Move q)
       (Let (pair let ,type) ,construct unit)))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Unit (Own)
     (LexicalScope
       (Let (x let (Owned Int)) (Move p)
         (Let (bx let ,ucore-mut-borrow) (BorrowMut x)
           (LexicalScope ,y-let))))))

(define (core-mut-pair-read)
  (define type (mutable-pair-type core-mut-borrow))
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Scope ()
         (Let (y let (Owned Int)) 2
           (Let (pair let ,type)
                (Construct ,type mpair (BorrowMut x) (BorrowMut y))
             (Eliminate pair
               ((mpair (left right)
                  -> (Let (read-left let Int) (Read left) (Read right)))))))))))

(define (core-mut-pair-escape)
  (define type (mutable-pair-type core-mut-borrow))
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Let (pair let ,type)
            (Scope ()
              (Let (y let (Owned Int)) 2
                (Construct ,type mpair (BorrowMut x) (BorrowMut y))))
         (Eliminate pair ((mpair (left right) -> (Read left))))))))

(define (core-mut-pair-move owner)
  (define type (mutable-pair-type core-mut-borrow))
  `(Scope ()
     (Let (x let (Owned Int)) 1
       (Scope ()
         (Let (y let (Owned Int)) 2
           (Let (pair let ,type)
                (Construct ,type mpair (BorrowMut x) (BorrowMut y))
             (Let (moved let (Owned Int)) (Move ,owner)
               (Eliminate pair ((mpair (_left _right) -> unit))))))))))

(define (ucore-mut-pair-read)
  (define type `(Data MutablePair (,ucore-mut-borrow)))
  (define branches
    '((mpair (left right)
       -> (Let (read-left let Int) (Read left) (Read right)))))
  (define construction
    `(Construct mpair (Types ,ucore-mut-borrow)
                (BorrowMut x) (BorrowMut y)))
  (define pair-let `(Let (pair let ,type) ,construction
                         (Eliminate pair ,branches)))
  (define y-let `(Let (y let (Owned Int)) (Move q) ,pair-let))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Int (Own)
     (LexicalScope
       (Let (x let (Owned Int)) (Move p)
         (LexicalScope ,y-let)))))

(define (ucore-mut-pair-escape)
  (define type `(Data MutablePair (,ucore-mut-borrow)))
  (define construction
    `(Construct mpair (Types ,ucore-mut-borrow)
                (BorrowMut x) (BorrowMut y)))
  (define y-scope
    `(LexicalScope (Let (y let (Owned Int)) (Move q) ,construction)))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Int (Own)
     (LexicalScope
       (Let (x let (Owned Int)) (Move p)
         (Let (pair let ,type) ,y-scope
           (Eliminate pair ((mpair (left right) -> (Read left)))))))))

(define (ucore-mut-pair-move owner)
  (define type `(Data MutablePair (,ucore-mut-borrow)))
  (define construction
    `(Construct mpair (Types ,ucore-mut-borrow)
                (BorrowMut x) (BorrowMut y)))
  (define eliminate
    '(Eliminate pair ((mpair (_left _right) -> unit))))
  (define pair-let
    `(Let (pair let ,type) ,construction
       (Let (moved let (Owned Int)) (Move ,owner) ,eliminate)))
  (define y-let `(Let (y let (Owned Int)) (Move q) ,pair-let))
  `(Fn ((p (Owned Int)) (q (Owned Int))) Unit (Own)
     (LexicalScope
       (Let (x let (Owned Int)) (Move p)
         (LexicalScope ,y-let)))))

(define (core-borrowpair-with-rparams)
  (define type `(Data BorrowPair (,core-borrow)))
  (define signature
    `(ForallRegion (r1 r2)
       (NFn ((Borrowed Int (RParam r1))
             (Borrowed Int (RParam r2)))
            (Data BorrowPair ((Borrowed Int (RParam r1))))
            () () () User)))
  (core-type
   `(RegionLam (r1 r2)
      (Lam User borrow-pair (p q) (Construct ,type pair p q)))
   `((borrow-pair ,signature))))

(define (core-borrowpair-with-rparam-and-local)
  (define type `(Data BorrowPair (,core-borrow)))
  (define signature
    `(ForallRegion (r)
       (NFn ((Borrowed Int (RParam r)))
            (Data BorrowPair ((Borrowed Int (RParam r))))
            () (Own) () User)))
  (core-type
   `(RegionLam (r)
      (Lam User borrow-pair (p)
        (Let (x let (Owned Int)) 1
          (Construct ,type pair p (Borrow x)))))
   `((borrow-pair ,signature))))

(define (core-invariant-borrowedmut-pair)
  (define type `(Data MutableInvariantPair (,core-mut-borrow)))
  (core-type/env
   `(Construct ,type mutable-invariant-pair p q)
   `((p (ForallRegion (out1)
          (BorrowedMut (Borrowed Int (RParam r1)) (RParam out1))))
     (q (ForallRegion (out2)
          (BorrowedMut (Borrowed Int (RParam r2)) (RParam out2)))))
   '(r1 r2)))

(test-case "BorrowPair Core は同じ型引数の欄を読めて短い owner の外へ逃がさない"
  (check-accepted (core-type (core-pair-read)))
  (check-rejected (core-type (core-pair-escape)) "E-BOR-004"))

(test-case "BorrowPair UCore は同じ型引数の欄を読めて短い owner の外へ逃がさない"
  (check-accepted (elaborated-type (ucore-pair-read)))
  (check-rejected (elaborated-type (ucore-pair-escape)) "E-BOR-004"))

(test-case "BorrowPair は異なる RParam の借用を E-TYP-023 で閉じる"
  (check-rejected (core-borrowpair-with-rparams) "E-TYP-023"))

(test-case "BorrowPair は RParam と局所借用の混在を E-TYP-023 で閉じる"
  (check-rejected (core-borrowpair-with-rparam-and-local) "E-TYP-023"))

(test-case "MutableInvariantPair は BorrowedMut の被型位置の型引数の寿命を揃える"
  (check-rejected (core-invariant-borrowedmut-pair) "E-TYP-023"))

(test-case "MutablePair Core は異なる寿命の可変借用を合流して読める"
  (check-accepted (core-type (core-mut-pair-read))))

(test-case "MutablePair Core は短い owner の外へ escape せず E-BOR-004 になる"
  (check-rejected (core-type (core-mut-pair-escape)) "E-BOR-004"))

(test-case "MutablePair Core が生存中は左右の owner を Move できない"
  (check-rejected (core-type (core-mut-pair-move 'x)) "E-BOR-008")
  (check-rejected (core-type (core-mut-pair-move 'y)) "E-BOR-008"))

(test-case "MutablePair UCore は異なる寿命の可変借用を合流して読める"
  (check-accepted (elaborated-type (ucore-mut-pair-read))))

(test-case "MutablePair UCore は短い owner の外へ escape せず E-BOR-004 になる"
  (check-rejected (elaborated-type (ucore-mut-pair-escape)) "E-BOR-004"))

(test-case "MutablePair UCore が生存中は左右の owner を Move できない"
  (check-rejected (elaborated-type (ucore-mut-pair-move 'x)) "E-BOR-008")
  (check-rejected (elaborated-type (ucore-mut-pair-move 'y)) "E-BOR-008"))

(test-case "Construct は同じ RParam の payload 寿命を保って読む"
  (define callables
    '((make-box (ForallRegion (r)
                  (NFn ((Borrowed Int (RParam r))) Int () () () User)))))
  (define core
    `(Scope ()
       (RegionLam (r)
         (Lam User make-box (p)
           (Let (box let ,(box-type core-borrow))
                (Construct ,(box-type core-borrow) box p)
             (Eliminate box ((box (value) -> (Read value)))))))))
  (check-accepted (core-type core callables)))

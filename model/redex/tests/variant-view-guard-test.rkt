#lang racket

(require rackunit
         racket/list
         racket/match
         "../borrow-gen.rkt"
         "../diagnostic.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../region.rkt"
         "../traits.rkt"
         "../typing.rkt")

(define option-int '(Option Int))
(define option-borrowed-mut '(BorrowedMut (Option Int) (RParam %omitted)))
(define integer-borrowed-mut '(BorrowedMut Int (RParam %omitted)))
(define union-int-string '(Union Int String))
(define union-borrowed-mut
  `(BorrowedMut ,union-int-string (RParam %omitted)))
(define borrowed-mut-int-rvar0 '(BorrowedMut Int (RVar 0)))
(define option-borrowed-mut-rvar0
  `(BorrowedMut ,option-int (RVar 0)))
(define option-borrowed-mut-int
  `(Option ,borrowed-mut-int-rvar0))

(define data-ledger
  (make-trait-ledger canonical-trait-env
                     #:data '((GuardCell (A) ((guard-cell ((Param A))))))
                     #:fail (lambda args (error 'test "unexpected ledger failure: ~s" args))))

(define (typed core [callables #f])
  (if callables
      (let* ([ir (build-region-ir core)]
             [owner-rho
              (region->rho ir (owner-let-body-region ir '()))]
             [filled
              (let replace ([term (fill-region-placeholders core ir)])
                (cond
                  [(eq? term 'owner-ph) owner-rho]
                  [(pair? term)
                   (cons (replace (car term)) (replace (cdr term)))]
                  [else term]))])
        (core-type-of/regions filled '() callables #:ir ir))
      (core-type-of/regions core '() '())))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 200])
    (when (zero? fuel) (error 'trace-g2 "fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (check-rejected core expected-id [callables #f])
  (define result (typed core callables))
  (check-true (diagnostic? result) (format "拒否を期待、実測: ~s" result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)))

(define (check-trace core expected-type [callables '()])
  (define result (typed core (and (pair? callables) callables)))
  (check-true (region-typed? result) (format "受理を期待、実測: ~s" result))
  (when (region-typed? result)
    (check-equal? (region-typed-type result) expected-type)
    (define configs
      (trace-g2 (inject-g2m (erase-core (region-execution-core result)))))
    (for ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config callables expected-type))
      (check-not-false row (format "config ~a に runtime-row がある" index))
      (when row
        (check-true (config-ok? config callables expected-type row)
                    (format "config ~a が config-ok? を通る" index))))
    (check-true (null? (raw-steps-g2/named (last configs)))
                "trace が終端まで進む")))

(define (option-case child-use result-type)
  `(Let (owner let (Owned ,option-int))
        (Construct ,option-int some 1)
     (Let (p let ,option-borrowed-mut) (BorrowMut owner)
       (Eliminate p
         ((some (child) ->
            (Let (changed let Unit) (Assign p (Construct ,option-int none))
              ,child-use))
          (none () -> ,(if (eq? result-type 'Unit) 'unit 0)))))))

(define (union-case child-use result-type)
  `(Let (owner let (Owned ,union-int-string))
        (UnionInject ,union-int-string Int 1)
     (Let (p let ,union-borrowed-mut) (BorrowMut owner)
       (UnionEliminate p
         ((Int child ->
            (Let (changed let Unit)
                 (Assign p (UnionInject ,union-int-string String "s"))
              ,child-use))
          (String other -> ,(if (eq? result-type 'Unit) 'unit 0)))))))

(define option-assign-core (option-case '(Assign child 2) 'Unit))
(define option-read-core (option-case '(Read child) 'Int))
(define union-assign-core (union-case '(Assign child 2) 'Unit))
(define union-read-core (union-case '(Read child) 'Int))

(define stored-borrow-union-type
  `(Union ,option-borrowed-mut String))
(define stored-borrow-core
  `(Let (owner let (Owned ,option-int))
        (Construct ,option-int some 1)
     (Let (p let ,option-borrowed-mut) (BorrowMut owner)
       (Let (box let ,stored-borrow-union-type)
            (UnionInject ,stored-borrow-union-type ,option-borrowed-mut p)
         (UnionEliminate box
           ((,option-borrowed-mut inner ->
              (Eliminate inner
                ((some (child) ->
                   (Let (changed let Unit)
                        (Assign inner (Construct ,option-int none))
                     (Read child)))
                 (none () -> 0))))
            (String text -> 0)))))))

(define nested-union-record
  '(Record ((value (Union Int String) mut))))
(define nested-union-type '(Union Int String))
(define nested-union-direct-core
  `(Let (owner let (Owned ,nested-union-record))
        (Rec ((value mut (UnionInject ,nested-union-type Int 1))))
     (Let (p let (BorrowedMut ,nested-union-record (RParam %omitted)))
          (BorrowMut owner)
       (Let (u let ,union-borrowed-mut) (ProjBorrow p value)
         (UnionEliminate u
           ((Int child ->
              (Let (changed let Unit)
                   (Assign u (UnionInject ,nested-union-type String "s"))
                (Read child)))
            (String other -> 0)))))))

(define (option-after-branch)
  `(Let (owner let (Owned ,option-int))
        (Construct ,option-int some 1)
     (Let (p let ,option-borrowed-mut) (BorrowMut owner)
       (Let (observed let Int)
            (Eliminate p
              ((some (child) -> (Read child))
               (none () -> 0)))
         (Assign p (Construct ,option-int none))))))

(define record-two-int
  '(Record ((left Int mut) (right Int mut))))
(define record-p7-core
  `(Let (owner let (Owned ,record-two-int))
        (Rec ((left mut 1) (right mut 2)))
     (Let (p let (BorrowedMut ,record-two-int (RParam %omitted)))
          (BorrowMut owner)
       (Let (child let ,integer-borrowed-mut) (ProjBorrow p left)
         (Let (changed let Unit)
              (Assign p (Rec ((left mut 3) (right mut 4))))
           (Read child))))))

(define one-cell-type '(Data GuardCell (Int)))
(define one-cell-core
  `(Let (owner let (Owned ,one-cell-type))
        (Construct ,one-cell-type guard-cell 1)
     (Let (p let (BorrowedMut ,one-cell-type (RParam %omitted)))
          (BorrowMut owner)
       (Eliminate p
         ((guard-cell (child) ->
            (Let (changed let Unit)
                 (Assign p (Construct ,one-cell-type guard-cell 2))
              (Read child))))))))

(define unrelated-field-core
  `(Let (owner let (Owned ,record-two-int))
        (Rec ((left mut 1) (right mut 2)))
     (Let (p let (BorrowedMut ,record-two-int (RParam %omitted)))
          (BorrowMut owner)
       (Let (child let ,integer-borrowed-mut) (ProjBorrow p left)
         (Let (changed let Unit)
              (Assign (ProjBorrow p right) 3)
           (Read child))))))

(define child-self-assign-core
  `(Let (owner let (Owned ,union-int-string))
        (UnionInject ,union-int-string Int 1)
     (Let (p let ,union-borrowed-mut) (BorrowMut owner)
       (UnionEliminate p
         ((Int child -> (Assign child 2))
          (String other -> unit))))))

(define parent-alias-core
  `(Let (owner let (Owned ,option-int))
        (Construct ,option-int some 1)
     (Let (p let ,option-borrowed-mut) (BorrowMut owner)
       (Let (alias let ,option-borrowed-mut) p
         (Eliminate p
           ((some (child) ->
              (Let (changed let Unit)
                   (Assign alias (Construct ,option-int none))
                (Read child)))
            (none () -> 0)))))))

(define record-child-let-core
  `(Let (owner let (Owned ,option-int))
        (Construct ,option-int some 1)
     (Let (other let (Owned Int)) 8
       (Let (q let ,integer-borrowed-mut) (BorrowMut other)
         (Let (p let ,option-borrowed-mut) (BorrowMut owner)
           (Eliminate p
             ((some (child) ->
                (Let (views let (Record ((inner ,integer-borrowed-mut imm))))
                     (Rec ((inner imm child)))
                  (Let (changed let Unit)
                       (Assign p (Construct ,option-int none))
                    (Read (Proj views inner)))))
              (none () -> 0))))))))

(define branch-result-child-core
  `(Let (owner let (Owned ,option-int))
        (Construct ,option-int some 1)
     (Let (other let (Owned Int)) 8
       (Let (q let ,integer-borrowed-mut) (BorrowMut other)
         (Let (p let ,option-borrowed-mut) (BorrowMut owner)
           (Let (view let ,integer-borrowed-mut)
                (Eliminate p
                  ((some (child) -> child)
                   (none () -> q)))
             (Let (changed let Unit)
                  (Assign p (Construct ,option-int none))
               (Read view))))))))

(define suspend-child-core
  `(Let (owner let (Owned ,option-int))
        (Construct ,option-int some 1)
     (Let (p let ,option-borrowed-mut) (BorrowMut owner)
       (Eliminate p
         ((some (child) ->
            (Let (suspended let ,integer-borrowed-mut) (Suspend child)
              (Let (changed let Unit)
                   (Assign p (Construct ,option-int none))
                (Read suspended))))
          (none () -> 0))))))

(define union-record-type
  `(Record ((value ,union-int-string mut))))
(define union-record-value
  `(Rec ((value mut (UnionInject ,union-int-string Int 1)))))
(define borrowed-mut-union '(BorrowedMut (Union Int String) ph))

(define replace-union-callables
  `((replace-union
     (ForallRegion (a)
       (NFn ((BorrowedMut ,union-int-string (RParam a)))
            Unit () (Mutation) () User)))
    (keep-union
     (ForallRegion (a)
       (NFn ((BorrowedMut ,union-int-string (RParam a)))
            Unit () () () User)))))

(define (replace-union-lambda writing?)
  `(RegionApp
    (RegionLam (a)
      (Lam User ,(if writing? 'replace-union 'keep-union) (target)
        ,(if writing?
             `(Assign target
                      (UnionInject ,union-int-string String "s"))
             'unit)))
    (owner-ph)))

(define (function-call-variant-core writing?)
  `(Let (owner let (Owned ,union-record-type)) ,union-record-value
     (Let (p let (BorrowedMut ,union-record-type ph)) (BorrowMut owner)
       (Let (u let ,borrowed-mut-union) (ProjBorrow p value)
         (UnionEliminate u
           ((Int b ->
              (Let (called let Unit)
                   (Apply ,(replace-union-lambda writing?) u)
                (Let (observed const Int) (Read b) unit)))
            (String other -> unit)))))))

(define (function-body-variant-core writing?)
  `(Let (owner let (Owned ,option-int)) (Construct ,option-int some 1)
     (Apply
      (RegionApp
       (RegionLam (a)
         (Lam User rewrite-option (p)
           (Eliminate p
             ((some (child) ->
                (Let (observed const Int) (Read child)
                  ,(if writing?
                       `(Assign p (Construct ,option-int none))
                       'unit)))
              (none () -> unit)))))
       (owner-ph))
      (BorrowMut owner))))

(define option-rewrite-callables
  `((rewrite-option
    (ForallRegion (a)
      (NFn ((BorrowedMut ,option-int (RParam a)))
            Unit () (Mutation) () User)))))

(define (return-payload-core writing?)
  `(Let (owner let (Owned ,option-int)) (Construct ,option-int some 1)
     (Let (other let (Owned Int)) 8
       (Let (fallback let ,borrowed-mut-int-rvar0) (BorrowMut other)
         (Let (p let ,option-borrowed-mut-rvar0) (BorrowMut owner)
           (Let (result let ,borrowed-mut-int-rvar0)
                (Handle (Return boundary ,borrowed-mut-int-rvar0)
                  (returned ->
                    (Let (changed let Unit)
                         ,(if writing?
                              `(Assign p (Construct ,option-int none))
                              'unit)
                      returned))
                  (Eliminate p
                    ((some (child) ->
                       (Perform (Return boundary ,borrowed-mut-int-rvar0)
                                child))
                     (none () ->
                       (Perform (Return boundary ,borrowed-mut-int-rvar0)
                                fallback)))))
             (Read result)))))))

(define (leave-payload-core writing?)
  ;; Leave は Core で Return<Option τ> の payload に some を包む。
  `(Let (owner let (Owned ,option-int)) (Construct ,option-int some 1)
     (Let (other let (Owned Int)) 8
       (Let (fallback let ,borrowed-mut-int-rvar0) (BorrowMut other)
         (Let (p let ,option-borrowed-mut-rvar0) (BorrowMut owner)
           (Let (result let ,option-borrowed-mut-int)
                (Handle (Return boundary ,option-borrowed-mut-int)
                  (returned ->
                    (Eliminate returned
                      ((some (captured) ->
                         (Let (changed let Unit)
                              ,(if writing?
                                   `(Assign p (Construct ,option-int none))
                                   'unit)
                           returned))
                       (none () -> returned))))
                  (Eliminate p
                    ((some (child) ->
                       (Perform
                        (Return boundary ,option-borrowed-mut-int)
                        (Construct ,option-borrowed-mut-int some child)))
                     (none () ->
                       (Perform
                        (Return boundary ,option-borrowed-mut-int)
                        (Construct ,option-borrowed-mut-int some fallback))))))
             (Eliminate result
               ((some (value) -> (Read value))
                (none () -> 0)))))))))

(define record-payload-type '(Record ((field Int mut))))
(define option-record-type `(Option ,record-payload-type))
(define option-record-owner
  `(Construct ,option-record-type some (Rec ((field mut 1)))))

(define (record-grandchild-core action)
  `(Let (owner let (Owned ,option-record-type)) ,option-record-owner
     (Let (p let (BorrowedMut ,option-record-type (RVar 0)))
          (BorrowMut owner)
       (Eliminate p
         ((some (child) ->
            (Let (grandchild let (BorrowedMut Int (RVar 0)))
                 (ProjBorrow child field)
              (Let (changed let Unit)
                   ,(case action
                      [(parent-variant)
                       `(Assign p (Construct ,option-record-type none))]
                      [(child-same-shape)
                       `(Assign child (Rec ((field mut 2))))]
                      [else 'unit])
                (Read grandchild))))
          (none () -> 0))))))

(test-case "Some の欄の子が生きる間に None を書くと E-BOR-025"
  (check-rejected option-assign-core "E-BOR-025")
  (check-rejected option-read-core "E-BOR-025"))

(test-case "Union payload の子が生きる間に member を替えると E-BOR-025"
  (check-rejected union-assign-core "E-BOR-025")
  (check-rejected union-read-core "E-BOR-025"))

(test-case "Union の by-value payload から得た借用 view に variant 印を保つ"
  (check-rejected stored-borrow-core "E-BOR-025"))

(test-case "Union を含む欄の孫が生きる間に欄の variant を替えると E-BOR-025"
  (check-rejected nested-union-direct-core "E-BOR-025"))

(test-case "分岐結果の子を束縛した後に親の variant を替えると E-BOR-025"
  (check-rejected branch-result-child-core "E-BOR-025"))

(test-case "親の alias を通して variant を替えると E-BOR-025"
  (check-rejected parent-alias-core "E-BOR-025"))

(test-case "record の欄へ入れた子が生きる間に親の variant を替えると E-BOR-025"
  (check-rejected record-child-let-core "E-BOR-025"))

(test-case "Suspend 後も子の variant 印を保って E-BOR-025"
  (check-rejected suspend-child-core "E-BOR-025"))

(test-case "Some の枝を出た後の親更新は受理される"
  (check-trace (option-after-branch) 'Unit))

(test-case "形の変わらない record でも子が生きている間の親更新を拒む"
  (check-rejected record-p7-core "E-BOR-025"))

(test-case "一構成子 data の child が生きる間の親更新も E-BOR-025"
  (call-with-trait-ledger data-ledger
    (lambda () (check-rejected one-cell-core "E-BOR-025"))))

(test-case "子と重ならない record 欄への書込みは受理される"
  (check-trace unrelated-field-core 'Int))

(test-case "可変借用の子自身への Assign は受理される"
  (check-trace child-self-assign-core 'Unit))

(test-case "Apply へ移した親の variant 書換えも生きた孫との衝突で E-BOR-025"
  (check-rejected (function-call-variant-core #t) "E-BOR-025"
                  replace-union-callables)
  (check-trace (function-call-variant-core #f) 'Unit
               replace-union-callables))

(test-case "関数本体で variant に依存する子が生きる間の親書換えを E-BOR-025"
  (check-rejected (function-body-variant-core #t) "E-BOR-025"
                  option-rewrite-callables)
  (check-trace (function-body-variant-core #f) 'Unit
               option-rewrite-callables))

(test-case "Perform Return payload の handler 子が生きる間の親書換えを E-BOR-025"
  (check-rejected (return-payload-core #t) "E-BOR-025")
  (check-trace (return-payload-core #f) 'Int))

(test-case "Leave の Option adapter payload の handler 子が生きる間の親書換えを E-BOR-025"
  (check-rejected (leave-payload-core #t) "E-BOR-025")
  (check-trace (leave-payload-core #f) 'Int))

(test-case "record payload の孫が生きる間は同じ形の子 Assign も拒む"
  (check-rejected (record-grandchild-core 'child-same-shape) "E-BOR-025"))

(test-case "record payload の孫について親を通す variant 書換えだけ E-BOR-025"
  (check-rejected (record-grandchild-core 'parent-variant) "E-BOR-025")
  (check-trace (record-grandchild-core 'read-only) 'Int))

#lang racket

(require rackunit racket/match
         "../annotate.rkt" "../borrow.rkt" "../erase.rkt"
         "../typing.rkt" "../region.rkt")

(define named '(Record ((name String imm))))
(define with-id '(Record ((id Int imm) (name String imm))))
(define name-int '(Record ((name Int imm))))
(define with-active '(Record ((active Int imm) (name String imm))))
(define with-other '(Record ((name String imm) (other Int imm))))
(define with-borrowed
  '(Record ((borrowed (Borrowed Int 0) imm opt) (name String imm))))
(define union-type '(Union Int String))

(define initial-record '(Rec ((name imm "A") (id imm 1))))
(define active-record '(Rec ((name imm "B") (active imm 2))))
(define other-record '(Rec ((name imm "C") (other imm 3))))

(define (result core [callables '()] [environment '()])
  (type-of/raw core '() callables environment (empty-region-ctx)))

(define (type-row core [callables '()] [environment '()])
  (match (result core callables environment)
    [(list 'ok value) value]
    [other other]))

(define (key-of core [callables '()] [environment '()])
  (match (result core callables environment)
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (reassign-to target type value)
  `(Reassign ,target ,type ,value))

(test-case "mut read observes the current record shape"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Let (ignored const Unit)
         ,(reassign-to 'x with-active active-record)
         (Proj x active))))
  (check-equal? (type-row core) '(Int (Mutation)))
  (check-equal?
   (key-of `(Let (x mut ,named) ,initial-record
              (Let (ignored const Unit)
                ,(reassign-to 'x with-active active-record)
                (Proj x id))))
   'unknown-record-label))

(test-case "Reassign checks current shape, declared upper bound, resources and pin"
  (check-equal?
   (key-of `(Let (x mut ,named) ,initial-record
              ,(reassign-to 'x with-active '(Rec ((name imm "B"))))))
   'reassign-type-mismatch)
  (check-equal?
   (key-of `(Let (x mut ,named) ,initial-record
              ,(reassign-to 'x name-int '(Rec ((name imm 1))))))
   'reassign-type-mismatch)
  (check-equal?
   (key-of `(Let (x mut ,named) ,initial-record
              ,(reassign-to 'x
                            '(Record ((bad (Owned Int) imm opt)
                                      (name String imm)))
                            '(Rec ((bad imm (Absent (Owned Int)))
                                   (name imm "B")))))
   '() '())
   'mut-binding-unsupported-type)
  (check-equal?
   (key-of `(Let (x mut ,named) ,initial-record
              ,(reassign-to 'x with-borrowed
                            '(Rec ((borrowed imm (Absent (Borrowed Int 0)))
                                   (name imm "B")))))
           '() '())
   'mut-binding-unsupported-type)
  (define closure-type '(NFn () Int () () () User))
  (define capture
    `(Let (x mut ,named) ,initial-record
       (Let (f const ,closure-type)
         (Lam User f () (Proj x id))
         (Let (ignored const Unit)
           ,(reassign-to 'x with-active active-record)
           0))))
  (check-equal? (key-of capture `((f ,closure-type)))
                'reassign-type-mismatch))

(test-case "flow branch join uses only live branch exits"
  (define (eliminate scrutinee left-type left-value right-type right-value)
    `(Let (x mut ,named) ,initial-record
       (Let (choice const Int)
         (Eliminate ,scrutinee
           ((true () -> (Let (ignored const Unit)
                          ,(reassign-to 'x left-type left-value)
                          0))
            (false () -> (Let (ignored const Unit)
                           ,(reassign-to 'x right-type right-value)
                           0))))
         (Proj x active))))
  (for ([scrutinee (in-list '(b (Apply g)))])
    (define env
      (if (eq? scrutinee 'b)
          '((b Bool))
          '((g (NFn () Bool () () () User)))))
    (check-equal?
     (type-row (eliminate scrutinee with-active active-record
                          with-active active-record)
               '() env)
     '(Int (Mutation)))
    (check-equal?
     (key-of (eliminate scrutinee with-active active-record
                        with-other other-record)
             '() env)
     'reassign-type-mismatch)
    (check-equal?
     (key-of
      `(Let (x mut ,named) ,initial-record
         (Let (choice const Int)
           (Eliminate ,scrutinee
             ((true () -> (Let (ignored const Unit)
                            ,(reassign-to 'x with-other other-record)
                            (Perform (Return outer Int) 1)))
              (false () -> (Let (ignored const Unit)
                             ,(reassign-to 'x with-active active-record)
                             0))))
           (Proj x active)))
      '() env)
     'ok)))

(test-case "one-sided closure capture pins after branch join"
  (define closure-type '(NFn () Int () () () User))
  (define core
    `(Let (x mut ,named) ,initial-record
       (Let (ignored const Unit)
         (Eliminate b
           ((true () -> (Let (f const ,closure-type)
                          (Lam User f () (Proj x id))
                          unit))
            (false () -> unit)))
         (Let (ignored2 const Unit)
           ,(reassign-to 'x with-active active-record)
           0))))
  (check-equal? (key-of core `((f ,closure-type)) '((b Bool)))
                'reassign-type-mismatch))

(test-case "RecurVal captures and pins mut slots"
  (define function-type '(NFn () Int () () () User))
  (define core
    `(Let (x mut ,named) ,initial-record
       (Let (f const ,function-type)
         (RecurVal recur-id f () (Proj x id))
         (Let (ignored const Unit)
           ,(reassign-to 'x with-active active-record)
           0))))
  (check-equal? (key-of core `((recur-id ,function-type)))
                'reassign-type-mismatch))

(test-case "a closure body also enforces its capture pin"
  (define function-type '(NFn () Unit () (Mutation) () User))
  (define core
    `(Let (x mut ,named) ,initial-record
       (Lam User f ()
         ,(reassign-to 'x with-active active-record))))
  (check-equal? (key-of core `((f ,function-type)))
                'reassign-type-mismatch))

(test-case "Let masks and restores shadowed mut flow, including bound effects"
  (define nested
    `(Let (x mut ,named) ,initial-record
       (Let (ignored const Int)
         (Let (x mut ,named) ,active-record
           (Let (inner const Unit)
             ,(reassign-to 'x with-other other-record)
             (Proj x other)))
         (Proj x id))))
  (check-equal? (type-row nested) '(Int (Mutation)))
  (define bound-reassigns-outer
    `(Let (x mut ,named) ,initial-record
       (Let (x mut ,with-active)
         (Let (updated const Unit)
           ,(reassign-to 'x with-active active-record)
           ,active-record)
         (Proj x active))))
  (check-equal? (type-row bound-reassigns-outer) '(Int (Mutation))))

(test-case "argument evaluation threads flow from earlier arguments"
  (define function-type '(NFn (Unit Int) Int () () () User))
  (define core
    `(Let (x mut ,named) ,initial-record
       (Apply f
              (Let (ignored const Unit)
                ,(reassign-to 'x with-active active-record)
                unit)
              (Proj x active))))
  (check-equal? (type-row core '() `((f ,function-type)))
                '(Int (Mutation))))

(test-case "UnionEliminate joins only its live branch exits for variable and call scrutinees"
  (define (union-when scrutinee)
    `(Let (x mut ,named) ,initial-record
       (Let (choice const Int)
         (UnionEliminate ,scrutinee
           ((Int n -> (Let (ignored const Unit)
                       ,(reassign-to 'x with-active active-record)
                       0))
            (String s -> (Let (ignored const Unit)
                           ,(reassign-to 'x with-active active-record)
                           0))))
         (Proj x active))))
  (for ([scrutinee (in-list '(u (Apply g)))])
    (define env
      (if (eq? scrutinee 'u)
          `((u ,union-type))
          `((g (NFn () ,union-type () () () User)))))
    (check-equal? (type-row (union-when scrutinee) '() env)
                  '(Int (Mutation)))
    (check-equal?
     (key-of
      `(Let (x mut ,named) ,initial-record
         (Let (choice const Int)
           (UnionEliminate ,scrutinee
             ((Int n -> (Let (ignored const Unit)
                         ,(reassign-to 'x with-other other-record)
                         0))
              (String s -> (Let (ignored const Unit)
                             ,(reassign-to 'x with-active active-record)
                             0))))
           (Proj x active)))
      '() env)
     'reassign-type-mismatch)))

(test-case "Never Reassign preserves the old flow and adds no Mutation"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Let (ignored const Unit)
         (Reassign x ,with-active (Perform (Return outer Int) 1))
         (Proj x id))))
  (check-equal?
   (type-row core)
   '(Never ((Return outer Int)))))

(test-case "spanless and spanful Reassign use the same flow annotation"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Let (ignored const Unit)
         ,(reassign-to 'x with-active active-record)
         (Proj x active))))
  (define spanful (annotate-core core))
  (check-equal? (erase-core spanful) core)
  (check-equal? (type-row spanful) (type-row core)))

(test-case "Handle resumes with the flow at the matching Return"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Handle (Return exit Int)
         (v -> (Proj x active))
         (Let (ignored const Unit)
           ,(reassign-to 'x with-active active-record)
           (Perform (Return exit Int) 7)))))
  (check-equal? (type-row core) '(Int (Mutation)))
  (check-equal?
   (key-of
    `(Let (x mut ,named) ,initial-record
       (Handle (Return exit Int)
         (v -> (Proj x active))
         (Proj x id))))
   'unknown-record-label))

(test-case "a Perform whose argument is Never does not establish a handler flow"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Handle (Return exit Int)
         (v -> (Proj x active))
         (Perform (Return exit Int)
                  (Perform (Return outer Int) 1)))))
  (check-equal? (key-of core) 'unknown-record-label))

(test-case "Handle joins the flow states of all matching exits"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Handle (Return exit Int)
         (v -> v)
         (Eliminate b
           ((true () -> (Let (ignored const Unit)
                          ,(reassign-to 'x with-active active-record)
                          (Perform (Return exit Int) 1)))
            (false () -> (Let (ignored const Unit)
                           ,(reassign-to 'x with-other other-record)
                           (Perform (Return exit Int) 2))))))))
  (check-equal? (key-of core '() '((b Bool)))
                'reassign-type-mismatch))

(test-case "Handler escapes propagate outward and latent Return is recorded"
  (check-equal?
   (type-row
    '(Handle (Return inner Int)
       (v -> (Perform (Return outer Int) 3))
       (Perform (Return inner Int) 1)))
   '(Int ((Return outer Int))))
  (define latent
    '(NFn () Int () ((Return exit Int)) () User))
  (define call-core
    `(Let (x mut ,named) ,initial-record
       (Handle (Return exit Int)
         (v -> (Proj x active))
         (Let (ignored const Unit)
           ,(reassign-to 'x with-active active-record)
           (Apply h)))))
  (check-equal? (type-row call-core '() `((h ,latent))) '(Int (Mutation))))

(test-case "nested Handle forwards the inner handler's outer escape state"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Handle (Return outer Int)
         (v -> (Proj x active))
         (Handle (Return inner Int)
           (v -> (Perform (Return outer Int) 2))
           (Let (ignored const Unit)
             ,(reassign-to 'x with-active active-record)
             (Perform (Return inner Int) 1))))))
  (check-equal? (type-row core) '(Int (Mutation))))

(test-case "check-position bottom retains escapes and excludes dead flow updates"
  (define all-return
    '(Eliminate (Construct Bool true)
       ((true () -> (Perform (Return exit Int) 1))
        (false () -> (Perform (Return exit Int) 2)))))
  (define core
    `(Let (x mut ,named) ,initial-record
       (Handle (Return exit Int)
         (v -> (Proj x id))
         (Let (dead const Int) ,all-return
         ,(reassign-to 'x with-id initial-record)))))
  (check-equal? (type-row core) '(Int (Mutation))))

(test-case "Recur back-edge checks normal flow but ignores all-escape exits"
  (define ftype '(NFn () Int () (Mutation) () User))
  (define bad
    `(Let (x mut ,named) ,initial-record
       (Recur f f ()
         (Let (ignored const Unit)
           ,(reassign-to 'x with-active active-record)
           (Proj x active))
         0)))
  ;; Capturing Recur pins the slot at entry, so its body cannot change the view.
  (check-equal? (key-of bad `((f ,ftype))) 'reassign-type-mismatch)
  (define exits-type '(NFn () Int () ((Return outer Int)) () User))
  (define exits
    '(Recur f f () (Perform (Return outer Int) 1) 0))
  (check-equal? (key-of exits `((f ,exits-type))) 'ok))

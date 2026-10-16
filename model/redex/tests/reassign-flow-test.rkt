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
(define rawptr-int
  '(RawPtr Int Mut NonNull (Align 1) (AddrSpace native) (Prov owned)))

(define initial-record '(Rec ((name imm "A") (id imm 1))))
(define active-record '(Rec ((name imm "B") (active imm 2))))
(define other-record '(Rec ((name imm "C") (other imm 3))))
(define with-active-id '(Record ((active Int imm) (id Int imm) (name String imm))))
(define active-id-record '(Rec ((active imm 2) (id imm 1) (name imm "B"))))
(define with-other-id '(Record ((id Int imm) (name String imm) (other Int imm))))
(define other-id-record '(Rec ((id imm 1) (name imm "C") (other imm 3))))

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

(define (owned-argument-key body result-type)
  (define signature
    `(NFn ((Owned Int)) ,result-type () (Own Unsafe) () User))
  (define core
    `(Lam User owned-check (raw)
       (Handle (Return boundary ,result-type)
         (return-value -> return-value)
         (Scope () (Let (x let (Owned Int)) raw ,body)))))
  (define ir (build-region-ir core))
  (match (type-of/raw (annotate-regions core ir)
                      '() `((owned-check ,signature)) '()
                      (region-ctx ir '() (hash) (hash)))
    [(list 'ok _) 'ok]
    [(list 'fail key _node _details ...) key]))

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

(test-case "mut binder の借用と Move は拒否し、Owned 引数なら許す"
  (for ([expression (in-list '((Read (Borrow x))
                               (Read (BorrowMut x))
                               (Unsafe (AddressOf (BorrowMut x)))))])
    (check-equal? (key-of `(Let (x mut Int) 1 ,expression))
                  'borrow-unknown-owner-region))
  (check-equal? (key-of '(Let (x mut Int) 1 (Move x))) 'move-non-owned)
  (check-equal? (owned-argument-key '(Read (Borrow x)) 'Int) 'ok)
  (check-equal? (owned-argument-key '(Read (BorrowMut x)) 'Int) 'ok)
  (check-equal?
   (owned-argument-key
    `(Unsafe (Let (pointer mut ,rawptr-int)
               (AddressOf (BorrowMut x))
               unit))
    'Unit)
   'ok)
  (check-equal? (owned-argument-key '(Drop (Move x)) 'Unit) 'ok))

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

(test-case "片側で捕捉した pin の合流後も現在の shape を読める"
  (define closure-type '(NFn () Int () () () User))
  (for ([scrutinee (in-list '(b (Apply g)))])
    (define environment
      (if (eq? scrutinee 'b)
          '((b Bool))
          '((g (NFn () Bool () () () User)))))
    (define core
      `(Let (x mut ,named) ,initial-record
         (Let (ignored const Unit)
           (Eliminate ,scrutinee
             ((true () -> (Let (f const ,closure-type)
                            (Lam User f () (Proj x id))
                            unit))
              (false () -> unit)))
           (Proj x id))))
    (check-equal? (type-row core `((f ,closure-type)) environment)
                  '(Int ()))))

(test-case "閉包を内側 scope から返して外側で呼び出せる"
  (define closure-type '(NFn () Int () () () User))
  (define core
    `(Let (x mut ,named) ,initial-record
       (Let (f const ,closure-type)
         (Let (inner const ,closure-type)
           (Lam User inner () (Proj x id))
           inner)
         (Apply f))))
  (check-equal? (type-row core `((inner ,closure-type))) '(Int ())))

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
       (Let (inner const Int)
         (Let (x mut ,with-active)
           (Let (updated const Unit)
             ,(reassign-to 'x with-active active-record)
             ,active-record)
           0)
         (Proj x active))))
  (check-equal? (type-row bound-reassigns-outer) '(Int (Mutation))))

(test-case "Let mut 以外の binder は同名の外側 flow を読まない"
  (define function-type '(NFn (Int) Int () () () User))
  (define parameter-shadow
    `(Let (x mut ,named) ,initial-record
       (Let (f const ,function-type)
         (Lam User f (x) x)
         0)))
  (check-equal? (type-row parameter-shadow `((f ,function-type))) '(Int ()))

  (define (data-shadow scrutinee)
    `(Let (x mut ,named) ,initial-record
       (Let (ignored const Int)
         (Eliminate ,scrutinee ((some (x) -> x) (none () -> 0)))
         0)))
  (for ([scrutinee (in-list '(option-value (Apply option-source)))])
    (define environment
      (if (eq? scrutinee 'option-value)
          '((option-value (Option Int)))
          '((option-source (NFn () (Option Int) () () () User)))))
    (check-equal? (type-row (data-shadow scrutinee) '() environment)
                  '(Int ())))

  (define (union-shadow scrutinee)
    `(Let (x mut ,named) ,initial-record
       (Let (ignored const Int)
         (UnionEliminate ,scrutinee ((Int x -> x) (String x -> 0)))
         0)))
  (for ([scrutinee (in-list '(union-value (Apply union-source)))])
    (define environment
      (if (eq? scrutinee 'union-value)
          '((union-value (Union Int String)))
          '((union-source (NFn () (Union Int String) () () () User)))))
    (check-equal? (type-row (union-shadow scrutinee) '() environment)
                  '(Int ())))

  (check-equal?
   (type-row
    `(Let (x mut ,named) ,initial-record
       (Handle (Return exit Int) (x -> x)
         (Perform (Return exit Int) 1))))
   '(Int ()))

  (check-equal?
   (type-row
    `(Let (x mut ,named) ,initial-record
       (Let (updated const Unit)
         ,(reassign-to 'x with-active active-record)
         (Let (y const Int) (Let (x const Int) 1 x) (Proj x active)))))
   '(Int (Mutation)))

  (check-equal?
   (type-row `(Let (x mut ,named) ,initial-record (Recur g g (x) x 0))
             `((g ,function-type)))
   '(Int ())))

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

(test-case "発行地点のない handler の正常 flow は後続へ混ぜない"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Let (handled const Int)
         (Handle (Return exit Int)
           (v -> (Let (updated const Unit)
                   ,(reassign-to 'x with-active active-record)
                   (Proj x active)))
           (Proj x id))
         (Proj x id))))
  (check-equal? (type-row core) '(Int (Mutation))))

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

(test-case "発行地点のない Never handler の脱出 flow を捨てる"
  (define core
    `(Let (x mut ,named) ,initial-record
       (Handle (Return outer Int)
         (v -> (Proj x id))
         (Let (inner-result const Int)
           (Handle (Return inner Int)
             (v -> (Let (updated const Unit)
                     ,(reassign-to 'x with-active active-record)
                     (Perform (Return outer Int) 2)))
             (Proj x id))
           (Proj x id)))))
  ;; inner Return の発行地点が無いため、Never な handler の outer Return は外へ漏れない。
  (check-equal? (type-row core) '(Int (Mutation))))

(test-case "正常に完了しない枝の発行地点を handler へ伝える"
  (for ([scrutinee (in-list '(b (Apply g)))])
    (define environment
      (if (eq? scrutinee 'b)
          '((b Bool))
          '((g (NFn () Bool () () () User)))))
    (define core
      `(Let (x mut ,named) ,initial-record
         (Handle (Return exit Int)
           (v -> (Proj x active))
           (Eliminate ,scrutinee
             ((true () -> (Let (updated const Unit)
                            ,(reassign-to 'x with-active active-record)
                            (Perform (Return exit Int) 1)))
              (false () -> (Let (updated const Unit)
                             ,(reassign-to 'x with-active active-record)
                             2)))))))
    (check-equal? (type-row core '() environment) '(Int (Mutation)))))

(test-case "関数本体の早期 return と正常出口で局所 mut の shape が異なってもよい"
  (define function-type '(NFn (Bool) Int () (Mutation) () User))
  (for ([scrutinee (in-list '(condition (Apply g)))])
    (define callables
      `((f ,function-type)))
    (define environment
      (if (eq? scrutinee 'condition)
          '()
          '((g (NFn () Bool () () () User)))))
    (define core
      `(Lam User f (condition)
         (Handle (Return f Int) (value -> value)
           (Let (x mut ,named) ,initial-record
             (Eliminate ,scrutinee
               ((true () -> (Let (updated const Unit)
                              ,(reassign-to 'x with-active active-record)
                              (Perform (Return f Int) 1)))
                (false () -> (Proj x id))))))))
    (check-equal? (key-of core callables environment) 'ok)))

(test-case "TryBind の失敗枝を除く Return と正常枝の flow を合流する"
  (for ([scrutinee (in-list '(option-value (Apply option-source)))])
    (define environment
      (if (eq? scrutinee 'option-value)
          '((option-value (Option Int)))
          '((option-source (NFn () (Option Int) () () () User)))))
    (define core
      `(Let (x mut ,named) ,initial-record
         (Let (handled const (Option Int))
           (Handle (Return exit (Option Int)) (value -> value)
             (Eliminate ,scrutinee
               ((some (payload) -> (Let (updated const Unit)
                                     ,(reassign-to 'x with-active active-record)
                                     (Construct (Option Int) some payload)))
                (none () -> (Let (updated const Unit)
                              ,(reassign-to 'x with-active active-record)
                              (Perform (Return exit (Option Int))
                                       (Construct (Option Int) none)))))))
           (Proj x active))))
    (check-equal? (type-row core '() environment) '(Int (Mutation)))))

(test-case "check-position bottom retains escapes and excludes dead flow updates"
  (for ([scrutinee (in-list '(condition (Apply choose)))])
    (define environment
      (if (eq? scrutinee 'condition)
          '((condition Bool))
          '((choose (NFn () Bool () () () User)))))
    (define all-return
      `(Eliminate ,scrutinee
         ((true () -> (Perform (Return exit Int) 1))
          (false () -> (Perform (Return exit Int) 2)))))
    (define core
      `(Let (x mut ,named) ,initial-record
         (Handle (Return exit Int)
           (v -> (Proj x id))
           (Let (dead const Int) ,all-return
             ,(reassign-to 'x with-active-id active-id-record)))))
    ;; 外側の handler は dead な Let 本体でなく、捕捉した Return 時点の状態を見る。
    (check-equal? (type-row core '() environment) '(Int (Mutation)))))

(test-case "Never 束縛値を持つ Handle と非正常 handler の脱出 flow を保つ"
  (for ([scrutinee (in-list '(condition (Apply choose)))])
    (define environment
      (if (eq? scrutinee 'condition)
          '((condition Bool))
          '((choose (NFn () Bool () () () User)))))
    (define all-return
      `(Eliminate ,scrutinee
         ((true () -> (Perform (Return inner Int) 1))
          (false () -> (Perform (Return inner Int) 2)))))
    (define core
      `(Let (x mut ,named) ,initial-record
         (Handle (Return outer Int)
           (v -> (Proj x active))
           (Let (handled const Int)
             (Handle (Return inner Int)
               (v -> (Let (updated const Unit)
                       ,(reassign-to 'x with-active-id active-id-record)
                       (Perform (Return outer Int) v)))
               (Let (dead const Int) ,all-return
                 ,(reassign-to 'x with-other-id other-id-record)))
             (Let (updated const Unit)
               ,(reassign-to 'x with-other-id other-id-record)
               (Perform (Return outer Int) 2))))))
    ;; 内側の handler からの外側 Return だけが到達可能で、後続の再代入は外側の view を変えない。
    (check-equal? (key-of core '() environment) 'ok)))

(test-case "Recur が捕捉した mut slot の shape 変更を拒否する"
  (define ftype '(NFn () Int () (Mutation) () User))
  (define bad
    `(Let (x mut ,named) ,initial-record
       (Recur f f ()
         (Let (ignored const Unit)
           ,(reassign-to 'x with-active active-record)
           (Proj x active))
         0)))
  ;; x は入口で capture pin されるため、ここでは back-edge 検査に到達しない。
  (check-equal? (key-of bad `((f ,ftype))) 'reassign-type-mismatch)
  (define exits-type '(NFn () Int () ((Return outer Int)) () User))
  (define exits
    '(Recur f f () (Perform (Return outer Int) 1) 0))
  (check-equal? (key-of exits `((f ,exits-type))) 'ok))

#lang racket

(require rackunit
         racket/list
         racket/set
         "../borrow.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define (config-trace initial)
  (let loop ([current initial]
             [configs '()]
             [fuel 200])
    (when (zero? fuel)
      (error 'config-trace "評価 fuel を使い切った: ~s" current))
    (define next (remove-duplicates (raw-steps-g2 current) equal?))
    (if (null? next)
        (reverse (cons current configs))
        (match next
          [(list following) (loop following (cons current configs) (sub1 fuel))]
          [_ (error 'config-trace "一意な次状態を期待したが複数ある: ~s" next)]))))

(define (check-config-trace configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row (format "config ~a の row: ~s" index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "config ~a: ~s" index configuration))))

(define initial-record '(Rec ((name imm "A") (id imm 1))))

(test-case "config の再代入後は新しい record view で欄を読み出す"
  (define old-view '(Record ((id Int imm) (name String imm))))
  (define view
    '(Record ((active Bool mut) (extra Int imm) (name String imm))))
  (define replacement
    '(Rec ((name mut "B") (active mut (Construct Bool true)) (extra imm 9))))
  (define initial
    `(cfg (Let (written const Unit)
                (Reassign (MutSlot 0) ,view ,replacement)
              (Proj (MutSlot 0) active))
          ((0 ,initial-record (declared ,old-view)))
          ((0 Available)) () ()))
  (define configs (config-trace initial))
  (check-config-trace configs '() 'Bool)
  (check-true
   (for/or ([configuration (in-list configs)])
     (equal? (config-declared-types configuration) `((0 ,view))))))

(test-case "config の Union 再代入後は tag 付き view で読み出す"
  (define union-type '(Union Int String))
  (define initial
    `(cfg (Let (written const Unit)
                (Reassign (MutSlot 0) ,union-type
                          (UnionInject ,union-type Int (MutSlot 0)))
              (UnionEliminate (MutSlot 0) ((Int n -> n) (String s -> 0))))
          ((0 1 (declared Int))) ((0 Available)) () ()))
  (define configs (config-trace initial))
  (check-config-trace configs '() 'Int)
  (check-true
   (for/or ([configuration (in-list configs)])
     (and (equal? (config-declared-types configuration)
                  `((0 ,union-type)))
          (match configuration
            [(list 'cfg _ heap _ _ _)
             (equal? (second (first heap)) `(UnionVal ,union-type Int 1))]
            [_ #f])))))

(define mut-record-view '(Record ((id Int imm) (name String imm))))
(define changed-record-view
  '(Record ((active Bool imm) (name String imm))))
(define mut-record-value '(Rec ((name imm "A") (id imm 1))))
(define changed-record-value
  '(Rec ((name imm "B") (active imm (Construct Bool true)))))
(define partial-closure-type '(NFn () Int () (Partial) () User))
(define capturing-closure
  '(Lam User f () (Proj (MutSlot 0) id)))
(define noncapturing-closure '(Lam User f () 1))
(define closure-callables `((f ,partial-closure-type)))

(define (closure-config control function-value state [trace '()])
  `(cfg ,control
        ((0 ,mut-record-value (declared ,mut-record-view))
         (1 ,function-value (declared ,partial-closure-type)))
        ((0 Available) (1 ,state)) () ,trace))

(test-case "captured-mut-slots は容器内 closure の body と再代入 target を集める"
  (define value
    '(Rec ((nested imm
                  (Lam User f (x)
                    (Let (x const Int) 1
                      (Reassign (MutSlot 4) Int (MutSlot 4))))))))
  (check-equal? (captured-mut-slots value) (set 4))
  (check-equal? (captured-mut-slots '(Rec ((a imm 1)))) (set)))

(test-case "Available heap の Partial closure が捕捉した view は pin される"
  (check-false
   (config-ok?
    (closure-config
     `(Reassign (MutSlot 0) ,changed-record-view ,changed-record-value)
     capturing-closure 'Available)
    closure-callables 'Unit '(Mutation)))
  (define same-view
    (closure-config
     `(Let (written const Unit)
          (Reassign (MutSlot 0) ,mut-record-view ,mut-record-value)
        (Apply (MutSlot 1)))
     capturing-closure 'Available))
  (check-true
   (config-ok? same-view closure-callables 'Int '(Mutation Partial))))

(test-case "Reassign の右辺で生成する closure も後続の place view を pin する"
  (define core
    `(Let (saved const Unit)
         (Reassign (MutSlot 1) ,partial-closure-type ,capturing-closure)
       (Reassign (MutSlot 0) ,changed-record-view ,changed-record-value)))
  (check-false
   (config-ok? (closure-config core noncapturing-closure 'Available)
               closure-callables 'Unit '(Mutation))))

(test-case "未実行の Eliminate 枝にある closure は view を pin しない"
  (define callables `((f ,partial-closure-type)))
  (define branch-closure
    `(Eliminate (Construct Bool false)
       ((true () ->
         (Let (temporary const ,partial-closure-type) ,capturing-closure 1))
        (false () -> 1))))
  (define core
    `(Let (chosen const Int) ,branch-closure
       (Reassign (MutSlot 0) ,changed-record-view ,changed-record-value)))
  (define selected-config
    (closure-config core noncapturing-closure 'Available))
  (check-true
   (config-ok?
    selected-config
    callables 'Unit '(Mutation))))

(test-case "実行した Eliminate 枝の view を後続の欄読み出しへ伝える"
  (define branch
    `(Eliminate (Construct Bool true)
       ((true () ->
         (Let (written const Unit)
           (Reassign (MutSlot 0) ,changed-record-view ,changed-record-value)
           unit))
        (false () -> unit))))
  (define core
    `(Let (written const Unit) ,branch
       (Proj (MutSlot 0) active)))
  (define initial
    `(cfg ,core
          ((0 ,mut-record-value (declared ,mut-record-view)))
          ((0 Available)) () ()))
  (check-config-trace (config-trace initial) '() 'Bool))

(test-case "Moved heap closure と trace の closure は初期 pin を作らない"
  (check-true
   (config-ok?
    (closure-config
     `(Reassign (MutSlot 0) ,changed-record-view ,changed-record-value)
     capturing-closure 'Moved)
    closure-callables 'Unit '(Mutation)))
  (check-true
   (config-ok?
    (closure-config
     `(Reassign (MutSlot 0) ,changed-record-view ,changed-record-value)
     noncapturing-closure 'Available
     `((obs ,capturing-closure)))
    closure-callables 'Unit '(Mutation))))

(test-case "config view の再帰的な Owned は mut slot で拒否する"
  (define config
    '(cfg (MutSlot 0)
          ((0 (OwnedLeaf (tok 0) (resource 1)) (declared (Owned Int))))
          ((0 Available)) (((tok 0) Available)) ()))
  (check-false (config-ok? config '() '(Owned Int) '(Own))))

(test-case "nested Owned と borrow を含む mut view は config でも拒否する"
  (for ([view (in-list
               '((Record ((payload (Owned Int) imm)))
                 (Record ((payload (Borrowed Int 0) imm)))))])
    (define configuration
      `(cfg (MutSlot 0) ((0 1 (declared ,view))) ((0 Available)) () ()))
    (check-false (config-ok? configuration '() view '()))))

(test-case "Return 後の Reassign は config の正常 flow を更新しない"
  (define configuration
    '(cfg (Handle (Return stop Int)
           (value -> 0)
           (Let (dead const Int) (Perform (Return stop Int) 1)
             (Reassign (MutSlot 0) Int 2)))
          ((0 1 (declared Int))) ((0 Available)) () ()))
  (check-config-trace (config-trace configuration) '() 'Int))

(test-case "C0 は mut Let、R-LetMutB、Reassign の view で一致する"
  (define core
    '(Scope ()
       (Let (x mut Int) 1
         (Let (written const Unit) (Reassign x Int 2) x))))
  (define machine-core (execution-core core '()))
  (define erased (erase-core machine-core))
  (define let-type
    (match erased
      [`(Scope () (Let (x mut ,type) ,_ ,_)) type]
      [_ #f]))
  (define reassign-type
    (let walk ([term erased])
      (match term
        [`(Reassign ,_ ,type ,_) type]
        [(? list? terms)
         (for/or ([child (in-list terms)]) (walk child))]
        [_ #f])))
  (check-equal? let-type 'Int)
  (check-equal? reassign-type let-type)
  (define configs (config-trace (inject-g2m machine-core)))
  (check-config-trace configs '() 'Int)
  (check-true
   (for/and ([configuration (in-list configs)]
             #:when (pair? (config-declared-types configuration)))
     (equal? (config-declared-types configuration) `((0 ,let-type))))))

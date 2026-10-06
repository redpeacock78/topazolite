#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../borrow.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../pr-machine.rkt"
         "../region.rkt"
         "../typing.rkt"
         "../type-shape.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         (only-in "../resource-type.rkt" resource-type?))

(define (type-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok (list type _row)) type]
    [_ 'ill-typed]))

(define (row-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok (list _type row)) row]
    [_ 'ill-typed]))

(define (key-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok _) 'ok]
    [(list 'fail key _node _details ...) key]))

(define (config-core config)
  (match config [`(cfg ,core ,_heap ,_states ,_tokens ,_trace) core]))

(define (g2-trace initial)
  (let loop ([current initial] [configs (list initial)] [rules '()] [fuel 40])
    (when (zero? fuel)
      (error 'g2-trace "fuel exhausted: ~s" current))
    (match (raw-steps-g2/named current)
      ['()
       (check-false (member 'R-LetOwned rules)
                    "RecRewrite traces must not use R-LetOwned")
       (check-false (member 'R-Move rules)
                    "RecRewrite traces must not use R-Move")
       (list configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps (error 'g2-trace "expected one step, got: ~s" steps)])))

(define (contains-mutation? core)
  (match core
    [`(Assign ,_ ,_) #t]
    [`(Reassign ,_ ,_) #t]
    [(? list? parts) (ormap contains-mutation? parts)]
    [_ #f]))

(define (config-row config row)
  (match config
    [`(cfg ,core ,_ ...)
     (if (and (member 'Mutation row)
              (not (contains-mutation? core)))
         (remove 'Mutation row)
         row)]))

(define (check-config-trace configs expected row)
  (for ([config (in-list configs)] [index (in-naturals)])
    (check-true (config-ok? config '() expected (config-row config row))
                (format "invalid intermediate config ~a: ~s" index config))))

(define (config-tokens config)
  (match config
    [`(cfg ,core ,heap ,_states ,_token-states ,trace)
     (append (collect-tokens core)
             (append-map (lambda (entry) (collect-tokens (second entry))) heap)
             (append-map (lambda (event)
                           (match event [`(obs ,value) (collect-tokens value)] [_ '()]))
                         trace))]))

(define (machine-result core)
  (match (run-g2 (inject-g2m core) 100)
    [`(cfg ,value ,_heap ,_states ,_tokens ,_trace) value]
    [other (error 'machine-result "unexpected result: ~s" other)]))

(define (lowered-core-result core)
  (define-values (status target) (lower core 'racket-cs))
  (check-eq? status 'ok (format "lower failed: ~s" target))
  (match (run-pr (inject-pr target) 1000)
    [`(pcfg ,value ,_heap ,_states ,_trace) value]
    [other (error 'lowered-core-result "unexpected result: ~s" other)]))

(define (tagged-pr-trace initial)
  (let loop ([current initial] [rules '()] [fuel 40])
    (when (zero? fuel)
      (error 'tagged-pr-trace "還元の上限に達した: ~s" current))
    (match (apply-reduction-relation/tag-with-names -->pr/rules current)
      ['() (list current rules)]
      [(list (list rule next))
       (loop next
             (append rules (list (string->symbol rule)))
             (sub1 fuel))]
      [steps (error 'tagged-pr-trace "1 ステップを期待したが複数あった: ~s" steps)])))

(define (lowered-value-result value)
  (define-values (status target) (lower-value value 'racket-cs))
  (check-eq? status 'ok (format "lower-value failed: ~s" target))
  target)

(define (check-rec-rewrite-lowering core)
  (check-equal? (lowered-core-result core)
                (lowered-value-result (machine-result core))
                (format "Core/PR result mismatch: ~s" core)))

(define (token-multiset config)
  (sort (map second (config-tokens config)) <))

(define (check-valid-token-trace configs expected row initial-tokens)
  (define initial (first configs))
  (check-true
   (config-ok? initial '() expected (config-row initial row))
   (format "initial config must be valid: ~s; normal=~s; type=~s"
           initial (core-types-normal? initial)
           (with-config-typing
            (lambda () (type-of/raw (config-core initial) '() '() '())))))
  (check-config-trace configs expected row)
  (for ([config (in-list configs)])
    (check-equal? (token-multiset config) initial-tokens
                  (format "token multiset changed: ~s" config))))

(define (record-parameter-type row)
  `(Record ,row))

(define-metafunction G2
  substitute-core : any x any -> any
  [(substitute-core any_1 x any_2) (substitute any_1 x any_2)])

(define (record-parameter-function-type input-row output-row)
  (define input-type (record-parameter-type input-row))
  `(NFn (,input-type) ,(record-parameter-type output-row)
        () ,(if (resource-type? input-type) '(Own) '()) () User))

(define (record-parameter-body body input-type output-type)
  (if (resource-type? input-type)
      (let ([transfer (gensym 'rec-rewrite-input)])
        `(Handle (Return rec-rewrite-return ,output-type)
                 (return-value -> return-value)
                 (Scope ()
                   (Let (,transfer let ,input-type)
                        record-source
                     ,(term (substitute-core ,body record-source
                                             (Move ,transfer)))))))
      body))

(define (type-with-record-parameter body input-row output-row
                                    [extra-callables '()])
  (define input-type (record-parameter-type input-row))
  (define output-type (record-parameter-type output-row))
  (define signature (record-parameter-function-type input-row output-row))
  (type-of `(Lam User rec-rewrite-test (record-source)
              ,(record-parameter-body body input-type output-type))
           (append
            `((rec-rewrite-test ,signature))
            extra-callables)))

(define (key-with-record-parameter body input-row output-row
                                   [extra-callables '()])
  (define input-type (record-parameter-type input-row))
  (define output-type (record-parameter-type output-row))
  (define signature (record-parameter-function-type input-row output-row))
  (key-of `(Lam User rec-rewrite-test (record-source)
             ,(record-parameter-body body input-type output-type))
          (append
           `((rec-rewrite-test ,signature))
           extra-callables)))

(define (key-with-rewritten-field body input-type output-type
                                  [extra-callables '()])
  (key-with-record-parameter
   `(RecRewrite record-source ((a x ,input-type imm ,output-type ,body)))
   `((a ,input-type imm)) `((a ,output-type imm)) extra-callables))

(define (test-fail reason kind key)
  (error 'rec-rewrite-test "~s ~s ~s" reason kind key))

(define rec-rewrite-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data
   '((Pair (A B) ((mkpair ((Param A) (Param B)))))
     (Nat () ((zero ()) (succ ((Data Nat ())))))
     (Chain () ((cnil ()) (ccons (Int (Owned (Data Chain ())))))))
   #:fail test-fail))

(define-syntax-rule (with-data body ...)
  (call-with-trait-ledger rec-rewrite-ledger (lambda () body ...)))

(define rewrite-a
  '(RecRewrite (Rec ((a imm 1) (b imm 2)))
               ((a x Int imm (Union Bool Int)
                 (UnionInject (Union Bool Int) Int x)))))

(test-case "RecRewrite は G2 と G2m の Core の項である"
  (check-true (redex-match? G2 c rewrite-a))
  (check-true (redex-match? G2m c rewrite-a)))

(test-case "評価文脈の穴は入力 e だけに置かれる"
  (define allowed (term (RecRewrite hole ((a x Int imm Int x)))))
  (define rejected
    (term (RecRewrite (Rec ((a imm 1))) ((a x Int imm Int hole)))))
  (check-true (redex-match? G2m F allowed))
  (check-true (redex-match? G2m E allowed))
  (check-true (redex-match? G2m G allowed))
  (check-false (redex-match? G2m F rejected))
  (check-false (redex-match? G2m E rejected))
  (check-false (redex-match? G2m G rejected)))

(test-case "子の順は e の後に各 entry の c で、再構成も一致する"
  (define core
    '(RecRewrite (Rec ((a imm 1)))
                 ((a x Int imm Int x)
                  (b y Bool imm Bool y))))
  (check-equal? (core-children core)
                '((Rec ((a imm 1))) x y))
  (check-equal? (core-with-children core '(input new-a new-b))
                '(RecRewrite input ((a x Int imm Int new-a)
                                    (b y Bool imm Bool new-b)))))

(test-case "entry の x は c だけを束縛し、外側の同名束縛と区別される"
  (define core
    '(Let (x Int) 5
       (RecRewrite x ((a x Int imm Int x)
                      (b y Int imm Int x)))))
  ;; input の x は外側の束縛、各 c の x はそれぞれの entry の束縛である。
  (check-equal? (core-free-vars core) (set))
  (check-equal?
   (core-free-vars '(RecRewrite x ((a x Int imm Int x))))
   (set 'x))
  ;; 先行 entry の binder は後続 entry の c へは届かない。
  (check-equal?
   (core-free-vars '(RecRewrite 0 ((a x Int imm Int x)
                                   (b y Int imm Int x))))
   (set 'x))
  (check-true
   (alpha-equivalent? G2
                      '(RecRewrite (Rec ((a imm 1))) ((a x Int imm Int x)))
                      '(RecRewrite (Rec ((a imm 1))) ((a y Int imm Int y)))))
  (check-false
   (alpha-equivalent? G2
                      '(RecRewrite (Rec ((a imm 1))) ((a x Int imm Int z)))
                      '(RecRewrite (Rec ((a imm 1))) ((a y Int imm Int w))))))

(test-case "列挙した欄の型を置き換え、入力の effect を保つ"
  (check-equal?
   (type-of rewrite-a)
   '(Record ((a (Union Bool Int) imm) (b Int imm))))
  (check-equal?
   (row-of
    '(RecRewrite (Suspend (Rec ((a imm 1) (b imm 2))))
                 ((a x Int imm (Union Bool Int)
                   (UnionInject (Union Bool Int) Int x)))))
   '(Suspend)))

(test-case "mut 欄の型変更と mut から imm の恒等 entry を型付けする"
  (check-equal?
   (type-of
    '(RecRewrite (Rec ((a mut 1)))
                 ((a x Int mut (Union Bool Int)
                   (UnionInject (Union Bool Int) Int x)))))
   '(Record ((a (Union Bool Int) mut))))
  (check-equal?
   (type-of '(RecRewrite (Rec ((a mut 1))) ((a x Int imm Int x))))
   '(Record ((a Int imm)))))

(test-case "Absent を含む入力で optional の印を保つ"
  (check-equal?
   (type-of
    '(RecRewrite (Rec ((a imm 1) (b imm (Absent Int))))
                 ((a x Int imm (Union Bool Int)
                   (UnionInject (Union Bool Int) Int x)))))
   '(Record ((a (Union Bool Int) imm) (b Int imm opt)))))

(test-case "present の欄は c を評価して置き換える"
  (define expected '(Record ((a (Union Bool Int) imm) (b Int imm))))
  (define-values (configs _rules)
    (apply values (g2-trace `(cfg ,rewrite-a () () () ()))))
  (check-valid-token-trace configs expected '() '())
  (check-equal? (config-core (last configs))
                '(Rec ((a imm (UnionVal (Union Bool Int) Int 1))
                      (b imm 2))))
  (check-equal?
   (machine-result rewrite-a)
   '(Rec ((a imm (UnionVal (Union Bool Int) Int 1)) (b imm 2)))))

(test-case "Absent の欄は c を評価せず optional Union として保つ"
  (define union-type '(Union Bool Int))
  (define core
    `(RecRewrite (Rec ((a imm (Absent Int))))
       ((a x Int imm ,union-type
         (UnionInject ,union-type Int
           (Apply (PrimVal (Reserved o-add) add) x 1))))))
  (define expected '(Record ((a (Union Bool Int) imm opt))))
  (define-values (configs _rules)
    (apply values (g2-trace `(cfg ,core () () () ()))))
  (check-valid-token-trace configs expected '() '())
  (check-equal? (config-core (last configs))
                '(Rec ((a imm (Absent (Union Bool Int))))))
  (check-equal? (type-of (config-core (last configs))) expected))

(test-case "列挙しない Owned 欄は Open 後も一度だけ残る"
  (define output-type
    (normalize-type
     '(Record ((owned (Owned Res) imm) (number (Union Bool Int) imm)))))
  (define core
    `(RecRewrite
      (Rec ((owned imm (OwnedLeaf (tok 11) (resource 11))) (number imm 1)))
      ((number x Int imm (Union Bool Int)
        (UnionInject (Union Bool Int) Int x)))))
  (define-values (configs _rules)
    (apply values
           (g2-trace `(cfg ,core () () (((tok 11) Available)) ()))))
  (check-valid-token-trace configs output-type '() '(11))
  (check-equal? (config-core (second configs))
                '(RecRewriteOpen
                  ((owned imm (OwnedLeaf (tok 11) (resource 11)))
                   (number imm (UnionInject (Union Bool Int) Int 1)))))
  (check-equal? (config-core (last configs))
                '(Rec ((owned imm (OwnedLeaf (tok 11) (resource 11)))
                      (number imm (UnionVal (Union Bool Int) Int 1))))))

(test-case "root-Owned identity entry は token を直接移し R-LetOwned と Move を使わない"
  (define output-type
    (normalize-type '(Record ((owned (Owned Res) imm) (number Int imm)))))
  (define core
    '(RecRewrite
      (Rec ((owned mut (OwnedLeaf (tok 12) (resource 12))) (number imm 1)))
      ((owned owner (Owned Res) imm (Owned Res) owner))))
  (define-values (configs rules)
    (apply values (g2-trace `(cfg ,core () () (((tok 12) Available)) ()))))
  (check-valid-token-trace configs output-type '() '(12))
  (check-equal? rules '(R-RecRewrite-Open R-RecRewrite-Close))
  (check-equal? (config-core (second configs))
                '(RecRewriteOpen
                  ((owned imm (OwnedLeaf (tok 12) (resource 12))) (number imm 1))))
  (check-equal? (config-core (last configs))
                '(Rec ((owned imm (OwnedLeaf (tok 12) (resource 12))) (number imm 1)))))

(test-case "資源型の entry は Open で一時 Let を作らず値を直接置換する"
  (define input-value
    '(Rec ((box imm (Rec ((owned imm (OwnedLeaf (tok 13) (resource 13)))))))))
  (define inner-type (normalize-type '(Record ((owned (Owned Res) imm)))))
  (define core
    `(RecRewrite ,input-value ((box x ,inner-type imm ,inner-type x))))
  (define-values (configs rules)
    (apply values
           (g2-trace `(cfg ,core () () (((tok 13) Available)) ()))))
  (check-false (member 'R-Let rules))
  (check-false (member 'R-LetOwned rules))
  (check-equal? (config-core (last configs)) input-value)
  (check-rec-rewrite-lowering core))

(test-case "PRecRewrite は entry を受け渡す PLet を加えない"
  (define input-value
    '(Rec ((box imm (Rec ((owned imm (OwnedLeaf (tok 14) (resource 14)))))))))
  (define inner-type (normalize-type '(Record ((owned (Owned Res) imm)))))
  (define core
    `(RecRewrite ,input-value ((box x ,inner-type imm ,inner-type x))))
  (define-values (status target) (lower core 'racket-cs))
  (check-eq? status 'ok)
  (define trace (tagged-pr-trace `(pcfg ,target () () ())))
  (define final-config (first trace))
  (define rules (second trace))
  (check-false (member 'R-PR-Let rules))
  (check-equal? final-config
                `(pcfg (PRec ((,(label-code 'box)
                               (PRec ((,(label-code 'owned) (PResource 14)))))))
                       () () ())))

(test-case "直接置換後も entry 本体が持つ別名 Let は Core と PR に残る"
  (define option-owned '(Option (Owned Res)))
  (define input
    '(Rec ((a imm (Construct (Option (Owned Res)) some
                             (OwnedLeaf (tok 15) (resource 15)))))))
  (define body `(Let (alias let ,option-owned) x alias))
  (define core
    `(RecRewrite ,input
       ((a x ,option-owned imm ,option-owned ,body))))
  (define expected `(Record ((a ,option-owned imm))))
  (define-values (configs rules)
    (apply values
           (g2-trace `(cfg ,core () () (((tok 15) Available)) ()))))
  (check-valid-token-trace configs expected '() '(15))
  (check-equal? rules
                '(R-RecRewrite-Open R-LetIdentityB R-RecRewrite-Close))
  (check-false (member 'R-LetOwned rules))
  (check-false (member 'R-Move rules))
  (define-values (status target) (lower core 'racket-cs))
  (check-eq? status 'ok)
  (check-true
   (match target
     [`(PRecRewrite ,_ ((,_label ,_source (PLet ,alias ,_value ,alias-use)))
                    ,_ ...)
      (equal? alias alias-use)]
     [_ #f])
   (format "entry 本体に由来する PLet が残っていない: ~s" target)))

(test-case "入れ子の RecRewrite は直接置換で OwnedLeaf を一度だけ運ぶ"
  (define inner-input
    (normalize-type '(Record ((owned (Owned Res) imm) (number Int imm)))))
  (define inner-output
    (normalize-type
     '(Record ((owned (Owned Res) imm) (number (Union Bool Int) imm)))))
  (define expected (normalize-type `(Record ((box ,inner-output imm)))))
  (define input-value
    '(Rec ((box imm (Rec ((owned imm (OwnedLeaf (tok 13) (resource 13)))
                         (number imm 1)))))))
  (define inner-rewrite
    `(RecRewrite nested
       ((number number-value Int imm (Union Bool Int)
         (UnionInject (Union Bool Int) Int number-value)))))
  (define core
    `(RecRewrite ,input-value
       ((box nested ,inner-input imm ,inner-output ,inner-rewrite))))
  (check-true (redex-match? G2m τ inner-input))
  (check-true (redex-match? G2m v input-value))
  (check-true (redex-match? G2m c inner-rewrite))
  (check-true (redex-match? G2m c core) (format "not G2m core: ~s" core))
  (define-values (configs rules)
    (apply values
           (g2-trace `(cfg ,core () () (((tok 13) Available)) ()))))
  (check-valid-token-trace configs expected '() '(13))
  (check-false (member 'R-Let rules))
  (check-false (member 'R-LetOwned rules))
  (check-false (member 'R-Move rules))
  (check-true
   (match (config-core (second configs))
     [`(RecRewriteOpen ((box imm (RecRewrite ,opened-input ,_))))
      (and (equal? opened-input
                   '(Rec ((owned imm (OwnedLeaf (tok 13) (resource 13)))
                          (number imm 1))))
           (contains-owned-leaf? opened-input))]
     [_ #f])
   "Open は欄の値を RecRewrite の入力へ直接置換する")
  (check-equal? (config-core (last configs))
                '(Rec ((box imm
                       (Rec ((owned imm (OwnedLeaf (tok 13) (resource 13)))
                             (number imm (UnionVal (Union Bool Int) Int 1)))))))))

(test-case "RecRewrite は entry 順でなく入力欄順に処理する"
  (define input '(Rec ((a mut 1) (b mut (Construct Bool false)))))
  (define union-type '(Union Bool Int))
  (define entry-a
    `(a x Int mut ,union-type
      (UnionInject ,union-type Int x)))
  (define entry-b
    `(b y Bool mut ,union-type
      (UnionInject ,union-type Bool y)))
  (define expected '(Record ((a (Union Bool Int) mut)
                            (b (Union Bool Int) mut))))
  (define forward `(RecRewrite ,input (,entry-a ,entry-b)))
  (define reverse `(RecRewrite ,input (,entry-b ,entry-a)))
  (for ([core (in-list (list forward reverse))])
    (define-values (configs _rules)
      (apply values (g2-trace `(cfg ,core () () () ()))))
    (check-valid-token-trace configs expected '() '()))
  (check-equal? (machine-result reverse) (machine-result forward))
  (check-equal? (machine-result forward)
                '(Rec ((a mut (UnionVal (Union Bool Int) Int 1))
                      (b mut (UnionVal (Union Bool Int)
                                       Bool (Construct Bool false)))))))

(test-case "出力印 m' は変換、identity、残余の欄でそれぞれ保たれる"
  (define union-type '(Union Bool Int))
  (define core
    `(RecRewrite (Rec ((a mut 1) (b mut 2) (c mut 3)))
       ((a x Int mut ,union-type
         (UnionInject ,union-type Int x))
        (b y Int imm Int y))))
  (define expected
    '(Record ((a (Union Bool Int) mut) (b Int imm) (c Int mut))))
  (define-values (configs _rules)
    (apply values (g2-trace `(cfg ,core () () () ()))))
  (check-valid-token-trace configs expected '() '())
  (check-equal? (config-core (last configs))
                '(Rec ((a mut (UnionVal (Union Bool Int) Int 1))
                      (b imm 2)
                      (c mut 3)))))

(test-case "RecRewrite の lowering は Core の結果と PR の結果を一致させる"
  (define union-type '(Union Bool Int))
  (define absent
    `(RecRewrite (Rec ((a imm (Absent Int))))
       ((a x Int imm ,union-type
         (UnionInject ,union-type Int
           (Apply (PrimVal (Reserved o-add) add) x 1))))))
  (define owned-unlisted
    '(RecRewrite
      (Rec ((owned imm (OwnedLeaf (tok 51) (resource 51)))
           (number imm 1)))
      ((number x Int imm (Union Bool Int)
        (UnionInject (Union Bool Int) Int x)))))
  (define owned-identity
    '(RecRewrite
      (Rec ((owned mut (OwnedLeaf (tok 52) (resource 52))) (number imm 1)))
      ((owned owner (Owned Res) imm (Owned Res) owner))))
  (define inner-input
    '(Record ((owned (Owned Res) imm) (number Int imm))))
  (define inner-output
    '(Record ((owned (Owned Res) imm) (number (Union Bool Int) imm))))
  (define nested
    `(RecRewrite
      (Rec ((box imm (Rec ((owned imm (OwnedLeaf (tok 53) (resource 53)))
                           (number imm 1))))))
      ((box nested ,inner-input imm ,inner-output
        (RecRewrite nested
          ((number number-value Int imm (Union Bool Int)
            (UnionInject (Union Bool Int) Int number-value))))))))
  (define reverse
    `(RecRewrite
      (Rec ((a mut 1) (b mut (Construct Bool false))))
      ((b y Bool mut ,union-type
        (UnionInject ,union-type Bool y))
       (a x Int mut ,union-type
        (UnionInject ,union-type Int x)))))
  (define output-modes
    `(RecRewrite (Rec ((a mut 1) (b mut 2) (c mut 3)))
       ((a x Int mut ,union-type
         (UnionInject ,union-type Int x))
        (b y Int imm Int y))))
  (define optional-present
    `(Let (present const (Record ((a Int imm opt))))
       (Rec ((a imm 5)))
       (RecRewrite present
         ((a payload Int imm ,union-type
           (UnionInject ,union-type Int payload))))))
  ;; Borrow / Assign は Portable Racket backend の対象外なので、copy-out 後の値を直接使う。
  (define snapshot-copy-out
    `(RecRewrite (Rec ((a mut 1)))
       ((a source Int mut ,union-type
         (UnionInject ,union-type Int source)))))
  (check-equal? (type-of optional-present)
                '(Record ((a (Union Bool Int) imm opt))))
  (for ([core (in-list (list rewrite-a absent owned-unlisted owned-identity
                             nested reverse output-modes optional-present
                             snapshot-copy-out))])
    (check-rec-rewrite-lowering core))
  (check-equal? (lowered-core-result absent) '(PRec ())))

(test-case "Owned の identity entry は PR 項から除かれる"
  (define core
    '(RecRewrite
      (Rec ((owned imm (OwnedLeaf (tok 54) (resource 54)))))
      ((owned owner (Owned Res) imm (Owned Res) owner))))
  (define-values (status target) (lower core 'racket-cs))
  (check-eq? status 'ok)
  (check-equal? target
                `(PRecRewrite (PRec ((,(label-code 'owned) (PResource 54)))) ())))

(test-case "Read の copy-out 後の RecRewrite は元 place の更新から独立する"
  (define input-type (normalize-type '(Record ((a Int mut)))))
  (define union-type (normalize-type '(Union Int String)))
  (define rewritten-type
    (normalize-type `(Record ((a ,union-type mut)))))
  (define borrow-ref '(BorrowMutRef 0 () 0))
  (define baseline-core
    `(Let (snapshot const ,input-type) (Read ,borrow-ref)
       (Let (written let Unit)
         (Reassign (MutSlot 0) (Rec ((a mut 2))))
         snapshot)))
  (define rewritten-core
    `(Let (snapshot const ,rewritten-type)
       (RecRewrite (Read ,borrow-ref)
         ((a source Int mut ,union-type
           (UnionInject ,union-type Int source))))
       (Let (written let Unit)
         (Reassign (MutSlot 0) (Rec ((a mut 2))))
         snapshot)))
  (define heap
    `((0 (Rec ((a mut 1))) (declared (Owned ,input-type)))))
  (define states '((0 Available)))
  (check-true
   (config-ok? `(cfg (Read ,borrow-ref) ,heap ,states () ())
               '() input-type '())
   "BorrowMutRef の copy-out は単独でも config-ok?")
  (define (trace core)
    (first (g2-trace `(cfg ,core ,heap ,states () ()))))
  (define baseline-configs (trace baseline-core))
  (define rewritten-configs (trace rewritten-core))
  (check-valid-token-trace baseline-configs input-type '(Mutation) '())
  (check-valid-token-trace rewritten-configs rewritten-type
                            '(Mutation) '())
  (define baseline-final (config-core (last baseline-configs)))
  (define rewritten-final (config-core (last rewritten-configs)))
  (check-equal? baseline-final
                '(Rec ((a mut 1))))
  (check-equal? rewritten-final
                `(Rec ((a mut (UnionVal ,union-type Int 1)))))
  (check-equal? (second (assoc 0 (list-ref (last baseline-configs) 2)))
                '(Rec ((a mut 2))))
  (check-equal? (second (assoc 0 (list-ref (last rewritten-configs) 2)))
                '(Rec ((a mut 2)))))

(test-case "root Owned 欄は identity transfer として印だけを変えられる"
  (define input-row '((a (Owned Int) mut) (b Int imm)))
  (define output-row '((a (Owned Int) imm) (b Int imm)))
  (check-equal?
   (type-with-record-parameter
    '(RecRewrite record-source ((a own (Owned Int) imm (Owned Int) own)))
    input-row output-row)
   (record-parameter-function-type input-row output-row)))

(test-case "Fn 型欄の Owned 仮引数は資源出現条件へ再帰しない"
  (define fn-type '(NFn ((Owned Int)) Int () () () User))
  (define row `((f ,fn-type imm)))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite record-source
                 ((f x ,fn-type imm ,fn-type (Let (y const ,fn-type) x x))))
    row row)
   `(NFn (,(record-parameter-type row))
         ,(record-parameter-type row) () () () User)))

(test-case "線形な Let と内側の RecRewrite は資源を一度だけ運ぶ"
  (define owned-row '((a (Owned Int) imm) (b Int imm)))
  (define outer-row `((box (Record ,owned-row) imm)))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite record-source
                 ((box x (Record ,owned-row) imm (Record ,owned-row)
                     (RecRewrite x
                                 ((a inner-own (Owned Int) imm
                                   (Owned Int) inner-own))))))
    outer-row outer-row)
   (record-parameter-function-type outer-row outer-row))
  (define option-owned '(Option (Owned Int)))
  (define option-row `((a ,option-owned imm)))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite record-source
                 ((a x ,option-owned imm ,option-owned
                     (Let (alias let ,option-owned) x alias))))
    option-row option-row)
   (record-parameter-function-type option-row option-row))
  (check-equal?
   (type-of
    `(RecRewrite (Rec ((a imm (Absent (Option (Owned Int))))))
                 ((a x (Option (Owned Int)) imm (Option (Owned Int))
                   x))))
   '(Record ((a (Option (Owned Int)) imm opt)))))

(test-case "資源型の判定は ForallRegion と data schema を辿り、NFn を除く"
  (check-true (resource-type? '(ForallRegion (r) (Option (Owned Int)))))
  (check-false
   (resource-type?
    '(ForallRegion (r) (NFn ((Owned Int)) (Owned Int) () () () User))))
  (check-true (resource-type? '(Intersection Int (Owned Int))))
  (check-true (resource-type? '(Untrusted (Owned Int))))
  (check-true (resource-type? '(Refined (Owned Int) (Prop p))))
  (check-false (resource-type? '(Borrowed (Owned Int) 0)))
  (check-true (resource-type? '(UnknownResourceType Int)))
  (check-true (resource-type? '(Data MissingSchema ())))
  (with-data
    (check-false (resource-type? '(Data Nat ())))
    (check-true (resource-type? '(Data Chain ())))))

(test-case "資源を持つ Union の UnionEliminate は各枝で線形に運ぶ"
  (define base (normalize-type '(Record ((o (Owned Int) imm)))))
  (define wide (normalize-type '(Record ((o (Owned Int) imm) (b Bool imm)))))
  (define resource-union (normalize-type `(Union ,base ,wide)))
  (define input-row `((a ,resource-union imm)))
  (define output-row `((a ,base imm)))
  (define branch-term
    `(UnionEliminate x
       ((,base direct -> direct)
        (,wide alias -> (Let (union_k let ,wide) alias union_k)))))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite record-source
                 ((a x ,resource-union imm ,base ,branch-term)))
    input-row output-row)
   (record-parameter-function-type input-row output-row))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite record-source
       ((a x ,resource-union imm ,base
         (Let (rewritten const ,base) ,branch-term rewritten))))
    input-row output-row)
   (record-parameter-function-type input-row output-row)))

(test-case "資源を持たない Union 枝の binder は複数回使える"
  (define resource-member (normalize-type '(Record ((o (Owned Int) imm)))))
  (define input-type (normalize-type `(Union Int ,resource-member)))
  (define output-type
    (normalize-type `(Record ((p Int imm) (q Int imm) (tag ,input-type imm)))))
  (define body
    `(UnionEliminate x
       ((Int number ->
         (Rec ((p imm number)
              (q imm number)
              (tag imm (UnionInject ,input-type Int number)))))
        (,resource-member payload ->
         (Rec ((p imm 0)
              (q imm 0)
              (tag imm (UnionInject ,input-type ,resource-member payload))))))))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite record-source
                 ((a x ,input-type imm ,output-type ,body)))
    `((a ,input-type imm)) `((a ,output-type imm)))
   (record-parameter-function-type `((a ,input-type imm))
                                   `((a ,output-type imm)))))

(test-case "RecRewrite の入力が Record でない場合は拒否する"
  (check-equal?
   (key-of '(RecRewrite 1 ((a x Int imm Int x))))
   'ill-typed))

(test-case "未知と重複した entry label は既存の診断を使う"
  (check-equal?
   (key-of '(RecRewrite (Rec ((a imm 1))) ((z x Int imm Int x))))
   'unknown-record-label)
  (check-equal?
   (key-of '(RecRewrite (Rec ((a imm 1)))
                        ((a x Int imm Int x) (a y Int imm Int y))))
   'duplicate-record-label))

(test-case "entry の環境は x だけで、変換本体は expected 型へ check する"
  (check-equal?
   (key-of '(RecRewrite (Rec ((a imm 1))) ((a x Int imm Int external))))
   'unbound-variable)
  (check-equal?
   (key-of '(RecRewrite (Rec ((a imm 1))) ((a x Int imm Bool x))))
   'type-mismatch))

(test-case "entry の変換本体は effect-free で OwnLeaf を含まない"
  (define effectful-core
    '(RecRewrite (Rec ((a imm 1)))
                 ((a x Int imm Int
                   (Apply (Lam User effectful () (Suspend 1)))))))
  (check-equal?
   (key-of effectful-core
           '((effectful (NFn () Int () (Suspend) () User))))
   'ill-typed)
  (check-equal?
   (key-of '(RecRewrite (Rec ((a imm 1))) ((a x Int imm (Owned Int) (OwnLeaf 1)))))
   'ill-typed))

(test-case "input 型の不一致と imm から mut への変更は ill-typed"
  (check-equal?
   (key-of '(RecRewrite (Rec ((a imm 1))) ((a x Bool imm Bool x))))
   'ill-typed)
  (check-equal?
   (key-of '(RecRewrite (Rec ((a imm 1))) ((a x Int mut Int x))))
   'ill-typed))

(test-case "root Owned entry は τ を変えず c が x の場合だけ許す"
  (check-equal?
   (key-with-record-parameter
    '(RecRewrite record-source ((a x (Owned Int) imm (Owned Bool) x)))
    '((a (Owned Int) imm))
    '((a (Owned Int) imm)))
   'ill-typed)
  (check-equal?
   (key-with-record-parameter
    '(RecRewrite record-source
                 ((a x (Owned Int) imm (Owned Int) (Move x))))
    '((a (Owned Int) imm))
    '((a (Owned Int) imm)))
   'ill-typed))

(test-case "資源を持つ値を線形文脈の外へ出す形は拒否する"
  (define option-owned '(Option (Owned Int)))
  (define row `((a ,option-owned imm)))
  (define nfn `(NFn () ,option-owned () () () User))
  (define nested-result `(Record ((seed ,option-owned imm))))
  (define resource-list '(List (Owned Int)))
  (define resource-result '(Result (Owned Int) Int))
  (define forall-resource `(ForallRegion (r) ,option-owned))
  (define union-base (normalize-type '(Record ((o (Owned Int) imm)))))
  (define union-wide (normalize-type '(Record ((o (Owned Int) imm) (b Bool imm)))))
  (define resource-union (normalize-type `(Union ,union-base ,union-wide)))
  (define resource-pair
    (normalize-type `(Record ((p ,union-base imm) (q ,union-base imm)))))
  (define int-resource-union (normalize-type `(Union Int ,union-base)))
  (check-equal?
   (key-with-rewritten-field
    '(Construct (Option (Owned Int)) none) option-owned option-owned)
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    `(Let (y let ,option-owned) x (Rec ((p imm y) (q imm y))))
    option-owned `(Record ((p ,option-owned imm) (q ,option-owned imm))))
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    `(Let (y mut ,option-owned) x y) option-owned option-owned)
   'ill-typed)
  (check-equal?
   (key-with-record-parameter
    `(RecRewrite record-source ((a x ,option-owned imm ,nfn
                     (Lam User rec-rewrite-inner () x))))
    row `((a ,nfn imm))
    `((rec-rewrite-inner (NFn () ,option-owned () () () User))))
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    `(RegionLam (r) x) option-owned option-owned)
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    '(Recur loop-id loop () x (Apply loop)) option-owned option-owned)
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    `(Eliminate x ((some (payload) -> (Construct ,option-owned none))
                   (none () -> (Construct ,option-owned none))))
    option-owned option-owned)
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    `(Handle (Return boundary ,option-owned) (returned -> returned) x)
    option-owned option-owned)
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    `(RecRewrite (Rec ((seed imm 0)))
                 ((seed inner Int imm ,option-owned x)))
    option-owned nested-result)
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    '(Rec ((p imm x) (q imm x)))
    resource-list `(Record ((p ,resource-list imm) (q ,resource-list imm))))
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    '(Rec ((p imm x) (q imm x)))
    resource-result
    `(Record ((p ,resource-result imm) (q ,resource-result imm))))
   'ill-typed)
  (check-true (resource-type? forall-resource))
  (check-equal?
   (key-with-record-parameter
    `(RecRewrite record-source
       ((a x ,resource-union imm ,resource-pair
         (UnionEliminate x
           ((,union-base left -> (Rec ((p imm left) (q imm left))))
            (,union-wide right -> (Rec ((p imm right) (q imm right)))))))))
    `((a ,resource-union imm)) `((a ,resource-pair imm)))
   'ill-typed)
  (check-equal?
   (key-with-rewritten-field
    `(UnionEliminate x ((,union-base left -> unit)
                        (,union-wide right -> unit)))
    resource-union 'Unit)
   'ill-typed)
  ;; 外側の x は scrutinee ではなく一方の枝だけに現れる。
  (check-equal?
   (key-with-rewritten-field
    `(UnionEliminate
      (UnionInject ,int-resource-union Int 1)
      ((Int number -> x)
       (,union-base payload -> (UnionInject ,int-resource-union ,union-base payload))))
    int-resource-union int-resource-union)
   'ill-typed))

(test-case "資源を持つ Data の schema を線形条件が辿る"
  (define chain '(Data Chain ()))
  (define output-type `(Record ((p ,chain imm) (q ,chain imm))))
  (define pair-type `(Data Pair (,chain ,chain)))
  (with-data
    (check-equal?
     (key-with-rewritten-field
      '(Rec ((p imm x) (q imm x))) chain output-type)
     'ill-typed)
    (check-equal?
     (key-with-rewritten-field
      `(Construct ,pair-type mkpair x x) chain pair-type)
     'ill-typed)))

(test-case "Intersection は正規化入口では使えないが資源判定は fail-closed に扱う"
  (check-true (resource-type? '(Intersection Int (Owned Int))))
  (check-true (resource-type? '(UnknownTypeConstructor (Owned Int)))))

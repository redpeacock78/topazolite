#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../typing.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         (submod "../typing.rkt" rec-rewrite-test-support))

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

(define (record-parameter-type row)
  `(Record ,row))

(define (type-with-record-parameter body input-row output-row
                                    [extra-callables '()])
  (define input-type (record-parameter-type input-row))
  (define output-type (record-parameter-type output-row))
  (type-of `(Lam User rec-rewrite-test (r) ,body)
           (append
            `((rec-rewrite-test
               (NFn (,input-type) ,output-type () () () User)))
            extra-callables)))

(define (key-with-record-parameter body input-row output-row
                                   [extra-callables '()])
  (define input-type (record-parameter-type input-row))
  (define output-type (record-parameter-type output-row))
  (key-of `(Lam User rec-rewrite-test (r) ,body)
          (append
           `((rec-rewrite-test
              (NFn (,input-type) ,output-type () () () User)))
           extra-callables)))

(define (key-with-rewritten-field body input-type output-type
                                  [extra-callables '()])
  (key-with-record-parameter
   `(RecRewrite r ((a x ,input-type imm ,output-type ,body)))
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

(test-case "root Owned 欄は identity transfer として印だけを変えられる"
  (define input-row '((a (Owned Int) mut) (b Int imm)))
  (define output-row '((a (Owned Int) imm) (b Int imm)))
  (check-equal?
   (type-with-record-parameter
    '(RecRewrite r ((a own (Owned Int) imm (Owned Int) own)))
    input-row output-row)
   `(NFn (,(record-parameter-type input-row))
         ,(record-parameter-type output-row) () () () User)))

(test-case "Fn 型欄の Owned 仮引数は資源出現条件へ再帰しない"
  (define fn-type '(NFn ((Owned Int)) Int () () () User))
  (define row `((f ,fn-type imm)))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite r ((f x ,fn-type imm ,fn-type (Let (y const ,fn-type) x x))))
    row row)
   `(NFn (,(record-parameter-type row))
         ,(record-parameter-type row) () () () User)))

(test-case "線形な Let と内側の RecRewrite は資源を一度だけ運ぶ"
  (define owned-row '((a (Owned Int) imm) (b Int imm)))
  (define outer-row `((box (Record ,owned-row) imm)))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite r ((box x (Record ,owned-row) imm (Record ,owned-row)
                     (RecRewrite x
                                 ((a inner-own (Owned Int) imm
                                   (Owned Int) inner-own))))))
    outer-row outer-row)
   `(NFn (,(record-parameter-type outer-row))
         ,(record-parameter-type outer-row) () () () User))
  (define option-owned '(Option (Owned Int)))
  (define option-row `((a ,option-owned imm)))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite r ((a x ,option-owned imm ,option-owned
                     (Let (alias let ,option-owned) x alias))))
    option-row option-row)
   `(NFn (,(record-parameter-type option-row))
         ,(record-parameter-type option-row) () () () User))
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
    `(RecRewrite r ((a x ,resource-union imm ,base ,branch-term)))
    input-row output-row)
   `(NFn (,(record-parameter-type input-row))
         ,(record-parameter-type output-row) () () () User))
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite r
       ((a x ,resource-union imm ,base
         (Let (rewritten const ,base) ,branch-term rewritten))))
    input-row output-row)
   `(NFn (,(record-parameter-type input-row))
         ,(record-parameter-type output-row) () () () User)))

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
    `(RecRewrite r ((a x ,input-type imm ,output-type ,body)))
    `((a ,input-type imm)) `((a ,output-type imm)))
   `(NFn (,(record-parameter-type `((a ,input-type imm))))
         ,(record-parameter-type `((a ,output-type imm))) () () () User)))

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
    '(RecRewrite r ((a x (Owned Int) imm (Owned Bool) x)))
    '((a (Owned Int) imm))
    '((a (Owned Int) imm)))
   'ill-typed)
  (check-equal?
   (key-with-record-parameter
    '(RecRewrite r ((a x (Owned Int) imm (Owned Int) (Move x))))
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
    `(RecRewrite r ((a x ,option-owned imm ,nfn
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
    `(RecRewrite r
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

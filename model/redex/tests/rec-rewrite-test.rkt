#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../typing.rkt")

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

(test-case "Let と内側の RecRewrite の再束縛は自由出現に数えない"
  (define owned-row '((a (Owned Int) imm) (b Int imm)))
  (define outer-row `((box (Record ,owned-row) imm)))
  (check-equal?
   (key-with-record-parameter
    `(RecRewrite r
                 ((box x (Record ,owned-row) imm (Record ,owned-row)
                   (Let (x const (Record ,owned-row)) x
                     (RecRewrite x
                                  ((a inner-own (Owned Int) imm
                                    (Owned Int) inner-own)))))))
    outer-row outer-row)
   'ok)
  (check-equal?
   (type-with-record-parameter
    `(RecRewrite r
                 ((box x (Record ,owned-row) imm (Record ,owned-row)
                   (Let (x const (Record ,owned-row)) x
                     (RecRewrite x
                                  ((a inner-own (Owned Int) imm
                                    (Owned Int) inner-own)))))))
    outer-row outer-row)
  `(NFn (,(record-parameter-type outer-row))
         ,(record-parameter-type outer-row) () () () User))
  (check-equal?
   (type-of
    `(RecRewrite (Rec ((a imm (Absent (Option (Owned Int))))))
                 ((a x (Option (Owned Int)) imm (Option (Owned Int))
                   x))))
   '(Record ((a (Option (Owned Int)) imm opt)))))

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

(test-case "資源を持つ欄の自由出現はちょうど 1 回で Lam の外に限る"
  (define row '((a (Option (Owned Int)) imm)))
  (define option-owned '(Option (Owned Int)))
  (define nfn `(NFn () ,option-owned () () () User))
  (define resource-union
    '(Union (Record ((o (Owned Int) imm))) Int))
  (check-equal?
   (key-with-record-parameter
    `(RecRewrite r ((a x ,option-owned imm ,option-owned
                     (Construct (Option (Owned Int)) none))))
    row row)
   'ill-typed)
  (check-equal?
   (key-with-record-parameter
    `(RecRewrite r
                 ((a x ,option-owned imm ,option-owned
                   (Let (y const ,option-owned) x
                     (Let (z const ,option-owned) x y)))))
    row row)
   'ill-typed)
  (check-equal?
   (key-with-record-parameter
    `(RecRewrite r ((a x ,option-owned imm ,nfn
                     (Lam User rec-rewrite-inner () x))))
    row `((a ,nfn imm))
    `((rec-rewrite-inner (NFn () ,option-owned () () () User))))
   'ill-typed)
  (check-equal?
   (key-with-record-parameter
    `(RecRewrite r
                 ((a x ,resource-union imm ,resource-union
                   (UnionInject ,resource-union Int 1))))
    `((a ,resource-union imm))
    `((a ,resource-union imm)))
   'ill-typed))

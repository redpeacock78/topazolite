#lang racket

(require rackunit "../typing.rkt")

(define ret1 '(Perform (Return b Int) 1))
(define test-callables
  '((f (NFn (Int) Int () () () User))
    (g (NFn (Int Int) Int () () () User))))
(define int-function-type '(NFn (Int) Int () () () User))
(define owned-function-type '(NFn (Int) (Owned Res) () (Own) () User))

(define (typed-with-normal core [places '()] [callables test-callables]
                           [environment '()])
  (match (type-of/raw*+normal core places callables environment)
    [(list 'ok (list type row _table _sigma _renamed normal-type))
     (list type row normal-type)]
    [_ 'ill-typed]))

(define (typed-type-normal core [places '()] [callables test-callables]
                           [environment '()])
  (match (typed-with-normal core places callables environment)
    [(list type _row normal-type) (list type normal-type)]
    [_ 'ill-typed]))

(define (never-with-normal type [name 'normal])
  `(Let (,name const ,type)
     (Perform (Return b ,type) ,ret1)
     ,name))

(test-case "実引数の Return で Apply が Never になる"
  (define core `(Apply (Lam User f (v) v) ,ret1))
  (check-equal? (typed-with-normal core) '(Never ((Return b Int)) Int)))

(test-case "Never の後ろの実引数の型の誤りを報告する"
  (check-equal?
   (core-type-of `(Apply (Lam User g (v w) v) ,ret1 unit) '()
                 test-callables)
   'ill-typed))

(test-case "Construct の欄の Return で Eliminate が Never になる"
  (define core
    `(Eliminate (Construct (Option Int) some ,ret1)
       ((some (y) -> y) (none () -> 0))))
  (check-equal?
   (typed-with-normal core)
   '(Never ((Return b Int)) Int)))

(test-case "Return を直接 scrutinee にした Eliminate は拒否する"
  (check-equal?
   (core-type-of `(Eliminate ,ret1 ((some (y) -> y) (none () -> 0))) '() '())
   'ill-typed))

(test-case "全枝 Never の Eliminate を receiver にした射影は正常型 bottom を伝える"
  (check-equal?
   (typed-type-normal
    `(Proj (Eliminate (Construct Bool true)
             ((true () -> (Perform (Return b Int) 1))
              (false () -> (Perform (Return b Int) 2))))
           a))
   '(Never ⊥)))

(test-case "全枝 Never の UnionEliminate の正常型は bottom"
  (check-equal?
   (typed-type-normal
    `(UnionEliminate
      (UnionInject (Union Int String) Int ,ret1)
      ((Int x -> ,ret1) (String y -> ,ret1))))
   '(Never ⊥)))

(test-case "Never 束縛の Let は本体の正常型を保持する"
  (check-equal?
   (typed-with-normal `(Let (x const Int) ,ret1 5))
   '(Never ((Return b Int)) Int)))

(test-case "束縛値と本体が Never の Let を receiver にした射影は正常型 bottom を伝える"
  (check-equal?
   (typed-type-normal
    (list 'Proj
          (list 'Let '(x const Int) ret1 '(Perform (Return b Int) 2))
          'a))
   '(Never ⊥)))

(test-case "外側への Return で Never の本体を持つ内側 Handle は Never"
  (check-equal?
   (typed-with-normal
    '(Handle (Return inner Int) (x -> x)
       (Apply (Lam User f (v) v)
              (Perform (Return outer Int) 1)))
    )
   '(Never ((Return outer Int)) Int)))

(test-case "到達しない Return だけを row に持つ捕まえる Handle は Never"
  (check-equal?
   (typed-with-normal
    '(Handle (Return inner Int) (x -> x)
       (Apply (Lam User g (v w) v)
              (Perform (Return outer Int) 1)
              (Perform (Return inner Int) 2))))
   '(Never ((Return outer Int)) Int)))

(test-case "Let の束縛値が外側への Return なら本体の Return は到達せず Handle は Never"
  (check-equal?
   (typed-with-normal
    '(Handle (Return inner Int) (x -> x)
       (Let (y const Int) (Perform (Return outer Int) 1)
         (Perform (Return inner Int) 2))))
   '(Never ((Return outer Int)) ⊥)))

(test-case "到達する枝の Return が残る捕まえる Handle は Never にならない"
  (check-equal?
   (typed-with-normal
    '(Handle (Return inner Int) (x -> x)
       (Let (y const Unit)
            (Eliminate c
              ((true () -> (Perform (Return outer Int) 1))
               (false () -> unit)))
         (Perform (Return inner Int) 2)))
    '() test-callables '((c Bool)))
   '(Int ((Return outer Int)) Int)))

(test-case "mut 束縛が無くても到達可能な Return を捕まえる Handle は Int"
  (check-equal?
   (car
    (typed-with-normal
     '(Handle (Return b Int) (x -> x)
        (Perform (Return b Int) 1))))
   'Int))

(test-case "latent Return を持つ関数の Apply は捕まえる Handle の E に鍵を残す"
  (check-equal?
   (car
    (typed-with-normal
     '(Handle (Return b Int) (x -> x)
        (Apply k 1))
     '() test-callables
     '((k (NFn (Int) Never () ((Return b Int)) () User)))))
   'Int))

(test-case "内側の Handle が同じ境界を消費すると外側の Handle は Never"
  (check-equal?
   (car
    (typed-with-normal
     '(Handle (Return b Int) (x -> x)
        (Let (y const Int)
             (Handle (Return b Int) (x -> x)
               (Perform (Return b Int) 1))
          (Perform (Return outer Int) 2)))))
   'Never))

(define (never-returning-branch)
  '(Handle (Return inner Bool) (x -> x)
     (Let (y const Int) (Perform (Return outer Int) 1)
       (Perform (Return inner Bool) (Construct Bool true)))))

(test-case "到達しない Return の枝は合成位置の Eliminate の候補に入らない"
  (check-equal?
   (typed-with-normal
    `(Eliminate c
       ((true () -> ,(never-returning-branch))
        (false () -> 2)))
    '() test-callables '((c Bool)))
   '(Int ((Return outer Int)) Int)))

(test-case "到達しない Return の枝は検査位置の Eliminate の候補に入らない"
  (check-equal?
   (typed-with-normal
    `(Let (result const Int)
       (Eliminate c
         ((true () -> ,(never-returning-branch))
          (false () -> 2)))
       result)
    '() test-callables '((c Bool)))
   '(Int ((Return outer Int)) Int)))

(test-case "同じ境界で型の違う Return は捕まえず Handle を Never にする"
  (check-equal?
   (typed-with-normal
    '(Handle (Return b Int) (x -> x)
       (Perform (Return b Bool) (Construct Bool true))))
   '(Never ((Return b Bool)) ⊥)))

(test-case "Apply の実引数の型違い Return も捕まえず Handle を Never にする"
  (check-equal?
   (typed-with-normal
    '(Handle (Return b Int) (x -> x)
       (Apply (Lam User g (v w) v) 1
              (Perform (Return b Bool) (Construct Bool true)))))
   '(Never ((Return b Bool)) Int)))

(test-case "Apply の関数位置は Never の正常型で呼出し型を決める"
  (define function-type '(NFn (Int) Int () () () User))
  (check-equal?
   (typed-type-normal
    `(Apply ,(never-with-normal function-type) 1))
   '(Never Int)))

(test-case "Curry は関数位置の Never の正常型で部分適用型を決める"
  (define function-type '(NFn (Int String) Int () () () User))
  (check-equal?
   (typed-type-normal
    `(Curry ,(never-with-normal function-type) 1))
   '(Never (NFn (String) Int () () () (Derived User (Curry 1))))))

(test-case "Curry は正常型の無い関数位置を拒否する"
  (check-equal? (core-type-of `(Curry ,ret1 1) '() '()) 'ill-typed))

(test-case "Construct 自身は欄の Return があっても正常型を保つ"
  (check-equal?
   (typed-type-normal `(Construct (Option Int) some ,ret1))
   '(Never (Option Int))))

(test-case "Perform Return の正常型は bottom"
  (check-equal? (typed-type-normal ret1) '(Never ⊥))
  (check-equal? (core-type-of ret1 '() '()) '(Never ((Return b Int)))))

(test-case "Drop は既知の Owned 正常型を使い、結果は Unit"
  (define owned-function
    '(NFn (Int) (Owned Res) () (Own) () User))
  (check-equal?
   (typed-type-normal
    '(Drop (Apply h (Perform (Return b Int) 1)))
    '() '() `((h ,owned-function)))
   '(Never Unit)))

(test-case "Drop は正常型が bottom の被演算子を拒否する"
  (check-equal? (core-type-of `(Drop ,ret1) '() '()) 'ill-typed))

(test-case "Yield の observed に正常型を使い next の型を伝える"
  (check-equal?
   (typed-type-normal
    '(Yield (Apply h (Perform (Return b Int) 1)) 5)
    '() '() `((h ,int-function-type)))
   '(Never Int)))

(test-case "Yield は正常型 bottom の observed を拒否する"
  (check-equal?
   (core-type-of (list 'Yield ret1 5) '() '())
   'ill-typed))

(test-case "Yield の Never な next は bottom を伝える"
  (check-equal?
   (typed-type-normal `(Yield 1 ,ret1))
   '(Never ⊥)))

(test-case "Scope は Never の本体の正常型を伝える"
  (check-equal?
   (typed-type-normal
    `(Scope () (Apply ,(never-with-normal '(NFn (Int) Int () () () User)) 1)))
   '(Never Int)))

(test-case "Suspend は本体の正常型を伝える"
  (check-equal?
   (typed-type-normal
    `(Suspend (Apply (Lam User f (v) v) ,ret1)))
   '(Never Int)))

(test-case "Discharge は関数の正常型で基底項を型付けする"
  (define function-type
    '(NFn (Int) Int () () (TypeNarrativeCap) User))
  (check-equal?
   (typed-type-normal
    `(Discharge (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
       (Apply h ,ret1))
    '() '() `((h ,function-type)))
   '(Never Int)))

(test-case "Discharge は正常型 bottom の基底を拒否する"
  (define function-type
    '(NFn (Int) Never () () (TypeNarrativeCap) User))
  (check-equal?
   (core-type-of
    '(Discharge (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
       (Apply h 1))
    '() '() `((h ,function-type)))
   'ill-typed))

(test-case "OwnLeaf は Never の payload の正常型を伝える"
  (define owned-function '(NFn (Int) (Owned Res) () (Own) () User))
  (check-equal?
   (typed-type-normal
    `(Construct (Option (Owned Res)) some
       (OwnLeaf (Apply h ,ret1)))
    '() '() `((h ,owned-function-type)))
   '(Never (Option (Owned Res)))))

(test-case "Rec synthesis は欄の正常型から record 型を作る"
  (check-equal?
   (typed-type-normal
    '(Rec ((a imm (Apply h (Perform (Return b Int) 1)))))
    '() '() `((h ,int-function-type)))
   '(Never (Record ((a Int imm))))))

(test-case "Rec synthesis は正常型が bottom の欄で正常型 bottom を伝える"
  (check-equal? (typed-type-normal `(Rec ((a imm ,ret1))) '() '())
                '(Never ⊥)))

(test-case "Rec synthesis は bottom の欄の後ろの欄の誤りを報告する"
  (check-equal?
   (core-type-of `(Rec ((a imm ,ret1) (b imm (Apply f unit)))) '()
                 test-callables)
   'ill-typed))

(test-case "Rec synthesis は bottom の欄があっても重複 label を拒否する"
  (check-equal? (core-type-of `(Rec ((a imm ,ret1) (a imm 1))) '() '())
                'ill-typed))

(test-case "Rec synthesis の row は bottom の欄の後ろの effect を含む"
  (check-equal?
   (typed-with-normal
    `(Rec ((a imm ,ret1) (b imm (Perform (Return c Int) 2)))))
   '(Never ((Return b Int) (Return c Int)) ⊥)))

(test-case "Rec checking は期待 record 型で Never の欄を検査する"
  (define parameter-type '(Record ((a Int imm))))
  (define function-type `(NFn (,parameter-type) Int () () () User))
  (check-equal?
   (typed-type-normal
    '(Apply h (Rec ((a imm (Perform (Return b Int) 1)))))
    '() '() `((h ,function-type)))
   '(Never Int)))

(test-case "Rec checking は期待型に無い bottom 欄を row から省く"
  (define parameter-type '(Record ((a Int imm))))
  (define function-type `(NFn (,parameter-type) Int () () () User))
  (define core
    '(Apply h (Rec ((a imm 1) (b imm (Perform (Return b Int) 2))))))
  (check-equal?
   (typed-with-normal core '() '() `((h ,function-type)))
   '(Never ((Return b Int)) Int))
  (check-equal?
   (core-type-of core '() '() `((h ,function-type)))
   '(Never ((Return b Int)))))

(test-case "Rec checking は Never 欄の正常型 bottom で owned gate を飛ばす"
  (define parameter-type '(Record ((a (Owned Res) imm))))
  (define function-type `(NFn (,parameter-type) Int () () () User))
  (check-equal?
   (typed-type-normal
    `(Apply h (Rec ((a imm ,ret1))))
    '() '() `((h ,function-type)))
   '(Never Int)))

(test-case "Rec checking は後続の正常な Owned 欄の gate を維持する"
  (define parameter-type '(Record ((a (Owned Res) imm) (b (Owned Res) imm))))
  (define function-type `(NFn (,parameter-type) Int () () () User))
  (check-equal?
   (core-type-of
    `(Apply h (Rec ((a imm ,ret1) (b imm (Apply f 1)))))
    '() '() `((h ,function-type) (f ,owned-function-type)))
   'ill-typed))

(test-case "Record check は欄を期待型で検査し、合成の拒否は保つ"
  (define record '(Rec ((a imm (Error 0)))))
  (check-true
   (core-check record '((0 Res)) '()
               '(Record ((a Int imm))) '()))
  (check-equal?
   (core-type-of record '((0 Res)) '())
   'ill-typed))

(test-case "UnionInject は注釈で payload を検査し正常型を保つ"
  (check-equal?
   (typed-type-normal
    `(UnionInject (Union Int String) Int ,ret1))
   '(Never (Union Int String))))

(test-case "UnionEliminate は scrutinee の正常型で schema を得る"
  (check-equal?
   (typed-type-normal
    `(UnionEliminate
      ,(never-with-normal '(Union Int String))
      ((Int x -> x) (String y -> 0)))
    )
   '(Never Int)))

(test-case "UnionEliminate は正常型の無い scrutinee を拒否する"
  (check-equal?
   (core-type-of `(UnionEliminate ,ret1 ((Int x -> x) (String y -> 0)))
                 '() '())
   'ill-typed))

(test-case "RecRewrite は target の正常型で結果 record を決める"
  (define record-type '(Record ((a Int imm))))
  (check-equal?
   (typed-type-normal
    `(RecRewrite ,(never-with-normal record-type)
       ((a x Int imm Int x)))
    )
   `(Never ,record-type)))

(test-case "RecRewrite は正常型の無い target を拒否する"
  (check-equal?
   (core-type-of `(RecRewrite ,ret1 ((a x Int imm Int x))) '() '())
   'ill-typed))

(test-case "RecRewriteOpen の未注釈欄は欄の正常型を使う"
  (check-equal?
   (typed-type-normal
    '(RecRewriteOpen ((a imm (Apply h (Perform (Return b Int) 1)))))
    '() '() `((h ,int-function-type)))
   '(Never (Record ((a Int imm))))))

(test-case "RecRewriteOpen の未注釈欄は正常型 bottom を伝える"
  (check-equal?
   (typed-type-normal `(RecRewriteOpen ((a imm ,ret1))) '() '())
   '(Never ⊥)))

(test-case "RecRewriteOpen は bottom 欄の後ろの欄の誤りを報告する"
  (check-equal?
   (core-type-of
    `(RecRewriteOpen ((a imm ,ret1) (b imm (Apply f unit))))
    '() test-callables)
   'ill-typed))

(test-case "RecRewriteOpen の注釈つき欄は bottom を検査型で受理する"
  (check-equal?
   (typed-type-normal `(RecRewriteOpen ((a imm Int ,ret1))))
   '(Never (Record ((a Int imm))))))

(test-case "Proj は receiver の正常型から欄型を得る"
  (check-equal?
   (typed-type-normal
    `(Proj ,(never-with-normal '(Record ((a Int imm)))) a))
   '(Never Int)))

(test-case "Proj は bottom の receiver で未知 label を診断しない"
  (check-equal? (typed-type-normal `(Proj ,ret1 nosuch)) '(Never ⊥)))

(test-case "ProjOpt は receiver の正常型から optional 欄型を得る"
  (check-equal?
   (typed-type-normal
    `(ProjOpt Int ,(never-with-normal '(Record ((a Int imm opt)))) a))
   '(Never (Option Int))))

(test-case "ProjOpt は bottom の receiver で欄を参照しない"
  (check-equal?
   (typed-type-normal `(ProjOpt Int ,ret1 nosuch))
   '(Never ⊥)))

(test-case "ProjOpt は正常型の定まる receiver の required 欄を Option で受理する"
  (check-equal?
   (typed-type-normal
    `(ProjOpt Int ,(never-with-normal '(Record ((a Int imm)))) a)
    '() '())
   '(Never (Option Int))))

(test-case "ProjOpt は正常型の定まる receiver の注釈の不一致を拒否する"
  (check-equal?
   (core-type-of
    `(ProjOpt Bool ,(never-with-normal '(Record ((a Int imm opt)))) a)
    '() '())
   'ill-typed))

(test-case "Reborrow と Read は正常型 bottom の receiver を拒否する"
  (check-equal? (core-type-of `(ReborrowAt rho ,ret1) '() '()) 'ill-typed)
  (check-equal? (core-type-of `(Read ,ret1) '() '()) 'ill-typed))

(test-case "Assign は正常型 bottom の target を拒否する"
  (check-equal? (core-type-of `(Assign ,ret1 1) '() '()) 'ill-typed))

(test-case "Reassign は値の注釈型で Never を受ける"
  (check-equal?
   (typed-type-normal
    `(Let (x mut Int) 1 (Reassign x Int ,ret1)))
   '(Never ⊥)))

(test-case "RegionApp は正常型 bottom の関数位置を拒否する"
  (check-equal? (core-type-of `(RegionApp ,ret1 ()) '() '()) 'ill-typed))

(test-case "borrow と pointer の各 shape 位置は bottom を拒否する"
  (check-equal? (core-type-of `(ProjBorrowAt rho ,ret1 a) '() '())
                'ill-typed)
  (check-equal? (core-type-of `(AddressOf ,ret1) '() '()) 'ill-typed)
  (check-equal? (core-type-of `(PtrOffset ,ret1 1) '() '()) 'ill-typed)
  (check-equal? (core-type-of `(RawLoad ,ret1) '() '()) 'ill-typed)
  (check-equal? (core-type-of `(Unsafe (RawLoad ,ret1)) '() '()) 'ill-typed)
  (check-equal? (core-type-of `(RawStore ,ret1 1) '() '()) 'ill-typed)
  (check-equal? (core-type-of `(FromRawPtr ,ret1 rho) '() '()) 'ill-typed))

(test-case "Unsafe は本体の Never の正常型を伝える"
  (check-equal?
   (typed-type-normal
    `(Unsafe (Apply ,(never-with-normal '(NFn (Int) Int () () () User)) 1)))
   '(Never Int)))

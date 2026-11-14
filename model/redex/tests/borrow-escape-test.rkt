#lang racket

;; [REQ: BOR-001] 借用は所有者の region を超えて生きられない。

(require rackunit
         racket/match
         "../borrow-gen.rkt"
         "../diagnostic.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../gen.rkt"
         "../typing.rkt")

;; 内側 Scope の結果は外側 owner の生存中に消費できる。
;; borrow.md §9 が退けたのは内側の出口だけで拒否する案であり、
;; owner の Scope を越える借用の拒否は維持する。
(let ()
  (define core '(Scope (1) (Read (Scope () (Borrow 1)))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal?
   (first (type-of/raw annotated (list (list 1 'Res)) '() '()
                       (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'ok))

;; 内側 Scope が管理する所有値を借りて外へ返す形は弾く。
(let ()
  (define core '(Scope () (Scope (1) (Borrow 1))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define result
    (type-of/raw annotated (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '(0))) (hash))))
  (match result
    [(list 'fail 'borrow-escapes-owner node _)
     ;; key だけでなく、破れた outlives 制約の node が Borrow であることを確認する。
     (check-true (match node [`(BorrowAt ,_ ,_ 1) #t] [_ #f]))]
    [_ (fail (format "expected borrow-escapes-owner at Borrow node, got ~s" result))]))

;; Scope 終了時は関数型だけでなく、捕捉した借用の来歴も調べる。
(define captured-closure-type
  '(NFn (Int) Int () ((Yield (Borrowed Int (RParam a)))) () User))
(define opaque-captured-closure-type
  '(NFn (Int) Int () () () User))
(define captured-maker-type
  `(ForallRegion (a)
     (NFn ((Borrowed Int (RParam a))) ,captured-closure-type () () () User)))
(define captured-maker
  '(RegionLam (a)
     (Lam User maker (p)
       (Lam User captured (q) (Read p)))))
(define opaque-captured-maker-type
  `(ForallRegion (a)
     (NFn ((Borrowed Int (RParam a))) ,opaque-captured-closure-type () () () User)))
(define opaque-closure-environment
  `((opaque-closure ,opaque-captured-closure-type)))
(define opaque-closure-identity-type
  `(NFn (,opaque-captured-closure-type)
        ,opaque-captured-closure-type () () () User))
(define no-capture-closure-type
  '(ForallRegion (a)
     (NFn (Int) Int () ((Yield (Borrowed Int (RParam a)))) () User)))
(define closure-identity-type
  '(ForallRegion (b)
     (NFn ((NFn (Int) Int () ((Yield (Borrowed Int (RParam b)))) () User))
          (NFn (Int) Int () ((Yield (Borrowed Int (RParam b)))) () User)
          () () () User)))
(define closure-identity
  '(RegionLam (b) (Lam User identity (f) f)))
(define captured-closure-type/owner
  '(NFn (Int) Int () ((Yield (Borrowed Int owner-ph))) () User))
(define capture-callables
  `((maker ,captured-maker-type)
    (captured ,captured-closure-type)
    (opaque-maker ,opaque-captured-maker-type)
    (opaque-captured ,opaque-captured-closure-type)
    (identity ,closure-identity-type)
    (opaque-identity ,opaque-closure-identity-type)
    (pure ,no-capture-closure-type)))

(define (typed-owner-core core [callables capture-callables] [environment '()]
                          [places '((1 Int))])
  (define ir (build-region-ir core))
  (define owner-rho (region->rho ir (region-at ir '())))
  (core-type-of/regions
   (replace-owner-region (fill-region-placeholders core ir) owner-rho)
   (replace-owner-region places owner-rho)
   (replace-owner-region callables owner-rho)
   (replace-owner-region environment owner-rho)
   #:ir ir))

(define (replace-owner-region term rho)
  (cond
    [(eq? term 'owner-ph) rho]
    [(pair? term)
     (cons (replace-owner-region (car term) rho)
           (replace-owner-region (cdr term) rho))]
    [else term]))

(define (capture-expression)
  '(Apply (RegionApp
           (RegionLam (a)
             (Lam User maker (p)
               (Lam User captured (q) (Read p))))
           (owner-ph))
          (Borrow 1)))

(define (opaque-closure-expression)
  'opaque-closure)

(define (opaque-identity-expression)
  '(Apply (Lam User opaque-identity (f) f) opaque-closure))

(define (invalid-hidden-capture-expression)
  '(Apply (RegionApp
           (RegionLam (a)
             (Lam User opaque-maker (p)
               (Lam User opaque-captured (q) (Read p))))
           (owner-ph))
          (Borrow 1)))

(define (capture-call-expression)
  `(Apply
    (RegionApp
     (RegionLam (a)
       (Lam User invoke (p)
         (Let (captured let ,captured-closure-type)
              (Lam User captured (q) (Read p))
           (Apply captured 0))))
     (ph))
    (Borrow 1)))

(define (identity-expression value)
  `(Apply (RegionApp ,closure-identity (owner-ph)) ,value))

(define (capture-return payload)
  `(Perform (Return boundary ,captured-closure-type/owner) ,payload))

(define capture-return-consumer-type
  `(ForallRegion (a)
     (NFn ((NFn (Int) Int () ((Yield (Borrowed Int (RParam a)))) () User))
          Int () () () User)))

(define (capture-return-consumer-apply)
  `(Apply (RegionApp
           (RegionLam (a) (Lam User consume (callback) 0))
           (owner-ph))
          ,(capture-return (capture-expression))))

(define (scope-return-handler body)
  `(Handle (Return boundary ,captured-closure-type/owner)
           (returned -> 0)
           ,body))

(define capture-box-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((CaptureBox (A) ((box ((Param A))))))
   #:fail (lambda (reason kind key)
           (error 'borrow-escape-test "~s ~s ~s" reason kind key))))

(define (with-capture-box thunk)
  (call-with-trait-ledger capture-box-ledger thunk))

(define (check-region-typed result)
  (check-true (region-typed? result) (format "型付け結果: ~s" result)))

(define (check-diagnostic-id result id)
  (check-true (diagnostic? result)
              (format "期待した診断 ~a、結果 ~a"
                      id (if (diagnostic? result) (diagnostic-id result) 'accepted)))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) id
                  (format "diagnostic result: ~s" result))))

(test-case "捕捉した閉包を Let の変数として owner Scope 外へ返すと E-BOR-004"
  (define core
    `(Scope (1)
       (Let (captured let ,captured-closure-type/owner)
             ,(capture-expression)
         captured)))
  (check-diagnostic-id (typed-owner-core core) "E-BOR-004"))

(test-case "捕捉した閉包の Apply 結果を owner Scope 外へ直接返すと E-BOR-004"
  (define core `(Scope (1) ,(capture-expression)))
  (check-diagnostic-id (typed-owner-core core) "E-BOR-004"))

(test-case "捕捉した閉包は owner Scope 内で呼び結果だけを返せる"
  (define invoke-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) Int ()
            ((Yield (Borrowed Int (RParam a)))) () User)))
  (check-region-typed
   (typed-owner-core `(Scope (1) ,(capture-call-expression))
                     (append capture-callables `((invoke ,invoke-type))))))

(test-case "閉包の実引数を恒等関数に通して Scope 外へ返す経路も捕捉を検査する"
  (define core
    `(Scope (1) ,(identity-expression (capture-expression))))
  (check-diagnostic-id (typed-owner-core core) "E-BOR-004"))

(test-case "Scope 外で束縛した関数値を Apply の結果として返しても inner owner を捕捉しない"
  (check-region-typed
   (typed-owner-core `(Scope (1) ,(opaque-identity-expression))
                     capture-callables
                     opaque-closure-environment)))

(test-case "捕捉しない RegionLam は owner を管理する Scope から恒等関数越しに返せる"
  (define core
    `(Scope (1)
       ,(identity-expression
         '(RegionApp (RegionLam (a) (Lam User pure (q) 0)) (ph)))))
  (check-region-typed (typed-owner-core core)))

(test-case "owner を管理しない Scope は関数値を返してよい"
  (check-region-typed
   (core-type-of/regions
    '(Scope () (RegionLam (a) (Lam User pure (p) 0)))
    '() capture-callables)))

(test-case "if 相当の Eliminate は捕捉しない枝同士なら閉包を返せる"
  (define core
    `(Scope (1)
       (Apply
         (RegionApp
          (RegionLam (a)
            (Lam User choose (p flag)
              (Eliminate (Construct Bool true)
                ((true () -> (Lam User pure-left (q) 0))
                 (false () -> (Lam User pure-right (q) 1))))))
          (ph))
         (Borrow 1)
         (Construct Bool true))))
  (define callables
    (append capture-callables
            `((choose
               (ForallRegion (a)
                 (NFn ((Borrowed Int (RParam a)) Bool)
                      ,captured-closure-type () () () User)))
              (pure-left ,captured-closure-type)
              (pure-right ,captured-closure-type))))
  (check-region-typed (typed-owner-core core callables)))

(test-case "Eliminate の一方の閉包枝が owner を捕捉すれば escape は E-BOR-004"
  (define core
    `(Scope (1)
       (Eliminate flag
         ((true () -> (Lam User pure-left (q) 0))
          (false () -> ,(capture-expression))))))
  (define callables
    (append capture-callables
            `((pure-left ,captured-closure-type/owner))))
  (check-diagnostic-id
   (typed-owner-core core callables '((flag Bool)))
   "E-BOR-004"))

(test-case "owner region を実体化した Return payload の捕捉閉包は Scope を越えて出せない"
  (define core
    (scope-return-handler
     `(Scope (1) ,(capture-return (capture-expression)))))
  (check-diagnostic-id (typed-owner-core core) "E-BOR-004"))

(test-case "Let の束縛式にある Perform(Return) の capture も Scope 脱出 E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    (scope-return-handler
     `(Scope (1)
        (Let (ignored const Never)
             ,(capture-return (capture-expression))
          0))))
   "E-BOR-004"))

(test-case "Eliminate の一枝にある Perform(Return) の capture も Scope 脱出 E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (Eliminate (Construct Bool true)
         ((true () -> ,(capture-return-consumer-apply))
          (false () -> 0))))
    (append capture-callables
            `((consume ,capture-return-consumer-type))))
   "E-BOR-004"))

(test-case "Apply の実引数にある Perform(Return) の capture も Scope 脱出 E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    (scope-return-handler
     `(Scope (1)
        ,(capture-return-consumer-apply)))
    (append capture-callables
            `((consume ,capture-return-consumer-type))))
   "E-BOR-004"))

(test-case "型に捕捉 region が現れる closure を Record 欄から Scope 外へ出す"
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (Rec ((callback imm ,(capture-expression))))))
   "E-BOR-004"))

(test-case "Record 欄の捕捉 closure を Scope 内で射影して外へ出す"
  (define record-type
    `(Record ((callback ,captured-closure-type/owner imm))))
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (Let (holder let ,record-type)
            (Rec ((callback imm ,(capture-expression))))
         (Proj holder callback))))
   "E-BOR-004"))

(test-case "型に捕捉 region が現れる closure を UnionInject から Scope 外へ出す"
  (define union-type `(Union ,captured-closure-type/owner Int))
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (UnionInject ,union-type ,captured-closure-type/owner
                    ,(capture-expression)))
    capture-callables)
   "E-BOR-004"))

(test-case "Scope 外で束縛した関数値を Record 欄に入れても inner owner を捕捉しない"
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (Rec ((callback imm ,(opaque-closure-expression)))))
    capture-callables
    opaque-closure-environment)))

(test-case "owner を型に持たない実捕捉 closure は Scope 検査より先に E-BOR-011"
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       ,(invalid-hidden-capture-expression)))
   "E-BOR-011"))

(test-case "Scope 外の関数値を Record の射影経由で運んでも inner owner を捕捉しない"
  (define record-type
    `(Record ((callback ,opaque-captured-closure-type imm))))
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (Let (holder let ,record-type)
            (Rec ((callback imm ,(opaque-closure-expression))))
         (Proj holder callback)))
    capture-callables
    opaque-closure-environment)))

(test-case "Scope 外で束縛した関数値を Union 欄から返しても inner owner を捕捉しない"
  (define union-type `(Union ,opaque-captured-closure-type Int))
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (UnionInject ,union-type ,opaque-captured-closure-type
                    ,(opaque-closure-expression)))
    capture-callables
    opaque-closure-environment)))

(define (loop-leave-core handler-inside-scope?)
  (define leave
    `(Perform (Return leave-boundary ,captured-closure-type/owner)
              ,(capture-expression)))
  (if handler-inside-scope?
      `(Scope (1)
         (Handle (Return leave-boundary ,captured-closure-type/owner)
                 (returned -> (Apply returned 0))
                 ,leave))
      `(Handle (Return leave-boundary ,captured-closure-type/owner)
         (returned -> returned)
         (Scope (1) ,leave))))

(define loop-leave-callables
  (append capture-callables `((returned ,captured-closure-type/owner))))

(test-case "Loop Leave の Return payload を外側 handler へ運ぶと Scope 脱出の E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core (loop-leave-core #f)
                     loop-leave-callables)
   "E-BOR-004"))

(test-case "既存の縮約 (Task 2c0b): owner Scope 内の handler binder から捕捉閉包を呼ぶと E-BOR-020"
  ;; Perform payload の callable summary が handler binder へ渡らない既存経路。
  (check-diagnostic-id
   (typed-owner-core (loop-leave-core #t)
                     loop-leave-callables)
   "E-BOR-020"))

(define recur-int-signature '(NFn () Int () () () User))
(define recur-int-callables
  (append capture-callables `((recur-int ,recur-int-signature))))

(test-case "Recur の継続結果として捕捉閉包を返すと E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (Recur recur-int loop () 0 ,(capture-expression)))
    recur-int-callables)
   "E-BOR-004"))

(test-case "RecurVal の latent Return は呼ばない限り Scope 出口に数えない"
  (define recursive-type
    `(NFn () Int ()
          ((Return boundary ,captured-closure-type/owner)) () User))
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (Recur recursive-return loop ()
         ,(capture-return (capture-expression))
         0))
    (append capture-callables `((recursive-return ,recursive-type))))))

(test-case "RecurVal の呼出しで生じる Perform(Return) は Scope 出口 E-BOR-004"
  (define recursive-type
    `(NFn () Int ()
          ((Return boundary ,captured-closure-type/owner)) () User))
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (Recur recursive-return loop ()
         ,(capture-return (capture-expression))
         (Apply loop)))
    (append capture-callables `((recursive-return ,recursive-type))))
   "E-BOR-004"))

(test-case "Recur の同じ継続位置で捕捉しない関数値を返せる"
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (Recur recur-int loop () 0
         (RegionApp
          (RegionLam (a) (Lam User pure (q) 1))
          (owner-ph))))
    recur-int-callables)))

(test-case "Scope 内の handler が Return payload を消費すれば capture は escape しない"
  (define core
    `(Scope (1)
       (Handle (Return boundary ,captured-closure-type/owner)
          (returned -> (Lam User discard (q) 0))
          (Perform (Return boundary ,captured-closure-type/owner)
                   ,(capture-expression)))))
  (check-region-typed
   (typed-owner-core core
                     (append capture-callables
                             `((discard ,captured-closure-type/owner))))))

(test-case "Unsafe の子にある Perform(Return) も Scope 脱出 E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    (scope-return-handler
     `(Scope (1) (Unsafe ,(capture-return (capture-expression)))))
    capture-callables)
   "E-BOR-004"))

(test-case "Yield payload 内の Perform(Return) も Scope 脱出 E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    (scope-return-handler
     `(Scope (1)
        (Yield 0 ,(capture-return (capture-expression)))))
    capture-callables)
   "E-BOR-004"))

(test-case "Read した外部 owner の関数値は無関係な managed owner から独立"
  (define external-function-type '(NFn () Int () () () User))
  (check-region-typed
   (typed-owner-core
    '(Scope (1) (Read (Borrow 2)))
    capture-callables '()
    `((1 Int) (2 ,external-function-type)))))

(test-case "Scope 内で借りた owner 参照 closure の Read は capture provenance を保つ"
  (define function-type '(NFn () Int () () () User))
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (Let (captured let (Owned ,function-type))
            (Lam User direct-owner () (Read (Borrow 1)))
         (Let (borrowed let (Borrowed ,function-type ph))
              (Borrow captured)
           (Read borrowed))))
    `((direct-owner ,function-type)))
   "E-BOR-004"))

(test-case "Scope 内で借りた非捕捉閉包の Read は独立"
  (define function-type '(NFn (Int) Int () () () User))
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (Let (plain let (Owned ,function-type))
            (Lam User plain (x) x)
         (Let (borrowed let (Borrowed ,function-type ph))
              (Borrow plain)
           (Read borrowed))))
    `((plain ,function-type)))))

(test-case "管理 owner 自身から Read した関数値は provenance unknown のため E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    '(Scope (1) (Read (Borrow 1)))
    capture-callables '()
    `((1 ,opaque-captured-closure-type)))
   "E-BOR-004"))

(test-case "heap closure が Scope 管理 owner を参照していれば Move 脱出を拒否する"
  (define function-type '(NFn () Int () () () User))
  (define core '(Scope (0 1) (Move 0)))
  (define ir (build-region-ir core))
  (define callables `((heap-reader ,function-type)))
  (define (config closure)
    `(cfg ,core
          ((0 ,closure (declared ,function-type))
           (1 23 (declared Int)))
          ((0 Available) (1 Available)) () ()))
  (define (type-failure-key closure)
    (match
        (with-config-typing
         (lambda ()
           (type-of/raw core `((0 ,function-type) (1 Int)) callables))
         #:region-ir ir
         #:heap-values `((0 ,closure) (1 23)))
      [(list 'fail key _node _details ...) key]
      [_ #f]))
  (define (check-config closure escapes?)
    (define cfg (config closure))
    (define row (runtime-row cfg callables function-type #:region-ir ir))
    (if escapes?
        (begin
          (check-eq? (type-failure-key closure) 'borrow-escapes-owner)
          (check-false row "heap capture は runtime-row の再型付けで拒否する")
          (check-false (config-ok? cfg callables function-type '(Own)
                                  #:region-ir ir)
                       "config-ok? も heap capture を拒否する"))
        (begin
          (check-equal? row '(Own))
          (check-true (config-ok? cfg callables function-type row
                                  #:region-ir ir)))))
  ;; BorrowAt は実行 Core の注釈形。裸の Borrow は config の region IR なしでは
  ;; 型付けできないため、この形で place 1 への参照を表す。
  (check-config
   '(Lam User heap-reader () (Read (BorrowAt 0 (Own 1 ()) 1)))
   #t)
  (check-config
   '(Lam User heap-reader () (Read (BorrowRef 1 () 0)))
   #t)
  (check-config '(Lam User heap-reader () 17) #f))

(test-case "管理 owner の未更新値を Move するだけでは借用捕捉にならない"
  (check-region-typed
   (typed-owner-core
    '(Scope (1) (Move 1))
    capture-callables '()
    `((1 ,opaque-captured-closure-type)))))

(test-case "BorrowMut Assign で owner に格納した捕捉閉包も Read 後に E-BOR-004"
  (define storable-closure-type
    '(NFn (Int) Int () (Partial (Yield (Borrowed Int owner-ph))) () User))
  (define storable-closure-formal-type
    '(NFn (Int) Int () (Partial (Yield (Borrowed Int (RParam a)))) () User))
  (define storable-maker-type
    `(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a)))
            (NFn (Int) Int () (Partial (Yield (Borrowed Int (RParam a))))
                 () User)
            () () () User)))
  (define core
    '(Scope (1 2)
       (Let (written const Unit)
            (Assign (BorrowMut 1)
              (Apply
               (RegionApp
                (RegionLam (a)
                  (Lam User storable-maker (p)
                    (Lam User stored-callback (q) (Read p))))
                (owner-ph))
               (Borrow 2)))
         (Read (Borrow 1)))))
  (check-diagnostic-id
   (typed-owner-core core
                     `((storable-maker ,storable-maker-type)
                       (stored-callback ,storable-closure-formal-type))
                     '()
                     `((1 ,storable-closure-type) (2 Int)))
   "E-BOR-004"))

(test-case "外側 BorrowMut slot への捕捉閉包 Assign は E-BOR-022 の type gate で止まる"
  (define core
    '(Scope (2)
       (Scope (1)
         (Assign (BorrowMut 2)
           (Apply
            (RegionApp
             (RegionLam (a)
               (Lam User maker (p)
                 (Lam User captured (q) (Read p))))
             (owner-ph))
            (Borrow 1))))))
  (define ir (build-region-ir core))
  (define local-rho (region->rho ir (region-at ir '(0))))
  (define outer-rho (region->rho ir (region-at ir '())))
  (define closure-type
    `(NFn (Int) Int () ((Yield (Borrowed Int ,outer-rho))) () User))
  (define maker-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a)))
            (NFn (Int) Int () ((Yield (Borrowed Int (RParam a)))) () User)
            () () () User)))
  (define captured-type
    '(NFn (Int) Int () ((Yield (Borrowed Int (RParam a)))) () User))
  (define core*
    (replace-owner-region core local-rho))
  (define places `((1 Int) (2 ,closure-type)))
  (define owners (hash 1 (region-at ir '(0))
                       2 (region-at ir '())))
  (define result
    (type-of/raw (annotate-regions core* ir) places
                 `((maker ,maker-type) (captured ,captured-type)) '()
                 (region-ctx ir '() owners (hash))))
  (check-equal? (match result
                  [(list 'fail key _node _details ...) key]
                  [_ #f])
                'assign-union-variant
                (format "外側 slot への書込み gate: ~s" result)))

(test-case "借用 region を含む callable 型の mut slot 宣言は E-VAR-009"
  (check-diagnostic-id
   (typed-owner-core
    `(Scope (1)
       (Let (slot mut ,captured-closure-type/owner) 0 0)))
   "E-VAR-009"))

(test-case "実際の捕捉閉包を Owned に入れる形は E-OWN-022"
  (define core
    `(Scope (1)
       (Let (stored let (Owned ,captured-closure-type/owner))
             ,(capture-expression)
         0)))
  (check-diagnostic-id (typed-owner-core core) "E-OWN-022"))

(test-case "Construct の値を Eliminate binder から返すと capture provenance を追う"
  (with-capture-box
   (lambda ()
     (check-diagnostic-id
      (typed-owner-core
       `(Scope (1)
          (Eliminate
           (Construct (Data CaptureBox (,captured-closure-type/owner)) box
                      ,(capture-expression))
           ((box (f) -> f))))
       capture-callables)
      "E-BOR-004"))))

(test-case "Scope の owner と無関係な外部 Apply の関数結果は fail-closed にしない"
  (define result-type '(NFn (Int) Int () () () User))
  (define maker-type `(NFn () ,result-type () () () User))
  (check-region-typed
   (typed-owner-core `(Scope (1) (Apply mk))
                     capture-callables `((mk ,maker-type))))
  (check-region-typed
   (typed-owner-core `(Scope (1) (Apply mk2 5))
                     capture-callables
                     `((mk2 (NFn (Int) ,result-type () () () User)))))
  (define outer-type
    `(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) ,result-type () () () User)))
  (check-diagnostic-id
   (typed-owner-core `(Scope (1)
                       (Apply (RegionApp outer (owner-ph)) (Borrow 1)))
                     capture-callables `((outer ,outer-type)))
   "E-BOR-004"))

(test-case "owner と無関係な外部 union の枝 binder は Scope 脱出に数えない"
  (define outside-union
    `(Union ,opaque-captured-closure-type Int))
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (UnionEliminate outside
         ((,opaque-captured-closure-type callback -> callback)
          (Int ignored
               -> (Lam User union-other (argument) argument)))))
    (append capture-callables
            `((union-other ,opaque-captured-closure-type)))
    `((outside ,outside-union)))))

(test-case "捕捉しない Curry は owner Scope から返せる"
  (define core
    `(Scope (1)
       (Curry
        (Lam User make-closure (fixed rest)
          (Lam User produced (argument) argument))
        5)))
  (check-region-typed
   (typed-owner-core
    core
    (append capture-callables
            `((make-closure
               (NFn (Int Int) ,opaque-captured-closure-type () () () User))
              (produced ,opaque-captured-closure-type))))))

(test-case "Absent を含む optional 関数欄の ProjOpt は捕捉しない"
  (define core
    `(Scope (1)
       (ProjOpt ,opaque-captured-closure-type
                (Rec ((callback imm
                               (Absent ,opaque-captured-closure-type))))
                callback)))
  (check-region-typed (typed-owner-core core)))

(test-case "RecRewrite で置き換えた捕捉しない関数欄は Scope 外へ出せる"
  (define core
    `(Scope (1)
       (RecRewrite
        (Rec ((callback imm
                       (Lam User old-callback (argument) argument))))
        ((callback old-callback ,opaque-captured-closure-type imm
                   ,opaque-captured-closure-type
                   (Lam User new-callback (argument) argument))))))
  (check-region-typed
   (typed-owner-core
    core
    (append capture-callables
            `((old-callback ,opaque-captured-closure-type)
              (new-callback ,opaque-captured-closure-type))))))

(test-case "Untrusted/Refined の関数ペイロードの provenance は透明に運ぶ"
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (UVal (Lam User untrusted-pure (argument) argument)))
    (append capture-callables
            `((untrusted-pure ,opaque-captured-closure-type)))))
  (check-region-typed
   (typed-owner-core
    `(Scope (1)
       (RVal (ProofRep User (Prop Valid))
             (Lam User refined-pure (argument) argument)))
    (append capture-callables
            `((refined-pure ,opaque-captured-closure-type))))))

(test-case "枝で合流した Record を Proj して捕捉閉包を返すと E-BOR-004"
  (define record-type
    `(Record ((callback ,captured-closure-type/owner imm))))
  (define core
    `(Scope (1)
       (Let (holder let ,record-type)
            (Eliminate flag
              ((true () -> (Rec ((callback imm ,(capture-expression)))))
               (false () -> (Rec ((callback imm ,(capture-expression)))))))
         (Proj holder callback))))
  (check-diagnostic-id
   (typed-owner-core core capture-callables '((flag Bool)))
   "E-BOR-004"))

(test-case "枝で合流した Record を ProjOpt して捕捉閉包を返すと E-BOR-004"
  (define core
    `(Scope (1)
       (ProjOpt ,captured-closure-type/owner
         (Eliminate flag
           ((true () -> (Rec ((callback imm ,(capture-expression)))))
            (false () -> (Rec ((callback imm ,(capture-expression)))))))
         callback)))
  (check-diagnostic-id
   (typed-owner-core core capture-callables '((flag Bool)))
   "E-BOR-004"))

(test-case "opaque Apply の Record 結果を Proj して実引数の capture を返すと E-BOR-004"
  (define function-type '(NFn (Int) Int () () () User))
  (define record-type `(Record ((callback ,function-type imm))))
  (define maker-type
    `(NFn (,function-type) ,record-type () () () User))
  (define core
    `(Scope (1)
       (Proj
        (Apply opaque-record-maker
               (Lam User direct-owner-argument (q) (Read (Borrow 1))))
        callback)))
  (check-diagnostic-id
   (typed-owner-core core
                     (append capture-callables
                             `((direct-owner-argument ,function-type)))
                     `((opaque-record-maker ,maker-type)))
   "E-BOR-004"))

(test-case "Move で外部 function place を渡しても managed owner に帰属しない"
  (define places `((1 Int) (2 ,opaque-captured-closure-type)))
  (check-region-typed
   (typed-owner-core '(Scope (1) (Move 2)) capture-callables '() places)))

(test-case "両枝 Borrow join 後の Read は更新済み owner の関数値を追う"
  (define external-type '(NFn () Int () (Partial (Yield Int)) () User))
  (define core
    '(Scope (1)
       (Let (written const Unit)
            (Assign (BorrowMut 1) outside-function)
         (Read
          (Eliminate flag
            ((true () -> (Borrow 1))
             (false () -> (Borrow 1))))))))
  (check-region-typed
   (typed-owner-core core capture-callables
                     `((outside-function ,external-type) (flag Bool))
                     `((1 ,external-type)))))

(test-case "Lam が整数 managed owner を本体から直接借りると E-BOR-004"
  (check-diagnostic-id
   (typed-owner-core
    '(Scope (1) (Lam User direct-owner (q) (Read (Borrow 1))))
    `((direct-owner (NFn (Int) Int () () () User))))
   "E-BOR-004"))

(test-case "RecRewrite entry の Lam が整数 managed owner を直接借りると E-BOR-004"
  (define function-type '(NFn (Int) Int () () () User))
  (define core
    `(Scope (1)
       (RecRewrite
        (Rec ((callback imm (Lam User old-callback (argument) argument))))
        ((callback old-callback ,function-type imm ,function-type
          (Lam User direct-owner-in-rewrite (argument) (Read (Borrow 1))))))))
  (check-diagnostic-id
   (typed-owner-core core
                     `((old-callback ,function-type)
                       (direct-owner-in-rewrite ,function-type)))
   "E-BOR-004"))

(test-case "外部 symbol owner は Scope 管理 place にならず E-BOR-006 が先行する"
  (check-diagnostic-id
   (typed-owner-core
    '(Scope (1) (Lam User symbol-owner (q) (Read (Borrow x))))
    `((symbol-owner (NFn (Int) Int () () () User)))
    '((x (Owned Int))))
   "E-VAR-006"))

#lang racket/base

;; G5c5b3b。値の内部の所有資源へ token を割り当てる producer 経路の回帰。
(require racket/match
         rackunit
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../borrow.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../typing.rkt"
         "../span-core.rkt"
         "../annotate.rkt"
         "../erase.rkt"
         "../elaborate.rkt")

(define (step config)
  (define results (apply-reduction-relation -->g1 config))
  (check-equal? (length results) 1
                (format "一手だけ進む: ~s" results))
  (car results))

(test-case "R-OwnLeaf は payload を OwnedLeaf へ置き換え Λtok へ Available を足す"
  (check-equal?
   (step (term (cfg (OwnLeaf (resource 1)) () () () ())))
   (term (cfg (OwnedLeaf (tok 0) (resource 1)) () () (((tok 0) Available)) ()))))

(test-case "R-OwnLeaf は Dropped の tombstone の番号を再利用しない"
  (check-equal?
   (step (term (cfg (OwnLeaf (resource 1)) () () (((tok 0) Dropped)) ())))
   (term (cfg (OwnedLeaf (tok 1) (resource 1)) () ()
              (((tok 0) Dropped) ((tok 1) Available)) ()))))

(test-case "R-OwnLeaf は Λtok に無い制御項の token も避ける"
  (check-equal?
   (step (term (cfg (Apply (OwnLeaf (resource 2))
                           (OwnedLeaf (tok 3) (resource 1)))
                    () () () ())))
   (term (cfg (Apply (OwnedLeaf (tok 4) (resource 2))
                     (OwnedLeaf (tok 3) (resource 1)))
              () () (((tok 4) Available)) ()))))

(test-case "producer 位置でない OwnLeaf は unexpected-ownleaf で落ちる"
  (check-equal? (core-type-of '(OwnLeaf 1) '() '()) 'ill-typed)
  (define diagnostic (core-type-of/diagnostic '(OwnLeaf 1) '() '()))
  (check-true (diagnostic? diagnostic))
  (check-equal? (diagnostic-id diagnostic)
                (diagnostic-code-of 'typing 'unexpected-ownleaf)))

(test-case "Construct の欄の Owned leaf を位置 path 付きで拾う"
  (check-equal?
   (walk-owned-leaves
    '(Construct (Option (Owned Res)) some
                (OwnedLeaf (tok 0) (resource 1))))
   '(((tok 0) (0)))))

(test-case "Construct の欄の Owned leaf は回収走査で辿れる位置である"
  (check-true
   (leaf-positions-ok?
    '(Construct (Option (Owned Res)) some
                (OwnedLeaf (tok 0) (resource 1))))))

(test-case "Construct の入れ子では位置 segment が連結される"
  (check-equal?
   (walk-owned-leaves
    '(Construct (Option (Option (Owned Res))) some
                (Construct (Option (Owned Res)) some
                           (OwnedLeaf (tok 3) (resource 1)))))
   '(((tok 3) (0 0)))))

(test-case "Construct の第 2 欄の位置 segment は 1 である"
  (check-equal?
   (walk-owned-leaves
    '(Construct (Pair Int (Owned Res)) pair
                1
                (OwnedLeaf (tok 5) (resource 1))))
   '(((tok 5) (1)))))

(test-case "Construct の欄の Owned leaf を OwnLeaf で包めば型付く"
  (check-equal?
   (core-type-of
    '(Construct (Option (Owned Res)) some
                (OwnLeaf (OwnedLeaf (tok 0) (resource 1))))
    '() '())
   '((Option (Owned Res)) ())))

(test-case "config の型導出は Construct の OwnedLeaf 欄を受理する"
  (define value
    '(Construct (Option (Owned Res)) some
                (OwnedLeaf (tok 0) (resource 1))))
  (define config
    `(cfg unit ((0 ,value)) ((0 Available)) (((tok 0) Available)) ()))
  (check-true (config-ok? config '() 'Unit '())))

(test-case "Construct 欄の leaf を finalize した trace を受理する"
  (define value
    '(Construct (Option (Owned Res)) some
                (OwnedLeaf (tok 0) (resource 1))))
  (define results
    (apply-reduction-relation
     -->g2
     `(cfg (Scope (0) unit)
           ((0 ,value))
           ((0 Available))
           (((tok 0) Available))
           ())))
  (check-equal? (length results) 1)
  (check-true (config-ok? (car results) '() 'Unit '())))

(test-case "Construct 欄の空 path の finLeaf は拒否する"
  (define value
    '(Construct (Option (Owned Res)) some
                (OwnedLeaf (tok 0) (resource 1))))
  (check-false
   (config-ok?
    `(cfg unit
          ((0 ,value))
          ((0 Dropped))
          (((tok 0) Dropped))
          ((finLeaf 0 ()) (fin 0)))
    '() 'Unit '())))

(test-case "通常の型検査は Construct の OwnedLeaf 欄を受理しない"
  (define core
    '(Construct (Option (Owned Res)) some
                (OwnedLeaf (tok 0) (resource 1))))
  (check-equal? (core-type-of core '() '()) 'ill-typed)
  (define diagnostic (core-type-of/diagnostic core '() '()))
  (check-equal? (diagnostic-id diagnostic)
                (diagnostic-code-of 'typing 'owned-constructor-field)))

(test-case "Construct の Owned 欄が OwnLeaf で包まれていなければ落ちる"
  (define core '(Construct (Option (Owned Res)) some (resource 1)))
  (check-equal? (core-type-of core '() '()) 'ill-typed)
  (define diagnostic (core-type-of/diagnostic core '() '()))
  (check-equal? (diagnostic-id diagnostic)
                (diagnostic-code-of 'typing 'owned-constructor-field)))

(test-case "Construct の Owned でない欄の OwnLeaf は許されない"
  (define core '(Construct (Option Int) some (OwnLeaf 1)))
  (check-equal? (core-type-of core '() '()) 'ill-typed)
  (define diagnostic (core-type-of/diagnostic core '() '()))
  (check-equal? (diagnostic-id diagnostic)
                (diagnostic-code-of 'typing 'unexpected-ownleaf)))

(define (ownleaf-span-in core)
  (cond
    [(and (list? core)
          (>= (length core) 3)
          (eq? (car core) 'OwnLeaf))
     (cadr core)]
    [(list? core)
     (for/or ([child (in-list core)])
       (ownleaf-span-in child))]
    [else #f]))

(define (head-span-in core head)
  (cond
    [(and (list? core)
          (>= (length core) 2)
          (eq? (car core) head))
     (cadr core)]
    [(list? core)
     (for/or ([child (in-list core)])
       (head-span-in child head))]
    [else #f]))

(test-case "elaborate の Construct producer は spanful OwnLeaf を生成する"
  (define result
    (elab '(Fn () (Option (Owned Res)) ()
             (Construct some (Apply acquire 1)))))
  (match result
    [(list core _type _row _callables)
     (check-true (redex-match? G2+ c core))
     (define leaf-span (ownleaf-span-in core))
     (define construct-span (head-span-in core 'Construct))
     (check-true (span-ok? leaf-span))
     (check-equal? leaf-span construct-span)]
    [_ (check-true #f (format "elab が失敗した: ~s" result))]))

(test-case "annotate-core は OwnLeaf を spanful G1+ へ持ち上げる"
  (define lifted (annotate-core '(OwnLeaf (resource 1))))
  (check-true (redex-match? G1+ c lifted))
  (check-equal? (erase-core lifted) '(OwnLeaf (resource 1))))

(test-case "CurryVal の固定引数の Owned leaf は位置 1 になる"
  (check-equal?
   (walk-owned-leaves
    '(CurryVal (Own) (PrimVal () add) (OwnedLeaf (tok 2) (resource 1))))
   '(((tok 2) (1)))))

(test-case "CurryVal の固定引数の Owned leaf は回収走査で辿れる位置である"
  (check-true
   (leaf-positions-ok?
    '(CurryVal (Own) (PrimVal () add) (OwnedLeaf (tok 2) (resource 1))))))

(test-case "CurryVal の入れ子では位置 segment が連結される"
  (check-equal?
   (walk-owned-leaves
    '(CurryVal (Own)
               (CurryVal (Own) (PrimVal () add)
                         (OwnedLeaf (tok 4) (resource 1)))
               1))
   '(((tok 4) (0 1)))))

(test-case "Yield の Owned な観測 payload は OwnLeaf で包めば型付く"
  (check-equal?
   (core-type-of '(Yield (OwnLeaf (resource 1)) 1) '() '())
   '(Int ((Yield (Owned Res))))))

(test-case "Yield の Owned な観測 payload が包まれていなければ落ちる"
  (define core '(Yield (resource 1) 1))
  (check-equal? (core-type-of core '() '()) 'ill-typed)
  (define diagnostic (core-type-of/diagnostic core '() '()))
  (check-equal? (diagnostic-id diagnostic)
                (diagnostic-code-of 'typing 'missing-ownleaf-root)))

(test-case "Yield の Owned でない観測 payload の OwnLeaf は許されない"
  (define core '(Yield (OwnLeaf 1) 1))
  (check-equal? (core-type-of core '() '()) 'ill-typed)
  (define diagnostic (core-type-of/diagnostic core '() '()))
  (check-equal? (diagnostic-id diagnostic)
                (diagnostic-code-of 'typing 'unexpected-ownleaf)))

(test-case "θ の obs が持つ leaf の token は live と数える"
  (check-true
   (config-ok? '(cfg 1 () () (((tok 0) Available))
                     ((obs (OwnedLeaf (tok 0) (resource 1)))))
               '()
               'Int
               '())))
  (check-true
   (config-ok? '(cfg (Drop (OwnedLeaf (tok 1) (resource 2)))
                     () () (((tok 1) Available)) ())
               '()
               'Unit
               '(Own)))
  (check-false
   (config-ok? '(cfg (Drop (OwnedLeaf (tok 1) (resource 2)))
                     () () (((tok 1) Available))
                     ((obs (OwnedLeaf (tok 1) (resource 3)))))
               '()
               'Unit
               '(Own)))

(test-case "obs に現れない Available な token は不正である"
  (check-false
   (config-ok? '(cfg 1 () () (((tok 0) Available)) ())
               '()
               'Int
               '())))

(test-case "obs の根が leaf であることは正当である"
  (check-true
   (config-ok? '(cfg 1 () () (((tok 0) Available))
                     ((obs (OwnedLeaf (tok 0) (Rec ((f mut 1)))))))
               '()
               'Int
               '())))

(test-case "未対応の構成子の内部へ隠れた obs の leaf は不正である"
  (check-false
   (config-ok?
    '(cfg 1 () () (((tok 0) Available))
          ((obs (UVal (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))))
    '()
    'Int
    '())))

(test-case "obs の根 leaf の直下の入れ子は不正である"
  (check-false
   (config-ok?
    '(cfg 1 () () (((tok 0) Available) ((tok 1) Available))
          ((obs (OwnedLeaf (tok 0) (OwnedLeaf (tok 1) (resource 1))))))
    '()
    'Int
    '())))

(test-case "Yield の観測 leaf を含む制御項は受理する"
  (check-true
   (config-ok?
    '(cfg (Yield (OwnedLeaf (tok 0) (resource 1)) 1)
          () () (((tok 0) Available)) ())
    '()
    'Int
    '((Yield (Owned Res))))))

(test-case "elaborate の Yield producer は spanful OwnLeaf を生成する"
  (define result
    (elab '(Fn () Int ((Yield (Owned Res)))
             (Yield (Apply acquire 1) 1))))
  (match result
    [(list core type row callables)
     (check-true (redex-match? G2+ c core))
     (check-equal? (core-type-of core '() callables) (list type row))
     (check-equal? (ownleaf-span-in core) (head-span-in core 'Yield))]
    [_ (check-true #f (format "elab が失敗した: ~s" result))]))

(test-case "elaborate の Curry producer は Owned 固定引数を包む"
  (define result
    (elab '(Let p
                (Apply acquire 1)
                (Let g
                     (Fn ((q (Owned Res))) Unit (Own) (Drop q))
                     (Curry g (Move p))))))
  (match result
    [(list core type row callables)
     (check-equal? type '(Owned (NFn () Unit (Own) ())))
     (check-equal? (core-type-of core '() callables) (list type row))
     (check-equal? (ownleaf-span-in core) (head-span-in core 'Curry))]
    [_ (check-true #f (format "elab が失敗した: ~s" result))]))

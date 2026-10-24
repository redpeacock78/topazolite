#lang racket

;; borrow.md §4。可変借用の値の複製は新しい借用ではない。
;; 性質 8 の oracle は同じ値の出現を一つと数え、R-BorrowMut の step で
;; 生存中の借用の再取得を拒否する。

(require rackunit
         racket/match
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define bm '(BorrowedMut Int (RVar 0)))
(define places '((1 Int) (2 Int)))

(define (type-core core [callables '()])
  (define ir (build-region-ir core))
  (define filled (fill-region-placeholders core ir))
  (core-type-of/regions filled places callables #:ir ir))

(define (failure-key result)
  (and (diagnostic? result) (diagnostic-id result)))

(define (runtime-result core [callables '()])
  (define ir (build-region-ir core))
  (define filled (fill-region-placeholders core ir))
  (define typed (core-type-of/regions filled places callables #:ir ir))
  (if (diagnostic? typed)
      (list 'not-run (diagnostic-id typed))
      (let* ([base (inject-g2m (region-execution-core typed))]
             [start
              (match base
                [`(cfg ,control ,_heap ,_omega ,tokens ,trace)
                 `(cfg ,control
                       ,(for/list ([place (in-list places)])
                          (list (first place) (+ 10 (first place))))
                       ,(for/list ([place (in-list places)])
                          (list (first place) 'Available))
                       ,tokens ,trace)])])
        (check-borrow-execution start (region-typed-sidecar typed)
                                (region-typed-ir typed) 300
                                (make-bcounters)))))

(define (pair-core body)
  `(Scope ()
     (Let (pair let (Record ((inner ,bm mut) (other ,bm mut))))
          (Rec ((inner mut (BorrowMut 1)) (other mut (BorrowMut 2))))
       ,body)))

(define a1-core
  `(Scope ()
     (Let (p let ,bm) (BorrowMut 1)
       (Let (u const Unit) (Assign p 1)
         (Assign p 2)))))

(define (a2-core body)
  `(Scope ()
     (Let (p let ,bm) (BorrowMut 1)
       (Let (a let ,bm) p
         (Let (b let ,bm) p
           ,body)))))

(define (b1-core body)
  (pair-core
   `(Let (a let ,bm) (Proj pair inner)
      (Let (b let ,bm) (Proj pair inner)
        ,body))))

(define (check-accepted core [callables '()])
  (define typed (type-core core callables))
  (check-true (region-typed? typed) (format "型検査: ~s" typed))
  (when (region-typed? typed)
    (check-equal? (runtime-result core callables) 'ok)))

(define (check-rejected core key [callables '()])
  (check-equal? (failure-key (type-core core callables)) key))

;; spec §5.1
(test-case "同じ可変借用を通して Assign を二度続ける形を受理する"
  (check-accepted a1-core))

(test-case "同じ可変借用を二つの変数へ束縛して順に Assign する形を受理する"
  (check-accepted
   (a2-core '(Let (u const Unit) (Assign a 1) (Assign b 2)))))

(test-case "record の同じ可変借用欄を二度取り出して順に Assign する形を受理する"
  (check-accepted
   (b1-core '(Let (u const Unit) (Assign a 1) (Assign b 2)))))

(test-case "record の一方の欄を読み、他方の可変借用欄を通して Assign する形を受理する"
  (check-accepted
   (pair-core '(Let (r const Int) (Read (Proj pair inner))
                 (Assign (Proj pair other) 7)))))

(test-case "二つの複製を通す Assign の間に一方を Read する形を受理する"
  (check-accepted
   (a2-core '(Let (u const Unit) (Assign a 1)
               (Let (r const Int) (Read a)
                 (Assign b 2))))))

;; spec §5.2
(test-case "複製の一方から作った子が生きている間に他方を通す Assign は E-BOR-025"
  (check-rejected
   (a2-core '(Let (c let (Borrowed Int (RVar 0))) (Reborrow a)
               (Let (u const Unit) (Assign b 3)
                 (Read c))))
   "E-BOR-025"))

(test-case "同じ欄の二度の取り出しの一方から作った子が生きている間に他方を通す Assign は E-BOR-025"
  (check-rejected
   (b1-core '(Let (c let (Borrowed Int (RVar 0))) (Reborrow a)
               (Let (u const Unit) (Assign b 3)
                 (Read c))))
   "E-BOR-025"))

(define f-callables
  '((f (ForallRegion (a)
         (NFn ((BorrowedMut Int (RParam a)) (BorrowedMut Int (RParam a)))
              Unit () (Mutation) () User)))))

(define f-body-core
  '(Scope ()
     (RegionLam (a)
       (Lam User f (x y)
         (Let (c let (Borrowed Int (RParam a))) (Reborrow x)
           (Let (u const Unit) (Assign y 3)
             (Let (r const Int) (Read c) unit)))))))

(test-case "二つの可変借用の仮引数の一方から子を作り他方を通して書く関数の本体を受理する"
  (check-true (region-typed? (type-core f-body-core f-callables))))

(define (f-callable-term)
  `(RegionApp
    (RegionLam (a)
      (Lam User f (x y)
        (Let (c let (Borrowed Int (RParam a))) (Reborrow x)
          (Let (u const Unit) (Assign y 3)
            (Let (r const Int) (Read c) unit)))))
    ((RVar 0))))

(test-case "同じ借用の二つの複製を二つの可変借用の実引数へ渡す呼出しは E-BOR-025"
  (check-rejected
   (a2-core `(Apply ,(f-callable-term) a b))
   "E-BOR-025" f-callables))

(test-case "同じ可変借用の変数を二つの可変借用の実引数へ渡す呼出しは E-BOR-025"
  (check-rejected
   `(Scope ()
      (Let (p let ,bm) (BorrowMut 1)
        (Apply ,(f-callable-term) p p)))
   "E-BOR-025" f-callables))

;; spec §5.3。1 は borrow-oracle-check-test.rkt の反転した試験が担う。
(test-case "重なる別々の可変借用は check-mut-exclusive で mut-not-exclusive になる"
  (match (check-mut-exclusive
          '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 0)
                                   (Read (BorrowMutRef 0 () 1))))
                ((0 (resource 1000))) ((0 Available)) () ()))
    [(list 'fail reason (list a b))
     (check-equal? reason 'mut-not-exclusive)
     (check-not-equal? a b)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "可変借用とその reborrow の子が生きていると reborrow-parent-live になる"
  (define parent '(mut 1 () 3))
  (define child '(shared 1 () 4))
  (match (check-reborrow-parents
          '(cfg (Scope (3 4) (Let (u const Unit)
                               (Assign (BorrowMutRef 1 () 3) 1)
                               (Read (BorrowRef 1 () 4))))
                ((1 (resource 1000))) ((1 Available)) () ())
          (list (list child parent)))
    [(list 'fail reason _)
     (check-equal? reason 'reborrow-parent-live)]
    [other (fail (format "unexpected: ~e" other))]))

;; spec §5.4。型を付けない config を sidecar 無しで実行する。
(define (run config)
  (check-borrow-execution config #f #f 200 (make-bcounters)))

(define double-acquire-config
  '(cfg (Scope (0)
         (Rec ((first mut (BorrowMutRef 0 () 0))
              (second mut (BorrowMutAt 0 (Own 0 ()) 0)))))
       ((0 7)) ((0 Available)) () ()))

(define sequential-acquire-core
  `(Scope ()
     (Let (x let (Owned Int)) 7
       (Let (u const Unit)
            (Scope ()
              (Let (p let ,bm) (BorrowMut x) (Assign p 2)))
         (Scope ()
           (Let (q let ,bm) (BorrowMut x) (Assign q 3)))))))

(define proj-child-config
  '(cfg (ProjBorrowAt 1 (BorrowMutRef 0 () 0) f)
        ((0 (Rec ((f mut 7) (g mut 8)))
            (declared (Record ((f Int mut) (g Int mut)))))
         (1 (BorrowMutRef 0 (f) 0)))
        ((0 Available) (1 Available)) () ()))

(define union-child-config
  '(cfg (UnionEliminate (BorrowMutRef 0 () 0)
          ((Int x -> unit) (String y -> unit)))
        ((0 (UnionVal (Union Int String) Int 7)
            (declared (Owned (Union Int String))))
         (1 (BorrowMutRef 0 ((Payload)) 0)))
        ((0 Available) (1 Available)) () ()))

(define data-child-config
  '(cfg (Eliminate (BorrowMutRef 0 () 0)
          ((nil () -> unit) (cons (head tail) -> unit)))
        ((0 (Construct (List Int) cons 7 (Construct (List Int) nil))
            (declared (Owned (List Int))))
         (1 (BorrowMutRef 0 (0) 0)))
        ((0 Available) (1 Available)) () ()))

(define from-raw-config
  '(cfg
    (Unsafe
     (FromRawPtr
      (PtrVal 0 (f)
        (RawPtr Int Mut NonNull (Align 1) (AddrSpace native) (Prov owned)))
      0))
    ((0 (Rec ((f mut 7)))
        (declared (Owned (Record ((f Int mut))))))
     (1 (BorrowMutRef 0 (f) 0)))
    ((0 Available) (1 Available)) () ()))

(test-case "同じ Scope で生存中の可変借用をもう一度取得すると取得の step で落ちる"
  (match (run double-acquire-config)
    [(list 'fail 'mut-not-exclusive (list a b))
     (check-equal? a b)]
    [other (fail (format "unexpected: ~e" other))])
  (check-equal?
   (failure-key
    (type-core
     `(Scope ()
        (Let (x let (Owned Int)) 7
          (Let (p let ,bm) (BorrowMut x)
            (Let (q let ,bm) (BorrowMut x)
              (Let (u const Unit) (Assign p 1) (Assign q 2))))))))
   "E-BOR-003"))

(test-case "使い終えた可変借用を同じ place から取り直す形は ok になる"
  (check-accepted sequential-acquire-core))

(for ([name (in-list '("ProjBorrowMut" "UnionEliminate" "Eliminate"))]
      [config (in-list (list proj-child-config
                             union-child-config
                             data-child-config))])
  (test-case (format "~a で二つ目の子を作る前に子が生きている config で落ちる" name)
    (match (run config)
      [(list 'fail 'mut-not-exclusive (list a b))
       (check-not-equal? a b)
       (check-equal? (second a) (second b))]
      [other (fail (format "unexpected: ~e" other))])))

(test-case "生存中の借用と同じ 4 つ組を作る FromRawPtrMut は unverified-borrow-form のまま"
  (match (run from-raw-config)
    [(list 'fail reason _) (check-equal? reason 'unverified-borrow-form)]
    [other (fail (format "unexpected: ~e" other))]))

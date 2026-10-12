#lang racket/base

(require rackunit
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../region.rkt"
         "../typing.rkt"
         "../type-shape.rkt")

(define leaf '(OwnedLeaf (tok 1) (resource 1)))
(define marker `(OwnedTransit 9 (Rec ((a imm ,leaf) (b imm 3)))))

(test-case "移送 marker は G2m の値であり G2 の値ではない"
  (check-true (redex-match? G2m v marker))
  (check-false (redex-match? G2 v marker)))

(test-case "移送 marker の子は payload だけである"
  (check-equal? (core-children marker) (list (list-ref marker 2)))
  (check-equal? (core-with-children marker '(7)) '(OwnedTransit 9 7)))

(test-case "移送 marker の内部 token と leaf を一度だけ走査する"
  (check-equal? (collect-tokens marker) '((tok 1)))
  (check-equal? (walk-owned-leaves marker) '(((tok 1) (a))))
  (check-true (contains-owned-leaf? marker))
  (check-false (contains-owned-leaf? '(OwnedTransit 9 7))))

(test-case "移送 marker の place を共通の走査で列挙する"
  (define nested `(Rec ((a imm ,marker) (b imm (OwnedTransit 10 4)))))
  (check-equal? (transit-places nested) '(9 10))
  (check-true (contains-owned-transit? nested))
  (check-false (contains-owned-transit? `(Rec ((a imm ,leaf)))))
  (check-true (owned-transit? marker))
  (check-false (owned-transit? leaf))
  (check-equal?
   (transit-places
    '(CurryVal (Derived User (Curry (OwnedTransit 9 7)))
               (Lam User f () unit) (OwnedTransit 9 7)))
   '(9)))

(test-case "移送 marker の内部にある leaf 位置を検査する"
  (check-false (leaf-positions-ok? marker))
  (check-true (observed-leaf-positions-ok? marker)))

(test-case "移送 marker を含む値の型の正規形を検査する"
  (check-true (core-types-normal? marker)))

(define (transit-config core declared [payload 7]
                        #:extra-heap [extra-heap '()]
                        #:extra-states [extra-states '()]
                        #:tokens [tokens '()]
                        #:trace [trace '()])
  `(cfg ,core
        ,(cons `(9 ,payload (declared ,declared)) extra-heap)
        ,(cons '(9 Moved) extra-states)
        ,tokens
        ,trace))

(define (check-runtime-config configuration callables expected)
  (define row (runtime-row configuration callables expected))
  (check-not-false row (format "runtime-row が無い: ~s" configuration))
  (check-true (config-ok? configuration callables expected row)
              (format "config-ok? が偽: ~s" configuration))
  row)

(define transit-leaf '(OwnedLeaf (tok 1) (resource 1)))
(define transit-marker-int '(OwnedTransit 9 7))
(define transit-marker-bad '(OwnedTransit 9 #t))
(define transit-marker-with-leaf
  `(OwnedTransit 9
                 (Construct (Option (Owned Res)) some
                            (OwnedLeaf (tok 1) (resource 1)))))

(test-case "移送 marker は Moved place の宣言型を保持する"
  (define config (transit-config '(OwnedTransit 9 7) '(Owned Int)))
  (check-runtime-config config '() '(Owned Int))
  (check-equal? (core-type-of '(OwnedTransit 9 7) '() '()) 'ill-typed))

(test-case "構成だけの Owned 欄と Yield で marker を受理する"
  (define fixtures
    (list
     (list `(Construct (Option (Owned Int)) some ,transit-marker-int)
           '(Option (Owned Int)))
     (list `(Rec ((owned imm ,transit-marker-int)))
           '(Record ((owned (Owned Int) imm))))
     (list `(Yield ,transit-marker-int unit) 'Unit)))
  (for ([fixture (in-list fixtures)])
    (match-define (list core expected) fixture)
    (check-runtime-config
     (transit-config core '(Owned Int)) '() expected))
  (define invalid-fixtures
    (list
     (list `(Construct (Option (Owned Int)) some ,transit-marker-bad)
           '(Option (Owned Int)))
     (list `(Rec ((owned imm ,transit-marker-bad)))
           '(Record ((owned (Owned Int) imm))))
     (list `(Yield ,transit-marker-bad unit) 'Unit)))
  (for ([fixture (in-list invalid-fixtures)])
    (match-define (list core expected) fixture)
    (check-false
     (config-ok? (transit-config core '(Owned Int)) '() expected '())
     (format "不正 marker が構成だけの Owned 位置を通った: ~s" core)))
  (define leaf-fixtures
    (list
     (list `(Construct (Option (Owned Res)) some ,transit-leaf)
           '(Option (Owned Res)))
     (list `(Rec ((owned imm ,transit-leaf)))
           '(Record ((owned (Owned Res) imm))))
     (list `(Yield ,transit-leaf unit) 'Unit)))
  (for ([fixture (in-list leaf-fixtures)])
    (match-define (list core expected) fixture)
    (check-runtime-config
     (transit-config core '(Owned Int) 7
                     #:tokens '(((tok 1) Available)))
     '() expected)))

(test-case "CurryVal の Owned 固定引数で marker と OwnedLeaf を受理する"
  (define marker-function
    '(Lam User transit-int-curry-lam (value n)
       (Handle (Return transit-int-boundary Int) (answer -> answer)
         (Scope () (Let (transfer let (Owned Int)) value n)))))
  (define marker-callables
    '((transit-int-curry-lam
       (NFn ((Owned Int) Int) Int () () () User))))
  (define marker-curry
    `(CurryVal (Derived User (Curry ,transit-marker-int))
               ,marker-function ,transit-marker-int))
  (check-runtime-config
   (transit-config marker-curry '(Owned Int))
   marker-callables
   `(Owned (NFn (Int) Int () () ()
                (Derived User (Curry ,transit-marker-int)))))
  (define invalid-curry
    `(CurryVal (Derived User (Curry ,transit-marker-bad))
               ,marker-function ,transit-marker-bad))
  (check-false
   (config-ok?
    (transit-config invalid-curry '(Owned Int))
    marker-callables
    `(Owned (NFn (Int) Int () () ()
                 (Derived User (Curry ,transit-marker-bad))))
    '())
   "不正 marker が CurryVal の Owned 固定引数を通った")

  (define leaf-function
    '(Lam User transit-res-curry-lam (value n)
       (Handle (Return transit-res-boundary Int) (answer -> answer)
         (Scope () (Let (transfer let (Owned Res)) value n)))))
  (define leaf-callables
    '((transit-res-curry-lam
       (NFn ((Owned Res) Int) Int () () () User))))
  (define leaf-curry
    `(CurryVal (Derived User (Curry ,transit-leaf))
               ,leaf-function ,transit-leaf))
  (check-runtime-config
   (transit-config leaf-curry '(Owned Int) 7
                   #:tokens '(((tok 1) Available)))
   leaf-callables
   `(Owned (NFn (Int) Int () () () (Derived User (Curry ,transit-leaf))))))

(test-case "移送 marker の四条件違反を構成型付けで拒否する"
  (define (rejected core
                    #:expected [expected '(Owned Int)]
                    #:declared [declared '(Owned Int)]
                    #:payload [payload 7]
                    #:states [states '((9 Moved))]
                    #:heap? [heap? #t])
    (define heap
      (if heap?
          `((9 ,payload (declared ,declared)))
          '()))
    (define cfg `(cfg ,core ,heap ,states () ()))
    (check-false (config-ok? cfg '() expected '())
                 (format "不正 marker が通った: ~s" cfg)))
  (rejected '(OwnedTransit 9 7) #:states '((9 Available)))
  (rejected '(OwnedTransit 9 7) #:heap? #f)
  (rejected '(OwnedTransit 9 7) #:declared 'Int #:expected 'Int)
  (rejected '(OwnedTransit 9 #t))
  (define root-leaf-marker
    `(cfg (OwnedTransit 9 (OwnedLeaf (tok 1) (resource 1)))
          ((9 (resource 7) (declared (Owned Res))))
          ((9 Moved)) (((tok 1) Available)) ()))
  ;; heap 側も Res と整合させ、marker payload 根の検査を単独で固定する。
  (check-false
   (runtime-row root-leaf-marker '() '(Owned Res)))
  (check-false (config-ok? root-leaf-marker '() '(Owned Res) '()))
  (define twice '(OwnedTransit 9 (OwnedTransit 10 7)))
  (define nested-cfg
    `(cfg ,twice
          ((9 7 (declared (Owned Int)))
           (10 7 (declared (Owned Int))))
          ((9 Moved) (10 Moved)) () ()))
  (check-false (config-ok? nested-cfg '() '(Owned Int) '()))
  (define duplicate
    `(Rec ((a imm ,transit-marker-int) (b imm ,transit-marker-int))))
  (define duplicate-type
    '(Record ((a (Owned Int) imm) (b (Owned Int) imm))))
  (check-false
   (config-ok?
    (transit-config duplicate duplicate-type)
    '() duplicate-type '()))
  (define root-heap-marker
    `(cfg (Move 0)
          ((0 ,transit-marker-int (declared (Owned Int)))
           (9 7 (declared (Owned Int))))
          ((0 Available) (9 Moved)) () ()))
  (check-false (config-ok? root-heap-marker '() '(Owned Int) '(Own))))

(test-case "OwnLeaf の marker は構成型付けだけで受け入れ、OwnedLeaf は拒否する"
  (define ownleaf-marker
    `(Construct (Option (Owned Int)) some (OwnLeaf ,transit-marker-int)))
  (check-runtime-config
   (transit-config ownleaf-marker '(Owned Int)) '() '(Option (Owned Int)))
  (check-equal? (core-type-of ownleaf-marker '() '()) 'ill-typed)
  (define ownedleaf-marker
    `(cfg (OwnedLeaf (tok 2) ,transit-marker-int)
          ((9 7 (declared (Owned Int))))
          ((9 Moved)) (((tok 2) Available)) ()))
  (check-false (runtime-row ownedleaf-marker '() '(Owned Int)))
  (define producer
    '(Construct (Option (Owned Res)) some (OwnLeaf (resource 1))))
  (check-runtime-config (transit-config producer '(Owned Int))
                        '() '(Option (Owned Res))))

(test-case "移送 marker は制御項と Available heap で一意に数え、θ は数えない"
  (define config
    (transit-config transit-marker-int '(Owned Int) 7
                    #:trace `((obs ,transit-marker-int))))
  (check-runtime-config config '() '(Owned Int))
  (define heap-field
    `(cfg (Move 0)
          ((0 (Rec ((owned imm ,transit-marker-int)))
             (declared (Record ((owned (Owned Int) imm)))))
           (9 7 (declared (Owned Int))))
          ((0 Available) (9 Moved)) () ()))
  (check-runtime-config heap-field '()
                        '(Record ((owned (Owned Int) imm))))
  (define stale-marker `(OwnedTransit 9 7))
  (define stale-record `(Rec ((owned imm ,stale-marker))))
  (define moved-heap-duplicate
    `(cfg (OwnedTransit 10 ,stale-record)
          ((9 7 (declared (Owned Int)))
           (10 ,stale-record
               (declared (Owned (Record ((owned (Owned Int) imm)))))))
          ((9 Moved) (10 Moved)) () ()))
  (check-runtime-config
   moved-heap-duplicate '()
   '(Owned (Record ((owned (Owned Int) imm)))))
  (define duplicate-in-core-and-heap
    `(cfg ,transit-marker-int
          ((0 (Rec ((owned imm ,transit-marker-int)))
             (declared (Record ((owned (Owned Int) imm)))))
           (9 7 (declared (Owned Int))))
          ((0 Available) (9 Moved)) () ()))
  (check-not-false
   (runtime-row duplicate-in-core-and-heap '() '(Owned Int))
   "Available heap の重複例は型と row を満たす")
  (check-false
   (config-ok? duplicate-in-core-and-heap '() '(Owned Int) '())
   "Available heap に同じ place の marker があれば拒否する"))

(test-case "移送 marker 内部の Owned token を通常どおり照合する"
  (define expected '(Owned (Option (Owned Res))))
  (define configuration
    (transit-config transit-marker-with-leaf expected
                    '(Construct (Option (Owned Res)) some
                                (OwnedLeaf (tok 1) (resource 1)))
                    #:tokens '(((tok 1) Available))))
  (check-runtime-config configuration '() expected)
  (define missing-token
    `(cfg ,(list-ref configuration 1)
          ,(list-ref configuration 2)
          ,(list-ref configuration 3) () ()))
  (check-false (config-ok? missing-token '() expected '())))

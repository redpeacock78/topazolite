#lang racket

(require rackunit
         racket/match
         "../borrow-oracle.rkt"
         "../borrow.rkt"
         "../gen.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../borrow-gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define inner-type '(Record ((h Int mut))))
(define owner-type `(Record ((f ,inner-type mut) (g Int mut) (k Int imm))))
(define owner-value '(Rec ((f mut (Rec ((h mut 1)))) (g mut 2) (k imm 3))))
(define (then e1 e2) `(Let (ignored let Unit) ,e1 ,e2))
(define (then/as τ e1 e2) `(Let (ignored let ,τ) ,e1 ,e2))

(define (with-parent body)
  `(Scope ()
     (Let (x let (Owned ,owner-type)) ,owner-value
       (Let (p let (BorrowedMut ,owner-type (RParam %omitted))) (BorrowMut x)
         ,body))))

(define (with-mut-child body)
  `(Let (c let (BorrowedMut ,inner-type (RParam %omitted))) (ProjBorrow p f)
     ,body))

(define (with-shared-child body)
  `(Let (s let (Borrowed Int (RParam %omitted))) (ProjBorrow p k)
     ,body))

(define (with-shared-parent body)
  `(Scope ()
     (Let (x let (Owned ,owner-type)) ,owner-value
       (Let (q let (Borrowed ,owner-type (RParam %omitted))) (Borrow x)
         ,body))))

(define projection-callables
  `((project-formal
     (ForallRegion (a)
       (NFn ((BorrowedMut ,owner-type (RParam a)))
            Int () (Mutation) () User)))))

(define (projection-call body)
  `(Apply
    (RegionApp
     (RegionLam (a) (Lam User project-formal (p) ,body))
     (owner-ph))
    p))

(define (type-core core [callables '()])
  (define ir (build-region-ir core))
  (define (contains-owner-ph? value)
    (cond [(eq? value 'owner-ph) #t]
          [(pair? value) (or (contains-owner-ph? (car value))
                             (contains-owner-ph? (cdr value)))]
          [else #f]))
  (define filled
    (if (contains-owner-ph? core)
        (let ([owner-rho (region->rho ir (owner-let-body-region ir '(0)))])
          (let walk ([value (fill-region-placeholders (erase-core core) ir)])
            (cond [(eq? value 'owner-ph) owner-rho]
                  [(pair? value) (cons (walk (car value)) (walk (cdr value)))]
                  [else value])))
        (fill-region-placeholders (erase-core core) ir)))
  (values ir filled (core-type-of/regions filled '() callables #:ir ir)))

(define (trace-g2 start [fuel 300])
  (let loop ([current start] [configs (list start)] [fuel fuel])
    (when (zero? fuel) (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-runtime typed ir callables expected label)
  (define start
    (inject-g2m (erase-core (region-execution-core typed))))
  (define configs (trace-g2 start))
  (for ([cfg (in-list configs)] [index (in-naturals)])
    (define row (runtime-row cfg callables expected))
    (check-not-false row
                     (format "~a config ~a の runtime-row: ~s" label index cfg))
    (check-true (config-ok? cfg callables expected row)
                (format "~a config ~a が config-ok? でない: ~s" label index cfg)))
  (check-equal? (check-borrow-execution start (region-typed-sidecar typed) ir
                                         300 (make-bcounters))
                'ok (format "~a: borrow oracle" label)))

(define (check-accepted core expected [callables '()] [label "fixture"])
  (define-values (ir _filled typed) (type-core core callables))
  (check-true (region-typed? typed) (format "~a: 型検査 ~s" label typed))
  (when (region-typed? typed)
    (check-equal? (region-typed-type typed) expected)
    (check-runtime typed ir callables expected label)))

(define (check-rejected core expected-id [callables '()] [label "fixture"])
  (define result
    (if (region-typed? core)
        core
        (let-values ([(_ir _filled typed) (type-core core callables)]) typed)))
  (check-true
   (diagnostic? result)
   (format "~a: 診断を期待したが、結果は ~s" label
           (if (region-typed? result) (region-typed-type result) result)))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id
                  (format "~a: diagnostic ~s" label result))))

(define (two-scope-view reject?)
  (with-parent
   (with-mut-child
    (then/as 'Int
      `(Scope ()
         (Let (r let (Borrowed ,inner-type (RParam %omitted)))
              (Reborrow c) (Read (ProjBorrow r h))))
      `(Let (e let (BorrowedMut Int (RParam %omitted))) (ProjBorrow c h)
         ,(if reject?
              (then '(Assign e 5)
                    (then/as 'Int '(Read (ProjBorrow c h)) '(Read e)))
              (then '(Assign e 5) '(Read e))))))))

;; §5.1: 子が生きている間の親・alias の衝突。
(test-case "可変の欄の子が生きている間に親全体を Assign すると E-BOR-025"
  (check-rejected
   (with-parent
    (with-mut-child
     (then `(Assign p ,owner-value) '(Read (ProjBorrow c h)))))
   "E-BOR-025" '() "§5.1-1"))

(test-case "可変の欄の子が生きている間に親を Read すると E-BOR-025"
  (check-rejected
   (with-parent
    (with-mut-child
     (then/as owner-type '(Read p) '(Read (ProjBorrow c h)))))
   "E-BOR-025" '() "§5.1-2"))

(test-case "共有の欄の子が生きている間に親全体を Assign すると E-BOR-025"
  (check-rejected
   (with-parent
    (with-shared-child
     (then `(Assign p ,owner-value) '(Read s))))
   "E-BOR-025" '() "§5.1-3"))

(test-case "0b0b3 で受理へ反転する共有の欄の子の間の親 Read"
  (check-rejected
   (with-parent
    (with-shared-child
     (then/as owner-type '(Read p) '(Read s))))
   "E-BOR-025" '() "§5.1-4"))

(test-case "可変の欄の子と親の Reborrow は重なり E-BOR-025"
  (check-rejected
   (with-parent
    (with-mut-child
     `(Let (r let (Borrowed ,owner-type (RParam %omitted))) (Reborrow p)
        ,(then/as 'Int '(Read (ProjBorrow r g)) '(Read (ProjBorrow c h))))))
   "E-BOR-003" '() "§5.1-5"))

(test-case "同じ Scope で子を使い終えた後も親の停止は続く"
  ;; 子の束縛と親の Assign は同じ Scope にある。
  (check-rejected
   (with-parent
    (then/as 'Int (with-mut-child '(Read (ProjBorrow c h)))
             `(Assign p ,owner-value)))
   "E-BOR-025" '() "§5.1-6"))

(test-case "Reborrow の間は可変の欄の子を再使用できない"
  (check-rejected
   (with-parent
    (with-mut-child
     `(Let (r let (Borrowed ,inner-type (RParam %omitted))) (Reborrow c)
        ,(then/as 'Int '(Read (ProjBorrow c h))
                  '(Read (ProjBorrow r h))))))
   "E-BOR-025" '() "§5.1-8"))

(test-case "Reborrow の間は親から同じ path を射影して Read できない"
  (check-rejected
   (with-parent
    (with-mut-child
     `(Let (r let (Borrowed ,inner-type (RParam %omitted))) (Reborrow c)
        ,(then/as 'Int '(Read (ProjBorrow (ProjBorrow p f) h))
                  '(Read (ProjBorrow r h))))))
   "E-BOR-025" '() "§5.1-9"))

(test-case "可変の欄の子が生きていても owner Move は E-BOR-008"
  (check-rejected
   (with-parent
    (with-mut-child
     `(Let (moved let (Owned ,owner-type)) (Move x)
        (Read (ProjBorrow c h)))))
   "E-BOR-008" '() "§5.1-10"))

(test-case "欄の子が生きている間に親を通して同じ欄へ place Assign すると E-BOR-025"
  (check-rejected
   (with-parent
    (with-mut-child
     `(Let (cg let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
        ,(then '(Assign (ProjBorrow p g) 1) '(Read cg)))))
   "E-BOR-025" '() "§5.1-12"))

(test-case "同じ欄の可変の射影を二度作ると E-BOR-003"
  ;; 二つの別 α の borrow-request が同じ path で衝突し、use 判定より先に走る。
  (check-rejected
   (with-parent
    `(Let (cg let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
       (Let (dg let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
         ,(then '(Assign cg 1) '(Read dg)))))
   "E-BOR-003" '() "§5.1-13"))

;; §5.2: 受理形。型だけでなく全 config と性質8 oracle を検査する。
(test-case "子の Scope 後に親の別欄を使える"
  (check-accepted
   (with-parent
    (then/as 'Int `(Scope () ,(with-mut-child '(Read (ProjBorrow c h))))
             (then `(Assign p ,owner-value) '(Read (ProjBorrow p g)))))
   'Int '() "§5.2-1"))

(test-case "別欄の読み書きと可変子の読み出しが共存する"
  (check-accepted
   (with-parent
    (with-mut-child
     (then/as 'Int '(Read (ProjBorrow p g))
              (then '(Assign (ProjBorrow p g) 5) '(Read (ProjBorrow c h))))))
   'Int '() "§5.2-2"))

(test-case "射影した可変子を通す Assign と Read"
  (check-accepted
   (with-parent
    (with-mut-child
     (then '(Assign (ProjBorrow c h) 5) '(Read (ProjBorrow c h)))))
   'Int '() "§5.2-3"))

(test-case "別欄の子を束縛して Assign した後に可変子を読む"
  (check-accepted
   (with-parent
    (with-mut-child
     `(Let (d let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
        ,(then '(Assign d 5) '(Read (ProjBorrow c h))))))
   'Int '() "§5.2-4"))

(test-case "共有親の別欄射影を Read する"
  (check-accepted
   (with-shared-parent
    `(Let (t let (Borrowed Int (RParam %omitted))) (ProjBorrow q g)
       ,(then/as 'Int '(Read (ProjBorrow q k)) '(Read t))))
   'Int '() "§5.2-5"))

(test-case "oracle は生存中の射影子を持つ可変親の消費を拒否する"
  (for ([parent-use (in-list
                     (list '(Read (BorrowMutRef 0 () 0))
                           '(Assign (BorrowMutRef 0 () 0) 9)))])
    (define config
      `(cfg
        (Scope (0 1)
          (Let (child let (BorrowedMut Int 1))
               (ProjBorrowAt 1 (BorrowMutRef 0 () 0) f)
            (Let (ignored const Unit) ,parent-use (Read child))))
        ((0 (Rec ((f mut 7) (g mut 8)))
           (declared (Record ((f Int mut) (g Int mut))))))
        ((0 Available) (1 Available)) () ()))
    (match (check-borrow-execution config #f #f 100 (make-bcounters))
      [(list 'fail 'reborrow-parent-live _detail) (check-true #t)]
      [other (fail (format "expected reborrow-parent-live for ~s, got ~e"
                           parent-use other))])))

(test-case "oracle は同じ可変 loan の兄弟射影を二度生存させない"
  (define config
    '(cfg
      (Scope (0 1)
        (Let (a1 let (BorrowedMut Int 1))
             (ProjBorrowAt 1 (BorrowMutRef 0 () 0) f)
          (Let (a2 let (BorrowedMut Int 1))
               (ProjBorrowAt 1 (BorrowMutRef 0 () 0) f)
            (Let (ignored const Unit) (Assign a1 9) (Read a2)))))
      ((0 (Rec ((f mut 7)))
         (declared (Record ((f Int mut))))))
      ((0 Available) (1 Available)) () ()))
  (match (check-borrow-execution config #f #f 100 (make-bcounters))
    [(list 'fail 'reborrow-parent-live
           '((mut 0 (f) 1) (mut 0 () 0))) (check-true #t)]
    [other (fail (format "expected reborrow-parent-live for sibling projections, got ~e"
                         other))]))

(test-case "oracle は共有射影子の間の可変親 Read も保守的に拒否する"
  (define config
    '(cfg
      (Scope (0 1)
        (Let (child let (Borrowed Int 1))
             (ProjBorrowAt 1 (BorrowMutRef 0 () 0) f)
          (Let (ignored const Unit) (Read (BorrowMutRef 0 () 0))
            (Read child))))
      ((0 (Rec ((f imm 7) (g mut 8)))
         (declared (Record ((f Int imm) (g Int mut))))))
      ((0 Available) (1 Available)) () ()))
  (match (check-borrow-execution config #f #f 100 (make-bcounters))
    [(list 'fail 'reborrow-parent-live _detail) (check-true #t)]
    [other (fail (format "expected reborrow-parent-live, got ~e" other))]))

(test-case "可変子の内側 Scope 後に子を使い直す"
  (check-accepted
   (with-parent
    (with-mut-child
     (then/as 'Int
       '(Scope () (Let (e let (BorrowedMut Int (RParam %omitted)))
                   (ProjBorrow c h) (Read e)))
       (then '(Assign (ProjBorrow c h) 5) '(Read (ProjBorrow c h))))))
   'Int '() "§5.2-6"))

(test-case "再借用の子の Scope 後に射影の親を再開する"
  (define core
    (with-parent
     (with-mut-child
      (then/as 'Int
        '(Scope ()
           (Let (r let (Borrowed (Record ((h Int mut))) (RParam %omitted)))
             (Reborrow c) (Read (ProjBorrow r h))))
        (then '(Assign (ProjBorrow c h) 5) '(Read (ProjBorrow c h)))))))
  (check-accepted core 'Int '() "§5.2-7"))

(test-case "内側 Reborrow の後に同じ欄を書いても field view は使える"
  (check-accepted
   (with-parent
    (with-mut-child
     (then/as 'Unit
       `(Scope ()
          (Let (r let (Borrowed ,inner-type (RParam %omitted)))
               (Reborrow c) ,(then/as inner-type '(Read r) 'unit)))
       '(Assign (ProjBorrow c h) 5))))
   'Unit '() "値位置の field view を通す対照"))

(test-case "field view が内側 Scope を出た後は root から同じ欄を書ける"
  (check-accepted
   (with-parent
    (then/as 'Unit
      '(Scope ()
         (Let (c let (BorrowedMut (Record ((h Int mut)))
                               (RParam %omitted)))
              (ProjBorrow p f) unit))
      '(Assign (ProjBorrow p f) (Rec ((h mut 5))))))
   'Unit '() "内側 Scope で field view を終える対照"))

(test-case "射影の子を幅部分型の借用欄へ束縛できる"
  (check-accepted
   (with-parent
    `(Let (r let
              (Record ((borrowed (BorrowedMut ,inner-type
                                               (RParam %omitted)) imm))))
          (Rec ((borrowed imm (ProjBorrow p f)) (extra imm 1)))
       (Read (ProjBorrow (Proj r borrowed) h))))
   'Int '() "射影の子の幅部分型"))

(test-case "Reborrow の子を幅部分型の借用欄へ束縛できる"
  (check-accepted
   (with-parent
    (with-mut-child
     `(Let (r let
               (Record ((borrowed (Borrowed ,inner-type
                                             (RParam %omitted)) imm))))
           (Rec ((borrowed imm (Reborrow c)) (extra imm 1)))
        (Read (ProjBorrow (Proj r borrowed) h)))))
   'Int '() "Reborrow の子の幅部分型"))

(test-case "宣言にだけある Record 欄は幅部分型でも拒否する"
  (check-rejected
   (with-parent
    `(Let (r let
              (Record ((borrowed (BorrowedMut ,inner-type
                                               (RParam %omitted)) imm)
                       (missing Int imm))))
          (Rec ((borrowed imm (ProjBorrow p f))))
       (Read (ProjBorrow (Proj r borrowed) h))))
   "E-RCD-008" '() "宣言側だけの幅部分型欄"))

(test-case "Option payload 内の Record 欄も名前で寿命を採る"
  (check-accepted
   (with-parent
    `(Let (wrapped let
                   (Option (Record ((borrowed (BorrowedMut ,inner-type
                                                            (RParam %omitted)) imm)))))
          (Construct (Option (Record ((borrowed (BorrowedMut ,inner-type
                                                             (RParam %omitted)) imm))))
                     some
                     (Rec ((borrowed imm (ProjBorrow p f)) (extra imm 1))))
       (Eliminate wrapped
         ((none () -> 0)
          (some (value) -> (Read (ProjBorrow (Proj value borrowed) h)))))))
   'Int '() "Option payload の Record"))

(test-case "Union payload の projection 欄も Record 幅部分型で寿命を採る"
  (define member-type
    `(Record ((borrowed (BorrowedMut ,inner-type (RParam %omitted)) imm))))
  (define union-type `(Union ,member-type String))
  (check-accepted
   (with-parent
    `(Let (wrapped let ,union-type)
       (UnionInject ,union-type ,member-type
         (Rec ((borrowed imm (ProjBorrow p f)) (extra imm 1))))
       (UnionEliminate wrapped
         ((,member-type value ->
           (Read (ProjBorrow (Proj value borrowed) h)))
          (String text -> 0)))))
   'Int '() "Union projection payload の Record"))

(test-case "Union payload の Reborrow 欄も Record 幅部分型で寿命を採る"
  (define member-type
    `(Record ((borrowed (Borrowed ,inner-type (RParam %omitted)) imm))))
  (define union-type `(Union ,member-type String))
  (check-accepted
   (with-parent
    (with-mut-child
     `(Let (wrapped let ,union-type)
        (UnionInject ,union-type ,member-type
          (Rec ((borrowed imm (Reborrow c)) (extra imm 1))))
        (UnionEliminate wrapped
          ((,member-type value ->
            (Read (ProjBorrow (Proj value borrowed) h)))
           (String text -> 0))))))
   'Int '() "Union Reborrow payload の Record"))

(test-case "Union payload にない宣言 Record 欄は HEAD と同じく拒否する"
  (define member-type
    `(Record ((borrowed (BorrowedMut ,inner-type (RParam %omitted)) imm)
              (missing Int imm))))
  (define union-type `(Union ,member-type String))
  (check-rejected
   (with-parent
    `(Let (wrapped let ,union-type)
       (UnionInject ,union-type ,member-type
         (Rec ((borrowed imm (ProjBorrow p f)) (extra imm 1))))
       (UnionEliminate wrapped
         ((,member-type value ->
           (Read (ProjBorrow (Proj value borrowed) h)))
          (String text -> 0)))))
   "E-TYP-023" '() "Union payload 欠落欄"))

(test-case "孫の射影停止を内側 Reborrow 後に立て直す"
  (check-accepted (two-scope-view #f) 'Int '() "§5.2-8-accept"))

(test-case "孫の射影停止中は親の同じ欄を Read できない"
  (check-rejected (two-scope-view #t) "E-BOR-025" '() "§5.2-8-reject"))

(test-case "同じ欄へ二度 Assign してから Read する"
  (check-accepted
   (with-parent
    (then '(Assign (ProjBorrow p g) 1)
          (then '(Assign (ProjBorrow p g) 1) '(Read (ProjBorrow p g)))))
   'Int '() "§5.2-9"))

(test-case "同じ欄へ Assign した後に Read する"
  (check-accepted
   (with-parent
    (then '(Assign (ProjBorrow p g) 1) '(Read (ProjBorrow p g))))
   'Int '() "§5.2-10"))

(test-case "入れ子 place 射影を二度 Read する"
  (check-accepted
   (with-parent
    (then/as 'Int '(Read (ProjBorrow (ProjBorrow p f) h))
             '(Read (ProjBorrow (ProjBorrow p f) h))))
   'Int '() "§5.2-11"))

(test-case "Span を剥がして同じ欄の place 射影を反復する"
  (check-accepted
   (with-parent
    (then '(Assign (ProjBorrow (#:span src 0 12) p g) 1)
          '(Read (ProjBorrow (#:span src 13 25) p g))))
   'Int '() "§5.2-12"))

(test-case "入れ子 place 射影へ Assign した後に同じ place を Read する"
  (check-accepted
   (with-parent
    (then '(Assign (ProjBorrow (ProjBorrow p f) h) 5)
          '(Read (ProjBorrow (ProjBorrow p f) h))))
   'Int '() "§5.2-14"))

(define repeated-read-source
  (string-append
   "let owner: Owned<{ n: Int }> = { n: 1 }\n"
   "let p = &mut owner\n"
   "deref(p.n)\n"
   "deref(p.n)"))

(test-case "Surface の同じ欄の反復 Read は place 射影として受理"
  (define compiled (compile-source/string 'probe repeated-read-source))
  (check-true (compiled? compiled) (format "Surface compile: ~s" compiled))
  (when (compiled? compiled)
    (define-values (ir _filled typed)
      (type-core (compiled-core compiled) (compiled-callables compiled)))
    (check-true (region-typed? typed) (format "Surface type: ~s" typed))
    (when (region-typed? typed)
      (check-equal? (region-typed-type typed) 'Int)
      (check-runtime typed ir (compiled-callables compiled) 'Int "§5.2-13"))))

(test-case "仮引数からの射影子の生存中に親を Assign すると呼出しで E-BOR-025"
  (check-rejected
   (with-parent
    (projection-call
     `(Let (c let (BorrowedMut ,inner-type (RParam a))) (ProjBorrow p f)
        ,(then `(Assign p ,owner-value) '(Read (ProjBorrow c h))))))
   "E-BOR-025" projection-callables "§5.1-7-live"))

(test-case "0b2 で窓の許可リストを広げて回収する仮引数の射影後 Assign"
  (check-rejected
   (with-parent
    (projection-call
     `(Let (child-read const Int)
           (Scope ()
             (Let (c let (BorrowedMut ,inner-type (RParam a))) (ProjBorrow p f)
               (Read (ProjBorrow c h))))
        ,(then `(Assign p ,owner-value) '(Read (ProjBorrow p g))))))
   "E-BOR-025" projection-callables "§5.1-7-after-scope"))

(test-case "仮引数の射影子の間も別欄の Read と Assign が通る"
  (define body
    `(Let (c let (BorrowedMut ,inner-type (RParam a))) (ProjBorrow p f)
       ,(then/as 'Int '(Read (ProjBorrow p g))
                 (then '(Assign (ProjBorrow p g) 5)
                       '(Read (ProjBorrow c h))))))
  (check-accepted (with-parent (projection-call body))
                  'Int projection-callables "§5.1-7-other-field"))

(test-case "仮引数の射影を Reborrow した子の間に親 view を使うと E-BOR-025"
  (check-rejected
   (with-parent
    (projection-call
     `(Let (c let (BorrowedMut ,inner-type (RParam a))) (ProjBorrow p f)
        (Let (r let (Borrowed ,inner-type (RParam a))) (Reborrow c)
          ,(then/as inner-type '(Read c) '(Read (ProjBorrow r h)))))))
   "E-BOR-025" projection-callables "§5.1-11-parent-view"))

(test-case "仮引数射影の Reborrow 中も別欄の Read は通る"
  (define body
    `(Let (c let (BorrowedMut ,inner-type (RParam a))) (ProjBorrow p f)
       (Let (r let (Borrowed ,inner-type (RParam a))) (Reborrow c)
         ,(then/as 'Int '(Read (ProjBorrow p g))
                   '(Read (ProjBorrow r h))))))
  (check-accepted (with-parent (projection-call body))
                  'Int projection-callables "§5.1-11-other-field"))

(test-case "仮引数の同じ place 欄へ二度 Assign して Read できる"
  (define body
    (then '(Assign (ProjBorrow p g) 1)
          (then '(Assign (ProjBorrow p g) 2)
                '(Read (ProjBorrow p g)))))
  (check-accepted (with-parent (projection-call body))
                  'Int projection-callables "§5.2-14"))

(define eliminate-projection-source
  (string-append
   "let owner: Owned<{ f: Option<Int> }> = { f: some(1) }\n"
   "let p = &mut owner\n"
   "when p.f { some child => 0\n none => 0 }\n"
   "deref(p.f)"))

(test-case "Eliminate scrutinee の射影の子は分解の出口で終わる"
  (define compiled (compile-source/string 'probe eliminate-projection-source))
  (check-true (compiled? compiled)
              (format "Surface compile: ~s" compiled))
  (when (compiled? compiled)
    (define-values (ir _filled typed)
      (type-core (compiled-core compiled) (compiled-callables compiled)))
    (check-true (region-typed? typed) (format "Surface type: ~s" typed))
    (when (region-typed? typed)
      (check-equal? (region-typed-type typed) '(Option Int))
      (check-runtime typed ir (compiled-callables compiled) '(Option Int)
                     "Eliminate scrutinee 射影の出口"))))

(define (surface-leave-probe payload)
  (string-append
   "fn main() -> Unit ! {Own, Mutation, Partial} {\n"
   " let owner: Owned<{ f: Option<Int> }> = { f: some(1) }\n"
   " let p = &mut owner\n"
   " let xs: List<Int> = cons(1, nil())\n"
   " let result = for item in xs {\n"
   "  when p.f { some child => leave " payload "\n none => () }\n"
   " }\n"
   " deref(p.f)\n"
   " ()\n"
   "}\nmain()"))

(test-case "Surface for の leave 借用 payload と Read 対照は E-BOR-011 で先に拒否"
  (for ([label (in-list '("escape-leave-child" "escape-leave-read-control"))]
        [payload (in-list '("child" "deref(child)"))])
    (define result
      (compile-source/string 'probe (surface-leave-probe payload)))
    (check-true (diagnostic? result) (format "~a: ~s" label result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-BOR-011"
                    (format "~a: diagnostic" label)))))

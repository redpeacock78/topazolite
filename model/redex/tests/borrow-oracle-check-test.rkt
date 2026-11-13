#lang racket

(require rackunit
         racket/match
         racket/set
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../gen.rkt"
         "../machine.rkt")

(define shared-skeleton
  '(Scope ()
     (Let (x let (Owned Res)) (resource 1000)
       (Scope ()
         (Let (y let (Borrowed Res ph)) (Borrow x) 1000)))))

;; 可変借用へ書き込む値は payload 型と互換でなければならない
;; （`infer-assign` の union 成分検査）。`Res` payload へ整数は代入できないので、
;; 代入を含む骨格は `Int` payload にする。
(define mut-skeleton
  '(Scope ()
     (Let (x let (Owned Int)) 1000
       (Scope ()
         (Let (y let (BorrowedMut Int ph)) (BorrowMut x)
           (Assign y 1001))))))

(define eliminate-ref-skeleton
  '(Scope ()
     (Let (d let (Owned (Option Int))) (Construct (Option Int) some 1000)
       (Scope ()
         (Let (q let (Borrowed (Option Int) ph)) (Borrow d)
           (Eliminate (Borrow d)
                      ((none () -> 1000)
                       (some (e) -> (Read e)))))))))

(define (run skeleton)
  (define counters (make-bcounters))
  (match (prepare-borrow-term skeleton)
    [(list 'ok config sidecar ir)
     (list (check-borrow-execution config sidecar ir 200 counters) counters)]
    [other (list other #f)]))

(define nested-owner-type
  '(Record ((g Int mut)
            (o (Option Int) mut)
            (ro (Option (Record ((h Int mut)))) mut)
            (u (Union Int String) mut))))
(define nested-owner-value
  '(Rec ((g mut 2)
         (o mut (Construct (Option Int) some 1))
         (ro mut (Construct (Option (Record ((h Int mut))))
                            some (Rec ((h mut 1)))))
         (u mut (UnionInject (Union Int String) Int 1)))))

(define (with-nested-mut-parent body)
  `(Scope ()
     (Let (x let (Owned ,nested-owner-type)) ,nested-owner-value
       (Let (p let (BorrowedMut ,nested-owner-type ph)) (BorrowMut x)
         ,body))))

(define (with-nested-shared-parent body)
  `(Scope ()
     (Let (x let (Owned ,nested-owner-type)) ,nested-owner-value
       (Let (p let (Borrowed ,nested-owner-type ph)) (Borrow x)
         ,body))))

(define (check-typed-oracle-ok skeleton label)
  (match (prepare-borrow-term* skeleton)
    [(list 'ok config sidecar ir _type)
     (check-equal?
      (check-borrow-execution config sidecar ir 300 (make-bcounters))
      'ok label)]
    [other (fail (format "~a: type check did not accept: ~s" label other))]))

(define (annotated-eliminate-config parent-path)
  `(cfg
    (EliminateAt
     (BorrowMutRef 0 (0) 7)
     ((Pair (child other) (11 %parent) ->
            (Construct (Record ((first Int imm) (second Int imm))) Pair
                       (Read (BorrowMutRef 0 ,parent-path 7))
                       (Read child)))))
    ((0 (Construct (Record ((left (Record ((first Int mut)
                                           (second Int mut))) mut)
                            (right Int mut)))
                   Outer
                   (Construct (Record ((first Int mut) (second Int mut)))
                              Pair 1 2)
                   3)))
    ((0 Available)) () ()))

(test-case "注釈付き分解は binder ごとの path と ρ で派生辺を作る"
  (check-equal?
   (borrow-form-candidates
    '(EliminateAt (BorrowMutRef 0 () 7)
       ((Pair (left right) (11 %parent) -> (Read left))))
    '(Read (BorrowMutRef 0 (0) 11))
    #:rule 'R-EliminateAtMutRef)
   '((derived mut 0 (0) 11 0 () 7)))
  (check-equal?
   (borrow-form-candidates
    '(EliminateAt (BorrowMutRef 0 () 7)
       ((Pair (left) (%parent) -> (Read left))))
    '(Read (BorrowMutRef 0 (0) 7))
    #:rule 'R-EliminateAtMutRef)
   '((derived mut 0 (0) 7 0 () 7)))
  (check-equal?
   (borrow-form-candidates
    '(UnionEliminateAt (BorrowMutRef 0 (2) 7)
       ((Int payload 11 -> (Read payload))))
    '(Read (BorrowMutRef 0 (2 (Payload)) 11))
    #:rule 'R-UnionEliminateAtMutRef)
   '((derived mut 0 (2 (Payload)) 11 0 (2) 7)))
  (check-equal?
   (borrow-form-candidates
    '(UnionEliminateAt (BorrowMutRef 0 (2) 7)
       ((Int payload %parent -> (Read payload))))
    '(Read (BorrowMutRef 0 (2 (Payload)) 7))
    #:rule 'R-UnionEliminateAtMutRef)
   '((derived mut 0 (2 (Payload)) 7 0 (2) 7))))

(test-case "通常値を返す Handle は未実行 handler の借用参照を捨てる"
  (define config
    '(cfg (Handle (Return boundary (Borrowed Int 0))
            (captured -> (Read (BorrowMutRef 0 () 0)))
            1)
          ((0 (resource 1000))) ((0 Available)) () ()))
  (check-equal? (check-borrow-execution config #f #f 20 (make-bcounters))
                'ok))

(test-case "派生 binder の生存中は親の同じ path の消費だけを拒否する"
  (define (run-parent-use path)
    (check-borrow-execution (annotated-eliminate-config path)
                            #f #f 20 (make-bcounters)))
  (match (run-parent-use '(0))
    [(list 'fail 'reborrow-parent-live _) (void)]
    [other (fail (format "same-path parent use was not rejected: ~s" other))])
  (check-equal? (run-parent-use '(1)) 'ok))

(test-case "注釈付き Owned 分解の transit は内側の借用値をそのまま運ぶ"
  (check-equal?
   (borrow-form-candidates
    '(EliminateAt (OwnedTransit 0
                    (Construct (Record ((left (Borrowed Int 7) mut))) Pair
                               (BorrowRef 1 () 7)))
       ((Pair (left) (9) -> left)))
    '(EliminateAt
      (Construct (Record ((left (Borrowed Int 7) mut))) Pair
                 (BorrowRef 1 () 7))
      ((Pair (left) (9) -> left)))
    #:rule 'R-EliminateAtTransit)
   '())
  (check-equal?
   (borrow-form-candidates
    '(UnionEliminateAt (OwnedTransit 0
                           (UnionVal (Union (Borrowed Int 7) String)
                                     (Borrowed Int 7)
                                     (BorrowRef 1 () 7)))
       (((Borrowed Int 7) payload 9 -> payload)))
    '(UnionEliminateAt
      (UnionVal (Union (Borrowed Int 7) String)
                (Borrowed Int 7) (BorrowRef 1 () 7))
      (((Borrowed Int 7) payload 9 -> payload)))
    #:rule 'R-UnionEliminateAtTransit)
   '()))

(define nested-mut-eliminate
  (with-nested-mut-parent
   '(Eliminate (ProjBorrow p ro)
      ((some (c) ->
              (Scope ()
                (Let (d let (BorrowedMut Int ph))
                     (Eliminate (ProjBorrow p o)
                       ((some (c) -> c)
                        (none () -> (ProjBorrow p g))))
                  (Assign d 1))))
       (none () -> unit)))))

(test-case "R-EliminateMutRef の置換照合は入れ子の binder を区別する"
  (check-typed-oracle-ok nested-mut-eliminate
                         "nested-binder-eliminate-mut-ref"))

(test-case "R-EliminateRef の置換照合は入れ子の binder を区別する"
  (check-typed-oracle-ok
   (with-nested-shared-parent
    '(Eliminate (ProjBorrow p ro)
       ((some (c) ->
               (Let (d let (Borrowed Int ph))
                    (Eliminate (ProjBorrow p o)
                      ((some (c) -> c)
                       (none () -> (ProjBorrow p g))))
                 (Read d)))
        (none () -> 0))))
   "nested-binder-eliminate-ref"))

(test-case "R-UnionEliminateMutRef の置換照合は入れ子の binder を扱う"
  (check-typed-oracle-ok
   (with-nested-mut-parent
    '(UnionEliminate (ProjBorrow p u)
       ((Int c -> (Let (c let Int) (Read c) unit))
        (String text -> unit))))
   "nested-binder-union-eliminate"))

(test-case "R-EliminateMutRef の照合は使用される同名内側 binder を shadow として扱う"
  (check-typed-oracle-ok
   (with-nested-mut-parent
    '(Eliminate (ProjBorrow p ro)
       ((some (c) -> (Let (c let Int) 1
                       (Assign (ProjBorrow p g) c)))
        (none () -> unit))))
   "shadowed-binder-eliminate"))

(test-case "Eliminate は枝本体で運ぶ親の借用を新規生成と誤認しない"
  (check-typed-oracle-ok
   (with-nested-mut-parent
    '(Eliminate (ProjBorrow p o)
       ((some (n) -> (Read (ProjBorrow p g)))
        (none () -> 0))))
   "branch-carries-parent-borrow/eliminate"))

(test-case "UnionEliminate は枝本体で運ぶ親の借用を新規生成と誤認しない"
  (check-typed-oracle-ok
   (with-nested-mut-parent
    '(UnionEliminate (ProjBorrow p u)
       ((Int n -> (Read (ProjBorrow p g)))
        (String text -> 0))))
   "branch-carries-parent-borrow/union-eliminate"))

(test-case "Eliminate の置換で生じない借用は未検証のままにする"
  (check-equal?
   (borrow-form-candidates
    '(Eliminate (BorrowMutRef 0 () 2) ((some (c) -> c)))
    '(BorrowMutRef 0 (1) 2)
    #:rule 'R-EliminateMutRef)
   '((unverified))))

(test-case "規則名なしの未注釈分解は親子の寿命が異なる借用を承認しない"
  (check-equal?
   (borrow-form-candidates
    '(Eliminate (BorrowMutRef 0 () 7)
       ((Pair (left right) -> (Read left))))
    '(Read (BorrowMutRef 0 (0) 11)))
   '((unverified)))
  (check-equal?
   (borrow-form-candidates
    '(UnionEliminate (BorrowMutRef 0 () 7)
       ((Int payload -> (Read payload))))
    '(Read (BorrowMutRef 0 ((Payload)) 11)))
   '((unverified))))

(test-case "R-HandleReturn の照合は alpha-equivalent な binder を同一視する"
  (define op '(Return answer Int))
  (define pre
    `(cfg (Handle ,op (x -> (Let (k let Int) 0 x))
                  (Perform ,op (BorrowRef 0 () 0)))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Let (k«oracle» let Int) 0 (BorrowRef 0 () 0))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define result
    (provenance-extend (empty-provenance) 'R-HandleReturn pre post))
  (check-true (provenance? result))
  (check-equal? (resolve-designator result 'x) '(0)))

(test-case "共有借用の実行は ok になる"
  (check-equal? (first (run shared-skeleton)) 'ok))

(test-case "共有借用の実行は shared カウンタを進める"
  (check-true (positive? (bcounters-shared (second (run shared-skeleton))))))

(test-case "可変借用と代入の実行は ok になり use カウンタが進む"
  (match-define (list outcome counters) (run mut-skeleton))
  (check-equal? outcome 'ok)
  (check-true (positive? (bcounters-mut counters)))
  (check-true (positive? (bcounters-use counters))))

(test-case "Eliminate を含む静的側の借用集合は重複除去後の件数と一致する"
  (match-define (list 'ok _config sidecar ir)
    (prepare-borrow-term eliminate-ref-skeleton))
  (define expected
    (remove-duplicates
     (filter borrow-request? (borrow-sidecar-requests sidecar))))
  (check-equal? (length (static-borrow-set sidecar ir))
                (length expected))
  (check-true (> (length expected) 1)))

(test-case "初期 config に借用値がある実行は入口で discard になる"
  ;; prepare-borrow-term が弾くので、oracle へは届かない。
  (check-equal? (prepare-borrow-term
                 '(Scope () (Read (BorrowRef 0 () 0))))
                'discard))

(test-case "未追跡の親からの reborrow は fail になる"
  ;; 親の可変借用を静的側の要求に持たない config を手で組み、
  ;; R-Reborrow が根として発火したときに静的側と照合できないことを見る。
  (define config
    '(cfg (Scope (0) (ReborrowAt 0 (BorrowMutRef 0 () 0)))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (define empty-sidecar (borrow-sidecar '() (hash)))
  (match (check-borrow-execution config empty-sidecar #f 200
                                 (make-bcounters))
    [(list 'fail reason _detail) (check-equal? reason 'unmatched-reborrow)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "静的側に無い root borrow は unmatched-root になる"
  (define config
    '(cfg (Scope (0) (BorrowAt (RVar 0) (Own 0 ()) 0))
          ((0 1)) ((0 Available)) () ()))
  (define empty-sidecar (borrow-sidecar '() (hash)))
  (match (check-borrow-execution config empty-sidecar #f 200
                                 (make-bcounters))
    [(list 'fail reason _detail) (check-equal? reason 'unmatched-root)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "多価 provenance の ambiguous は後続の一意一致を隠さない"
  (define prov (provenance (hash 'w (set 0 1))))
  (define statics
    (list (list 'shared 'w '() 0)
          (list 'shared 0 '() 0)))
  (check-true (static-match-verdict statics 'shared '() 0 0 prov)))

(test-case "一意一致が無い ambiguous provenance は fail-closed になる"
  (define prov (provenance (hash 'w (set 0 1))))
  (match (static-match-verdict (list (list 'shared 'w '() 0))
                               'shared '() 0 0 prov)
    [(list 'fail 'ambiguous-designator _detail) (check-true #t)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "カウンタが 0 の欄を列挙できる"
  (define counters (make-bcounters))
  (check-equal? (sort (map symbol->string (bcounters-zeros counters))
                      string<?)
                '("mut" "proj" "reborrow" "scope-exit" "shared" "use")))

(test-case "raw pointer 規則は借用の置換規則へ分類されない"
  (for ([name (in-list '(R-AddressOf R-PtrOffset R-RawLoad R-RawStore
                         R-FromRawPtrConst R-FromRawPtrMut R-UnsafeExit))])
    (check-equal? (rule-bucket name) 'non-substituting)))

(test-case "R-RegionAppRecur は借用の置換規則へ分類されない"
  (check-equal? (rule-bucket 'R-RegionAppRecur) 'non-substituting))

(define borrowed-value '(BorrowRef 3 (a) 7))
(define transit-union-value
  `(UnionVal (Union Int (Borrowed Int 7)) (Borrowed Int 7) ,borrowed-value))

(test-case "R-ScopeAbort は同じ operation と payload の搬送だけを承認する"
  (define operation '(Return abort-boundary (Borrowed Int 7)))
  (define redex
    `(Scope (0)
       (Let (result const Never)
            (Perform ,operation ,borrowed-value)
            unit)))
  (define (candidates perform #:rule [rule 'R-ScopeAbort])
    (borrow-form-candidates redex perform #:rule rule))
  (check-equal? (candidates `(Perform ,operation ,borrowed-value)) '())
  (for ([wrong (in-list
                (list `(Perform (Return other-boundary (Borrowed Int 7))
                                ,borrowed-value)
                      `(Perform ,operation (BorrowRef 4 (a) 7))
                      `(Perform ,operation (BorrowRef 3 (b) 7))
                      `(Perform ,operation (BorrowRef 3 (a) 8))))])
    (check-equal? (candidates wrong) '((unverified))))
  (check-equal? (candidates `(Perform ,operation ,borrowed-value)
                            #:rule 'R-ScopeValue)
                '((unverified))))

(test-case "R-ScopeAbort 後の局所 owner を指す payload は runtime-row が拒否する"
  (define operation '(Return abort-boundary (Borrowed Int 0)))
  (define before-abort
    `(cfg (Scope (0) (Perform ,operation (BorrowRef 0 () 0)))
          ((0 7)) ((0 Available)) () ()))
  (match (raw-steps-g2/named before-abort)
    [(list (list 'R-ScopeAbort after-abort))
     (check-equal? (match after-abort
                     [`(cfg ,_ ,_ ,states ,_ ,_) states])
                   '((0 Dropped)))
     ;; ScopeAbort 後も payload が残るが、Dropped owner を指すため fail closed。
     (check-false (runtime-row after-abort '() 'Never))]
    [steps (fail (format "expected a single R-ScopeAbort step, got ~s" steps))]))

(define (check-approved-shape label redex contractum wrong-contractum)
  (check-equal? (borrow-form-candidates redex contractum) '()
                (format "~a redex=~s contractum=~s" label redex contractum))
  (check-equal? (borrow-form-candidates redex wrong-contractum)
                '((unverified)) label))

(test-case "借用値をそのまま運ぶ非置換規則だけを形で承認する"
  (check-approved-shape
   "R-Proj"
   `(Proj (Rec ((borrow imm ,borrowed-value))) borrow)
   borrowed-value
   '(BorrowRef 3 (a) 8))
  (check-approved-shape
   "R-ProjOpt"
   `(ProjOpt Int (Rec ((borrow imm ,borrowed-value))) borrow)
   `(Construct (Option Int) some ,borrowed-value)
   '(Construct (Option Int) some (BorrowRef 3 (a) 8)))
  (check-approved-shape
   "R-ProjOpt は Absent 欄から none を作る"
   `(ProjOpt Int (Rec ((borrow imm ,borrowed-value)
                       (missing imm (Absent Int))))
                missing)
   '(Construct (Option Int) none)
   `(Construct (Option Int) some ,borrowed-value))
  (check-approved-shape
   "R-UnionInject"
   `(UnionInject (Union (Borrowed Int 7) String)
                 (Borrowed Int 7) ,borrowed-value)
   `(UnionVal (Union (Borrowed Int 7) String)
             (Borrowed Int 7) ,borrowed-value)
   '(UnionVal (Union (Borrowed Int 7) String)
             (Borrowed Int 7) (BorrowRef 3 (a) 8)))
  (check-approved-shape
   "R-RecurBind の未使用 callable を含まない継続"
   `(Recur rf f () unit ,borrowed-value)
   borrowed-value
   '(BorrowRef 3 (a) 8))
  (check-approved-shape
   "R-RecRewrite-Close"
   `(RecRewriteOpen ((borrow imm (Borrowed Int 7) ,borrowed-value)))
   `(Rec ((borrow imm ,borrowed-value)))
   '(Rec ((borrow imm (BorrowRef 3 (a) 8)))))
  (check-approved-shape
   "R-HandleValue"
   `(Handle op (x -> unit) ,borrowed-value)
   borrowed-value
   '(BorrowRef 3 (a) 8))
  (check-approved-shape
   "R-HandleSkip"
   `(Handle op-a (x -> unit) (Perform op-b ,borrowed-value))
   `(Perform op-b ,borrowed-value)
   '(Perform op-b (BorrowRef 3 (a) 8)))
  (check-approved-shape "R-Suspend" `(Suspend ,borrowed-value)
                        borrowed-value
                        '(BorrowRef 3 (a) 8))
  (check-approved-shape
   "R-Discharge"
   `(Discharge
     (ProofRep (Reserved o-proof) (Implements Int Example))
     ,borrowed-value)
   borrowed-value
   '(BorrowRef 3 (a) 8))
  (check-approved-shape
   "R-DischargeRemainder"
   `(Discharge
     (ProofRep
      (Reserved o-proof)
      (RemainderSafelyDropped
       (Record ((borrow (Borrowed Int 7) imm) (owned (Owned Int) imm)))
       (Record ((borrow (Borrowed Int 7) imm)))))
     (Rec ((borrow imm ,borrowed-value) (owned imm 9))))
   `(Rec ((borrow imm ,borrowed-value)))
   '(Rec ((borrow imm (BorrowRef 3 (a) 8))))))

(test-case "R-UnsafeExit は包みだけを外して借用値を保つ"
  (check-equal?
   (borrow-form-candidates `(Unsafe ,borrowed-value) borrowed-value
                           #:rule 'R-UnsafeExit)
   '())
  (check-equal?
   (borrow-form-candidates `(Unsafe ,borrowed-value) borrowed-value
                           #:rule 'R-Suspend)
   '((unverified)))
  (check-equal?
   (borrow-form-candidates `(Unsafe ,borrowed-value) '(BorrowRef 3 (a) 8)
                           #:rule 'R-UnsafeExit)
   '((unverified))))

(test-case "Unsafe を抜けた借用は生存したまま競合を検出する"
  (define config
    '(cfg
      (Scope (0)
        (Let (first let (BorrowedMut Int 1))
             (Unsafe (BorrowMutAt 1 (Own 0 ()) 0))
          (Let (second let (BorrowedMut Int 2))
               (BorrowMutAt 2 (Own 0 ()) 0)
            (Assign first 3))))
      ((0 1)) ((0 Available)) () ()))
  (define sidecar
    (borrow-sidecar
     (list (borrow-request 0 '() 'mut 1 1 'first '(0))
           (borrow-request 0 '() 'mut 2 2 'second '(1)))
     (hash)))
  (match (check-borrow-execution config sidecar #f 30 (make-bcounters))
    [(list 'fail 'mut-not-exclusive _) (check-true #t)]
    [other (fail (format "競合の拒否を期待した: ~s" other))]))

(test-case "R-RegionAppRecur の空の借用 trace は oracle を通る"
  (define config
    '(cfg (Scope ()
           (Apply
            (RegionApp
             (RecurVal (Inst recf () (Poly (a))) f () 0)
             ())))
          () () () ()))
  (check-equal?
   (check-borrow-execution config (borrow-sidecar '() (hash)) #f 20
                          (make-bcounters))
   'ok))

(test-case "R-RecurBind は借用の無い本体から同じ継続への置換だけを承認する"
  (define redex
    `(Recur (Inst recf () (Poly (a))) loop (b) (Read b)
            (Apply (RegionApp loop (8)) ,borrowed-value)))
  (define contractum
    `(Apply
      (RegionApp
       (RecurVal (Inst recf () (Poly (a))) loop (b) (Read b))
       (8))
      ,borrowed-value))
  (define step
    (findf (lambda (tagged) (eq? (first tagged) 'R-RecurBind))
           (raw-steps-g2/named `(cfg ,redex () () () ()))))
  (check-not-false step "machine の R-RecurBind で継続が置換される")
  (when step
    (match (second step)
      [`(cfg ,after ,_ ...) (check-equal? after contractum)]
      [other (fail (format "cfg を期待した: ~s" other))]))
  (check-equal? (borrow-form-candidates redex contractum #:rule 'R-RecurBind)
                '())
  (for ([bad (in-list
              (list
               `(Apply (RegionApp (RecurVal (Inst recf () (Poly (a)))
                                          loop (b) (Read b)) (8))
                       (BorrowRef 4 (a) 7))
               `(Apply (RegionApp (RecurVal (Inst recf () (Poly (a)))
                                          loop (b) (Read b)) (8))
                       (BorrowRef 3 (b) 7))
               `(Apply (RegionApp (RecurVal (Inst recf () (Poly (a)))
                                          loop (b) (Read b)) (8))
                       (BorrowRef 3 (a) 8))
               `(Apply (RegionApp (RecurVal (Inst other () (Poly (a)))
                                          loop (b) (Read b)) (8))
                       ,borrowed-value)
               `(Apply (RegionApp (RecurVal (Inst recf () (Poly (a)))
                                          loop (q) (Read b)) (8))
                       ,borrowed-value)
               `(Apply (RegionApp (RecurVal (Inst recf () (Poly (a)))
                                          loop (b) 0) (8))
                       ,borrowed-value)
               `(Apply (RegionApp loop (8)) ,borrowed-value)))])
    (check-equal? (borrow-form-candidates redex bad #:rule 'R-RecurBind)
                  '((unverified)) (format "改変した contractum: ~s" bad)))
  (define body-borrow-redex
    `(Recur (Inst recf () (Poly (a))) loop (b)
            (Read ,borrowed-value)
            (Apply (RegionApp loop (8)) ,borrowed-value)))
  (define body-borrow-contractum
    `(Apply
      (RegionApp
       (RecurVal (Inst recf () (Poly (a))) loop (b)
                 (Read ,borrowed-value))
       (8))
      ,borrowed-value))
  (check-equal?
   (borrow-form-candidates body-borrow-redex body-borrow-contractum
                           #:rule 'R-RecurBind)
   '((unverified)) "本体内の BorrowRef は複製の恐れがあるため拒否")
  (for ([wrong-rule (in-list '(R-RegionApp R-RegionAppRecur R-RecurUnfold))])
    (check-equal? (borrow-form-candidates redex contractum #:rule wrong-rule)
                  '((unverified)) (symbol->string wrong-rule)))
  (check-equal? (borrow-form-candidates redex contractum)
                '((unverified)) "規則名なし"))

(test-case "R-RegionAppRecur は同じ実引数の搬送だけを承認する"
  (define redex
    `(Apply
      (RegionApp
       (RecurVal (Inst recf () (Poly (a))) f () (Read f))
       (8))
      ,borrowed-value (BorrowRef 3 (b) 9)))
  (define contractum
    `(Apply
      (RecurVal (Inst recf ((a 8)) Mono) f () (Read f))
      ,borrowed-value (BorrowRef 3 (b) 9)))
  (check-equal? (borrow-form-candidates redex contractum
                                        #:rule 'R-RegionAppRecur)
                '())
  (for ([bad (in-list
              (list
               `(Apply (RecurVal (Inst recf ((a 8)) Mono) f () (Read f))
                       (BorrowRef 4 (a) 7) (BorrowRef 3 (b) 9))
               `(Apply (RecurVal (Inst recf ((a 8)) Mono) f () (Read f))
                       (BorrowRef 3 (b) 7) (BorrowRef 3 (b) 9))
               `(Apply (RecurVal (Inst recf ((a 8)) Mono) f () (Read f))
                       (BorrowRef 3 (a) 8) (BorrowRef 3 (b) 9))
               `(Apply (RecurVal (Inst recf ((a 8)) Mono) f () (Read f))
                       (BorrowRef 3 (b) 9) ,borrowed-value)
               `(Apply (RecurVal (Inst recf ((a 8)) Mono) f () (Read f))
                       ,borrowed-value)))])
    (check-equal? (borrow-form-candidates redex bad
                                          #:rule 'R-RegionAppRecur)
                  '((unverified))))
  (for ([wrong-rule (in-list '(R-RegionApp R-AppRecur R-RecurUnfold))])
    (check-equal? (borrow-form-candidates redex contractum
                                          #:rule wrong-rule)
                  '((unverified)) (symbol->string wrong-rule)))
  (check-equal? (borrow-form-candidates redex contractum)
                '((unverified)) "規則名なし"))

(test-case "R-RegionApp は同じ実引数を保つ BorrowRef の置換を運ぶ"
  (define redex
    `(Apply
      (RegionApp
       (RegionLam (a) (BorrowRef 1 () (RParam a)))
       (8))
      ,borrowed-value (BorrowRef 3 (b) 9)))
  (define contractum
    `(Apply (BorrowRef 1 () 8) ,borrowed-value (BorrowRef 3 (b) 9)))
  (define start `(cfg ,redex () () () ()))
  (define step
    (findf (lambda (tagged) (eq? (first tagged) 'R-RegionApp))
           (raw-steps-g2/named start)))
  (check-not-false step "R-RegionApp が BorrowRef を含む本体で発火する")
  (when step
    (match (second step)
      [`(cfg ,after ,_ ...)
       (check-equal? after contractum "実際の R-RegionApp が BorrowRef の rho だけを置換する")]
      [other (fail (format "cfg を期待した: ~s" other))]))
  (check-equal? (borrow-form-candidates redex contractum
                                        #:rule 'R-RegionApp)
                '())
  (for ([bad (in-list
              (list
               `(Apply (BorrowRef 1 () 8) (BorrowRef 4 (a) 7)
                       (BorrowRef 3 (b) 9))
               `(Apply (BorrowRef 1 () 8) (BorrowRef 3 (b) 7)
                       (BorrowRef 3 (b) 9))
               `(Apply (BorrowRef 1 () 8) (BorrowRef 3 (a) 8)
                       (BorrowRef 3 (b) 9))
               `(Apply (BorrowRef 1 () 8) (BorrowRef 3 (b) 9)
                       ,borrowed-value)
               `(Apply (BorrowRef 1 () 8) ,borrowed-value)))])
    (check-equal? (borrow-form-candidates redex bad #:rule 'R-RegionApp)
                  '((unverified))))
  (for ([wrong-rule (in-list '(R-RegionAppRecur R-AppRecur))])
    (check-equal? (borrow-form-candidates redex contractum
                                          #:rule wrong-rule)
                  '((unverified)) (symbol->string wrong-rule)))
  (check-equal? (borrow-form-candidates redex contractum)
                '((unverified)) "規則名なし"))

(test-case "R-UnionEliminateTransit は UnionVal 全体を保つ移送だけを承認する"
  (define redex `(OwnedTransit p ,transit-union-value))
  (check-equal? (borrow-form-candidates redex transit-union-value
                                        #:rule 'R-UnionEliminateTransit)
                '())
  (check-equal?
   (borrow-form-candidates
    redex `(UnionVal (Union Int (Borrowed Int 7)) (Borrowed Int 7)
                     (BorrowRef 3 (a) 8))
    #:rule 'R-UnionEliminateTransit)
   '((unverified)) "payload が変わる")
  (check-equal?
   (borrow-form-candidates
    redex `(UnionVal (Union (Borrowed Int 7) Int) (Borrowed Int 7)
                     ,borrowed-value)
    #:rule 'R-UnionEliminateTransit)
   '((unverified)) "Union 型 tag が変わる")
  (check-equal?
   (borrow-form-candidates
    redex `(UnionVal (Union Int (Borrowed Int 7)) Int ,borrowed-value)
    #:rule 'R-UnionEliminateTransit)
   '((unverified)) "member 型 tag が変わる"))

(test-case "Union の移送の承認形は他の規則名へ漏れない"
  (define redex `(OwnedTransit p ,transit-union-value))
  (for ([name (in-list '(R-EliminateTransit R-ApplyTransit
                         R-CurryTransit R-OwnLeafTransit))])
    (check-equal? (borrow-form-candidates redex transit-union-value
                                          #:rule name)
                  '((unverified)) (symbol->string name)))
  (check-equal? (borrow-form-candidates redex transit-union-value)
                '((unverified)) "規則名なし"))

(test-case "R-UnionEliminateTransit でも UnionVal でない移送は承認しない"
  (check-equal?
   (borrow-form-candidates `(OwnedTransit p ,borrowed-value) borrowed-value
                           #:rule 'R-UnionEliminateTransit)
   '((unverified))))

(test-case "R-UnionEliminateTransit でも枝の列が変わる遷移は承認しない"
  (define diff
    (control-diff
     `(UnionEliminate (OwnedTransit p ,transit-union-value) ((Int n -> n)))
     `(UnionEliminate ,transit-union-value ((Int n -> 0)))))
  (check-equal? (borrow-form-candidates (car diff) (cdr diff)
                                        #:rule 'R-UnionEliminateTransit)
                '((unverified))))

(test-case "Owned Union の除去の実行は oracle を通る"
  (define skeleton
    '(Scope ()
       (Let (u let (Owned (Union Int String)))
            (UnionInject (Union Int String) Int 1000)
         (UnionEliminate (Move u) ((Int n -> n) (String s -> 0))))))
  (check-equal? (first (run skeleton)) 'ok))

(test-case "Union payload binder の reborrow は oracle を通る"
  (define skeleton
    '(Scope ()
       (Let (x let (Owned (Record ((u (Union Int String) mut)))))
            (Rec ((u mut (UnionInject (Union Int String) Int 1000))))
         (Scope ()
           (Let (p let (BorrowedMut (Record ((u (Union Int String) mut))) ph))
                (BorrowMut x)
             (UnionEliminate (ProjBorrow p u)
               ((Int c ->
                  (Let (r let (Borrowed Int ph)) (Reborrow c)
                    (Let (value let Int) (Read r) unit)))
                (String text -> unit))))))))
  (match (prepare-borrow-term* skeleton)
    [(list 'ok config sidecar ir _type)
     (check-equal? (check-borrow-execution config sidecar ir 200
                                           (make-bcounters))
                   'ok)]
    [other (fail (format "Core が型検査されなかった: ~s" other))]))

(test-case "生きている借用の place を move する遷移は fail になる"
  ;; 条件 1。Ω が Available から Moved へ変わる前後の config を手で組む。
  ;; place 0 を指す共有借用が制御項に生きているので落ちる。
  (define pre
    '(cfg (Scope (0) (Read (BorrowRef 0 () 0)))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 () 0)))
          ((0 (resource 1000))) ((0 Moved)) () ()))
  (match (check-no-move-of-live pre post)
    [(list 'fail reason place)
     (check-equal? reason 'move-of-live-borrow)
     (check-equal? place 0)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "Dropped place の stale BorrowRef は生きている loan に数えない"
  (define heap
    '((0 7) (1 (BorrowRef 0 () 0))))
  (define pre
    `(cfg unit ,heap ((0 Available) (1 Dropped)) () ()))
  (define post
    `(cfg unit ,heap ((0 Dropped) (1 Dropped)) () ()))
  (check-false (check-no-move-of-live pre post)))

(test-case "同じ Scope 遷移で owner と BorrowRef holder が Dropped になる"
  (define heap
    '((0 7) (1 (BorrowRef 0 () 0))))
  (define pre
    `(cfg (Scope (0 1) unit) ,heap ((0 Available) (1 Available)) () ()))
  (define post
    `(cfg unit ,heap ((0 Dropped) (1 Dropped)) () ()))
  ;; Scope の終了後には両 place の値へ到達できず、post に live loan は無い。
  (check-false (check-no-move-of-live pre post)))

(test-case "Available 値の BorrowRef 先を Move すると move-of-live-borrow"
  (define heap
    '((0 7) (1 (BorrowRef 0 () 0))))
  (define pre
    `(cfg unit ,heap ((0 Available) (1 Available)) () ()))
  (define post
    `(cfg unit ,heap ((0 Moved) (1 Available)) () ()))
  (match (check-no-move-of-live pre post)
    [(list 'fail reason place)
     (check-equal? reason 'move-of-live-borrow)
     (check-equal? place 0)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "同じ可変借用値の二つの出現は check-mut-exclusive で失敗しない"
  ;; 同じ 4 つ組の二つの出現は一つの借用の複製である（borrow.md §4）。
  (define config
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 0)
                             (Read (BorrowMutRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (check-false (check-mut-exclusive config)))

(test-case "直接 Reborrow の子と親の同時出現だけでは失敗しない"
  ;; 子は共有で ρ が 0、親は可変で ρ が 1 であり、place と欄 path は同じ。
  (define config
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 1)
                             (Read (BorrowRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (check-false
   (check-reborrow-parents
    config (list (list 'reborrow '(shared 0 () 0) '(mut 0 () 1))))))

(define (direct-reborrow-parent-use-result parent-use)
  (define sidecar
    (borrow-sidecar
     (list (borrow-request 0 '() 'shared 'oracle-alpha 1 'child '(0 0)))
     (hash)))
  (define config
    `(cfg
      (Scope (0)
        (Let (child let (Borrowed Int 1))
             (ReborrowAt 1 (BorrowMutRef 0 () 0))
          (Let (ignored const Unit) ,parent-use (Read child))))
      ((0 (resource 1000))) ((0 Available)) () ()))
  (check-borrow-execution config sidecar #f 100 (make-bcounters)))

(define (two-direct-reborrows-result parent-use)
  (define sidecar
    (borrow-sidecar
     (list (borrow-request 0 '() 'shared 'oracle-alpha-first 1
                           'first-child '(0 0))
           (borrow-request 0 '() 'shared 'oracle-alpha-second 2
                           'second-child '(0 1)))
     (hash)))
  (define after
    '(Let (first-use const Unit) (Read first)
       (Read second)))
  (define body
    (if parent-use
        `(Let (parent-use const Unit) ,parent-use ,after)
        after))
  (define config
    `(cfg
      (Scope (0 1 2)
        (Let (first let (Borrowed Int 1))
             (ReborrowAt 1 (BorrowMutRef 0 () 0))
          (Let (second let (Borrowed Int 2))
               (ReborrowAt 2 (BorrowMutRef 0 () 0))
            ,body)))
      ((0 (resource 1000))) ((0 Available)) () ()))
  (check-borrow-execution config sidecar #f 100 (make-bcounters)))

(test-case "直接 Reborrow の子が生きている間の親 Assign は拒否する"
  (match (direct-reborrow-parent-use-result '(Assign (BorrowMutRef 0 () 0) 9))
    [(list 'fail 'reborrow-parent-live _detail) (check-true #t)]
    [other (fail (format "expected Assign rejection, got ~e" other))]))

(test-case "直接 Reborrow の子が生きている間の親 Read は受理"
  (match (direct-reborrow-parent-use-result '(Read (BorrowMutRef 0 () 0)))
    ['ok (check-true #t)]
    [other (fail (format "expected Read acceptance, got ~e" other))]))

(test-case "oracle は共有子の生存中に直接 Reborrow をもう一つ作れる"
  (check-equal? (two-direct-reborrows-result #f) 'ok))

(test-case "oracle は共有 Reborrow 子の生存中の親 Assign を拒否する"
  (match (two-direct-reborrows-result '(Assign (BorrowMutRef 0 () 0) 9))
    [(list 'fail 'reborrow-parent-live _detail) (check-true #t)]
    [other (fail (format "expected reborrow-parent-live, got ~e" other))]))

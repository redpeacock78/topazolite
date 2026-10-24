#lang racket

(require rackunit
         racket/match
         racket/set
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt")

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

(test-case "同じ可変借用値の二つの出現は check-mut-exclusive で失敗しない"
  ;; 同じ 4 つ組の二つの出現は一つの借用の複製である（borrow.md §4）。
  (define config
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 0)
                             (Read (BorrowMutRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (check-false (check-mut-exclusive config)))

(test-case "reborrow の子が生きている間に親が現れると fail になる"
  ;; 条件 3。update-parents が積む (子 親) の対をそのまま渡す。
  ;; 子は共有で ρ が 0、親は可変で ρ が 1 であり、place と欄 path は同じ。
  (define config
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 1)
                             (Read (BorrowRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (define parents (list (list '(shared 0 () 0) '(mut 0 () 1))))
  (match (check-reborrow-parents config parents)
    [(list 'fail reason _pair) (check-equal? reason 'reborrow-parent-live)]
    [other (fail (format "unexpected: ~e" other))]))

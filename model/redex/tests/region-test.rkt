#lang racket

(require rackunit
         racket/match
         racket/set
         "../elaborate.rkt"
         "../erase.rkt"
         "../region.rkt"
         "../resource-type.rkt")

;; [REQ: BOR-003] point は意味的な子の添字の列である。
;; 生の位置で数えると、spanful な項と spanless な項で同じ部分項が別の添字に来る。
(test-case "Apply の子は被適用項に続けて引数である"
  (check-equal? (core-children '(Apply f 1 2)) '(f 1 2)))

(test-case "span、束縛子、型、op は子に数えない"
  (check-equal? (core-children '(Let (x Int) 1 2)) '(1 2))
  (check-equal? (core-children '(Let (x const Int) 1 2)) '(1 2))
  (check-equal? (core-children '(Perform (Return b Int) 1)) '(1))
  (check-equal? (core-children '(Handle (Return b Int) (k -> 1) 2)) '(1 2))
  (check-equal? (core-children '(Scope () 1)) '(1))
  (check-equal? (core-children '(Proj 1 fld)) '(1))
  (check-equal? (core-children '(ProjOpt Int 1 fld)) '(1))
  (check-equal? (core-children '(Lam User c0 (x y) 1)) '(1)))

(test-case "Eliminate は scrutinee に続けて分岐の本体を分岐の順に並べる"
  (check-equal?
   (core-children '(Eliminate 0 ((nil () -> 1) (cons (h t) -> 2))))
   '(0 1 2)))

(test-case "UnionEliminate の全枝が同じ borrow owner を返す"
  (define core
    '(Scope (1)
       (Let (borrowed const (Borrowed Res 0))
            (UnionEliminate (Borrow 1)
              ((Int i -> (Borrow 1))
               (String s -> (Borrow 1))))
         (Reborrow borrowed))))
  (define annotated (annotate-regions core (build-region-ir core)))
  (match annotated
    [`(Scope ,_ (Let (borrowed const ,_)
                      (UnionEliminate ,_ ,_)
                      (ReborrowAt ,_ borrowed)))
     (void)]
    [_ (fail (format "unexpected annotated UnionEliminate: ~s" annotated))]))

;; docs/specification/region.md §3 の production を 1 件ずつ実データで通す。
;; 未知形の error は落ちた production を見つけない。既定へ落ちず個別の節が
;; 受けていることは、この試験だけが押さえる。
;; Construct と Rec は c 側と v 側の双方に同じ形の production を持つ。
;; G2 は c ::= v なので、子を整数だけにすると v 側の実装でも通ってしまう。
;; c 専用の形である Apply を子に置き、c 側の経路を分けて押さえる。
(test-case "c 側の残る production も子を返す"
  (check-equal? (core-children '(Construct Int Wrap (Apply f 1) 2))
                '((Apply f 1) 2))
  (check-equal? (core-children '(Rec ((fst imm (Apply f 1)) (snd mut 2))))
                '((Apply f 1) 2))
  (check-equal? (core-children '(Recur c0 f (x) 1 2)) '(1 2))
  (check-equal? (core-children '(Yield 1 2)) '(1 2))
  (check-equal? (core-children '(Suspend 1)) '(1))
  (check-equal? (core-children '(Drop 1)) '(1))
  (check-equal? (core-children '(Curry 1 2)) '(1 2))
  (check-equal? (core-children '(Discharge (ProofRep User ValidNarrativeTrait) 1))
                '(1))
  (check-equal?
   (core-children
    '(Discharge
      (ProofRep (#:span #:synthetic 0 0)
                (Reserved o-type-narrative)
                TypeNarrativeCap)
      (Apply f 1)))
   '((Apply f 1))))

;; Construct と Rec は c 側と v 側で同じ形を持つ。
;; 1 つの節が両方を受けることを、値だけを子に持つ実データで確かめる。
;; 内側に Scope を置くのは、値を葉として扱うと Scope を落とすためである。
(test-case "v 側の Construct と Rec も内側を歩く"
  (check-equal?
   (core-children '(Construct Int Wrap (Lam User c0 (x) (Scope () x))))
   '((Lam User c0 (x) (Scope () x))))
  (check-equal?
   (core-children '(Rec ((fst imm (Lam User c0 (x) (Scope () x))))))
   '((Lam User c0 (x) (Scope () x))))
  (check-equal?
   (core-points '(Rec ((fst imm (Lam User c0 (x) (Scope () x))))))
   '(() (0) (0 0) (0 0 0))))

;; 値の内側も歩く。Lam の本体は Scope を含むため、値を葉として扱うと
;; Scope を 1 つも見つけられない。
(test-case "値の内側も歩く"
  (check-equal? (core-children '(UVal 1)) '(1))
  (check-equal? (core-children '(RVal (ProofRep User ValidNarrativeTrait) 1))
                '(1))
  (check-equal? (core-children '(CurryVal User 1 2)) '(1 2))
  (check-equal? (core-children '(RecurVal c0 f (x) 1)) '(1)))

(test-case "core-children は Owned leaf の payload を子にする"
  (check-equal? (core-children '(OwnedLeaf (tok 0) x)) '(x)))

(test-case "core-with-children は Owned leaf を組み直す"
  (check-equal? (core-with-children '(OwnedLeaf (tok 0) x) '(y))
                '(OwnedLeaf (tok 0) y)))

(test-case "ProjOpt の意味的な子を差し替える"
  (check-equal? (core-with-children '(ProjOpt Int (Apply f 1) fld)
                                     '((Apply g 2)))
                '(ProjOpt Int (Apply g 2) fld)))

(test-case "UnionVal の region walker は payload だけを一度辿る"
  (define value '(UnionVal (Union Int String) Int x))
  (check-equal? (core-children value) '(x))
  (check-equal? (core-with-children value '(y))
                '(UnionVal (Union Int String) Int y))
  (check-equal? (core-points value) '(() (0)))
  (check-equal? (core-free-vars value) (set 'x)))

(test-case "RecRewriteOpen は型注釈を子にせず作業項だけを歩く"
  (define output-type '(Record ((value Int imm))))
  (define core
    `(RecRewriteOpen ((a imm (Apply f 1))
                     (b mut ,output-type (Scope () x)))))
  (check-equal? (core-children core) '((Apply f 1) (Scope () x)))
  (check-equal? (core-with-children core '(g (Scope () y)))
                `(RecRewriteOpen ((a imm g)
                                  (b mut ,output-type (Scope () y)))))
  (check-equal? (core-points core)
                '(() (0) (0 0) (0 1) (1) (1 0)))
  (check-equal? (core-free-vars core) (set 'f 'x)))

(test-case "Absent は Rec の欄の子であり、自身は葉である"
  (define core '(Rec ((a imm 1) (o imm (Absent Int)))))
  (define children (core-children core))
  (check-equal? children '(1 (Absent Int)))
  (check-equal? (core-children '(Absent Int)) '())
  (define rebuilt (core-with-children core children))
  (check-equal? rebuilt core)
  (check-equal? (core-points rebuilt) (core-points core)))

(test-case "core-free-vars は Owned leaf の payload を見る"
  (check-equal? (core-free-vars '(OwnedLeaf (tok 0) x)) (set 'x)))

(test-case "子を持たない形は空を返す"
  (for ([t (in-list (list 3 "s" 'unit 'x '(Move y)
                          '(MutSlot 0)
                          '(PrimVal User add)
                          '(TypeRep User Int Type)
                          '(ProofRep User ValidNarrativeTrait)
                          '(resource 0)))])
    (check-equal? (core-children t) '() (format "~s" t))
    (check-equal? (core-with-children t '()) t (format "~s round-trip" t))))

;; 既定を空にすると、c の production が増えたときに走査が黙って内側を飛ばし、
;; 内部の Scope を落とした IR が試験を通ってしまう。
(test-case "知らない形は error を出す"
  (check-exn exn:fail? (lambda () (core-children '(NotACoreForm 1)))))

(test-case "core-points は根から前順で全 point を返す"
  (check-equal? (core-points '(Apply f (Suspend 1)))
                '(() (0) (1) (1 0))))

(test-case "core-node は point の指す節点を返し、指せない point で error を出す"
  (define core '(Apply f (Suspend 1)))
  (check-equal? (core-node core '()) core)
  (check-equal? (core-node core '(1 0)) 1)
  (check-exn exn:fail? (lambda () (core-node core '(2))))
  (check-exn exn:fail? (lambda () (core-node core '(0 0)))))

;; erase-core は span と metadata を落とす写像である。
;; point は erase-core を通した項の上で数えるため、spanful な項を渡しても
;; spanless な項を渡しても同じ point の集合になる。
(test-case "core-points は erase-core を入口に通す"
  (match-define (list raw-core _ _ _) (elab '(Apply (Fn ((x Int)) Int () x) 1)))
  (check-equal? (core-points raw-core) (core-points (erase-core raw-core))))

;; [REQ: BOR-003] 問い合わせの層を builder と切り離して試験する。
;; IR をここで手組みするのは、builder の誤りが問い合わせの試験を通す経路を
;; 断つためである。
(define ρ0 (region 0))
(define ρ1 (region 1))
(define ρ2 (region 2))

;; 根の節点が Scope でない Core を選ぶ。
;; 根が Scope だと root region がどの point からも返らず、C6 の σ が
;; root を覆えない。
(define nested '(Apply f (Scope () (Apply g (Scope () 1)))))
(define nested-points (list->set (core-points nested)))

(define (hand-ir #:regions [regions (set ρ0 ρ1 ρ2)]
                 #:outlives [outlives (set (list ρ0 ρ1) (list ρ1 ρ2))]
                 #:owners [owners (hash ρ0 '() ρ1 '() ρ2 '())]
                 #:parents [parents (hash ρ1 ρ0 ρ2 ρ1)]
                 #:at-table [at-table (hash '(1) ρ1 '(1 0 1) ρ2)]
                 #:exit-table [exit-table at-table]
                 #:owner-body-table [owner-body-table (hash)]
                 #:points [points nested-points]
                 #:control-order-barriers [control-order-barriers (set)]
                 #:projborrow-place-points [projborrow-place-points (set)]
                 #:eliminate-table [eliminate-table (hash)]
                 #:branch-table [branch-table (hash)]
                 #:callable-body-points [callable-body-points (set)])
  (lexical-region-ir regions outlives owners parents at-table exit-table
                     owner-body-table points control-order-barriers
                     projborrow-place-points eliminate-table
                     callable-body-points branch-table))

(test-case "既定の手組み IR は 8 条件と 2 条件を満たす"
  (check-true (region-ir-ok? (hand-ir) nested))
  (check-true (lexical-region-ir-ok? (hand-ir)))
  (check-true (region-solver? (hand-ir))))

(test-case "Handle と Recur の制御境界を point に記録する"
  (define handle-ir (build-region-ir '(Handle (Return b Int) (k -> k) 0)))
  (define recur-ir (build-region-ir '(Recur c0 f () 0 1)))
  (check-equal? (lexical-region-ir-control-order-barriers handle-ir)
                (set (list '() 'handle)))
  (check-equal? (lexical-region-ir-control-order-barriers recur-ir)
                (set (list '() 'recur)))
  (check-true (lexical-region-ir-ok? handle-ir))
  (check-true (lexical-region-ir-ok? recur-ir)))

(test-case "Read/Assign の place 射影 chain だけを IR に記録する"
  (define ir
    (build-region-ir
     '(Scope ()
        (Let (a let Int) (Read (ProjBorrow (#:span src 0 1) (ProjBorrow p f) h))
          (Assign (ProjBorrow p g) 1)))))
  (check-true (region-projborrow-place? ir '(0 0 0)))
  (check-true (region-projborrow-place? ir '(0 0 0 0)))
  (check-true (region-projborrow-place? ir '(0 1 0)))
  (check-true (lexical-region-ir-ok? ir))
  (define value-ir (build-region-ir '(Eliminate (ProjBorrow p f) ())))
  (check-false (region-projborrow-place? value-ir '(0))))

(test-case "分解の region は Scope の子で region-at には現れない"
  (define core
    '(Scope ()
       (Let (x let Int) 1
         (Eliminate y ((none () -> unit) (some (v) -> unit))))))
  (define ir (build-region-ir core))
  (define scope-region (region-at ir '(0)))
  (define elim-point '(0 1))
  (define elim-region (region-at/eliminate ir '(0 1 0)))
  (check-equal? (region-at ir '(0 1 0)) scope-region)
  (check-not-equal? elim-region scope-region)
  (check-true (region-decomposition-point? ir elim-point))
  (check-equal? (regions-exiting-at ir elim-point)
                (set elim-region
                     (branch-region-of ir elim-point 0)
                     (branch-region-of ir elim-point 1)))
  (check-true (region-outlives? ir scope-region elim-region))
  (check-equal? (region->rho ir elim-region) (region->rho ir scope-region))
  (check-true
   (region-decomposition-scrutinee?
    (build-region-ir '(Scope () (Eliminate (ProjBorrow p f) ()))) '(0 0)))
  (check-true (lexical-region-ir-ok? ir)))

(test-case "owner 型の Let の本体にある分解の親は owner-body の region"
  (define core
    '(Let (x let (Owned Int)) 1
       (Eliminate y ((none () -> unit) (some (v) -> unit)))))
  (define ir (build-region-ir core))
  (define body-region (region-at ir '(1)))
  (define elim-region (region-at/eliminate ir '(1 0)))
  (check-not-equal? elim-region body-region)
  (check-true (region-outlives? ir body-region elim-region))
  (check-true (lexical-region-ir-ok? ir)))

(test-case "枝の中の Scope の親の鎖は分解の region を経由する"
  (define core
    '(Scope ()
       (Eliminate y ((none () -> (Scope () unit)) (some (v) -> unit)))))
  (define ir (build-region-ir core))
  (define elim-region (region-at/eliminate ir '(0 0)))
  (define inner (region-at ir '(0 1 0)))
  (check-true (region-outlives? ir elim-region inner))
  (check-equal? (region-at/eliminate ir '(0 1 0)) inner))

(test-case "入れ子の分解の region の親は外側の枝 region"
  (define core
    '(Scope ()
       (Eliminate y
         ((none () -> (Eliminate z ((none () -> unit) (some (w) -> unit))))
          (some (v) -> unit)))))
  (define ir (build-region-ir core))
  (define outer (region-at/eliminate ir '(0 0)))
  (define inner (region-at/eliminate ir '(0 1 0)))
  (define outer-branch (branch-region-of ir '(0) 0))
  (check-not-equal? inner outer)
  (check-equal? (region-parent ir inner) outer-branch)
  (check-equal? (region-parent ir outer-branch) outer)
  (check-equal? (region-parent ir outer) (region-at ir '(0)))
  (check-equal? (region->rho ir inner) (region->rho ir (region-at ir '(0))))
  (check-true (lexical-region-ir-ok? ir)))

(test-case "閉包の本体の境界の外の分解は数えない"
  (define core
    '(Scope ()
       (Eliminate y
         ((none () -> (Lam User c0 ()
                        (Eliminate z ((none () -> unit) (some (w) -> unit)))))
          (some (v) -> unit)))))
  (define ir (build-region-ir core))
  (check-equal? (region-enclosing-decompositions ir '(0 1 0 1))
                '((0 1 0)))
  (check-equal? (region-enclosing-decompositions ir '(0 2)) '((0))))

(test-case "RecurVal と Recur の本体は境界、Recur の継続は境界でない"
  (define inner-eliminate
    '(Eliminate z ((none () -> unit) (some (w) -> unit))))
  (define outer '(0))
  (define core/recurval
    `(Scope ()
       (Eliminate y
         ((none () -> (RecurVal c0 f () ,inner-eliminate))
          (some (v) -> unit)))))
  (define inner/recurval '(0 1 0))
  (define point/recurval-inner '(0 1 0 1))
  (define ir-recurval (build-region-ir core/recurval))
  (check-equal? (region-enclosing-decompositions ir-recurval point/recurval-inner)
                (list inner/recurval))
  (define core/recur
    `(Scope ()
       (Eliminate y
         ((none () -> (Recur c1 f () ,inner-eliminate ,inner-eliminate))
          (some (v) -> unit)))))
  (define inner/recur-body '(0 1 0))
  (define inner/recur-continuation '(0 1 1))
  (define ir-recur (build-region-ir core/recur))
  (check-equal? (region-enclosing-decompositions ir-recur
                                                  '(0 1 0 1))
                (list inner/recur-body))
  (check-equal? (region-enclosing-decompositions ir-recur
                                                  '(0 1 1 1))
                (list inner/recur-continuation outer)))

(test-case "3 成分の器の形を検査する"
  ;; 1. regions が region の集合である。
  (check-false (region-ir-ok? (hand-ir #:regions (set ρ0 'not-a-region))
                              nested))
  ;; 2. outlives の対は要素をちょうど 2 個持ち、いずれも region である。
  (check-false (region-ir-ok? (hand-ir #:outlives (set (list ρ0))) nested))
  (check-false (region-ir-ok? (hand-ir #:outlives (set (list ρ0 'x))) nested))
  ;; 3. owners の値は π、すなわち p の列である。
  (check-false (region-ir-ok? (hand-ir #:owners (hash ρ0 'nope ρ1 '() ρ2 '()))
                              nested)))

(test-case "3 成分の間の整合を検査する"
  ;; 4. regions が空でない。
  (check-false (region-ir-ok?
                (hand-ir #:regions (set) #:outlives (set) #:owners (hash)
                         #:parents (hash) #:at-table (hash))
                nested))
  ;; 5. outlives に現れる region がすべて regions に含まれる。
  (check-false (region-ir-ok?
                (hand-ir #:outlives (set (list ρ0 (region 9)))) nested))
  ;; 6. owners の定義域が regions と一致する。
  (check-false (region-ir-ok? (hand-ir #:owners (hash ρ0 '() ρ1 '())) nested)))

(test-case "問い合わせの返値を検査する"
  ;; 7. regions-exiting-at が Core のどの point でも regions の部分集合を返す。
  (check-false (region-ir-ok?
                (hand-ir #:exit-table (hash '(1) ρ1 '(1 0 1) (region 9)))
                nested))
  ;; 8. region-at が Core のどの point でも regions の元を返す。
  ;;    parents を循環させると親を持たない region が無くなり、lexical-root が
  ;;    #f を返す。at-table を空にすれば region-at はどの point でも #f となり、
  ;;    条件 8 だけが偽になる。region を regions の外の値へ向ける at-table では、
  ;;    先に条件 7 が偽になるため、条件 8 を切り分けられない。
  (check-false (region-ir-ok?
                (hand-ir #:regions (set ρ1 ρ2)
                         #:outlives (set (list ρ1 ρ2))
                         #:owners (hash ρ1 '() ρ2 '())
                         #:parents (hash ρ1 ρ2 ρ2 ρ1)
                         #:at-table (hash))
                nested)))

(test-case "lexical-region-ir-ok? は親子の 2 条件を検査する"
  ;; parents の定義域と値域が regions に含まれる。
  (check-false (lexical-region-ir-ok?
                (hand-ir #:parents (hash ρ1 ρ0 ρ2 (region 9)))))
  ;; 親を持たない region がちょうど 1 つある。
  (check-false (lexical-region-ir-ok? (hand-ir #:parents (hash ρ1 ρ0))))
  ;; 循環が無い。
  (check-false (lexical-region-ir-ok?
                (hand-ir #:parents (hash ρ1 ρ2 ρ2 ρ1)))))

(test-case "region-at は Scope を指す最長の接頭辞が開いた region を返す"
  (define ir (hand-ir))
  (check-equal? (region-at ir '()) ρ0)
  (check-equal? (region-at ir '(0)) ρ0)
  (check-equal? (region-at ir '(1)) ρ1)
  (check-equal? (region-at ir '(1 0)) ρ1)
  (check-equal? (region-at ir '(1 0 0)) ρ1)
  (check-equal? (region-at ir '(1 0 1)) ρ2)
  (check-equal? (region-at ir '(1 0 1 0)) ρ2))

(test-case "regions-exiting-at は Scope の point でちょうど 1 件を返す"
  (define ir (hand-ir))
  (check-equal? (regions-exiting-at ir '(1)) (set ρ1))
  (check-equal? (regions-exiting-at ir '(1 0 1)) (set ρ2))
  (check-equal? (regions-exiting-at ir '()) (set))
  (check-equal? (regions-exiting-at ir '(1 0)) (set)))

(define owner-let-scope '(Let (owner let (Owned Int)) 1 (Scope () owner)))
(define owner-let-value '(Let (owner let (Owned Int)) 1 0))

(test-case "owner Let body と直下 Scope の region と退場を区別する"
  (define ir (build-region-ir owner-let-scope))
  (define λ (owner-let-body-region ir '()))
  (define σ (region-at ir '(1)))
  (check-not-equal? λ σ)
  (check-equal? (region-parent ir σ) λ)
  (check-equal? (region-at ir '(1 0)) σ)
  (check-equal? (regions-exiting-at ir '(1)) (set σ))
  (check-false (set-member? (regions-exiting-at ir '(1)) λ))
  (check-equal? (regions-exiting-at ir '()) (set))
  (check-true (region-ir-ok? ir owner-let-scope))
  (check-true (lexical-region-ir-ok? ir)))

(test-case "Scope の無い owner Let は body point に region を持ち退場を作らない"
  (define ir (build-region-ir owner-let-value))
  (define λ (owner-let-body-region ir '()))
  (check-equal? (region-at ir '(1)) λ)
  (check-equal? (region-at ir '(0)) (region-at ir '()))
  (check-equal? (regions-exiting-at ir '()) (set))
  (check-equal? (regions-exiting-at ir '(1)) (set))
  (check-true (region-ir-ok? ir owner-let-value))
  (check-true (lexical-region-ir-ok? ir)))

;; Core の節点を指さない point に対しては、#f や空集合ではなく error を出す。
;; #f を返すと、呼び出し側が「point が無効である」と「その位置に region が
;; 無い」を区別できない。
(test-case "Core の節点を指さない point は error になる"
  (define ir (hand-ir))
  (check-exn exn:fail? (lambda () (region-at ir '(5))))
  (check-exn exn:fail? (lambda () (region-at ir '(0 0))))
  (check-exn exn:fail? (lambda () (regions-exiting-at ir '(5)))))

(test-case "region-outlives? は outlives の到達可能性であり反射的である"
  (define ir (hand-ir))
  (check-true (region-outlives? ir ρ0 ρ0))
  (check-true (region-outlives? ir ρ0 ρ1))
  ;; 推移閉包は outlives に入れないが、到達可能性としては真になる。
  (check-true (region-outlives? ir ρ0 ρ2))
  (check-false (region-outlives? ir ρ2 ρ0)))

(test-case "region-parent と region-contains? は親子の鎖を辿る"
  (define ir (hand-ir))
  (check-equal? (region-parent ir ρ2) ρ1)
  (check-false (region-parent ir ρ0))
  (check-true (region-contains? ir ρ0 ρ2))
  (check-true (region-contains? ir ρ1 ρ1))
  (check-false (region-contains? ir ρ2 ρ0)))

(test-case "regions-overlap? は包含のいずれかである"
  (define ir (hand-ir))
  (check-true (regions-overlap? ir ρ0 ρ2))
  (check-true (regions-overlap? ir ρ2 ρ0))
  (check-true (regions-overlap? ir ρ1 ρ1)))

(test-case "Eliminate と UnionEliminate は枝ごとの region を持ち退場時に全て閉じる"
  (for ([core (in-list
               (list '(Scope () (Eliminate s
                                ((some (x) -> x)
                                 (none () -> unit))))
                     '(UnionEliminate s
                        ((Int x -> x)
                         (String y -> y)))))])
    (define ir (build-region-ir core))
    (define eliminate-point (if (eq? (first core) 'Scope) '(0) '()))
    (define eliminate-region (region-at/eliminate ir eliminate-point))
    (define branch-0 (branch-region-of ir eliminate-point 0))
    (define branch-1 (branch-region-of ir eliminate-point 1))
    (define branch-0-point (append eliminate-point '(1)))
    (define branch-1-point (append eliminate-point '(2)))
    (check-not-equal? branch-0 branch-1)
    (check-equal? (region-parent ir branch-0) eliminate-region)
    (check-equal? (region-parent ir branch-1) eliminate-region)
    (check-false (regions-overlap? ir branch-0 branch-1))
    (check-equal? (region-at/branch ir branch-0-point) branch-0)
    (check-equal? (region-at/branch ir branch-1-point) branch-1)
    (check-equal? (region-at/branch ir (append eliminate-point '(0)))
                  eliminate-region)
    (check-equal? (region-at/eliminate ir branch-0-point) eliminate-region)
    (check-equal? (regions-exiting-at ir eliminate-point)
                  (set eliminate-region branch-0 branch-1))
    (check-equal? (region->rho ir branch-0)
                  (region->rho ir (region-at ir '())))
    (check-equal? (region->rho ir eliminate-region)
                  (region->rho ir (region-at ir '())))
    (check-true (lexical-region-ir-ok? ir)))
  (define owner-core
    '(Let (owner let (Owned Int)) 1
       (Eliminate s ((some (x) -> x) (none () -> unit)))))
  (define owner-ir (build-region-ir owner-core))
  (define owner-body (owner-let-body-region owner-ir '()))
  (define owner-eliminate (region-at/eliminate owner-ir '(1)))
  (define owner-branch (branch-region-of owner-ir '(1) 0))
  (check-equal? (region-parent owner-ir owner-eliminate) owner-body)
  (check-equal? (region-parent owner-ir owner-branch) owner-eliminate)
  (check-equal? (region->rho owner-ir owner-eliminate)
                (region->rho owner-ir owner-body))
  (check-equal? (region->rho owner-ir owner-branch)
                (region->rho owner-ir owner-body)))

(define (region-ancestor-list ir ρ)
  (let loop ([current ρ] [ancestors '()])
    (if current
        (loop (region-parent ir current) (cons current ancestors))
        ancestors)))

(test-case "callable 本体は最外の分解 region の親から始まり Recur 継続は枝に残る"
  (define lam-core
    '(Scope ()
       (Eliminate s
         ((some (x) ->
            (Scope ()
              (Lam User c0 ()
                (Let (owner let (Owned Int)) 1 (Scope () unit)))))
          (none () -> unit)))))
  (define lam-ir (build-region-ir lam-core))
  (define outer-scope (region-at lam-ir '()))
  (define lam-eliminate (region-at/eliminate lam-ir '(0)))
  (define lam-branch (branch-region-of lam-ir '(0) 0))
  (define branch-scope (region-at lam-ir '(0 1)))
  (define owner-body (owner-let-body-region lam-ir '(0 1 0 0)))
  (define callable-scope (region-at/branch lam-ir '(0 1 0 0 1)))
  (define callable-ancestors (region-ancestor-list lam-ir callable-scope))
  (check-equal? (region-parent lam-ir owner-body) outer-scope)
  (check-equal? (region-parent lam-ir callable-scope) owner-body)
  (check-false (member lam-eliminate callable-ancestors))
  (check-false (member lam-branch callable-ancestors))
  (check-false (member branch-scope callable-ancestors))

  (define recur-core
    '(Eliminate s
       ((some (x) ->
          (Recur c0 f () (Scope () unit) (Scope () unit)))
        (none () -> unit))))
  (define recur-ir (build-region-ir recur-core))
  (define recur-branch (branch-region-of recur-ir '() 0))
  (define recur-body-scope (region-at/branch recur-ir '(1 0)))
  (define recur-cont-scope (region-at/branch recur-ir '(1 1)))
  (check-false
   (member recur-branch (region-ancestor-list recur-ir recur-body-scope)))
  (check-not-false
   (member recur-branch (region-ancestor-list recur-ir recur-cont-scope)))

  (define recurval-ir
    (build-region-ir
     '(Eliminate s
        ((some (x) -> (RecurVal c0 f () (Scope () unit)))
         (none () -> unit)))))
  (define recurval-branch (branch-region-of recurval-ir '() 0))
  (define recurval-scope (region-at/branch recurval-ir '(1 0)))
  (check-false
   (member recurval-branch (region-ancestor-list recurval-ir recurval-scope)))

  (define nested-ir
    (build-region-ir
     '(Eliminate outer
        ((some (x) ->
           (Eliminate inner
             ((yes () -> (Lam User c1 () (Scope () unit)))
              (no () -> unit))))
         (none () -> unit)))))
  (define nested-outer (region-at/eliminate nested-ir '()))
  (define nested-outer-branch (branch-region-of nested-ir '() 0))
  (define nested-inner (region-at/eliminate nested-ir '(1)))
  (define nested-inner-branch (branch-region-of nested-ir '(1) 0))
  (define nested-lam-scope (region-at/branch nested-ir '(1 1 0)))
  (define nested-ancestors (region-ancestor-list nested-ir nested-lam-scope))
  (check-false (member nested-outer nested-ancestors))
  (check-false (member nested-outer-branch nested-ancestors))
  (check-false (member nested-inner nested-ancestors))
  (check-false (member nested-inner-branch nested-ancestors))

  (define non-overlap-ir
    (build-region-ir
     '(Eliminate s
        ((some (x) ->
           (Let (b let Int) (BorrowMut x)
             (Lam User c0 () (Scope () unit))))
         (none () -> unit)))))
  (check-false
   (regions-overlap? non-overlap-ir
                     (region-at/branch non-overlap-ir '(1 0))
                     (region-at/branch non-overlap-ir '(1 1 0)))))

;; [REQ: BOR-003] builder は Scope ごとに region を開く。
;; 手で組んだ IR と外延的に同じものを作ることを確かめる。
(test-case "build-region-ir は手組みの IR と同じ答えを返す"
  (define ir (build-region-ir nested))
  (check-true (region-ir-ok? ir nested))
  (check-true (lexical-region-ir-ok? ir))
  (check-equal? (set-count (region-ir-regions ir)) 3)
  (define root (region-at ir '()))
  (check-equal? (region-at ir '(0)) root)
  (check-not-equal? (region-at ir '(1)) root)
  (check-equal? (region-at ir '(1 0)) (region-at ir '(1)))
  (check-not-equal? (region-at ir '(1 0 1)) (region-at ir '(1)))
  (check-equal? (region-at ir '(1 0 1 0)) (region-at ir '(1 0 1)))
  (check-equal? (region-parent ir (region-at ir '(1 0 1)))
                (region-at ir '(1)))
  (check-equal? (region-parent ir (region-at ir '(1))) root)
  (check-false (region-parent ir root)))

(test-case "outlives は直接の制約だけを持つ"
  (define ir (build-region-ir nested))
  (define root (region-at ir '()))
  (define ρa (region-at ir '(1)))
  (define ρb (region-at ir '(1 0 1)))
  (check-equal? (region-ir-outlives ir)
                (set (list root ρa) (list ρa ρb))))

(test-case "owners の定義域は regions と一致し、値は π である"
  (define ir (build-region-ir nested))
  (check-equal? (list->set (hash-keys (region-ir-owners ir)))
                (region-ir-regions ir))
  (for ([v (in-hash-values (region-ir-owners ir))])
    (check-equal? v '())))

(test-case "Scope を持たない Core では全 point が root を指す"
  (define core '(Apply f 1))
  (define ir (build-region-ir core))
  (check-equal? (set-count (region-ir-regions ir)) 1)
  (for ([point (in-list (core-points core))])
    (check-equal? (region-at ir point) (region-at ir '()))
    (check-true (set-empty? (regions-exiting-at ir point)))))

(test-case "builder が作った IR も不正な point で error を出す"
  (define ir (build-region-ir nested))
  (check-exn exn:fail? (lambda () (region-at ir '(5))))
  (check-exn exn:fail? (lambda () (regions-exiting-at ir '(0 0)))))

;; [REQ: BOR-003] docs/specification/region.md §6 の adapter 性質 C1 から C4。
;; 兄弟の Scope を含み、根が Scope でない Core を使う。
(define sibling-core
  '(Apply f (Scope () (Apply (Scope () 1) (Scope () 2)))))

(test-case "C1: region-contains? が真なら region-outlives? も真である"
  (define ir (build-region-ir sibling-core))
  (for* ([a (in-set (region-ir-regions ir))]
         [b (in-set (region-ir-regions ir))])
    (when (region-contains? ir a b)
      (check-true (region-outlives? ir a b) (format "~s ~s" a b)))))

(test-case "C2: 兄弟の region は互いに包まず、同時に生きない"
  (define ir (build-region-ir sibling-core))
  (define a (region-at ir '(1 0 0)))
  (define b (region-at ir '(1 0 1)))
  (check-not-equal? a b)
  (check-false (region-contains? ir a b))
  (check-false (region-contains? ir b a))
  (check-false (regions-overlap? ir a b)))

(define (count-scopes core)
  (for/sum ([point (in-list (core-points core))])
    (match (core-node core point)
      [`(Scope ,_ ,_) 1]
      [_ 0])))

(define (count-owner-lets core)
  (for/sum ([point (in-list (core-points core))])
    (match (core-node core point)
      [`(Let (,_ ,_ ,type) ,_ ,_)
       (if (resource-type? type) 1 0)]
      [`(Let (,_ ,type) ,_ ,_)
       (if (resource-type? type) 1 0)]
      [_ 0])))

(define (count-decomposition-branches core)
  (for/sum ([point (in-list (core-points core))])
    (match (core-node core point)
      [`(,(or 'Eliminate 'UnionEliminate) ,_ (,branches ...))
       (length branches)]
      [_ 0])))

(test-case "C3: Scope、owner Let、分解の個数が root 以外の region と一致する"
  (for ([core (in-list (list '(Apply f 1) nested sibling-core
                             owner-let-scope owner-let-value
                             '(Scope () (Eliminate y ((none () -> unit)
                                                       (some (v) -> unit))))
                             '(Scope () (UnionEliminate x ((Int i -> unit))))))])
    (define ir (build-region-ir core))
    (check-equal? (sub1 (set-count (region-ir-regions ir)))
                  (+ (count-scopes core) (count-owner-lets core)
                     (count-decomposition-branches core)
                     (for/sum ([point (in-list (core-points core))])
                       (match (core-node core point)
                         [`(,(or 'Eliminate 'UnionEliminate) ,_ ,_) 1]
                         [_ 0])))
                  (format "~s" core))))

(test-case "C4: 退場は Scope と分解の point でちょうど 1 件、それ以外で空である"
  (for ([core (in-list (list sibling-core owner-let-scope owner-let-value
                             '(Scope () (Eliminate y ((none () -> unit)
                                                       (some (v) -> unit))))
                             '(Scope () (UnionEliminate x ((Int i -> unit))))))])
    (define ir (build-region-ir core))
    (define root
      (for/first ([ρ (in-set (region-ir-regions ir))]
                  #:unless (region-parent ir ρ))
        ρ))
    (for ([point (in-list (core-points core))])
      (define exiting (regions-exiting-at ir point))
      (match (core-node core point)
        [`(Scope ,_ ,_)
         (check-equal? exiting (set (region-at ir point)) (format "~s" point))]
        [`(,(or 'Eliminate 'UnionEliminate) ,_ ,_)
         (define branch-count
           (match (core-node core point)
             [`(,(or 'Eliminate 'UnionEliminate) ,_ (,branches ...))
              (length branches)]))
         (check-equal?
          exiting
          (for/fold ([regions (set (region-at/eliminate ir point))])
                    ([index (in-range branch-count)])
            (set-add regions (branch-region-of ir point index)))
                       (format "~s" point))]
        [_ (check-true (set-empty? exiting) (format "~s" point))])
      ;; root region はどの point でも返らない。
      (check-false (set-member? exiting root) (format "~s" point)))))

;; C6: spanful な Core と erase-core を通した項が、外延的に同型な IR を作る。
;; region 識別子は不透明なので equal? では比べられない。
;; region-at と region-at/eliminate が返す region の対応を親の鎖で root まで延ばす。
(define (build-σ ir-a ir-b core)
  (define σ (make-hash))
  (define (link! a b)
    (cond
      [(hash-has-key? σ a) (equal? (hash-ref σ a) b)]
      [else
       (hash-set! σ a b)
       (match* ((region-parent ir-a a) (region-parent ir-b b))
         [(#f #f) #t]
         [(pa pb) (and pa pb (link! pa pb))])]))
  (and (for/and ([point (in-list (core-points core))])
         (and (link! (region-at ir-a point) (region-at ir-b point))
              (link! (region-at/eliminate ir-a point)
                     (region-at/eliminate ir-b point))))
       σ))

(define (extensionally-isomorphic? ir-a ir-b core)
  (define σ (build-σ ir-a ir-b core))
  (define regions-a (region-ir-regions ir-a))
  (define regions-b (region-ir-regions ir-b))
  (and
   ;; 空集合同士の比較で通さない。
   (positive? (set-count regions-a))
   ;; 1. σ が写像として矛盾しない。build-σ が矛盾で #f を返す。
   (hash? σ)
   ;; 2. σ が全単射である。
   (equal? (list->set (hash-keys σ)) regions-a)
   (equal? (list->set (hash-values σ)) regions-b)
   (= (hash-count σ) (set-count regions-b))
   ;; 3. regions-exiting-at の結果が σ の下で一致する。
   (for/and ([point (in-list (core-points core))])
     (equal? (for/set ([ρ (in-set (regions-exiting-at ir-a point))])
               (hash-ref σ ρ))
             (regions-exiting-at ir-b point)))
   ;; 4. region-outlives? と regions-overlap? が σ の下で一致する。
   (for*/and ([a (in-set regions-a)] [b (in-set regions-a)])
     (and (equal? (region-outlives? ir-a a b)
                  (region-outlives? ir-b (hash-ref σ a) (hash-ref σ b)))
          (equal? (regions-overlap? ir-a a b)
                  (regions-overlap? ir-b (hash-ref σ a) (hash-ref σ b)))))))

(test-case "C6: spanful と spanless から外延的に同型な IR ができる"
  (match-define (list raw-core _ _ _)
    (elab '(Apply (Fn ((x Int)) Int () x) 1)))
  (define erased (erase-core raw-core))
  (check-not-equal? raw-core erased)
  ;; 入口の erase-core を外すと、spanful 側の point の数え方がずれてここが落ちる。
  (check-true (extensionally-isomorphic? (build-region-ir raw-core)
                                         (build-region-ir erased)
                                         erased)))

;; [REQ: BOR-003] C5: core-calculus.md §8 の golden program 2 本で、
;; Scope の入れ子から読み取れる親子関係、outlives、退場を、問い合わせだけで
;; 再構成できる。
;; golden-test.rkt:38-79 の写しである。あちらは provide していない。
(define golden-find-positive
  '(Apply
    (Fn ((values (List Int))) (Result Int Unit) ()
        (NarrativeExpr
         (Recur loop ((rest (List Int))) (Result Int Unit) (Return)
                (Eliminate
                 rest
                 ((nil () -> (Construct ng unit))
                  (cons
                   (head tail)
                   ->
                   (Eliminate
                    (Apply lt 0 head)
                    ((true () -> (Return (Construct ok head)))
                     (false () -> (Apply loop tail)))))))
                (Apply loop values))))
    (Construct cons (Types Int)
               -1
               (Construct cons (Types Int)
                          2
                          (Construct nil (Types Int))))))

(define golden-doubled
  '(Apply
    (Fn ((f (NFn (Int) Int () ()))
         (values (List Int)))
        (List Int) ()
        (Recur go ((rest (List Int))) (List Int) ()
               (Eliminate
                rest
                ((nil () -> (Construct nil))
                 (cons
                  (h t)
                  ->
                  (Construct cons (Apply f h) (Apply go t)))))
               (Apply go values)))
    (Curry mul 2)
    (Construct cons (Types Int)
               -1
               (Construct cons (Types Int)
                          2
                          (Construct nil (Types Int))))))

;; 木の形を直接読んで親子関係を組む。問い合わせ側と独立に書く。
;; 問い合わせの実装を借りると、実装の誤りが期待値にも同じ形で現れ、比較で相殺される。
(define (scope-points core)
  (for/list ([point (in-list (core-points core))]
             #:when (match (core-node core point)
                      [`(Scope ,_ ,_) #t]
                      [_ #f]))
    point))

(define (decomposition-points core)
  (for/list ([point (in-list (core-points core))]
             #:when (match (core-node core point)
                      [`(,(or 'Eliminate 'UnionEliminate) ,_ ,_) #t]
                      [_ #f]))
    point))

(define (golden-parent-map core ir)
  (define expected (make-hash))
  (define (walk t point current enclosing-decompositions)
    (match t
      [`(Scope ,_ ,body)
       (define ρ (region-at ir point))
       (hash-set! expected ρ current)
       (walk body (append point '(0)) ρ enclosing-decompositions)]
      [`(,(or 'Eliminate 'UnionEliminate) ,_ ,_)
       (define ρ (region-at/eliminate ir point))
       (hash-set! expected ρ current)
       (define children (core-children t))
       (define nested-decompositions (append enclosing-decompositions (list ρ)))
       (walk (first children) (append point '(0)) ρ nested-decompositions)
       (for ([body (in-list (rest children))] [index (in-naturals)])
         (define branch (branch-region-of ir point index))
         (hash-set! expected branch ρ)
         (walk body (append point (list (add1 index))) branch
               nested-decompositions))]
      [`(Lam ,_ ,_ ,_ ,body)
       (define base
         (if (null? enclosing-decompositions)
             current
             (region-parent ir (first enclosing-decompositions))))
       (walk body (append point '(0)) base '())]
      [`(RecurVal ,_ ,_ ,_ ,body)
       (define base
         (if (null? enclosing-decompositions)
             current
             (region-parent ir (first enclosing-decompositions))))
       (walk body (append point '(0)) base '())]
      [`(Recur ,_ ,_ ,_ ,body ,continuation)
       (define base
         (if (null? enclosing-decompositions)
             current
             (region-parent ir (first enclosing-decompositions))))
       (walk body (append point '(0)) base '())
       (walk continuation (append point '(1)) current enclosing-decompositions)]
      [`(Let (,_ ,_ ,binding-type) ,bound ,body)
       (define body-region
         (if (resource-type? binding-type)
             (owner-let-body-region ir point)
             current))
       (walk bound (append point '(0)) current enclosing-decompositions)
       (when (not (equal? body-region current))
         (hash-set! expected body-region current))
       (walk body (append point '(1)) body-region enclosing-decompositions)]
      [`(Let (,_ ,binding-type) ,bound ,body)
       (define body-region
         (if (resource-type? binding-type)
             (owner-let-body-region ir point)
             current))
       (walk bound (append point '(0)) current enclosing-decompositions)
       (when (not (equal? body-region current))
         (hash-set! expected body-region current))
       (walk body (append point '(1)) body-region enclosing-decompositions)]
      [_
       (for ([child (in-list (core-children t))] [index (in-naturals)])
         (walk child (append point (list index)) current
               enclosing-decompositions))]))
  (define root
    (for/first ([ρ (in-set (region-ir-regions ir))]
                #:unless (region-parent ir ρ))
      ρ))
  (walk core '() root '())
  expected)

(define (check-golden-region name source)
  (match-define (list raw-core _ _ _) (elab source))
  (define core (erase-core raw-core))
  (define ir (build-region-ir core))
  (define scope-points* (scope-points core))
  (define points (append scope-points* (decomposition-points core)))
  ;; Scope を 1 つも含まない golden では、以下の走査が空回りする。
  (check-true (pair? scope-points*) (format "~a: Scope を 1 つも含まない" name))
  (check-true (region-ir-ok? ir core) name)
  (check-true (lexical-region-ir-ok? ir) name)
  (check-equal? (sub1 (set-count (region-ir-regions ir)))
                (+ (length points) (count-owner-lets core)
                   (count-decomposition-branches core)) name)
  (define expected-parents (golden-parent-map core ir))
  (define root
    (for/first ([ρ (in-set (region-ir-regions ir))]
                #:unless (region-parent ir ρ))
      ρ))
  (check-equal? (list->set (hash-keys expected-parents))
                (set-remove (region-ir-regions ir) root) name)
  (for ([(child parent) (in-hash expected-parents)])
    (check-equal? (region-parent ir child) parent name)
    (check-true (region-outlives? ir parent child) name)
    (check-true (regions-overlap? ir parent child) name))
  (for ([point (in-list (core-points core))])
    (define expected-exits
      (match (core-node core point)
        [`(Scope ,_ ,_) (set (region-at ir point))]
        [`(,(or 'Eliminate 'UnionEliminate) ,_ ,_)
         (for/fold ([exiting (set (region-at/eliminate ir point))])
                   ([index (in-range
                            (match (core-node core point)
                              [`(,(or 'Eliminate 'UnionEliminate) ,_ (,branches ...))
                               (length branches)]))])
           (set-add exiting (branch-region-of ir point index)))]
        [_ (set)]))
    (check-equal? (regions-exiting-at ir point) expected-exits name)))

(test-case "C5: golden program の Scope と分解の region を問い合わせだけで再構成できる"
  (check-golden-region "findPositive" golden-find-positive)
  (check-golden-region "map" golden-doubled))

;; 関数境界の捕捉検査は束縛と意味的な子を区別する。
(check-equal? (core-free-vars '(Let (x let Int) 1 x)) (set))
(check-equal? (core-free-vars '(Let (x let Int) y x)) (set 'y))
(check-equal? (core-free-vars '(Lam () c0 (x) x)) (set))
(check-equal? (core-free-vars '(Handle op (x -> x) y)) (set 'y))
(check-equal? (core-free-vars '(Eliminate s ((some (x) -> x) (none () -> y))))
              (set 's 'y))
(check-equal? (core-free-vars '(Proj r x)) (set 'r))
(check-equal? (core-free-vars '(Rec ((x imm 1)))) (set))
(check-equal? (core-free-vars '(Construct Int some x)) (set 'x))
(check-equal? (core-free-vars '(Move x)) (set 'x))
(check-equal? (core-free-vars '(Let (x let Int) 1 (Move x))) (set))
(check-equal? (core-free-vars '(Borrow y)) (set 'y))
(check-equal? (core-free-vars '(BorrowMut y)) (set 'y))
(check-equal? (core-free-vars '(BorrowAt 0 (Own y ()) y)) (set 'y))
(check-equal? (core-free-vars '(BorrowMutAt 0 (Own y ()) y)) (set 'y))
(check-equal? (core-free-vars '(Borrow (#:var y (#:span src 1 2)))) (set 'y))
(check-equal? (core-free-vars '(BorrowMutAt 0 (Own y ()) (#:var y (#:span src 1 2))))
              (set 'y))
(check-equal? (core-free-vars '(ReborrowAt 0 (BorrowMutAt 0 (Own y ()) y)))
              (set 'y))
(check-equal? (core-free-vars '(ProjBorrowAt 0
                               (BorrowMutAt 0 (Own y ()) y) a))
              (set 'y))
(check-equal? (core-free-vars '(Let (y let Int) 1 (Borrow y))) (set))
(check-equal? (core-free-vars '(Lam () c0 (y) (BorrowMut y))) (set))
(check-equal? (core-free-vars '(Let (y let Int) 1 (BorrowAt 0 (Own y ()) y))) (set))
(check-equal? (core-free-vars '(Reborrow (BorrowMut y))) (set 'y))
(check-equal? (core-free-vars '(BorrowMut 7)) (set))
(check-equal? (core-free-vars 'unit) (set))

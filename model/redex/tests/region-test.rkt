#lang racket

(require rackunit
         racket/match
         racket/set
         "../elaborate.rkt"
         "../erase.rkt"
         "../region.rkt")

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
  (check-equal? (core-children '(Lam User c0 (x y) 1)) '(1)))

(test-case "Eliminate は scrutinee に続けて分岐の本体を分岐の順に並べる"
  (check-equal?
   (core-children '(Eliminate 0 ((nil () -> 1) (cons (h t) -> 2))))
   '(0 1 2)))

;; spec §4 の production を 1 件ずつ実データで通す。
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
                '(1)))

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

(test-case "子を持たない形は空を返す"
  (for ([t (in-list (list 3 "s" 'unit 'x '(Move y)
                          '(PrimVal User add)
                          '(TypeRep User Int Type)
                          '(ProofRep User ValidNarrativeTrait)
                          '(resource 0)))])
    (check-equal? (core-children t) '() (format "~s" t))))

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
                 #:points [points nested-points])
  (lexical-region-ir regions outlives owners parents at-table points))

(test-case "既定の手組み IR は 8 条件と 2 条件を満たす"
  (check-true (region-ir-ok? (hand-ir) nested))
  (check-true (lexical-region-ir-ok? (hand-ir)))
  (check-true (region-solver? (hand-ir))))

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
                (hand-ir #:at-table (hash '(1) ρ1 '(1 0 1) (region 9)))
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

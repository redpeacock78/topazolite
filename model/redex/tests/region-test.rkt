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

(test-case "core-children は Owned leaf の payload を子にする"
  (check-equal? (core-children '(OwnedLeaf (tok 0) x)) '(x)))

(test-case "core-with-children は Owned leaf を組み直す"
  (check-equal? (core-with-children '(OwnedLeaf (tok 0) x) '(y))
                '(OwnedLeaf (tok 0) y)))

(test-case "core-free-vars は Owned leaf の payload を見る"
  (check-equal? (core-free-vars '(OwnedLeaf (tok 0) x)) (set 'x)))

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

(test-case "C3: Core の Scope の個数と root 以外の region の個数が一致する"
  (for ([core (in-list (list '(Apply f 1) nested sibling-core))])
    (define ir (build-region-ir core))
    (check-equal? (sub1 (set-count (region-ir-regions ir)))
                  (count-scopes core)
                  (format "~s" core))))

(test-case "C4: 退場は Scope の point でちょうど 1 件、それ以外で空である"
  (define ir (build-region-ir sibling-core))
  (define root (region-at ir '()))
  (for ([point (in-list (core-points sibling-core))])
    (define exiting (regions-exiting-at ir point))
    (match (core-node sibling-core point)
      [`(Scope ,_ ,_)
       (check-equal? exiting (set (region-at ir point)) (format "~s" point))]
      [_ (check-true (set-empty? exiting) (format "~s" point))])
    ;; root region はどの point でも返らない。
    (check-false (set-member? exiting root) (format "~s" point))))

;; C6: spanful な Core と erase-core を通した項が、外延的に同型な IR を作る。
;; region 識別子は不透明なので equal? では比べられない。
;; region-at が返す region の対応から写像 σ を作り、親の鎖で root まで延ばす。
;; region-at は root Scope を持つ Core で root を返さないため、parents を辿らないと
;; σ が root を覆えない。
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
         (link! (region-at ir-a point) (region-at ir-b point)))
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

;; 親は、自身より真に短い Scope の point のうち最長の接頭辞である。
(define (scope-parent points point)
  (for/fold ([best #f]) ([other (in-list points)])
    (if (and (< (length other) (length point))
             (equal? other (take point (length other)))
             (or (not best) (> (length other) (length best))))
        other
        best)))

(define (check-golden-region name source)
  (match-define (list raw-core _ _ _) (elab source))
  (define core (erase-core raw-core))
  (define ir (build-region-ir core))
  (define points (scope-points core))
  ;; Scope を 1 つも含まない golden では、以下の走査が空回りする。
  (check-true (pair? points) (format "~a: Scope を 1 つも含まない" name))
  (check-true (region-ir-ok? ir core) name)
  (check-true (lexical-region-ir-ok? ir) name)
  (check-equal? (sub1 (set-count (region-ir-regions ir))) (length points) name)
  (define root (region-at ir '()))
  (for ([point (in-list points)])
    (define ρ (region-at ir point))
    ;; 退場は自身の point でちょうど 1 件である。
    (check-equal? (regions-exiting-at ir point) (set ρ) name)
    ;; 親子関係が一致する。
    (define parent-point (scope-parent points point))
    (define parent-region
      (if parent-point (region-at ir parent-point) root))
    (check-equal? (region-parent ir ρ) parent-region name)
    ;; 親が子より長生きし、同時に生きる。
    (check-true (region-outlives? ir parent-region ρ) name)
    (check-true (regions-overlap? ir parent-region ρ) name))
  ;; Scope でない point では退場が無い。
  (for ([point (in-list (core-points core))]
        #:unless (member point points))
    (check-true (set-empty? (regions-exiting-at ir point)) name)))

(test-case "C5: golden program 2 本の region を問い合わせだけで再構成できる"
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
(check-equal? (core-free-vars '(ReborrowAt 0 (Own z ()) (BorrowMutAt 0 (Own y ()) y)))
              (set 'y 'z))
(check-equal? (core-free-vars '(ProjBorrowAt 0 (Own z (a))
                               (BorrowMutAt 0 (Own y ()) y) a))
              (set 'y 'z))
(check-equal? (core-free-vars '(Let (y let Int) 1 (Borrow y))) (set))
(check-equal? (core-free-vars '(Lam () c0 (y) (BorrowMut y))) (set))
(check-equal? (core-free-vars '(Let (y let Int) 1 (BorrowAt 0 (Own y ()) y))) (set))
(check-equal? (core-free-vars '(Reborrow (BorrowMut y))) (set 'y))
(check-equal? (core-free-vars '(BorrowMut 7)) (set))
(check-equal? (core-free-vars 'unit) (set))

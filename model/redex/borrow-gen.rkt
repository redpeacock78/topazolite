#lang racket

(require racket/match
         "borrow.rkt"
         "machine.rkt"
         "region.rkt"
         "typing.rkt")

(provide gen-borrow-term
         literal-positions
         fill-region-placeholders
         prepare-borrow-term)

;; spec §4.1。G2 core を直に作る。elaborate も surface 構文も通さない。
;; 生成域は借用の 3 形と、その借用が意味を持つのに必要な最小の周辺だけである。
;;   Scope / Let(Owned) / Let(Borrowed) / Let(BorrowedMut)
;;   Borrow / BorrowMut / Reborrow / Read / Assign
;;   Rec / ProjBorrow / Construct / Eliminate / Perform / Handle / Yield / Drop / Move
;; Rec と Construct は射影と分解の対象を作るためだけに生成する。所有の値を
;; そのまま読む Proj は借用値を作らないので生成しない。
;; Recur は生成しない。RecurVal の本体へ借用値が入ると R-RecurUnfold が
;; 借用値を複製し、Task 2 の借用形候補が承認済みの形へ照合できなくなる。

(define binder-counter (box 0))

(define (fresh-binder! prefix)
  (define n (unbox binder-counter))
  (set-box! binder-counter (add1 n))
  (string->symbol (format "~a~a" prefix n)))

(define (gen-literal) (+ 1000 (random 1000)))

;; c の位置に現れるリテラルだけを返す。型の中の ρ と placeholder は含めない。
(define (literal-positions t)
  (match t
    [`(Let (,_x ,_bmode ,_τ) ,bound ,body)
     (append (literal-positions bound) (literal-positions body))]
    [(? exact-integer?) (list t)]
    [(and (? list?) (? pair?))
     (append* (map literal-positions t))]
    [_ '()]))

;; 生成中に保つ環境。所有束縛と借用束縛を別に持つ。owned は Res の所有束縛
;; だけを持ち、Int と record と data の所有束縛は ints / recs / datas に分ける。
;; gen-borrow-let が型を (Borrowed Res ph) に固定しているため、型の違う束縛を
;; owned へ混ぜると借用の型が合わなくなる。
(struct genv (owned ints shared muts recs datas) #:transparent)
(define empty-genv (genv '() '() '() '() '() '()))

(define (pick lst) (list-ref lst (random (length lst))))

(define (gen-borrow-term depth)
  (set-box! binder-counter 0)
  (gen-scope depth empty-genv))

(define (gen-scope depth env)
  `(Scope () ,(gen-core depth env)))

;; 借用値を作れる形は所有束縛が 1 つ以上あるときだけ選ぶ。
(define (gen-core depth env)
  (define choices
    (append
     (list (lambda () (gen-literal))
           (lambda () (gen-own-let depth env)))
     (if (positive? depth)
         (list (lambda () (gen-scope (sub1 depth) env))
               (lambda () (gen-yield depth env)))
         '())
     (if (and (positive? depth) (pair? (genv-owned env)))
         (list (lambda () (gen-borrow-let depth env))
               (lambda () (gen-mut-let depth env))
               ;; 子 Scope で作った借用を外側で直ちに読む。借用値が Scope
               ;; の退出をまたぐので scope-exit を数えられるが、同じ Scope
               ;; の owner から借用を返す反例は生成しない。
               (lambda () (gen-scope-borrow env))
               (lambda () `(Drop (Move ,(pick (genv-owned env))))))
         '())
     (if (positive? depth)
         (list (lambda () (gen-rec-let depth env))
               (lambda () (gen-data-let depth env))
               (lambda () (gen-int-let depth env)))
         '())
     (if (and (positive? depth) (pair? (genv-recs env)))
         (list (lambda () (gen-proj-borrow-let depth env))
               (lambda () (gen-proj-borrow-mut-let depth env)))
         '())
     (if (pair? (genv-datas env))
         (list (lambda () (gen-eliminate-ref env))
               (lambda () (gen-eliminate-mut-ref env))
               (lambda () (gen-eliminate env)))
         '())
     (if (and (positive? depth) (pair? (genv-shared env)))
         (list (lambda () `(Read ,(pick (genv-shared env)))))
         '())
     (if (and (positive? depth) (pair? (genv-muts env)))
         (list (lambda () `(Read ,(pick (genv-muts env))))
               (lambda () `(Assign ,(pick (genv-muts env))
                                   ,(gen-literal)))
               (lambda () (gen-reborrow-let depth env)))
         '())
     (if (and (positive? depth) (pair? (genv-ints env)))
         (list (lambda () (gen-int-mut-let depth env))
               (lambda () (gen-handle depth env)))
         '())))
  ((pick choices)))

(define (gen-own-let depth env)
  (define x (fresh-binder! 'o))
  `(Let (,x let (Owned Res)) (resource ,(gen-literal))
     ,(gen-core (max 0 (sub1 depth))
                (struct-copy genv env
                             [owned (cons x (genv-owned env))]))))

(define (gen-int-let depth env)
  (define x (fresh-binder! 'i))
  `(Let (,x let (Owned Int)) ,(gen-literal)
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [ints (cons x (genv-ints env))]))))

(define (gen-borrow-let depth env)
  (define y (fresh-binder! 's))
  `(Let (,y let (Borrowed Res ph)) (Borrow ,(pick (genv-owned env)))
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [shared (cons y (genv-shared env))]))))

(define (gen-scope-borrow env)
  (define y (fresh-binder! 'sx))
  `(Let (,y let (Borrowed Res ph))
     (Scope () (Borrow ,(pick (genv-owned env))))
     (Read ,y)))

(define (gen-mut-let depth env)
  (define y (fresh-binder! 'm))
  `(Let (,y let (BorrowedMut Res ph)) (BorrowMut ,(pick (genv-owned env)))
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [muts (cons y (genv-muts env))]))))

(define (gen-int-mut-let depth env)
  (define y (fresh-binder! 'mi))
  `(Let (,y let (BorrowedMut Int ph)) (BorrowMut ,(pick (genv-ints env)))
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [muts (cons y (genv-muts env))]))))

;; R-HandleReturn と、その handler 内で発生する借用を実 trace へ通す。
;; payload は Int のままにし、handler 本体の Borrow/Read で借用形を作る。
;; Borrowed 型を operation signature へ直接埋めると、注釈前 core の ph を
;; operation 側にも解く必要が生じるため、ここでは型付けと機械経路を狭く保つ。
(define (gen-handle depth env)
  `(Handle (Return borrow-boundary Int)
           (k -> (Read (Borrow ,(pick (genv-ints env)))))
           (Perform (Return borrow-boundary Int) ,(gen-literal))))

(define (gen-reborrow-let depth env)
  (define y (fresh-binder! 'r))
  `(Let (,y let (Borrowed Res ph)) (Reborrow ,(pick (genv-muts env)))
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [shared (cons y (genv-shared env))]))))

;; 欄への射影ができる record を作る。f0 は mut、f1 は imm であり、親が可変の
;; ときだけ子の可変性が欄で分かれる（spec §5.2 の表、proj-borrow-mode）。
(define rec-τ '(Record ((f0 Int mut) (f1 Int imm))))

(define (gen-rec-let depth env)
  (define x (fresh-binder! 'c))
  `(Let (,x let (Owned ,rec-τ))
     (Rec ((f0 mut ,(gen-literal)) (f1 imm ,(gen-literal))))
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [recs (cons x (genv-recs env))]))))

;; R-ProjBorrow を発火させ、oracle の 'derived 分類を実 trace へ通す。
;; 親が共有ならば欄の可変性によらず子は共有なので、欄はどちらでもよい。
(define (gen-proj-borrow-let depth env)
  (define y (fresh-binder! 'q))
  `(Let (,y let (Borrowed Int ph))
     (ProjBorrow (Borrow ,(pick (genv-recs env))) ,(pick '(f0 f1)))
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [shared (cons y (genv-shared env))]))))

;; R-ProjBorrowMut を発火させる。親が可変で欄が mut のときだけ子が可変になる
;; ため、欄は f0 に固定する。f1 を選ぶと子が Borrowed になり型が合わない。
(define (gen-proj-borrow-mut-let depth env)
  (define y (fresh-binder! 'qm))
  `(Let (,y let (BorrowedMut Int ph))
     (ProjBorrow (BorrowMut ,(pick (genv-recs env))) f0)
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [muts (cons y (genv-muts env))]))))

;; 分解の対象になる data 値を作る。schema.rkt が構成子を持つ型は Bool、List、
;; Option、Result だけであり、Res には構成子が無い。some の欄は Int なので
;; 所有の欄にはならず、check-construct の OwnLeaf 要求もかからない。
(define data-τ '(Option Int))

(define (gen-data-let depth env)
  (define x (fresh-binder! 'd))
  `(Let (,x let (Owned ,data-τ))
     (Construct ,data-τ some ,(gen-literal))
     ,(gen-core (sub1 depth)
                (struct-copy genv env
                             [datas (cons x (genv-datas env))]))))

;; R-EliminateRef を発火させる。枝は (K (x ...) -> c) であり、schema と同数で
;; なければ branch-contexts が non-exhaustive-eliminate で落ちる。借用を分解
;; すると束縛子へは欄の値ではなく欄を指す借用参照が渡る。
(define (gen-eliminate-ref env)
  (define a (fresh-binder! 'e))
  `(Eliminate (Borrow ,(pick (genv-datas env)))
              ((none () -> ,(gen-literal))
               (some (,a) -> (Read ,a)))))

;; R-EliminateMutRef を発火させる。scrutinee が可変借用であることを除いて
;; gen-eliminate-ref と同じ形であり、束縛子へは欄を指す可変借用参照が渡る。
(define (gen-eliminate-mut-ref env)
  (define a (fresh-binder! 'e))
  `(Eliminate (BorrowMut ,(pick (genv-datas env)))
              ((none () -> ,(gen-literal))
               (some (,a) -> (Read ,a)))))

;; R-Eliminate を発火させる。所有の値を分解するので束縛子へは欄の値が渡る。
(define (gen-eliminate env)
  (define a (fresh-binder! 'e))
  `(Eliminate (Move ,(pick (genv-datas env)))
              ((none () -> ,(gen-literal))
               (some (,a) -> ,a))))

;; payload は借用形を含まないリテラルに限る。spec §4.5 が obs 経由の借用だけの
;; 実行を捨てるため、借用を入れても必ず捨てられる。
(define (gen-yield depth env)
  `(Yield ,(gen-literal) ,(gen-core (sub1 depth) env)))

;; spec §4.1。借用束縛の型の placeholder `ph` を、その Let の被束縛式の point で
;; 解いた ρ へ置き換える。point の数え方は core-children であり、
;; annotate-regions が (here) を計算する位置と同じである。
(define (fill-region-placeholders core ir)
  (let walk ([t core] [point '()])
    (match t
      [`(Let (,x ,bmode ,τ) ,bound ,body)
       (define bound-point (append point (list 0)))
       (define body-point (append point (list 1)))
       `(Let (,x ,bmode ,(fill-type τ ir bound-point))
             ,(walk bound bound-point)
             ,(walk body body-point))]
      [(? list?)
       (core-with-children
        t
        (for/list ([k (in-list (core-children t))]
                   [i (in-naturals)])
          (walk k (append point (list i)))))]
      [_ t])))

(define (fill-type τ ir point)
  (match τ
    [`(Borrowed ,inner ph)
     `(Borrowed ,inner ,(region->rho ir (region-at ir point)))]
    [`(BorrowedMut ,inner ph)
     `(BorrowedMut ,inner ,(region->rho ir (region-at ir point)))]
    [_ τ]))

;; spec §4.1。生成した core を検査対象の config へ通す。
;; 型検査が受理しない項は静かに捨てる。受理した項だけが性質 8 の対象である。
(define (prepare-borrow-term core)
  (define ir (build-region-ir core))
  (define filled (fill-region-placeholders core ir))
  ;; typing.rkt の raw 入口は G2m core を受け取るため、注釈を先に注入する。
  ;; surface 形の Borrow / ProjBorrow を直接渡すと not-core-term になる。
  (define annotated
    (with-handlers ([exn:fail? (lambda (_e) #f)])
      (annotate-regions filled ir)))
  (define result
    (if annotated
        (with-handlers ([exn:fail? (lambda (_e) 'discard)])
          (type-of/raw*+borrows annotated '() '()
                                '() (region-ctx ir '() (hash) (hash))))
        'discard))
  (match result
    [(list 'ok (list _type _row _table _σ _renamed sidecar))
     (define config (inject-g2m annotated))
     ;; spec §4.6。初期 config に借用値が現れる項は入口の制限に反する。
     (if (initial-has-borrow? config)
         'discard
         (list 'ok config sidecar ir))]
    [_ 'discard]))

(define (initial-has-borrow? t)
  (match t
    [(or `(BorrowRef ,_ ,_ ,_) `(BorrowMutRef ,_ ,_ ,_)) #t]
    [(? list?) (ormap initial-has-borrow? t)]
    [_ #f]))

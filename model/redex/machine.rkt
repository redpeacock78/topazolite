#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt"
         "borrow.rkt"
         "origins.rkt"
         "region-param.rkt"
         "traits.rkt"
         "validators.rkt")

(provide -->g1
         -->g2
         -->g1/rules
         -->g2/rules
         raw-steps-g2
         inject
         inject-g2
         inject-g2m
         substitute*/g2
         heap-walk-path
         proj-borrow-mut
         value-set-path
         path-lookup
         path-set
         fresh-token
         run
         run-g2
         g2-primitive-name?)

(define-metafunction G1m
  δ : nm v ... -> any
  [(δ add n_1 n_2) ,(+ (term n_1) (term n_2))]
  [(δ sub n_1 n_2) ,(- (term n_1) (term n_2))]
  [(δ mul n_1 n_2) ,(* (term n_1) (term n_2))]
  [(δ lt n_1 n_2)
   ,(if (< (term n_1) (term n_2))
        (term (Construct Bool true))
        (term (Construct Bool false)))]
  [(δ le n_1 n_2)
   ,(if (<= (term n_1) (term n_2))
        (term (Construct Bool true))
        (term (Construct Bool false)))]
  [(δ eq n_1 n_2)
   ,(if (= (term n_1) (term n_2))
        (term (Construct Bool true))
        (term (Construct Bool false)))]
  [(δ acquire n) (resource n)]
  [(δ nm v ...) undefined])

;; Redex's substitute uses the binding forms declared by G1.  Keeping the
;; simultaneous substitution here also makes arity mismatches non-reducible
;; instead of raising a metafunction exception.
(define-metafunction G1m
  substitute* : c (x ...) (v ...) -> any
  [(substitute* c_body (x ...) (v_arg ...))
   (substitute c_body (x v_arg) ...)
   (side-condition
    (and (= (length (term (x ...)))
            (length (term (v_arg ...))))
         (not (check-duplicates (term (x ...))))))]
  [(substitute* c_body (x ...) (v_arg ...)) #f])

(define-metafunction G1m
  select-branch : K (v ...) (br ...) -> any
  [(select-branch K (v_arg ...)
                  ((K (x ...) -> c_body) br_rest ...))
   (substitute* c_body (x ...) (v_arg ...))]
  [(select-branch K (v_arg ...)
                  ((K_other (x_other ...) -> c_other) br_rest ...))
   (select-branch K (v_arg ...) (br_rest ...))]
  [(select-branch K (v_arg ...) ()) #f])

;; カーネル primitive の δ。primitive ごとに異なる引数個数を受け、名前または
;; arity が合わなければ undefined を返して R-Delta を不発火にする。
(define (kernel-delta/proc name . arguments)
  (match arguments
    [(list argument)
     (cond
       [(validator-row-by-name name)
        => (lambda (row)
             (define payload-type (validator-payload-type row))
             (define proposition (validator-proposition row))
             (define result-type
               `(Result (Refined ,payload-type ,proposition) String))
             (match argument
               [`(UVal ,payload)
                (if ((validator-check row) payload)
                    `(Construct ,result-type ok
                                (RVal
                                 (ProofRep (Reserved ,(validator-oid row))
                                           ,proposition)
                                 ,payload))
                    `(Construct ,result-type ng
                                ,(validator-error-message name)))]
               [_ 'undefined]))]
       ;; 値を未検証と宣言する操作は安全であるため check を伴わない。
       [(introduction-row-by-name name) `(UVal ,argument)]
       ;; Proof を捨てて弱める操作であるため無条件に安全である。
       [(projection-row-by-name name)
        (match argument
          [`(RVal (ProofRep ,_ ,_) ,payload) payload]
          [_ 'undefined])]
       ;; impl と derive は同じ規則で Implements Proof を返す。
       [(impl-row-by-name name)
        => (lambda (row)
             `(ProofRep (Reserved ,(impl-oid row))
                        (Implements ,(impl-target-type row)
                                    ,(impl-trait-name row))))]
       [else 'undefined])]
    [(list _ _)
     (cond
       [(intersect-row-by-name name)
        => (lambda (row)
             `(ProofRep (Reserved ,(intersect-oid row))
                        (RequiresBoth ,(intersect-left row)
                                      ,(intersect-right row))))]
       [else 'undefined])]
    [_ 'undefined]))

;; δ/g2 の側条件。既存の判定 primitive と trait primitive だけを拡張節へ通す。
(define (g2-primitive-name? name)
  (or (kernel-primitive-name? name)
      (trait-primitive-name? name)))

(define-metafunction/extension δ
  G2m
  δ/g2 : nm v ... -> any
  [(δ/g2 nm v ...)
   ,(apply kernel-delta/proc (term nm) (term (v ...)))
   (side-condition (g2-primitive-name? (term nm)))])

(define-metafunction/extension substitute*
  G2m
  substitute*/g2 : c (x ...) (v ...) -> any)

(define-metafunction/extension select-branch
  G2m
  select-branch/g2 : K (v ...) (br ...) -> any
  [(select-branch/g2 K (v_arg ...)
                     ((K (x ...) -> c_body) br_rest ...))
   (substitute*/g2 c_body (x ...) (v_arg ...))]
  [(select-branch/g2 K (v_arg ...)
                     ((K_other (x_other ...) -> c_other) br_rest ...))
   (select-branch/g2 K (v_arg ...) (br_rest ...))]
  [(select-branch/g2 K (v_arg ...) ()) #f])

(define-metafunction G2m
  proj-lookup : ((label v) ...) label -> any
  [(proj-lookup ((label_target v_target)
                 (label_rest v_rest) ...)
                label_target)
   v_target]
  [(proj-lookup ((label_head v_head)
                 (label_rest v_rest) ...)
                label_target)
   (proj-lookup ((label_rest v_rest) ...) label_target)]
  [(proj-lookup () label_target) #f])

(define-metafunction G2m
  unique-labels? : (label ...) -> boolean
  [(unique-labels? (label ...))
   ,(not (check-duplicates (term (label ...))))])

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

(define (table-ref table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

;; spec §5.3。H の record を field path に沿って辿る。
;; path が list でない、record でない値を辿る、または label が無い場合は
;; #f を返し、呼び出し側の where を不成立にする。
(define (heap-walk-path value fp)
  (and (list? fp)
       (for/fold ([current value]) ([seg (in-list fp)])
         (and current
              (match current
                [`(Rec ,fields)
                 (match (assoc seg fields)
                   [(list _ _ field-value) field-value]
                   [_ #f])]
                [_ #f])))))

;; 可変借用から field を射影するときの実行時 mode は H から読む。
;; 型付け側の field mode と食い違う configuration は型付け済みの項からは
;; 作れないので、ここでは heap の値だけを根拠にする。空 path、非 list、
;; record でない親、欠落 label はすべて #f で返す。
(define (proj-borrow-mut p fp ρ H)
  (and (record-path? fp)
       (pair? fp)
       (let* ([label (last fp)]
              [parent-fp (take fp (sub1 (length fp)))]
              [record (heap-walk-path (table-ref H p) parent-fp)])
         (match record
           [`(Rec ,fields)
            (match (assoc label fields)
              [(list _ field-mode _)
               (if (eq? field-mode 'mut)
                   `(BorrowMutRef ,p ,fp ,ρ)
                   `(BorrowRef ,p ,fp ,ρ))]
              [_ #f])]
           [_ #f]))))

;; spec §6.3。H から p の値を引き、record path の label を順に辿る。
;; 不正な path や不一致は #f となり、呼び出し側の規則を不発火にする。
(define (path-lookup H p fp)
  (and (record-path? fp)
       (heap-walk-path (table-ref H p) fp)))

;; spec §7.3。field path の先だけを関数的に差し替える。
(define (value-set-path old fp new)
  (cond
    [(not (list? fp)) #f]
    [(null? fp) new]
    [else
     (match old
       [`(Rec ,fields)
        (define label (first fp))
        (and (assoc label fields)
             (let ([rebuilt
                    (for/list ([field (in-list fields)])
                      (match-define (list name mode value) field)
                      (if (equal? name label)
                          (let ([updated
                                 (value-set-path value (rest fp) new)])
                            (and updated (list name mode updated)))
                          field))])
               (and (andmap values rebuilt) `(Rec ,rebuilt))))]
       [_ #f])]))

(define (path-set H p fp value)
  (define updated (value-set-path (table-ref H p) fp value))
  (and updated (table-set H p updated)))

(define (table-set table key value)
  (if (assoc key table)
      (for/list ([entry (in-list table)])
        (if (equal? (first entry) key)
            (list key value)
            entry))
      (append table (list (list key value)))))

;; An OwnedLeaf that crosses an Owned binding becomes the root value managed by
;; the new place. Retain a Dropped token tombstone to prevent token reuse.
(define (rehome-owned-root value tokens)
  (match value
    [`(OwnedLeaf ,tk ,payload)
     (and (not (owned-leaf? payload))
          (eq? (table-ref tokens tk) 'Available)
          (list payload (table-set tokens tk 'Dropped)))]
    [_ (list value tokens)]))

(define (fresh-place heap states)
  (for/fold ([next 0])
            ([entry (in-list (append heap states))])
    (max next (add1 (first entry)))))

(define (token-numbers value)
  (match value
    [`(tok ,(? exact-nonnegative-integer? n)) (list n)]
    [(? pair?) (append (token-numbers (car value))
                       (token-numbers (cdr value)))]
    [_ '()]))

;; Λtok、H、制御項、θ のどこかに現れる token を避けて採番する。
(define (fresh-token configuration)
  (match-define `(cfg ,core ,heap ,_states ,tokens ,events) configuration)
  (define used
    (append (token-numbers core)
            (token-numbers heap)
            (token-numbers tokens)
            (token-numbers events)))
  (term (tok ,(if (null? used) 0 (add1 (apply max used))))))

;; leaf の token が Λtok にあり、すべて Available か。
(define (leaves-available? leaves tokens)
  (for/and ([leaf (in-list leaves)])
    (define entry (assoc (first leaf) tokens))
    (and entry (eq? (second entry) 'Available))))

;; π の Available な root と、その値の内部の leaf を一緒に回収する。
;; H は不変。失敗時は #f を返し、呼び出し側の where を不成立にする。
(define (finalize/proc places heap states tokens trace)
  (define-values (final-states final-tokens final-events)
    (for/fold ([states states]
               [tokens tokens]
               [events '()])
              ([place (in-list (reverse places))])
      (cond
        [(not states) (values #f tokens events)]
        [(eq? (table-ref states place) 'Available)
         (define leaves (walk-owned-leaves (table-ref heap place)))
         (if (not (leaves-available? leaves tokens))
             (values #f tokens events)
             (values
              (table-set states place 'Dropped)
              (for/fold ([updated tokens])
                        ([leaf (in-list leaves)])
                (table-set updated (first leaf) 'Dropped))
              (append events
                      (for/list ([leaf (in-list leaves)])
                        (list 'finLeaf place (second leaf)))
                      (list (list 'fin place)))))]
        [else (values states tokens events)])))
  (and final-states
       (list final-states final-tokens (append trace final-events))))

(define-metafunction G1m
  finalize : π H Ω Λtok θ -> any
  [(finalize π H Ω Λtok θ)
   ,(finalize/proc (term π) (term H) (term Ω) (term Λtok) (term θ))])

(define (drop-leaves/proc value tokens)
  (for/fold ([updated tokens])
            ([leaf (in-list (walk-owned-leaves value))])
    (table-set updated (first leaf) 'Dropped)))

(define (leaves-droppable?/proc value tokens)
  (leaves-available? (walk-owned-leaves value) tokens))

(define-metafunction G1m
  drop-leaves : v Λtok -> Λtok
  [(drop-leaves v Λtok)
   ,(drop-leaves/proc (term v) (term Λtok))])

(define-metafunction G1m
  leaves-droppable? : v Λtok -> boolean
  [(leaves-droppable? v Λtok)
   ,(leaves-droppable?/proc (term v) (term Λtok))])

(define-metafunction/extension finalize
  G2m
  finalize/g2 : π H Ω Λtok θ -> any)

(define-metafunction/extension drop-leaves
  G2m
  drop-leaves/g2 : v Λtok -> Λtok)

(define-metafunction/extension leaves-droppable?
  G2m
  leaves-droppable?/g2 : v Λtok -> boolean)

(define (unique-binders? term)
  (and (match term
         [`(Lam ,_ ,_ ,parameters ,_)
          (not (check-duplicates parameters))]
         [`(Recur ,_ ,function ,parameters ,_ ,_)
          (not (check-duplicates (cons function parameters)))]
         [`(RecurVal ,_ ,function ,parameters ,_)
          (not (check-duplicates (cons function parameters)))]
         [`(,_ ,parameters -> ,_)
          #:when (list? parameters)
          (not (check-duplicates parameters))]
         [_ #t])
       (or (not (list? term))
           (andmap unique-binders? term))))

;; Construct fields are evaluated by E; (Construct τ K v ...) is already a value,
;; so the data rule needs no separate administrative transition.
(define -->g1/rules
  (reduction-relation
   G1m
   #:domain config

   (--> (cfg (in-hole E (Apply (PrimVal O nm) v_arg ...)) H Ω Λtok θ)
        (cfg (in-hole E v_result) H Ω Λtok θ)
        (where v_result (δ nm v_arg ...))
        R-Delta)

   (--> (cfg (in-hole E (Apply (Lam O cid_lam (x ...) c_body)
                               v_arg ...))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (where c_result
               (substitute* c_body (x ...) (v_arg ...)))
        R-Beta)

   (--> (cfg (in-hole E (Curry ov_f v_arg)) H Ω Λtok θ)
        (cfg (in-hole E
                      (CurryVal (Derived O_f (Curry v_arg))
                                ov_f
                                v_arg))
             H Ω Λtok θ)
        (where O_f (origin-of ov_f))
        R-CurryVal)

   (--> (cfg (in-hole E
                      (Apply (CurryVal O v_f v_fixed)
                             v_arg ...))
             H Ω Λtok θ)
        (cfg (in-hole E (Apply v_f v_fixed v_arg ...)) H Ω Λtok θ)
        R-ApplyCurry)

   (--> (cfg (in-hole E (Let (x τ) v_bound c_body)) H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (side-condition (not (owned-type? (term τ))))
        (where c_result (substitute c_body x v_bound))
        R-Let)

   (--> (cfg (in-hole E_outer
                      (Scope (p_managed ...)
                             (in-hole G_inner
                                      (Let (x τ_owned)
                                           v_bound
                                           c_body))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer
                      (Scope (p_managed ... p_new)
                             (in-hole G_inner c_result)))
             H_new Ω_new Λtok_new θ)
        (side-condition (owned-type? (term τ_owned)))
        (where p_new ,(fresh-place (term H) (term Ω)))
        (where c_result (substitute c_body x p_new))
        (where (v_stored Λtok_new)
               ,(rehome-owned-root (term v_bound) (term Λtok)))
        (where H_new
               ,(table-set (term H) (term p_new) (term v_stored)))
        (where Ω_new
               ,(table-set (term Ω) (term p_new) 'Available))
        R-LetOwned)

   (--> (cfg (in-hole E
                      (Eliminate (Construct τ K v_arg ...)
                                 (br ...)))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (where c_result
               (select-branch K (v_arg ...) (br ...)))
        R-Eliminate)

   (--> (cfg (in-hole E
                      (Recur cid_recur f (x ...) c_body c_next))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (where v_recur (RecurVal cid_recur f (x ...) c_body))
        (where c_result (substitute c_next f v_recur))
        R-RecurBind)

   (--> (cfg (in-hole E
                      (Apply (RecurVal cid_recur f (x ...) c_body)
                             v_arg ...))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (where v_recur (RecurVal cid_recur f (x ...) c_body))
        (where c_result
               (substitute* c_body
                            (f x ...)
                            (v_recur v_arg ...)))
        R-RecurUnfold)

   (--> (cfg (in-hole E (Move p)) H Ω Λtok θ)
        (cfg (in-hole E v_result) H Ω_new Λtok θ)
        (where Available ,(table-ref (term Ω) (term p)))
        (where v_result ,(table-ref (term H) (term p)))
        (where Ω_new ,(table-set (term Ω) (term p) 'Moved))
        R-Move)

   (--> (cfg (in-hole E (Move p)) H Ω Λtok θ)
        (cfg (in-hole E (Error p)) H Ω Λtok θ)
        (where state_old ,(table-ref (term Ω) (term p)))
        (side-condition (memq (term state_old) '(Moved Dropped)))
        R-MoveError)

   ;; 値の内部の所有資源へ token を割り当てる。値の変換と Λtok への
   ;; Available 追加を一つの規則で同時に行い、token 状態の更新を省いた
   ;; 単なる値変換にしない。
   (--> (cfg (in-hole E (OwnLeaf v_payload)) H Ω Λtok θ)
        (cfg (in-hole E (OwnedLeaf tk_new v_payload)) H Ω Λtok_new θ)
        (where c_whole (in-hole E (OwnLeaf v_payload)))
        (where tk_new ,(fresh-token (term (cfg c_whole H Ω Λtok θ))))
        (where Λtok_new
               ,(append (term Λtok) (list (list (term tk_new) 'Available))))
        R-OwnLeaf)

   (--> (cfg (in-hole E (Drop v_arg)) H Ω Λtok θ)
        (cfg (in-hole E unit) H Ω Λtok_final θ)
        (where Λtok_final (drop-leaves v_arg Λtok))
        (side-condition (term (leaves-droppable? v_arg Λtok)))
        R-Drop)

   (--> (cfg (in-hole E (Yield v_observed c_next))
             H Ω Λtok (event_old ...))
        (cfg (in-hole E c_next)
             H Ω Λtok (event_old ... (obs v_observed)))
        R-Yield)

   (--> (cfg (in-hole E (Suspend c_next)) H Ω Λtok θ)
        (cfg (in-hole E c_next) H Ω Λtok θ)
        R-Suspend)

   (--> (cfg (in-hole E_outer (Scope π_managed v_result)) H Ω Λtok θ)
        (cfg (in-hole E_outer v_result) H Ω_final Λtok_final θ_final)
        (where (Ω_final Λtok_final θ_final)
               (finalize π_managed H Ω Λtok θ))
        R-ScopeValue)

   (--> (cfg (in-hole E_outer
                      (Scope π_managed
                             (in-hole F_inner (Perform op v_arg))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer (Perform op v_arg)) H Ω_final Λtok_final θ_final)
        (where (Ω_final Λtok_final θ_final)
               (finalize π_managed H Ω Λtok θ))
        R-ScopeAbort)

   (--> (cfg (in-hole E_outer
                      (Scope π_managed
                             (in-hole F_inner (Error p_error))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer (Error p_error)) H Ω_final Λtok_final θ_final)
        (where (Ω_final Λtok_final θ_final)
               (finalize π_managed H Ω Λtok θ))
        R-ScopeError)

   (--> (cfg (in-hole E_outer
                      (Handle op
                              (x -> c_handler)
                              v_result))
             H Ω Λtok θ)
        (cfg (in-hole E_outer v_result) H Ω Λtok θ)
        R-HandleValue)

   (--> (cfg (in-hole E_outer
                      (Handle (Return b τ)
                              (x -> c_handler)
                              (in-hole F_inner
                                       (Perform (Return b τ) v_arg))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer c_result) H Ω Λtok θ)
        (where c_result (substitute c_handler x v_arg))
        R-HandleReturn)

   (--> (cfg (in-hole E_outer
                      (Handle op_handler
                              (x -> c_handler)
                              (in-hole F_inner
                                       (Perform op_performed v_arg))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer (Perform op_performed v_arg)) H Ω Λtok θ)
        (side-condition
         (not (equal? (term op_handler) (term op_performed))))
        R-HandleSkip)

   (--> (cfg (in-hole E_outer
                      (Handle op
                              (x -> c_handler)
                              (in-hole F_inner (Error p_error))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer (Error p_error)) H Ω Λtok θ)
        R-HandleError)))

(define -->g2/rules
  (extend-reduction-relation
   -->g1/rules
   G2m
   #:domain config

   ;; spec §13.1。H、Ω、θ は借用値の生成では変更しない。
   ;; own と designator が食い違う configuration では、どの規則も進まない。
   (--> (cfg (in-hole E (BorrowAt ρ (Own p fp) w)) H Ω Λtok θ)
        (cfg (in-hole E (BorrowRef p fp ρ)) H Ω Λtok θ)
        (where Available ,(table-ref (term Ω) (term p)))
        (side-condition (own-agrees? (term w) (term p) (term fp)))
        R-Borrow)

   (--> (cfg (in-hole E (BorrowAt ρ (Own p fp) w)) H Ω Λtok θ)
        (cfg (in-hole E (Error p)) H Ω Λtok θ)
        (where state_old ,(table-ref (term Ω) (term p)))
        (side-condition (memq (term state_old) '(Moved Dropped)))
        (side-condition (own-agrees? (term w) (term p) (term fp)))
        R-BorrowError)

   (--> (cfg (in-hole E (BorrowMutAt ρ (Own p fp) w)) H Ω Λtok θ)
        (cfg (in-hole E (BorrowMutRef p fp ρ)) H Ω Λtok θ)
        (where Available ,(table-ref (term Ω) (term p)))
        (side-condition (own-agrees? (term w) (term p) (term fp)))
        R-BorrowMut)

   (--> (cfg (in-hole E (BorrowMutAt ρ (Own p fp) w)) H Ω Λtok θ)
        (cfg (in-hole E (Error p)) H Ω Λtok θ)
        (where state_old ,(table-ref (term Ω) (term p)))
        (side-condition (memq (term state_old) '(Moved Dropped)))
        (side-condition (own-agrees? (term w) (term p) (term fp)))
        R-BorrowMutError)

   (--> (cfg (in-hole E (ReborrowAt ρ (Own p fp) (BorrowMutRef p fp ρ_parent))) H Ω Λtok θ)
        (cfg (in-hole E (BorrowRef p fp ρ)) H Ω Λtok θ)
        R-Reborrow)

   ;; spec §5.3。H、Ω、θ は射影で変更しない。
   (--> (cfg (in-hole E (ProjBorrowAt ρ own (BorrowRef p fp ρ_parent) label)) H Ω Λtok θ)
        (cfg (in-hole E (BorrowRef p fp_result ρ)) H Ω Λtok θ)
        (where fp_result ,(append (term fp) (list (term label))))
        (where (Own p fp_result) own)
        R-ProjBorrow)

   (--> (cfg (in-hole E (ProjBorrowAt ρ own (BorrowMutRef p fp ρ_parent) label)) H Ω Λtok θ)
        (cfg (in-hole E v_result) H Ω Λtok θ)
        (where fp_result ,(append (term fp) (list (term label))))
        (where (Own p fp_result) own)
        (where v_result ,(proj-borrow-mut (term p) (term fp_result)
                                          (term ρ) (term H)))
        R-ProjBorrowMut)

   ;; spec §6.3。H、Ω、θ は読み出しで変更しない。
   ;; Ω を見るのは Moved と Dropped の place を読まないためである。
   (--> (cfg (in-hole E (Read (BorrowRef p fp ρ))) H Ω Λtok θ)
        (cfg (in-hole E v_result) H Ω Λtok θ)
        (where Available ,(table-ref (term Ω) (term p)))
        (where v_result ,(path-lookup (term H) (term p) (term fp)))
        R-Read)

   (--> (cfg (in-hole E (Read (BorrowMutRef p fp ρ))) H Ω Λtok θ)
        (cfg (in-hole E v_result) H Ω Λtok θ)
        (where Available ,(table-ref (term Ω) (term p)))
        (where v_result ,(path-lookup (term H) (term p) (term fp)))
        R-ReadMut)

   ;; spec §7.3。Assign は capability の path 先だけを更新し、Ω と θ は保つ。
   (--> (cfg (in-hole E (Assign (BorrowMutRef p fp ρ) v)) H Ω Λtok θ)
        (cfg (in-hole E unit) H_new Ω Λtok θ)
        (where Available ,(table-ref (term Ω) (term p)))
        (where H_new ,(path-set (term H) (term p) (term fp) (term v)))
        R-Assign)

   ;; G2 の Lam 本体を含む値にも origin-of を適用できるよう、G1 の
   ;; R-CurryVal を G2m の入口で上書きする。
   (--> (cfg (in-hole E (Curry ov_f v_arg)) H Ω Λtok θ)
        (cfg (in-hole E
                      (CurryVal (Derived O_f (Curry v_arg))
                                ov_f
                                v_arg))
             H Ω Λtok θ)
        (where O_f (origin-of/g2 ov_f))
        R-CurryVal)

   (--> (cfg (in-hole E (Apply (PrimVal O nm) v_arg ...)) H Ω Λtok θ)
        (cfg (in-hole E v_result) H Ω Λtok θ)
        (where v_result (δ/g2 nm v_arg ...))
        R-Delta)

   (--> (cfg (in-hole E (Apply (Lam O cid_lam (x ...) c_body)
                               v_arg ...))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (where c_result
               (substitute*/g2 c_body (x ...) (v_arg ...)))
        R-Beta)

   (--> (cfg (in-hole E
                      (Eliminate (Construct τ K v_arg ...)
                                 (br ...)))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (where c_result
               (select-branch/g2 K (v_arg ...) (br ...)))
        R-Eliminate)

   (--> (cfg (in-hole E
                      (Apply (RecurVal cid_recur f (x ...) c_body)
                             v_arg ...))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (where v_recur (RecurVal cid_recur f (x ...) c_body))
        (where c_result
               (substitute*/g2 c_body
                              (f x ...)
                              (v_recur v_arg ...)))
        R-RecurUnfold)

   (--> (cfg (in-hole E
                      (Proj (Rec ((label_field m v_field) ...))
                            label_target))
             H Ω Λtok θ)
        (cfg (in-hole E v_result) H Ω Λtok θ)
        (side-condition
         (term (unique-labels? (label_field ...))))
        (where v_result
               (proj-lookup ((label_field v_field) ...)
                            label_target))
        R-Proj)

   ;; PRF-004: 搬送された ProofRep を一段で剥がす。Discharge は評価文脈では
   ;; ないため、包まれた c は Discharge が消えるまで還元されない。入れ子は外側から一段
   ;; ずつ消える。
   (--> (cfg (in-hole E (Discharge (ProofRep O φ) c_inner)) H Ω Λtok θ)
        (cfg (in-hole E c_inner) H Ω Λtok θ)
        R-Discharge)

   ;; RegionApp は静的な包みを剥がし、rp へ ρ を代入する。
   ;; 還元そのものは RParam を読まないが、剥がした本体は型注釈を運ぶ。
   ;; 代入しないと、束ねるものが無くなった RParam が注釈に残り、
   ;; config-ok? の再型付けで束縛の無い region 引数として落ちる。
   ;; 長さの不一致は region-app-arity が型検査で落とすため、還元では
   ;; 合わない形として詰まらせる。
   (--> (cfg (in-hole E
                      (RegionApp (RegionLam (rp ...) c_body) (ρ ...)))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (side-condition
         (= (length (term (rp ...))) (length (term (ρ ...)))))
        (where c_result
               ,(subst-region-params
                 (term c_body)
                 (for/hash ([name (in-list (term (rp ...)))]
                            [argument (in-list (term (ρ ...)))])
                   (values name argument))))
        R-RegionApp)

   (--> (cfg (in-hole E
                      (Let (x bmode τ) v_bound c_body))
             H Ω Λtok θ)
        (cfg (in-hole E c_result) H Ω Λtok θ)
        (side-condition (not (owned-type? (term τ))))
        (where c_result (substitute c_body x v_bound))
        R-LetB)

   (--> (cfg (in-hole E_outer
                      (Scope (p_managed ...)
                             (in-hole G_inner
                                      (Let (x bmode τ_owned)
                                           v_bound
                                           c_body))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer
                      (Scope (p_managed ... p_new)
                             (in-hole G_inner c_result)))
             H_new Ω_new Λtok_new θ)
        (side-condition (owned-type? (term τ_owned)))
        (where p_new ,(fresh-place (term H) (term Ω)))
        (where c_result (substitute c_body x p_new))
        (where (v_stored Λtok_new)
               ,(rehome-owned-root (term v_bound) (term Λtok)))
        (where H_new
               ,(table-set (term H) (term p_new) (term v_stored)))
        (where Ω_new
               ,(table-set (term Ω) (term p_new) 'Available))
        R-LetOwnedB)

   ;; G2m の Rec を含む値にも leaf 回収を適用する。G1m の同名規則は
   ;; G2m の v を受けられないため、G2m 拡張を明示する。
   (--> (cfg (in-hole E (Drop v_arg)) H Ω Λtok θ)
        (cfg (in-hole E unit) H Ω Λtok_final θ)
        (where Λtok_final (drop-leaves/g2 v_arg Λtok))
        (side-condition (term (leaves-droppable?/g2 v_arg Λtok)))
        R-Drop)

   (--> (cfg (in-hole E_outer (Scope π_managed v_result)) H Ω Λtok θ)
        (cfg (in-hole E_outer v_result) H Ω_final Λtok_final θ_final)
        (where (Ω_final Λtok_final θ_final)
               (finalize/g2 π_managed H Ω Λtok θ))
        R-ScopeValue)

   (--> (cfg (in-hole E_outer
                      (Scope π_managed
                             (in-hole F_inner (Perform op v_arg))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer (Perform op v_arg))
             H Ω_final Λtok_final θ_final)
        (where (Ω_final Λtok_final θ_final)
               (finalize/g2 π_managed H Ω Λtok θ))
        R-ScopeAbort)

   (--> (cfg (in-hole E_outer
                      (Scope π_managed
                             (in-hole F_inner (Error p_error))))
             H Ω Λtok θ)
        (cfg (in-hole E_outer (Error p_error))
             H Ω_final Λtok_final θ_final)
        (where (Ω_final Λtok_final θ_final)
               (finalize/g2 π_managed H Ω Λtok θ))
        R-ScopeError)))

;; Binding-aware matching freshens binders before destructuring.  Check the raw
;; configuration first so repeated source binders cannot be freshened apart.
(define (raw-steps config)
  (if (unique-binders? config)
      (apply-reduction-relation -->g1/rules config)
      '()))

(define (raw-steps-g2 config)
  (if (unique-binders? config)
      (apply-reduction-relation -->g2/rules config)
      '()))

(define -->g1
  (reduction-relation
   G1m
   #:domain config
   (--> config_before
        config_after
        (where (config_prefix ... config_after config_suffix ...)
               ,(raw-steps (term config_before)))
        R-Step)))

(define -->g2
  (reduction-relation
   G2m
   #:domain config
   (--> config_before
        config_after
        (where (config_prefix ... config_after config_suffix ...)
               ,(raw-steps-g2 (term config_before)))
        R-Step)))

(define (inject core)
  (unless (redex-match? G1 c core)
    (raise-argument-error 'inject "G1 core term" core))
  `(cfg (Scope () ,core) () () () ()))

(define (inject-g2 core)
  (unless (redex-match? G2 c core)
    (raise-argument-error 'inject-g2 "G2 core term" core))
  `(cfg (Scope () ,core) () () () ()))

(define (inject-g2m core)
  (unless (redex-match? G2m c core)
    (raise-argument-error 'inject-g2m "G2m core term" core))
  `(cfg (Scope () ,core) () () () ()))

(define (run config fuel)
  (unless (redex-match? G1m config config)
    (raise-argument-error 'run "G1m configuration" config))
  (unless (exact-nonnegative-integer? fuel)
    (raise-argument-error 'run "exact-nonnegative-integer?" fuel))
  (let loop ([current config]
             [remaining fuel])
    (define next
      (remove-duplicates
       (apply-reduction-relation -->g1 current)
       equal?))
    (cond
      [(null? next) current]
      [(zero? remaining) 'timeout]
      [(null? (cdr next)) (loop (car next) (sub1 remaining))]
      [else
       (error 'run
              "nondeterministic reduction from ~e to ~e"
              current
              next)])))

(define (run-g2 config fuel)
  (unless (redex-match? G2m config config)
    (raise-argument-error 'run-g2 "G2m configuration" config))
  (unless (exact-nonnegative-integer? fuel)
    (raise-argument-error 'run-g2 "exact-nonnegative-integer?" fuel))
  (let loop ([current config]
             [remaining fuel])
    (define next
      (remove-duplicates
       (apply-reduction-relation -->g2 current)
       equal?))
    (cond
      [(null? next) current]
      [(zero? remaining) 'timeout]
      [(null? (cdr next)) (loop (car next) (sub1 remaining))]
      [else
       (error 'run-g2
              "nondeterministic reduction from ~e to ~e"
              current
              next)])))

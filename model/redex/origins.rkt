#lang racket

(require racket/match
         redex/reduction-semantics
         "diagnostic.rkt"
         "erase.rkt"
         "lang.rkt"
         "macro-expand.rkt"
         "span-core.rkt"
         "traits.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide Δ0
         Γ0
         Π0
         R0
         valid-origin?
         kernel-gamma0-entries
         current-trait-ledger
         current-trait-env
         current-R0
         current-Γ0
         current-trait-r0-entries
         current-trait-gamma0-entries
         make-trait-ledger
         (struct-out trait-ledger)
         canonical-trait-ledger
         kindOf
         lookup
         origin-of
         origin-of/g2
         proof-issuer-ok?
         proof-occurrence-ok?
         trait-gamma0-entries
         trait-global-bindings
         verify-origins
         verify-origins/diagnostic
         verify-initial-origins
         verify-initial-origins/diagnostic)

;; 判定表の行と、導入・射影 primitive の行から R0 の追加分を生成する。
;; oid は primitive の発行者であると同時に ProofRep の発行者でもある。
(define kernel-r0-entries
  (append
   (for/list ([row (in-list validator-table)])
     (list (validator-oid row) (list 'prim (validator-name row))))
   (for/list ([row (in-list introduction-table)])
     (list (first row) (list 'prim (second row))))
   (for/list ([row (in-list projection-table)])
     (list (first row) (list 'prim (second row))))))

(define kernel-r0
  (append
   (term ((o-add (prim add))
          (o-sub (prim sub))
          (o-mul (prim mul))
          (o-lt (prim lt))
          (o-le (prim le))
          (o-eq (prim eq))
          (o-acquire (prim acquire))
          (o-int (type Int))
          (o-bool (type Bool))
          (o-unit (type Unit))
          (o-string (type String))
          (o-never (type Never))
          (o-res (type Res))
          (o-list (type List))
          (o-option (type Option))
          (o-result (type Result))
          (o-type-narrative typeNarrative)
          ;; POL-001: 標準 Policy Narrative の二つの親のうち、まだ R0 に無い
          ;; 方。policy 自身は id を持たない。
          (o-language-narrative languageNarrative)))
   kernel-r0-entries
   ;; RFN-002: merge が発行する常在性 witness の発行者。primitive を持たない
   ;; ため (prim ...) ではなく単独の id として登録する。
   (term ((o-merge merge)))
   ;; PRF-005: narrowing が発行する残余安全性 witness。Policy Narrative の
   ;; 判定であり Γ0 に載らないため、単独の id として登録する。
   (term ((o-narrow narrow)))))

;; RFN-001: validate primitive の型は行ごとの単相型である。latent effect と
;; obligation は空とする。判定は純粋な全域計算であるためである。
(define kernel-gamma0-entries
  (append
   (for/list ([row (in-list validator-table)])
     (define payload-type (validator-payload-type row))
     (list (validator-name row)
           (list `(NFn ((Untrusted ,payload-type))
                       (Result (Refined ,payload-type
                                        ,(validator-proposition row))
                               String)
                       () () () (Reserved ,(validator-oid row)))
                 `(PrimVal (Reserved ,(validator-oid row))
                           ,(validator-name row)))))
   (for/list ([row (in-list introduction-table)])
     (match-define (list oid name payload-type) row)
     (list name
           (list `(NFn (,payload-type) (Untrusted ,payload-type) () () () (Reserved ,oid))
                 `(PrimVal (Reserved ,oid) ,name))))
   (for/list ([row (in-list projection-table)])
     (match-define (list oid name proposition payload-type) row)
     (list name
           (list `(NFn ((Refined ,payload-type ,proposition))
                       ,payload-type () () () (Reserved ,oid))
                 `(PrimVal (Reserved ,oid) ,name))))))

(define kernel-gamma0
  (append
   (term ((add ((NFn (Int Int) Int () () () (Reserved o-add))
                (PrimVal (Reserved o-add) add)))
          (sub ((NFn (Int Int) Int () () () (Reserved o-sub))
                (PrimVal (Reserved o-sub) sub)))
          (mul ((NFn (Int Int) Int () () () (Reserved o-mul))
                (PrimVal (Reserved o-mul) mul)))
          (lt ((NFn (Int Int) Bool () () () (Reserved o-lt))
               (PrimVal (Reserved o-lt) lt)))
          (le ((NFn (Int Int) Bool () () () (Reserved o-le))
               (PrimVal (Reserved o-le) le)))
          (eq ((NFn (Int Int) Bool () () () (Reserved o-eq))
               (PrimVal (Reserved o-eq) eq)))
          (acquire ((NFn (Int) (Owned Res) () () () (Reserved o-acquire))
                    (PrimVal (Reserved o-acquire) acquire)))))
   kernel-gamma0-entries))

(define (trait-r0-entries/env env)
  (append
   (for/list ([row (in-list (trait-env-impl-rows env))])
     (list (impl-oid row) (list 'prim (impl-name row))))
   (for/list ([row (in-list (trait-env-intersect-rows env))])
     (list (intersect-oid row) (list 'prim (intersect-name row))))))

(define (trait-gamma0-entries/env env)
  (append
   (for/list ([row (in-list (trait-env-trait-rows env))])
     (define proposition `(ValidNarrativeTrait ,(trait-name row)))
     (list (trait-constant-name row)
           (list `(Proof ,proposition)
                 `(ProofRep ,(trait-derived-origin row) ,proposition))))
   (for/list ([row (in-list (trait-env-impl-rows env))])
     (define trait-row (trait-row-by-name (impl-trait-name row) env))
     (define requirements
       (instantiate-requirements (trait-template trait-row)
                                 (impl-target-type row)))
     (list (impl-name row)
           (list `(NFn ((Record ,requirements))
                       (Proof (Implements ,(impl-target-type row)
                                          ,(impl-trait-name row)))
                       () () () ,(impl-derived-origin row))
                 `(PrimVal (Reserved ,(impl-oid row)) ,(impl-name row)))))
   (for/list ([row (in-list (trait-env-intersect-rows env))])
     (list (intersect-name row)
           (list `(NFn ((Proof (ValidNarrativeTrait ,(intersect-left row)))
                        (Proof (ValidNarrativeTrait ,(intersect-right row))))
                       (Proof (RequiresBoth ,(intersect-left row)
                                            ,(intersect-right row)))
                       () () () ,(intersect-derived-origin row))
                 `(PrimVal (Reserved ,(intersect-oid row))
                           ,(intersect-name row)))))))

(define (trait-global-bindings/env env)
  (append
   (for/list ([row (in-list (trait-env-impl-rows env))])
     (define trait-row (trait-row-by-name (impl-trait-name row) env))
     (list (impl-name row)
           (list `(Implements ,(impl-target-type row)
                              ,(impl-trait-name row))
                 (impl-derived-origin row)
                 (impl-name row)
                 'root
                 'default
                 (list (trait-origin trait-row) (impl-oid row)))))
   (for/list ([row (in-list (trait-env-intersect-rows env))])
     (list (intersect-name row)
           (list `(RequiresBoth ,(intersect-left row)
                                ,(intersect-right row))
                 (intersect-derived-origin row)
                 (intersect-name row)
                 'root
                 'default
                 (list (intersect-oid row)))))))

(define (check-unique-keys! table bail kind)
  (let loop ([rows table] [seen (seteq)])
    (cond [(null? rows) (void)]
          [(set-member? seen (first (car rows)))
           (bail 'surface-trait-name-collision kind (first (car rows)))]
          [else (loop (cdr rows) (set-add seen (first (car rows))))])))

(struct trait-ledger (env r0 gamma0 global-bindings) #:transparent)

(define (make-trait-ledger env #:fail fail)
  (let/ec return
    (define (bail reason kind key) (return (fail reason kind key)))
    (define r0 (append kernel-r0 (trait-r0-entries/env env)))
    (define gamma0 (append kernel-gamma0 (trait-gamma0-entries/env env)))
    ;; NAR-003: 行の origin を R0 の実値まで含めて照合する。壊れた origin を
    ;; 持つ Proof 値は gamma0 に入るが、検査を通るまで台帳の外へ出ない。
    (for ([row (in-list (trait-env-trait-rows env))])
      (unless (trait-origin-ok? r0 row env)
        (bail 'surface-trait-name-collision 'origin-id (trait-origin row))))
    ;; trait 行の id は R0 の行ではないが、global binding の系譜で
    ;; R0 の鍵と並ぶので、同じ名前空間で一意にする。
    (check-unique-keys!
     (append (for/list ([row (in-list (trait-env-trait-rows env))])
               (list (trait-origin row) #f))
             r0)
     bail 'origin-id)
    (check-unique-keys! gamma0 bail 'primitive-name)
    (trait-ledger env r0 gamma0 (trait-global-bindings/env env))))

(define canonical-trait-ledger
  (make-trait-ledger canonical-trait-env
                     #:fail (λ (reason kind key)
                              (error 'origins "~a: ~s ~s" reason kind key))))

(define current-trait-ledger (make-parameter canonical-trait-ledger))

(define (current-trait-env) (trait-ledger-env (current-trait-ledger)))
(define (current-R0) (trait-ledger-r0 (current-trait-ledger)))
(define (current-Γ0) (trait-ledger-gamma0 (current-trait-ledger)))
;; 台帳の構築順は kernel 行の後ろへ trait 行を append する。
;; 呼出しのたびに env から組み直さず、台帳の欄の後半を切り出す。
(define (current-trait-r0-entries)
  (drop (current-R0) (length kernel-r0)))
(define (current-trait-gamma0-entries)
  (drop (current-Γ0) (length kernel-gamma0)))

(define R0 (trait-ledger-r0 canonical-trait-ledger))
(define Γ0 (trait-ledger-gamma0 canonical-trait-ledger))
(define trait-gamma0-entries (drop Γ0 (length kernel-gamma0)))

(define Δ0
  (term ((Int (TypeRep (Reserved o-int) Int Type))
         (Bool (TypeRep (Reserved o-bool) Bool Type))
         (Unit (TypeRep (Reserved o-unit) Unit Type))
         (String (TypeRep (Reserved o-string) String Type))
         (Never (TypeRep (Reserved o-never) Never Type))
         (Res (TypeRep (Reserved o-res) Res Type))
         (List (TypeRep (Reserved o-list) List (Type -> Type)))
         (Option (TypeRep (Reserved o-option) Option (Type -> Type)))
         (Result (TypeRep (Reserved o-result)
                          Result
                          (Type -> (Type -> Type)))))))

(define kernel-pi0-entries
  (term ((typeNarrativeCap
          (TypeNarrativeCap (Reserved o-type-narrative))))))

(define Π0 kernel-pi0-entries)

;; Γ-pc⁰ へ足す global 候補。entry は (φ O cid sid pid hook) の 6 要素で、
;; origin と hook は同じ表の行へ決定的に結び付く。
;; TRT-005: intersect 行は RequiresBoth 候補も供給する。合成 trait が正典表に
;; 載っている以上、その二項要求は利用側が明示的に Apply しなくても立つ。
(define (trait-global-bindings)
  (trait-global-bindings/env (current-trait-env)))

(define (kind-of/proc type-form)
  (case type-form
    [(List Option) '(Type -> Type)]
    [(Result) '(Type -> (Type -> Type))]
    [else 'Type]))

(define-metafunction G1
  kindOf : t -> κ
  [(kindOf t) ,(kind-of/proc (term t))])

(define (lookup table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

(define (valid-origin? r0 origin)
  (match origin
    ['User #t]
    [`(Reserved ,id) (and (assoc id r0) #t)]
    [`(Derived ,parent ,_) (valid-origin? r0 parent)]
    [_ #f]))

(define (origin-data/proc value)
  (match value
    [`(Lam ,origin ,_ ,_ ,_) `(Lam ,origin)]
    [`(PrimVal ,origin ,primitive) `(PrimVal ,origin ,primitive)]
    [`(CurryVal ,origin ,function ,argument)
     `(CurryVal ,origin ,function ,argument)]
    [`(TypeRep ,origin ,type-form ,kind)
     `(TypeRep ,origin ,type-form ,kind)]
    [`(ProofRep ,origin ,proposition)
     `(ProofRep ,origin ,proposition)]
    [`(RVal (ProofRep ,origin ,proposition) ,payload)
     `(RVal ,origin ,proposition ,payload)]
    [`(RecurVal ,_ ,_ ,_ ,_) '(RecurVal User)]
    [_ #f]))

(define (origin-of/proc value)
  (define data (origin-data/proc value))
  (and data (second data)))

(define-metafunction G1
  origin-of : ov -> O
  [(origin-of ov) ,(origin-of/proc (term ov))])

;; G2m の closure 本体は G1 の c より広いので、G1 の origin-of を
;; G2m へ拡張した入口を用意する。判定本体は同じ origin-data/proc である。
(define-metafunction/extension origin-of
  G2m
  origin-of/g2 : ov -> O
  [(origin-of/g2 ov) ,(origin-of/proc (term ov))])

(define (reserved-type-rep? type-form value)
  (equal? (lookup Δ0 type-form) value))

;; RFN-003: 発行者対応。「この origin はこの φ を発行してよいか」だけを見る。
;; 出現許可（どの層に置いてよいか）は含めない。探索側の候補 wf はこの判定
;; だけを参照する。両方を混ぜると、merge が立てた常在性 witness が候補 wf を
;; 通らず、(Goal (Presence f)) を局所検査で discharge できなくなる。
(define (proof-issuer-ok? r0 origin proposition)
  (match proposition
    ['TypeNarrativeCap
     (and (equal? origin '(Reserved o-type-narrative))
          (eq? (lookup r0 'o-type-narrative) 'typeNarrative))]
    [`(Prop ,_)
     (match origin
       [`(Reserved ,id)
        (define row (validator-row-by-oid id))
        (and row
             (equal? (validator-proposition row) proposition)
             (equal? (lookup r0 id) `(prim ,(validator-name row))))]
       [_ #f])]
    [`(ValidNarrativeTrait ,trait)
     (match origin
       ;; NAR-003: trait の Proof は予約 Narrative から継承した派生 origin を
       ;; 持つ。正規の構成子は trait-derived-origin であり、origin がその像と
       ;; 一致することと、行そのものが R0 に対して正しいことを見る。親と step
       ;; の形をここへ書き写さないのは、正規の構成子を 1 箇所に保つためである。
       [`(Derived ,_ ,_)
        (define env (current-trait-env))
        (define row (trait-row-by-name trait env))
        (and row
             (equal? origin (trait-derived-origin row))
             (trait-origin-ok? r0 row env)
             #t)]
       [_ #f])]
    [`(Implements ,type ,trait)
     (match origin
       [`(Derived ,_ (Impl ,id ,_ ,_ ,_))
        (define row (impl-row-by-oid id (current-trait-env)))
        (define actual-key (canonical-proposition-key proposition))
        (define expected-key
          (and row
               (canonical-proposition-key
                `(Implements ,(impl-target-type row)
                             ,(impl-trait-name row)))))
        (and row
             actual-key
             expected-key
             (equal? actual-key expected-key)
             (equal? origin (impl-derived-origin row))
             (equal? (lookup r0 id) `(prim ,(impl-name row))))]
       ;; TRT-004/NAR-004: 合成 trait への所属。親は intersect 行の派生 origin
       ;; であり、成分の origin は step の中に残る。成果物の検証層は origin しか
       ;; 見ないため、成分を落とすと手書きの合成 origin が検証を通る。
       ;; 停止性は intersect-table の非巡回性（intersect-acyclic?）から従う。
       [`(Derived (Derived ,_ (Intersect ,iid ,_ ,_ ,_))
                  (Compose ,output ,origin-left ,origin-right))
        (define row (intersect-row-by-oid iid (current-trait-env)))
        (and row
             (eq? output trait)
             (eq? (intersect-output row) trait)
             (equal? (second origin) (intersect-derived-origin row))
             (equal? (lookup r0 iid) `(prim ,(intersect-name row)))
             (proof-issuer-ok? r0 origin-left
                               `(Implements ,type ,(intersect-left row)))
             (proof-issuer-ok? r0 origin-right
                               `(Implements ,type ,(intersect-right row))))]
       [_ #f])]
    [`(RequiresBoth ,_ ,_)
     (match origin
       [`(Derived ,_ (Intersect ,id ,_ ,_ ,_))
        (define row (intersect-row-by-oid id (current-trait-env)))
        (define actual-key (canonical-proposition-key proposition))
        (define expected-key
          (and row
               (canonical-proposition-key
                `(RequiresBoth ,(intersect-left row)
                               ,(intersect-right row)))))
        (and row
             actual-key
             expected-key
             (equal? actual-key expected-key)
             (equal? origin (intersect-derived-origin row))
             (equal? (lookup r0 id) `(prim ,(intersect-name row))))]
       [_ #f])]
    [`(Presence ,_)
     (and (equal? origin '(Reserved o-merge))
          (eq? (lookup r0 'o-merge) 'merge))]
    [`(FieldType ,_ ,_)
     (and (equal? origin '(Reserved o-merge))
          (eq? (lookup r0 'o-merge) 'merge))]
    [`(RemainderSafelyDropped ,_ ,_)
     (and (equal? origin '(Reserved o-narrow))
          (eq? (lookup r0 'o-narrow) 'narrow))]
    [_ #f]))

;; RFN-002: 出現許可。常在性 witness は merge の局所検査のためだけに立つ値で
;; あり、初期成果物にも到達成果物にも現れてはならない。artifact に現れたら
;; merge の位置情報が失われ、φ の集約が merge をまたいでしまう。
(define (proof-occurrence-ok? proposition [discharge-proof? #f])
  (match proposition
    [`(Presence ,_) #f]
    [`(FieldType ,_ ,_) #f]
    ;; PRF-005: narrowing の Proof は Discharge の proof 欄でだけ許す。
    [`(RemainderSafelyDropped ,_ ,_) discharge-proof?]
    [_ #t]))

;; RFN-001: RVal のペイロード束縛検査。witness の命題が判定表の行に対応し、
;; ペイロードのリテラル型がその行の τ と一致し、check がそのペイロードを
;; 受理することを求める。validate を通さずに手で組んだ RVal をここで落とす。
(define (refined-value-valid? r0 origin proposition payload)
  (define row (validator-row-by-proposition proposition))
  (and row
       (proof-issuer-ok? r0 origin proposition)
       (equal? (literal-type payload) (validator-payload-type row))
       (and ((validator-check row) payload) #t)))

(define (origin-shape-valid? r0 value [discharge-proof? #f])
  ;; span.md §4 の通り O は spanless である。CurryVal の origin へ埋まる値も、
  ;; Δ0 の行も、validator の payload も spanless であるため、形の検査は
  ;; 投影の上で行う。走査そのものは spanful な項の上を進む。
  (define erased (erase-core value))
  (match (origin-data/proc erased)
    [`(PrimVal (Reserved ,id) ,primitive)
     (equal? (lookup r0 id) `(prim ,primitive))]
    ;; macro.md §8.2: 展開由来の Lam は (Derived O_call (Expand nm)) を持つ。
    ;; 展開はこの 1 つの step だけを足すため、他の step は受理しない。
    [`(Lam ,origin)
     (or (eq? origin 'User)
         (match origin
           [`(Derived ,parent (Expand ,_nm)) (valid-origin? r0 parent)]
           [_ #f]))]
    [`(CurryVal ,origin ,function ,argument)
     (define parent (origin-of/proc function))
     (and parent
          (valid-origin? r0 origin)
          (equal? origin `(Derived ,parent (Curry ,argument))))]
    [`(TypeRep ,origin ,type-form ,kind)
     (and (valid-origin? r0 origin)
          (equal? kind (kind-of/proc type-form))
          (match origin
            [`(Reserved ,id)
             (and (equal? (lookup r0 id) `(type ,type-form))
                  (reserved-type-rep? type-form erased))]
            [`(Derived (Reserved o-type-narrative) (Make ,made))
             (and (eq? (lookup r0 'o-type-narrative) 'typeNarrative)
                  (equal? made type-form))]
            [_ #f]))]
    [`(ProofRep ,origin ,proposition)
     (and (proof-issuer-ok? r0 origin proposition)
          (proof-occurrence-ok? proposition discharge-proof?))]
    [`(RVal ,origin ,proposition ,payload)
     (refined-value-valid? r0 origin proposition payload)]
    [_ #f]))

(define origin-bearing-heads '(Lam PrimVal CurryVal TypeRep ProofRep RVal))

(define (origin-bearing-head? value)
  (and (pair? value)
       (memq (car value) origin-bearing-heads)))

(define (core-term? value)
  (or (and (redex-match? G2m c value) #t)
      (and (redex-match? G2+ c value) #t)))

(define (check-core! who value)
  (unless (core-term? value)
    (error who "c でも G2+ の c でもない: ~s" value)))

(define (verify-origins/proc r0 core [expanded? #t])
  (define (walk-list terms)
    (cond
      [(null? terms) 'ok]
      [else
       (define result (walk (car terms)))
       (if (eq? result 'ok)
           (walk-list (cdr terms))
           result)]))
  (define (walk term [discharge-proof? #f])
    (cond
      [(origin-bearing-head? term)
       (if (origin-shape-valid? r0 term discharge-proof?)
           (walk-list term)
           `(forged ,term))]
      [(and (pair? term) (eq? (car term) 'Discharge))
       (match (peel-node term)
         [`(Discharge ,proof ,inner)
          (define result (walk proof #t))
          (if (eq? result 'ok) (walk inner) result)]
         [_ (walk-list term)])]
      [(list? term) (walk-list term)]
      [else 'ok]))
  (check-core! 'verify-origins core)
  (when expanded?
    (require-expanded! 'verify-origins core))
  (walk core))

(define-metafunction G2m
  verify-origins : any any -> any
  [(verify-origins any_R0 any_core)
   ,(verify-origins/proc (term any_R0) (term any_core))])

;; RFN-001: 初期成果物の層。UCore は UVal と RVal の構文を持たないため、
;; elaboration の出力にこれらが現れることはない。到達成果物では validate が
;; 作るので許す。層ごとに許す値が違うため入口を分ける。
(define (initial-layer-violation core)
  (let walk ([subject core])
    (cond
      [(and (pair? subject) (memq (car subject) '(UVal RVal)))
       `(forged ,subject)]
      [(list? subject)
       (for/or ([element (in-list subject)]) (walk element))]
      [else #f])))

(define (verify-initial-origins/proc r0 core)
  (check-core! 'verify-initial-origins core)
  (or (initial-layer-violation core)
      (verify-origins/proc r0 core #f)))

(define-metafunction G2m
  verify-initial-origins : any any -> any
  [(verify-initial-origins any_R0 any_core)
   ,(verify-initial-origins/proc (term any_R0) (term any_core))])

;; spec §3: G4d2 の公開 Diagnostic 境界はこの 2 つの adapter である。
;; metafunction は (forged ...) を返す形のまま残す。diagnostic.md §1 が Diagnostic
;; IR を項でないと定めており、metafunction の返り値へ struct を混ぜられない。
;; diagnostic.md §9 が origins の registry key を (forged ...) の頭から導いている
;; のも、metafunction が形を保つ前提の記述である。
(define (origins-result->diagnostic result [expansion-context (hash)])
  (match result
    [(list 'forged subject)
     ;; subject は棄却の対象になった部分項である。typing と違い位置が分かるため、
     ;; 根へ丸めずここから span を取り、値そのものを found へ入れる。
     (diagnostic-of 'origins 'forged
                    #:primary-span (entry-span subject)
                    #:found subject
                    #:expansion-context expansion-context)]
    [other other]))

(define (verify-origins/diagnostic r0 core [expansion-context (hash)])
  (origins-result->diagnostic (verify-origins/proc r0 core)
                              expansion-context))

(define (verify-initial-origins/diagnostic r0 core)
  (origins-result->diagnostic (verify-initial-origins/proc r0 core)))

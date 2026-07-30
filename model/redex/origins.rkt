#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt"
         "traits.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide Δ0
         Γ0
         Π0
         R0
         kindOf
         origin-of
         proof-issuer-ok?
         trait-global-bindings
         verify-origins
         verify-initial-origins)

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

(define trait-r0-entries
  (append
   (for/list ([row (in-list trait-table)])
     (list (trait-origin row) (list 'trait (trait-name row))))
   (for/list ([row (in-list impl-table)])
     (list (impl-oid row) (list 'prim (impl-name row))))
   (for/list ([row (in-list intersect-table)])
     (list (intersect-oid row) (list 'prim (intersect-name row))))))

(define R0
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
          (o-type-narrative typeNarrative)))
   kernel-r0-entries
   ;; RFN-002: merge が発行する常在性 witness の発行者。primitive を持たない
   ;; ため (prim ...) ではなく単独の id として登録する。
   (term ((o-merge merge)))
   trait-r0-entries))

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
                       () ())
                 `(PrimVal (Reserved ,(validator-oid row))
                           ,(validator-name row)))))
   (for/list ([row (in-list introduction-table)])
     (match-define (list oid name payload-type) row)
     (list name
           (list `(NFn (,payload-type) (Untrusted ,payload-type) () ())
                 `(PrimVal (Reserved ,oid) ,name))))
   (for/list ([row (in-list projection-table)])
     (match-define (list oid name proposition payload-type) row)
     (list name
           (list `(NFn ((Refined ,payload-type ,proposition))
                       ,payload-type () ())
                 `(PrimVal (Reserved ,oid) ,name))))))

(define (trait-constant-name row)
  (string->symbol (format "~a-trait" (trait-name row))))

(define trait-gamma0-entries
  (append
   (for/list ([row (in-list trait-table)])
     (define proposition `(ValidNarrativeTrait ,(trait-name row)))
     (list (trait-constant-name row)
           (list `(Proof ,proposition)
                 `(ProofRep (Reserved ,(trait-origin row)) ,proposition))))
   (for/list ([row (in-list impl-table)])
     (define trait-row (trait-row-by-name (impl-trait-name row)))
     (define requirements
       (instantiate-requirements
        (trait-template trait-row)
        (impl-target-type row)))
     (list (impl-name row)
           (list `(NFn ((Record ,requirements))
                       (Proof (Implements ,(impl-target-type row)
                                          ,(impl-trait-name row)))
                       () ())
                 `(PrimVal (Reserved ,(impl-oid row)) ,(impl-name row)))))
   (for/list ([row (in-list intersect-table)])
     (list (intersect-name row)
           (list `(NFn ((Proof (ValidNarrativeTrait ,(intersect-left row)))
                        (Proof (ValidNarrativeTrait ,(intersect-right row))))
                       (Proof (RequiresBoth ,(intersect-left row)
                                            ,(intersect-right row)))
                       () ())
                 `(PrimVal (Reserved ,(intersect-oid row))
                           ,(intersect-name row)))))))

(define Γ0
  (append
   (term ((add ((NFn (Int Int) Int () ())
                (PrimVal (Reserved o-add) add)))
          (sub ((NFn (Int Int) Int () ())
                (PrimVal (Reserved o-sub) sub)))
          (mul ((NFn (Int Int) Int () ())
                (PrimVal (Reserved o-mul) mul)))
          (lt ((NFn (Int Int) Bool () ())
               (PrimVal (Reserved o-lt) lt)))
          (le ((NFn (Int Int) Bool () ())
               (PrimVal (Reserved o-le) le)))
          (eq ((NFn (Int Int) Bool () ())
               (PrimVal (Reserved o-eq) eq)))
          (acquire ((NFn (Int) (Owned Res) () ())
                    (PrimVal (Reserved o-acquire) acquire)))))
   kernel-gamma0-entries
   trait-gamma0-entries))

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

(define trait-pi0-entries
  (for/list ([row (in-list trait-table)])
    (list (trait-constant-name row)
          (list `(ValidNarrativeTrait ,(trait-name row))
                `(Reserved ,(trait-origin row))))))

(define Π0 (append kernel-pi0-entries trait-pi0-entries))

;; traits.rkt は 3 表の内部だけを検査する。kernel 行との衝突は、表を既存の
;; 環境へ足した後にだけ検査できる。
(define (check-unique-keys! who table message)
  (define keys (map car table))
  (unless (= (length keys) (length (remove-duplicates keys)))
    (error who message)))

(check-unique-keys! 'origins R0 "trait rows collide with kernel R0 entries")
(check-unique-keys! 'origins Γ0 "trait rows collide with kernel Γ0 entries")

;; Γ-pc⁰ へ足す global 候補。entry は (φ O cid sid pid hook) の 6 要素で、
;; origin と hook は同じ impl 行へ決定的に結び付く。
(define (trait-global-bindings)
  (for/list ([row (in-list impl-table)])
    (define trait-row (trait-row-by-name (impl-trait-name row)))
    (list (impl-name row)
          (list `(Implements ,(impl-target-type row)
                             ,(impl-trait-name row))
                `(Reserved ,(impl-oid row))
                (impl-name row)
                'root
                'default
                (list (trait-origin trait-row) (impl-oid row))))))

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
       [`(Reserved ,id)
        (define row (trait-row-by-name trait))
        (and row
             (eq? (trait-origin row) id)
             (equal? (lookup r0 id) `(trait ,trait)))]
       [_ #f])]
    [`(Implements ,_ ,_)
     (match origin
       [`(Reserved ,id)
        (define row (impl-row-by-oid id))
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
             (equal? (lookup r0 id) `(prim ,(impl-name row))))]
       [_ #f])]
    [`(RequiresBoth ,_ ,_)
     (match origin
       [`(Reserved ,id)
        (define row (intersect-row-by-oid id))
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
             (equal? (lookup r0 id) `(prim ,(intersect-name row))))]
       [_ #f])]
    [`(Presence ,_)
     (and (equal? origin '(Reserved o-merge))
          (eq? (lookup r0 'o-merge) 'merge))]
    [`(FieldType ,_ ,_) #f]
    [_ #f]))

;; RFN-002: 出現許可。常在性 witness は merge の局所検査のためだけに立つ値で
;; あり、初期成果物にも到達成果物にも現れてはならない。artifact に現れたら
;; merge の位置情報が失われ、φ の集約が merge をまたいでしまう。
(define (proof-occurrence-ok? proposition)
  (match proposition
    [`(Presence ,_) #f]
    [`(FieldType ,_ ,_) #f]
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

(define (origin-shape-valid? r0 value)
  (match (origin-data/proc value)
    [`(PrimVal (Reserved ,id) ,primitive)
     (equal? (lookup r0 id) `(prim ,primitive))]
    [`(Lam ,origin) (eq? origin 'User)]
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
                  (reserved-type-rep? type-form value))]
            [`(Derived (Reserved o-type-narrative) (Make ,made))
             (and (eq? (lookup r0 'o-type-narrative) 'typeNarrative)
                  (equal? made type-form))]
            [_ #f]))]
    [`(ProofRep ,origin ,proposition)
     (and (proof-issuer-ok? r0 origin proposition)
          (proof-occurrence-ok? proposition))]
    [`(RVal ,origin ,proposition ,payload)
     (refined-value-valid? r0 origin proposition payload)]
    [_ #f]))

(define origin-bearing-heads '(Lam PrimVal CurryVal TypeRep ProofRep RVal))

(define (origin-bearing-head? value)
  (and (pair? value)
       (memq (car value) origin-bearing-heads)))

(define (verify-origins/proc r0 core)
  (define (walk-list terms)
    (cond
      [(null? terms) 'ok]
      [else
       (define result (walk (car terms)))
       (if (eq? result 'ok)
           (walk-list (cdr terms))
           result)]))
  (define (walk term)
    (cond
      [(origin-bearing-head? term)
       (if (origin-shape-valid? r0 term)
           (walk-list term)
           `(forged ,term))]
      [(list? term) (walk-list term)]
      [else 'ok]))
  (walk core))

(define-metafunction G2m
  verify-origins : any c -> any
  [(verify-origins any_R0 c)
   ,(verify-origins/proc (term any_R0) (term c))])

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
  (or (initial-layer-violation core)
      (verify-origins/proc r0 core)))

(define-metafunction G2m
  verify-initial-origins : any c -> any
  [(verify-initial-origins any_R0 c)
   ,(verify-initial-origins/proc (term any_R0) (term c))])

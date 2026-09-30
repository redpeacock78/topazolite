#lang racket

(require racket/match
         redex/reduction-semantics
         "diagnostic.rkt"
         "data-env.rkt"
         "erase.rkt"
         "lang.rkt"
         "macro-expand.rkt"
         "span-core.rkt"
         "traits.rkt"
         "type-equiv.rkt"
         "type-shape.rkt"
         "validators.rkt"
         (submod "data-env.rkt" data-env-internal))

(provide Δ0
         Γ0
         Π0
         R0
         valid-origin?
         kernel-gamma0-entries
         current-trait-ledger
         call-with-trait-ledger
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

(define (data-type-occurrences type)
  (define found '())
  (define (walk term)
    (match term
      [`(Data ,T (,arguments ...))
       (set! found (cons (list T arguments) found))
       (for-each walk arguments)]
      [(? pair? terms) (for-each walk terms)]
      [_ (void)]))
  (walk type)
  (reverse found))

(define (type-param-occurrences type)
  (define found '())
  (define (walk term)
    (match term
      [`(Param ,X) (set! found (cons X found))]
      [(? pair? terms) (for-each walk terms)]
      [_ (void)]))
  (walk type)
  (reverse found))

(define (contains-param? type X)
  (match type
    [`(Param ,Y) (eq? X Y)]
    [(? pair? terms) (ormap (λ (term) (contains-param? term X)) terms)]
    [_ #f]))

(define (contains-component-data? type component)
  (match type
    [`(Data ,T (,arguments ...))
     (or (memq T component)
         (ormap (λ (argument)
                  (contains-component-data? argument component))
                arguments))]
    [(? pair? terms)
     (ormap (λ (term) (contains-component-data? term component)) terms)]
    [_ #f]))

(define (region-closed-in? type bound)
  (match type
    [`(ForallRegion (,parameters ...) ,body)
     (region-closed-in? body (append parameters bound))]
    [`(Borrowed ,payload ,region)
     (and (match region [`(RParam ,name) (memq name bound)] [_ #f])
          (region-closed-in? payload bound))]
    [`(BorrowedMut ,payload ,region)
     (and (match region [`(RParam ,name) (memq name bound)] [_ #f])
          (region-closed-in? payload bound))]
    [(? pair? terms) (andmap (λ (term) (region-closed-in? term bound)) terms)]
    [_ #t]))

(define (field-param-shape type)
  (match type
    [`(Param ,_) 'Int]
    [(? pair? terms) (map field-param-shape terms)]
    [_ type]))

(define (data-field-rows declarations)
  (append-map
   (λ (declaration)
     (append-map
      (λ (constructor)
        (for/list ([type (in-list (second constructor))]
                    [position (in-naturals)])
          (list (first declaration) (first constructor) position type)))
      (third declaration)))
   declarations))

(define (validate-data-decls! declarations index bail)
  (define (fail-data reason T [K #f] [position #f] [X #f])
    (bail reason 'data (list T K position X)))
  (define decl-table (data-index-decls index))
  (define fields (data-field-rows declarations))

  ;; 欄の参照を確かめる前に名前を集めるため、相互再帰を書ける。
  (let loop ([remaining declarations] [seen (seteq)])
    (unless (null? remaining)
      (define T (first (car remaining)))
      (when (set-member? seen T) (fail-data 'duplicate-data-type T))
      (when (memq T data-reserved-type-names) (fail-data 'reserved-data-type T))
      (loop (cdr remaining) (set-add seen T))))

  (for ([declaration (in-list declarations)])
    (define T (first declaration))
    (let loop ([parameters (second declaration)] [seen (seteq)])
      (unless (null? parameters)
        (define X (car parameters))
        (when (set-member? seen X) (fail-data 'duplicate-type-parameter T #f #f X))
        (loop (cdr parameters) (set-add seen X))))
    (when (null? (third declaration))
      (fail-data 'empty-data-type T)))

  (let loop ([remaining declarations] [seen (list->seteq builtin-data-constructors)])
    (unless (null? remaining)
      (define declaration (car remaining))
      (for ([constructor (in-list (third declaration))])
        (define K (first constructor))
        (when (set-member? seen K) (fail-data 'duplicate-constructor
                                              (first declaration) K))
        (set! seen (set-add seen K)))
      (loop (cdr remaining) seen)))

  (for ([field (in-list fields)])
    (match-define (list T K position type) field)
    (define parameters (second (hash-ref decl-table T)))
    (for ([X (in-list (type-param-occurrences type))])
      (unless (memq X parameters)
        (fail-data 'unknown-type-parameter T K position X)))
    (for ([occurrence (in-list (data-type-occurrences type))])
      (match-define (list referenced arguments) occurrence)
      (unless (hash-ref decl-table referenced #f)
        (fail-data 'unknown-data-type T K position)))
    (for ([occurrence (in-list (data-type-occurrences type))])
      (match-define (list referenced arguments) occurrence)
      (define target (hash-ref decl-table referenced))
      (unless (= (length arguments) (length (second target)))
        (fail-data 'data-arity-mismatch T K position)))
    (unless (region-closed-in? type '())
      (fail-data 'unbound-region-in-field T K position)))

  (define names (map first declarations))
  (define dependencies
    (for/hasheq ([declaration (in-list declarations)])
      (values
       (first declaration)
       (remove-duplicates
        (append-map (λ (field)
                      (map first (data-type-occurrences (fourth field))))
                    (filter (λ (field) (eq? (first field) (first declaration))) fields))
        eq?))))
  ;; ponytail: 対ごとの到達可能性は O(V(V+E))。宣言の集合が大きく、台帳構築に
  ;; 時間がかかるようになったら Tarjan に替える。
  (define (reachable-from start)
    (let loop ([todo (list start)] [seen '()])
      (cond
        [(null? todo) seen]
        [(memq (car todo) seen) (loop (cdr todo) seen)]
        [else
         (loop (append (hash-ref dependencies (car todo) '()) (cdr todo))
               (cons (car todo) seen))])))
  (define reachability
    (for/hasheq ([T (in-list names)])
      (values T (reachable-from T))))
  (define (component-of T)
    (filter (λ (other)
              (and (memq other (hash-ref reachability T))
                   (memq T (hash-ref reachability other))))
            names))
  (define components
    (for/hasheq ([T (in-list names)]) (values T (component-of T))))
  (define (cyclic-component? component)
    (or (> (length component) 1)
        (memq (car component) (hash-ref dependencies (car component) '()))))
  (define (first-internal-field component)
    (for/first ([field (in-list fields)]
                #:when (and (memq (first field) component)
                            (ormap (λ (occurrence)
                                     (memq (first occurrence) component))
                                   (data-type-occurrences (fourth field)))))
      field))

  (define checked-components '())
  (for ([T (in-list names)])
    (define component (hash-ref components T))
    (unless (member component checked-components equal?)
      (set! checked-components (cons component checked-components))
      (when (cyclic-component? component)
        (define arities
          (remove-duplicates
           (map (λ (member) (length (second (hash-ref decl-table member)))) component)))
        (when (> (length arities) 1)
          (match-define (list source K position _) (first-internal-field component))
          (fail-data 'irregular-recursion source K position))
        (for ([field (in-list fields)] #:when (memq (first field) component))
          (match-define (list source K position type) field)
          (define parameters (second (hash-ref decl-table source)))
          (for ([occurrence (in-list (data-type-occurrences type))]
                #:when (memq (first occurrence) component))
            (unless (equal? (second occurrence)
                            (map (λ (X) `(Param ,X)) parameters))
              (fail-data 'irregular-recursion source K position)))))))

  (define variance-cache (make-hasheq))
  (letrec
      ([component-variances
        (λ (T)
          (or (hash-ref variance-cache T #f)
              (let* ([component (hash-ref components T)]
                     [_ (for* ([field (in-list fields)]
                               #:when (memq (first field) component)
                               [occurrence (in-list
                                            (data-type-occurrences (fourth field)))]
                               #:unless (memq (first occurrence) component))
                          (component-variances (first occurrence)))]
                     [arity (length (second (hash-ref decl-table T)))]
                     [variances
                      (for/list ([position (in-range arity)])
                        (for/and ([member (in-list component)])
                          (define parameters (second (hash-ref decl-table member)))
                          (define X (list-ref parameters position))
                          (for/and ([field (in-list fields)]
                                    #:when (eq? (first field) member))
                            (parameter-positive? (fourth field) X component))))])
                (for ([member (in-list component)])
                  (hash-set! variance-cache member variances))
                variances)))]
       [parameter-positive?
        (λ (type X component)
          (match type
            [`(Param ,_) #t]
            [`(Owned ,inner) (parameter-positive? inner X component)]
            [`(Untrusted ,inner) (parameter-positive? inner X component)]
            [`(Refined ,inner ,_) (parameter-positive? inner X component)]
            [`(List ,inner) (parameter-positive? inner X component)]
            [`(Option ,inner) (parameter-positive? inner X component)]
            [`(Result ,left ,right)
             (and (parameter-positive? left X component)
                  (parameter-positive? right X component))]
            [`(Union ,left ,right)
             (and (parameter-positive? left X component)
                  (parameter-positive? right X component))]
            [`(Record ,row)
             (for/and ([field (in-list row)])
               (if (eq? (third field) 'imm)
                   (parameter-positive? (second field) X component)
                   (not (contains-param? (second field) X))))]
            [`(NFn (,parameters ...) ,return-type ,in-row ,out-row ,obligations ,origin)
             (and (not (or (contains-param? parameters X)
                           (contains-param? in-row X)
                           (contains-param? out-row X)
                           (contains-param? obligations X)
                           (contains-param? origin X)))
                  (parameter-positive? return-type X component))]
            [`(Data ,target (,arguments ...))
             (if (memq target component)
                 (andmap (λ (argument) (parameter-positive? argument X component))
                         arguments)
                 (let ([variances (component-variances target)])
                   (for/and ([argument (in-list arguments)]
                             [positive? (in-list variances)])
                     (or (not (contains-param? argument X))
                         (and positive?
                              (parameter-positive? argument X component))))))]
            [_ (not (contains-param? type X))]))]
       [recursive-positive?
        (λ (type component)
          (match type
            [`(Owned ,inner) (recursive-positive? inner component)]
            [`(Untrusted ,inner) (recursive-positive? inner component)]
            [`(Refined ,inner ,_) (recursive-positive? inner component)]
            [`(List ,inner) (recursive-positive? inner component)]
            [`(Option ,inner) (recursive-positive? inner component)]
            [`(Result ,left ,right)
             (and (recursive-positive? left component)
                  (recursive-positive? right component))]
            [`(Union ,left ,right)
             (and (recursive-positive? left component)
                  (recursive-positive? right component))]
            [`(Record ,row)
             (for/and ([field (in-list row)])
               (if (eq? (third field) 'imm)
                   (recursive-positive? (second field) component)
                   (not (contains-component-data? (second field) component))))]
            [`(NFn (,parameters ...) ,return-type ,in-row ,out-row ,obligations ,origin)
             (and (not (or (contains-component-data? parameters component)
                           (contains-component-data? in-row component)
                           (contains-component-data? out-row component)
                           (contains-component-data? obligations component)
                           (contains-component-data? origin component)))
                  (recursive-positive? return-type component))]
            [`(Data ,target (,arguments ...))
             (if (memq target component)
                 #t
                 (let ([variances (component-variances target)])
                   (for/and ([argument (in-list arguments)]
                             [positive? (in-list variances)])
                     (or (not (contains-component-data? argument component))
                         (and positive?
                              (recursive-positive? argument component))))))]
            [`(Borrowed ,payload ,_) (not (contains-component-data? payload component))]
            [`(BorrowedMut ,payload ,_) (not (contains-component-data? payload component))]
            [`(RawPtr ,payload ,_ ,_ ,_ ,_ ,_)
             (not (contains-component-data? payload component))]
            [`(ForallRegion (,_ ...) ,body)
             (not (contains-component-data? body component))]
            [_ (not (contains-component-data? type component))]))])
    (for ([field (in-list fields)])
      (match-define (list T K position type) field)
      (unless (recursive-positive? type (hash-ref components T))
        (fail-data 'non-positive-recursion T K position)))

  (parameterize ([caching-enabled? #f]
                 [data-index-parameter index])
    (for ([field (in-list fields)])
      (match-define (list T K position type) field)
      (define shape-type (field-param-shape type))
      (unless (and (redex-match? G2m τ shape-type)
                   (type-shape-ok? shape-type))
        (fail-data 'ill-formed-field-type T K position))))))

(struct trait-ledger (env r0 gamma0 global-bindings data) #:transparent)

(define (make-trait-ledger env #:data [data-declarations '()] #:fail fail)
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
    (define data-index (build-data-index data-declarations))
    (validate-data-decls! data-declarations data-index bail)
    (trait-ledger env r0 gamma0 (trait-global-bindings/env env) data-index)))

(define canonical-trait-ledger
  (make-trait-ledger canonical-trait-env
                     #:fail (λ (reason kind key)
                              (error 'origins "~a: ~s ~s" reason kind key))))

;; spec §5.2。Redex の metafunction と judgment form は項だけを鍵にキャッシュし、
;; hit のときは本体を走らせない。台帳を差し替える入口を call-with-trait-ledger の
;; 1 つに限り、custom の台帳の下ではキャッシュを止める。parameter 自体は provide しない。
(define ledger-parameter (make-parameter canonical-trait-ledger))

;; custom の台帳をキャッシュが有効なまま読むのは、call-with の thunk が
;; caching-enabled? を戻した証拠である。キャッシュに当たった節はここを通らないので、
;; この検査は防御であり保証ではない（spec §5.2 の前提）。
(define (current-trait-ledger)
  (define ledger (ledger-parameter))
  (unless (or (eq? ledger canonical-trait-ledger) (not (caching-enabled?)))
    (error 'current-trait-ledger "custom ledger read with Redex caching enabled"))
  ledger)

;; caching-enabled? と ledger-parameter を同じ parameterize で束縛する。
;; canonical の台帳は外側のキャッシュ設定を保ち、custom の台帳は必ず止める。
(define (call-with-trait-ledger ledger thunk)
  (parameterize ([caching-enabled? (and (caching-enabled?)
                                        (eq? ledger canonical-trait-ledger))]
                 [ledger-parameter ledger]
                 [data-index-parameter (trait-ledger-data ledger)])
    (thunk)))

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

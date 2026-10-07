#lang racket

(require racket/match
         racket/runtime-path
         racket/string
         redex/reduction-semantics
         "elaborate.rkt"
         "erase.rkt"
         "lang.rkt"
         "machine.rkt"
         "rows.rkt"
         "type-equiv.rkt"
         "typing.rkt"
         "validators.rkt")

(provide G1gen
         G2gen
         (struct-out bounds)
         (struct-out execution)
         (struct-out search-counts)
         (struct-out owned-leaf-case)
         read-bounds
         call-with-search-seed
         make-search-counts
         prepare-elaborable
         note-accepted!
         elaboration-result
         bounded-trace
         bounded-trace-g2
         config-core
         config-heap
         config-states
         config-tokens
         config-events
         runtime-row
         row-subset?
         pick-one
         refine-propositions
         random-validator-row
         random-payload-for
         random-refine-row
         random-branch-rows
         random-obligation-subset
         random-variance-type
         narrow-variance-type
         widen-variance-type
         permute-variance-type
         generate-union-core
         generate-owned-leaf-case)

(struct owned-leaf-case (kind action initial callables expected) #:transparent)

;; Every generated form is a closed UCore term.  Separate nonterminals make the
;; seven searches hit the rules they are intended to check instead of spending
;; the discard budget on arbitrary, overwhelmingly ill-typed syntax.
(define-extended-language G1gen UCore
  (gn ::= -2 -1 0 1 2 7)
  (g-bool ::= (Construct true (Types))
              (Construct false (Types)))
  (gt ::= (TypeMake Int)
          (TypeMake (Spec List Int))
          (TypeMake (Spec Option Bool))
          (TypeMake (Spec Result Int String))
          (LetType Box (TypeMake List)
                   (TypeMake (Spec Box Int))))
  (g-boundary ::=
              (Apply (Fn () Int () (Return gn)))
              (Apply (Fn () Int () (NarrativeExpr (Return gn))))
              (Apply (Fn ((flag Bool)) Int ()
                         (Eliminate flag
                          ((true () -> (Return gn))
                           (false () -> gn))))
                     g-bool))
  (g-productive ::=
                (Recur nats ((counter Int)) Unit ((Yield Int))
                       (Yield counter
                              (Apply nats (Apply add counter 1)))
                       (Apply nats gn)))
  (g-own ::=
         (Let item (Apply acquire gn) unit)
         (Let item (Apply acquire gn) (Move item))
         (Let item (Apply acquire gn) (Drop item))
         (Let item (Apply acquire gn)
              (Let ignored (Drop item) (Drop item)))
         (Let item (Apply acquire gn)
              (Let saved (Move item) (Move item)))
         (Apply (Fn () Int (Own)
                    (Let item (Apply acquire gn) (Return gn)))))
  (g-own-g5 ::= g-own
         ;; Owned を 1 件捕捉する closure を inline で呼ぶ。
         (Let item (Apply acquire gn)
              (Apply (Fn () Unit (Own) (Drop item))))
         ;; 捕捉する closure を place へ束ね、Move 経由で 1 回呼ぶ。
         (Let item (Apply acquire gn)
              (Let f (Fn () Unit (Own) (Drop item))
                   (Apply (Move f))))
         ;; 捕捉する closure を 2 回 Move する。2 回目が R-MoveError で止まる。
         (Let item (Apply acquire gn)
              (Let f (Fn () Unit (Own) (Drop item))
                   (Let ignored (Apply (Move f))
                        (Apply (Move f)))))
         ;; Owned を固定引数に取る Curry を Move 経由で呼ぶ。
         (Let item (Apply acquire gn)
              (Let g (Fn ((q (Owned Res))) Unit (Own) (Drop q))
                   (Let h (Curry g (Move item))
                        (Apply (Move h))))))
  (g-type ::= gt)
  (ga-list ::= (Construct nil (Types Int))
               (Construct cons (Types Int) gn ga-list))
  (g-analysis ::=
              gn
              (Apply add gn gn)
              (Yield gn unit)
              (Recur constant () Int () gn gn)
              (Recur loop ((items (List Int))) Int ()
                     (Eliminate items
                      ((nil () -> 0)
                       (cons (head tail) -> (Apply loop tail))))
                     (Apply loop ga-list))
              g-productive)
  (g ::= gn
         (Apply add gn gn)
         (Apply sub gn gn)
         (Apply mul gn gn)
         (Apply lt gn gn)
         (Apply le gn gn)
         (Apply eq gn gn)
         (Let value gn value)
         (Apply (Fn ((argument Int)) Int () argument) gn)
         (Apply (Curry add gn) gn)
         g-bool
         ga-list
         unit
         (Drop (Apply acquire gn))
         (Yield gn unit)
         (Suspend unit)
         (Recur constant () Int () gn gn)
         (Recur loop ((items (List Int))) Int ()
                (Eliminate items
                 ((nil () -> 0)
                  (cons (head tail) -> (Apply loop tail))))
                (Apply loop ga-list))
         g-boundary
         g-own
         g-type))

;; Record generation is deliberately finite by construction: every row has at
;; most three fields, and nested record types/terms have at most two Rec/Record
;; layers.  The general Redex size bound still controls surrounding syntax.
(define-extended-language G2gen G1gen
  (gr-leaf ::= ()
               ((a Int imm))
               ((a Int imm) (extra Unit mut))
               ((a Int imm) (extra Unit mut) (flag Bool imm)))
  (gr-nested ::= gr-leaf
                 ((nested (Record gr-leaf) imm))
                 ((nested (Record gr-leaf) imm) (a Int mut)))
  (g-record-type ::= (Record gr-leaf)
                     (Record gr-nested))

  (g-rec-leaf ::= (Rec ((a imm gn)))
                  (Rec ((a imm gn) (extra mut unit)))
                  (Rec ((a imm gn) (extra mut unit) (flag imm g-bool))))
  (g-rec ::= g-rec-leaf
             (Rec ((nested imm g-rec-leaf)))
             (Rec ((nested imm g-rec-leaf) (a mut gn))))
  (g-record ::= g-rec
                (Proj g-rec-leaf a)
                (Proj (Let (record const
                                   (Record ((a Int imm) (opt-field Int imm opt))))
                           (Rec ((a imm gn) (opt-field imm gn)))
                           record)
                      opt-field)
                (Proj (Let (record const
                                   (Record ((a Int imm) (opt-field Int imm opt))))
                           (Rec ((a imm gn)))
                           record)
                      opt-field)
                (Proj (Rec ((a imm gn) (extra mut unit))) extra)
                (Proj (Rec ((nested imm g-rec-leaf))) nested)
                (Let (record let (Record ((a Int imm))))
                     (Rec ((a imm gn) (extra mut unit)))
                     (Proj record extra)))

  ;; Dedicated sources keep the G2a laws reachable without arbitrary invalid
  ;; record syntax dominating the discard budget.
  (g-row-const ::=
               (Let (record const (Record ((a Int imm))))
                    (Rec ((a imm gn) (extra mut unit)))
                    (Proj record a)))
  (g-row-let ::=
             (Let (record let (Record ((a Int imm))))
                  (Rec ((a imm gn) (extra mut unit)))
                  (Proj record extra)))
  (g-row-merge ::=
               (Eliminate (Construct Bool true)
                          ((true () ->
                                 (Rec ((a imm gn) (extra imm unit))))
                           (false () ->
                                  (Rec ((a imm gn) (flag imm unit)))))))
  (g-row-mut ::= (Rec ((a mut gn))))

  (g-boundary ::= ....
                (Apply
                 (Fn () Int ()
                     (NarrativeExpr
                      (Proj (Rec ((result imm (Return gn)))) result)))))
  (g-own ::= ....
           (Let record g-rec-leaf
                (Let item (Apply acquire gn) (Drop item))))
  (g-type ::= ....
            (Let (record const (Record ((a Int imm))))
                 (Rec ((a imm gn)))
                 gt)
            (Let (record const
                         (Record
                          ((nested (Record ((a Int imm))) imm))))
                 (Rec ((nested imm (Rec ((a imm gn))))))
                 gt))
  (g-analysis ::= ....
                (Recur loop ((items (List Int))) Int ()
                       (Eliminate items
                        ((nil () -> 0)
                         (cons (head tail) ->
                               (Let (next const Int)
                                    (Proj
                                     (Rec ((value imm (Apply loop tail))))
                                     value)
                                    next))))
                       (Apply loop ga-list)))
  (g ::= ....
         g-record
         g-row-let
         (Let (value let) gn value)))

(struct bounds (attempts term-depth fuel observation-depth discard-limit seed)
  #:transparent)
(struct execution (configs outcome) #:transparent)
(struct search-counts (accepted discarded limit) #:mutable #:transparent)

(define-runtime-path readme-path "README.md")

(define (read-setting settings key)
  (hash-ref settings key
            (lambda ()
              (error 'read-bounds "README setting is missing: ~a" key))))

(define (read-bounds)
  (define settings
    (call-with-input-file readme-path
      (lambda (input)
        (for/fold ([found (hash)])
                  ([line (in-lines input)])
          (match (regexp-match #px"^\\|\\s*([^|]+?)\\s*\\|\\s*([0-9]+)\\s*\\|$"
                               line)
            [(list _ key value)
             (hash-set found (string-trim key) (string->number value))]
            [_ found])))))
  (bounds (read-setting settings "redex-check 試行数")
          (read-setting settings "生成項の深さ上限")
          (read-setting settings "評価 fuel")
          (read-setting settings "観測深度上限")
          (read-setting settings "discard 上限")
          (read-setting settings "乱数 seed")))

(define (call-with-search-seed limits thunk)
  (define generator (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator generator])
    (random-seed (bounds-seed limits)))
  (parameterize ([current-pseudo-random-generator generator]
                 [redex-pseudo-random-generator generator])
    (thunk)))

;; Union は G2gen の表層文法には無いため、Core の property から直接使う。
(define union-generation-types
  (list '(Union Int String)
        '(Union (Union Int Bool) String)
        '(Union (Record ((a Int imm))) (Union Bool String))))

(define (generate-union-core #:embedded-count [embedded-count #f]
                             #:literal-count [literal-count #f])
  (define (choose choices)
    (list-ref choices (random (length choices))))
  (define (increment! counter)
    (when counter (set-box! counter (add1 (unbox counter)))))
  (define (embedded-int-core depth)
    (match (elaboration-result (generate-term G2gen g depth))
      [(list core 'Int '() '()) core]
      [_ #f]))
  (define (int-payload)
    (or (let ([core (embedded-int-core 3)])
          (and core (begin (increment! embedded-count) core)))
        (begin
          (increment! literal-count)
          (random 100000))))
  (define (payload-for member)
    (match member
      ['Int (int-payload)]
      ['String (format "union-~a" (random 100000))]
      ['Bool `(Construct Bool ,(choose '(true false)))]
      [`(Record ((a Int imm))) `(Rec ((a imm ,(random 100000))))]))
  (define (inject type member)
    (define normalized-type (normalize-type type))
    (define normalized-member (normalize-type member))
    `(UnionInject ,normalized-type ,normalized-member
                  ,(payload-for normalized-member)))
  (define (elimination-arms type)
    (define members (union-members (normalize-type type)))
    (define arms
      (for/list ([member (in-list members)] [index (in-naturals)])
        (define binder (string->symbol (format "union-payload-~a" index)))
        (match member
          ['Int `(Int ,binder -> ,binder)]
          ['String `(String ,binder -> (Let (ignored const String) ,binder 0))]
          ['Bool `(Bool ,binder ->
                        (Eliminate ,binder
                         ((true () -> 1) (false () -> 0))))]
          [`(Record ((a Int imm)))
           `(,member ,binder -> (Proj ,binder a))])))
    (if (zero? (random 2)) arms (reverse arms)))
  (case (random 3)
    [(0 1)
     (define type (normalize-type (choose union-generation-types)))
     (define member (choose (union-members type)))
     (define value (inject type member))
     (define arms (elimination-arms type))
     (if (zero? (random 2))
         `(UnionEliminate ,value ,arms)
         `(Let (union-value const ,type) ,value
               (UnionEliminate union-value ,arms)))]
    [else
     (define left-type (normalize-type '(Union Int Bool)))
     (define right-type (normalize-type '(Union String Bool)))
     (define result-type
       (normalize-type '(Union (Union Int Bool) (Union String Bool))))
     (define boolean-arms
       `((true () -> ,(inject left-type 'Int))
         (false () -> ,(inject right-type 'String))))
     (define selected-arms
       (if (zero? (random 2)) boolean-arms (reverse boolean-arms)))
     `(Let (union-value const ,result-type)
           (Eliminate (Construct Bool ,(choose '(true false)))
                      ,selected-arms)
           (UnionEliminate union-value
                           ,(elimination-arms result-type)))]))

;; P2m2c1c2 Task 6。通常の生成文法は変えず、資源を内側に持つ値を
;; 有効な runtime config として作り、transfer encoding を通る Core を個別に組む。
;; 直接 Owned 欄の Rec リテラルは型付けが拒否するため、Record の値だけは
;; token と宣言型を持つ初期 heap から資源型仮引数へ渡す。
(define option-owned-leaf-type '(Option (Owned Res)))
(define record-owned-leaf-type
  '(Record ((n Int imm) (owned (Owned Res) imm))))
(define union-owned-leaf-type
  (normalize-type `(Union Int ,option-owned-leaf-type)))

(define (generate-owned-leaf-case kind action)
  (unless (memq kind '(lambda-option lambda-record union-eliminate eliminate
                       return-handler))
    (raise-argument-error 'generate-owned-leaf-case
                          "owned-leaf-case-kind" kind))
  (unless (memq action '(move drop unused))
    (raise-argument-error 'generate-owned-leaf-case
                          "owned-leaf-case-action" action))
  (define token-number (random 100000))
  (define token `(tok ,token-number))
  (define payload `(resource ,token-number))
  (define option-value
    `(Construct ,option-owned-leaf-type some
                (OwnedLeaf ,token ,payload)))
  (define-values (resource-type runtime-value)
    (case kind
      [(lambda-record)
       (values record-owned-leaf-type
               `(Rec ((n imm ,(random 100000))
                     (owned imm (OwnedLeaf ,token ,payload)))))]
      [(union-eliminate)
       (values union-owned-leaf-type
               `(UnionVal ,union-owned-leaf-type ,option-owned-leaf-type
                          ,option-value))]
      [else (values option-owned-leaf-type option-value)]))
  (define (encoded-binding name type raw body)
    `(Scope () (Let (,name let ,type) ,raw ,body)))
  (define (action-body name)
    (case action
      [(move) `(Move ,name)]
      [(drop) `(Drop (Move ,name))]
      [else 'unit]))
  (define (result-for-action type)
    (if (eq? action 'move) type 'Unit))
  (define (producer-lambda)
    `(Lam User nested-owned-producer (raw-producer)
       (Handle (Return producer-boundary ,resource-type)
               (producer-return -> producer-return)
               ,(encoded-binding 'producer-place resource-type 'raw-producer
                                 '(Move producer-place)))))
  (define (lambda-consumer)
    (define result-type (result-for-action resource-type))
    (define body (action-body 'consumer-place))
    `(Apply
      (Lam User nested-owned-consumer (raw-consumer)
        (Handle (Return consumer-boundary ,result-type)
                (consumer-return -> consumer-return)
                ,(encoded-binding 'consumer-place resource-type
                                  'raw-consumer body)))
      (Move produced)))
  (define (option-eliminate)
    (define some-body
      (encoded-binding 'option-leaf '(Owned Res) 'raw-option
                       (action-body 'option-leaf)))
    (define none-body
      (if (eq? action 'move) '(resource 0) 'unit))
    (define elimination
      `(Eliminate
        (Move produced)
        ((some (raw-option) -> ,some-body)
         (none () -> ,none-body))))
    (if (eq? action 'move) `(Drop ,elimination) elimination))
  (define (union-eliminate)
    (define option-body
      (encoded-binding 'union-leaf option-owned-leaf-type 'raw-union
                       (action-body 'union-leaf)))
    (define int-body
      (if (eq? action 'move)
          `(Construct ,option-owned-leaf-type none)
          'unit))
    `(UnionEliminate
      (Move produced)
      ((Int ignored-int -> ,int-body)
       (,option-owned-leaf-type raw-union -> ,option-body))))
  (define (return-handler)
    (define body
      (case action
        [(move) '(Move return-place)]
        [(drop)
         `(Let (ignored-drop let Unit)
               (Drop (Move return-place))
               (Construct ,option-owned-leaf-type none))]
        [else `(Construct ,option-owned-leaf-type none)]))
    `(Handle (Return nested-return-boundary ,option-owned-leaf-type)
             (raw-return ->
               ,(encoded-binding 'return-place option-owned-leaf-type
                                 'raw-return body))
             (Perform (Return nested-return-boundary ,option-owned-leaf-type)
                      (Move produced))))
  (define consumer
    (case kind
      [(lambda-option lambda-record) (lambda-consumer)]
      [(union-eliminate) (union-eliminate)]
      [(eliminate) (option-eliminate)]
      [else (return-handler)]))
  (define expected
    (case kind
      [(lambda-option lambda-record)
       (result-for-action resource-type)]
      [(union-eliminate)
       (result-for-action option-owned-leaf-type)]
      [(eliminate) 'Unit]
      [else option-owned-leaf-type]))
  (define source-signature
    `(NFn (,resource-type) ,resource-type () (Own) () User))
  (define consumer-signature
    (and (memq kind '(lambda-option lambda-record))
         `(NFn (,resource-type) ,expected () (Own) () User)))
  (define callables
    (if consumer-signature
        `((nested-owned-producer ,source-signature)
          (nested-owned-consumer ,consumer-signature))
        `((nested-owned-producer ,source-signature))))
  (define core
    `(Scope (0)
       (Let (produced let ,resource-type)
            (Apply ,(producer-lambda) (Move 0))
            ,consumer)))
  (define initial
    `(cfg ,core
          ((0 ,runtime-value (declared ,resource-type)))
          ((0 Available))
          ((,token Available))
          ()))
  (owned-leaf-case kind action initial callables expected))

(define (make-search-counts limits)
  (search-counts 0 0 (bounds-discard-limit limits)))

(define elaboration-cache (make-hash))
(define trace-cache (make-hash))

(define (cached-ref! table key compute)
  (if (caching-enabled?)
      (hash-ref! table key compute)
      (compute)))

(define (elaboration-result source)
  (match (cached-ref! elaboration-cache source (lambda () (elab source)))
    [(list core type row callables)
     (list (erase-core core) type row callables)]
    [other other]))

(define (prepare-elaborable counts source)
  (match (elaboration-result source)
    [(list _ _ _ _) source]
    [_
     (set-search-counts-discarded!
      counts (add1 (search-counts-discarded counts)))
     (when (> (search-counts-discarded counts)
              (search-counts-limit counts))
       (error 'redex-check "elaboration discard limit exceeded"))
     ;; This is deliberately outside G1gen's generated nonterminals, so Redex
     ;; treats it as a generation failure rather than a passing property case.
     '(discarded-elaboration)]))

(define (note-accepted! counts)
  (set-search-counts-accepted!
   counts (add1 (search-counts-accepted counts))))

(define (config-core configuration)
  (match-define `(cfg ,core ,_ ,_ ,_tokens ,_) configuration)
  core)

(define (config-heap configuration)
  (match-define `(cfg ,_ ,heap ,_ ,_tokens ,_) configuration)
  heap)

(define (config-states configuration)
  (match-define `(cfg ,_ ,_ ,states ,_tokens ,_) configuration)
  states)

(define (config-tokens configuration)
  (match-define `(cfg ,_ ,_ ,_ ,tokens ,_) configuration)
  tokens)

(define (config-events configuration)
  (match-define `(cfg ,_ ,_ ,_ ,_tokens ,events) configuration)
  events)

(define (runtime-row configuration callables type)
  ;; Runtime heap entries may contain callable values whose root type is not
  ;; Res.  Reconstruct the same Ξ and configuration-only typing scope used by
  ;; config-ok? before checking the row.
  (with-config-typing
   (lambda ()
     (define places
       (derive-places (config-heap configuration)
                      callables
                      #:declared (config-declared-types configuration)))
     (and places
          (core-check-row (config-core configuration)
                          places
                          callables
                          type
                          #:declared (config-declared-types configuration))))))

(define (row-subset? left right)
  (term (row-⊆ ,left ,right)))

(define (bounded-trace/using who relation initial fuel)
  (cached-ref!
   trace-cache
   (list who initial fuel)
   (lambda ()
     (let loop ([current initial]
                [remaining fuel]
                [reversed-configs '()])
       (define configs (cons current reversed-configs))
       (define successors
         (remove-duplicates
          (apply-reduction-relation relation current)
          equal?))
       (cond
         [(null? successors)
          (execution (reverse configs) 'terminal)]
         [(zero? remaining)
          (execution (reverse configs) 'timeout)]
         [(null? (cdr successors))
          (loop (car successors) (sub1 remaining) configs)]
         [else
          (error who
                 "nondeterministic reduction from ~e to ~e"
                 current
                 successors)])))))

(define (bounded-trace initial fuel)
  (bounded-trace/using 'bounded-trace -->g1 initial fuel))

(define (bounded-trace-g2 initial fuel)
  (bounded-trace/using 'bounded-trace-g2 -->g2 initial fuel))

;; ---------------------------------------------------------------------------
;; G2c: variance 型生成器。compat? の性質検査（properties-variance-test.rkt）
;; 専用で、項は生成しない。narrow は compat?(narrow(t), t) を、widen は
;; compat?(t, widen(t)) を、permute は type-equiv?(t, permute(t)) を構成的に
;; 保つ変換である。
;; ---------------------------------------------------------------------------

(define variance-leaves '(Int Bool Unit String))
(define variance-effect-pool
  '(Own Mutation Suspend (Yield Int) (Yield (Record ((a Int imm) (b Bool imm))))))
(define variance-obligation-pool '(ValidNarrativeTrait TypeNarrativeCap))
(define variance-extra-labels '(x y z))

(define (pick-one items)
  (list-ref items (random (length items))))

;; pool の並び順を保った部分列を返す。E/Q が常に pool 順の部分列になるため、
;; 相互包含が成り立つ二つの E/Q は同一リストになり、性質 4 の反対称性検査が
;; type-equiv? の equal? 比較（Q は順序敏感）と衝突しない。
(define (random-subset items)
  (for/list ([item (in-list items)] #:when (zero? (random 2))) item))

(define (append-missing row pool)
  (append row
          (for/list ([item (in-list pool)]
                     #:unless (member item row))
            item)))

(define (map-imm-fields row transform)
  (for/list ([field (in-list row)])
    (if (eq? (third field) 'imm)
        (field-with-type field (transform (second field)))
        field)))

(define (random-variance-row depth)
  (for/list ([label (in-list (take '(a b c) (add1 (random 3))))])
    (list label (random-variance-type depth) (pick-one '(imm mut)))))

(define (random-variance-type depth)
  (cond
    [(or (zero? depth) (zero? (random 3))) (pick-one variance-leaves)]
    [(zero? (random 2)) `(Record ,(random-variance-row (sub1 depth)))]
    [else `(NFn (,(random-variance-type (sub1 depth)))
                ,(random-variance-type (sub1 depth))
                ,(random-subset variance-effect-pool)
                ,(random-subset variance-effect-pool)
                ,(random-subset variance-obligation-pool)
                User)]))

;; 部分型方向: Record は imm field の narrow か余剰 field 追加、NFn は
;; 引数 widen・返り値 narrow・E/Q の部分列化。mut field は触らない。
(define (narrow-variance-type type)
  (cond
    [(zero? (random 4)) 'Never]
    [else
     (match type
       [`(Record ,row)
        (define fresh-labels
          (for/list ([label (in-list variance-extra-labels)]
                     #:unless (assq label row))
            label))
        (if (and (pair? fresh-labels) (zero? (random 2)))
            `(Record ,(append row (list (list (first fresh-labels) 'Int 'imm))))
            `(Record ,(map-imm-fields row narrow-variance-type)))]
       [`(NFn ,parameters ,return-type ,latent-in ,row ,obligations ,origin)
        `(NFn ,(map widen-variance-type parameters)
              ,(narrow-variance-type return-type)
              ,latent-in
              ,(random-subset row)
              ,(random-subset obligations)
              ,origin)]
       [_ type])]))

;; 上位型方向: Never は任意型へ、Record は先頭 field 削除か imm field の
;; widen、NFn は引数 narrow・返り値 widen・E/Q へ pool の残りを追加。
(define (widen-variance-type type)
  (match type
    ['Never (random-variance-type 1)]
    [`(Record ,row)
     (if (and (pair? row) (zero? (random 2)))
         `(Record ,(rest row))
         `(Record ,(map-imm-fields row widen-variance-type)))]
    [`(NFn ,parameters ,return-type ,latent-in ,row ,obligations ,origin)
     `(NFn ,(map narrow-variance-type parameters)
           ,(widen-variance-type return-type)
           ,latent-in
           ,(append-missing row variance-effect-pool)
           ,(append-missing obligations variance-obligation-pool)
           ,origin)]
    [_ type]))

(define (permute-effect-label label)
  (match label
    [`(Yield ,payload) `(Yield ,(permute-variance-type payload))]
    [`(Return ,boundary ,payload)
     `(Return ,boundary ,(permute-variance-type payload))]
    [_ label]))

;; type-equiv? を保つ並び替え。field row と Effect row は順序独立なので
;; reverse する。Q は type-equiv? が equal? で比較するため順序を保存する。
(define (permute-variance-type type)
  (match type
    [`(Record ,row)
     `(Record ,(reverse
                (for/list ([field (in-list row)])
                  (field-with-type field
                                   (permute-variance-type (second field))))))]
    [`(NFn ,parameters ,return-type ,latent-in ,row ,obligations ,origin)
     `(NFn ,(map permute-variance-type parameters)
           ,(permute-variance-type return-type)
           ,(reverse (map permute-effect-label latent-in))
           ,(reverse (map permute-effect-label row))
           ,obligations
           ,origin)]
    [_ type]))

;; ---------------------------------------------------------------------------
;; G2d: refinement 生成器。properties-refine-test.rkt 専用で、項は生成しない。
;; ペイロードは判定表の check を通る値と落ちる値の両方を含む。片方だけだと
;; 性質 1 の ng 側または ok 側が空洞になる。
;; ---------------------------------------------------------------------------

(define refine-propositions
  (for/list ([row (in-list validator-table)])
    (validator-proposition row)))

(define refine-labels '(a b c d))
(define refine-field-types '(Int Bool String))
(define merge-field-types
  (append refine-field-types
          (list (normalize-type '(Union Int Bool))
                (normalize-type '(Union String Bool)))))

(define (random-validator-row)
  (pick-one validator-table))

(define (random-payload-for row)
  (case (validator-payload-type row)
    [(Int) (pick-one '(-1 0 1 80 8080 65535 65536))]
    [(String) (pick-one '("" " " "a" "localhost"))]
    [else 'unit]))

(define (random-refine-row)
  (for/list ([label (in-list refine-labels)]
             #:when (zero? (random 2)))
    (list label (pick-one refine-field-types) (pick-one '(imm mut)))))

(define (random-branch-rows)
  (for/list ([_i (in-range (add1 (random 3)))])
    (for/list ([field (in-list (random-refine-row))])
      (list (first field)
            (pick-one merge-field-types)
            (third field)))))

(define (random-obligation-subset)
  (for/list ([proposition (in-list refine-propositions)]
             #:when (zero? (random 2)))
    proposition))

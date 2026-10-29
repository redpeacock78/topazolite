#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "borrow.rkt"
         "backend-matrix.rkt"
         "compat.rkt"
         "data-env.rkt"
         "diagnostic.rkt"
         "erase.rkt"
         "lang.rkt"
         "macro-expand.rkt"
         "machine.rkt"
         "origins.rkt"
         "ownership.rkt"
         "policy.rkt"
         "ptr-static.rkt"
         "region.rkt"
         "region-param.rkt"
         "rows.rkt"
         "resource-type.rkt"
         "schema.rkt"
         "search.rkt"
         "span-core.rkt"
         "type-equiv.rkt"
         "type-shape.rkt"
         "validators.rkt")

(provide core-type-of
         core-type-of/normal
         core-type-of/diagnostic
         core-check
         core-check-row
         type-of/raw
         type-of/raw*+normal
         type-of/raw*+borrows
         type-of/raw*+ptr
         (struct-out region-typed)
         borrow-bearing-core?
         core-type-of/regions
         region-execution-core
         annotate-mut-binding-types
         annotate-callable-contexts
         callable-signature
         execution-core
         typing-visited-points
         config-ok?
         elimination-annotations-well-formed?
         config-view-compatible?
         config-runtime-borrow-types
         recover-runtime-borrow-types
         captured-mut-slots
         with-config-typing
         ownleaf-permitted
         unsafe-permitted
         raw-obligations
         raw-load-obligation-ids
         raw-store-obligation-ids
         ptr-offset-obligation-ids
         raw-store-target-check
         pointer-parts
         check-raw-obligations!
         infer-address-of
         infer-ptr-offset
         infer-raw-load
         infer-raw-store
         infer-from-raw-ptr
         from-raw-ptr-obligation-ids
         from-raw-ptr-result-type
         infer-unsafe
         ownleaf-root?
         require-ownleaf-root
         config-runtime-leaf?
         control-leaf-positions-ok?
         derive-places
         config-declared-types
         tag-upper-bound
         tag-types-upper-bound
         branch-types-upper-bound
         (struct-out tag-bound-failure)
         merge-field
         presence-binding-name
         field-type-binding-name
         merge-record-types/impl
         merge-record-types
         owned-lift-compatible?
         check-merge-return
         curry-payload-erase
         merge-witnesses-dischargeable?
         lifetime-unify-context
         unify-borrow-lifetimes
         with-lifetime-unify
         merge-position
         merge-alpha-sources
         lifetime-counter
         alpha-table
         lifetime-owner-region
         borrow-payload-borrow-free?
         payload-borrows-traceable?
         register-owner
         lifetime-collector
         emit-constraint!
         collected-constraints
         with-lifetime-collector
         (struct-out region-arg-request)
         region-arg-collector
         emit-region-arg-request!
         collected-region-args
         check-region-args
         (struct-out callable-summary)
         (struct-out forwarding-summary)
         (struct-out deferred-leaf-exit)
         leaf-exit-sites
         current-leaf-exit-sites
         current-leaf-exit-capability-reader
         current-local-exit-window-probe
         leaf-exit-destinations
         site-position-matches?
         normalize-leaf-exits
         callable-summary-leaf-exits
         classify-leaf-exits
         leaf-exit-local-safe?
         signature-forwarding-summary
         formal-leaf-info
         instantiate-capability-path
         lookup-binding
         make-recur-frame
         recur-check-roots
         collected-callable-summaries
         collect-use-regions!
         typing-inference
         typing-solve
         sigma-ref
         subst-type-regions
         forall-region-free?
         alpha-set
         capability-source
         contains-lifetime-var?
         materialize-fail-result
         core-type-of/materialized
         unwrap-forall-region
         function-body-environment
         check-owned-encoding
         ;; P1c2b。環境 entry の 3 要素化を回帰で固定するために出す。
         valid-environment?
         binding-mode-of
         ;; lookup は origins.rkt が、extend は classify.rkt と
         ;; properties-lowering-test.rkt が同じ綴りを持つ。衝突を避けるため
         ;; この 2 つは environment- を冠した名前で出す。
         (rename-out [extend environment-extend]
                     [lookup environment-lookup]))

;; 段 1 の試験専用。既定は何もしない。
;; 本体の走査へ観測を混ぜないため、probe の呼出しは infer と check-as の入口、
;; および Discharge の層を降りる loop の 3 箇所に限る。
(define typing-point-probe (make-parameter void))

;; Return payload の寿命と実型を対応する Handle へ返す。関数本体へは引き継がない。
(define return-handler-regions (make-parameter '()))

;; 分解の scrutinee から派生した借用 α を同じ型付け走査内で追う。
(define scrutinee-child-alphas (make-parameter #f))

;; 分解 binder の α は check/infer の再走査で共有する。
(define branch-binder-alphas (make-parameter #f))
;; 仮引数を親に持つ binder は、materialize 時に %parent を保つ。
(define branch-binder-parent-keys (make-parameter #f))
;; binder source ごとの親と、出口を積む callable を保持する。
(define branch-binder-event-info (make-parameter #f))
;; 合流・再借用後も binder 起点の出口を追えるよう、派生 α の親を保持する。
(define branch-binder-alpha-sources (make-parameter #f))

;; lexical binder ごとの本体 point。出口の型がどの束縛へ届くかを判定する。
(define binder-points (make-parameter (hash)))

;; config-ok? が heap の値を再型付けするときだけ、OwnedLeaf を持つ Rec 欄を
;; 通す。通常の Core 型検査では従来どおり owned-record-field を拒否する。
(define deriving-config? (make-parameter #f))

;; 構成の row 再型付けでも、check-as 内部の型検査へ同じ Ω を渡す。
(define forward-config-states (make-parameter #f))

;; config-ok? の再型付けでだけ runtime borrow に型を与える。
;; 通常の型検査入口では #f のままなので BorrowRef は ill-typed である。
(define config-runtime-borrow-types (make-parameter #f))

;; config の再型付けでは Λ に region IR が無いので、検査する Core 全体の
;; place 位置の射影の point を保持する。
(define config-projborrow-place-points (make-parameter #f))

;; configuration の型導出と runtime-row が同じ抑止範囲を共有する。
(define (with-config-typing thunk)
  (parameterize ([deriving-config? #t])
    (thunk)))

;; 制約の収集器（spec §5.2）。既定は #f であり、その場合は何も記録しない。
;; G4b が入れた typing-point-probe と同じ形の記録先である。
;; 走査の各段へ手を入れず、infer の出口 1 か所で集める。
(define lifetime-collector (make-parameter #f))

(define (emit-constraint! c)
  (define b (lifetime-collector))
  (when b (set-box! b (cons c (unbox b)))))

(define (collected-constraints)
  (define b (lifetime-collector))
  (if b (reverse (unbox b)) '()))

(define (with-lifetime-collector thunk)
  (define b (box '()))
  (parameterize ([lifetime-collector b]) (thunk))
  (reverse (unbox b)))

;; 判定の要求の収集器（spec §7.3）。既定は #f であり、その場合は何も記録しない。
(define request-collector (make-parameter #f))

;; unsafe.md §5.2。raw 操作の出現の収集器。既定は #f であり、その場合は
;; 既存の型検査 API の結果と副作用を変えない。
(define ptr-request-collector (make-parameter #f))

(define (record-ptr-request! kind node obligations)
  (define b (ptr-request-collector))
  (when b
    (set-box! b
              (cons (ptr-request kind node obligations (unsafe-permitted))
                    (unbox b)))))

(define (emit-request! r)
  (define b (request-collector))
  (when b (set-box! b (cons r (unbox b)))))

(define (collected-requests)
  (define b (request-collector))
  (if b (reverse (unbox b)) '()))

;; §5.4。formal 鍵の designator。出現の point と節点と仮引数の位置から決める。
;; 仮引数の名前から採ると同名の仮引数を持つ入れ子の Lam が衝突し、callable の
;; 識別子から採ると 1 つの識別子を使う複数の出現が衝突し、処理系全体の
;; counter から採ると同じ項を二度型付けした結果が一致しなくなる。
;; point だけでも足りない。Task 4a の付け替えは同じ形の部分項を複製するため、
;; 1 つの点へ別の Lam が来る形がある。summary-key と同じ組を土台にする。
;; 先頭の 'formal は形で見分けるための札である。利用者の designator は
;; borrow-designator? が示すとおり記号か非負整数であり、この形とは重ならない。
;; 見分けは全形で行う。先頭の札だけを見ると、長さや添字の壊れた (formal ...)
;; を内部の鍵として受け入れてしまい、fail closed の主張が弱くなる。
(define (formal-designator Λ node index)
  (list 'formal (region-ctx-point Λ) (peel-node node) index))

(define (formal-parameter-context Λ node parameters parameter-types)
  (define entries
    (for/list ([type (in-list parameter-types)] [index (in-naturals)])
      (define root (formal-designator Λ node index))
      (define-values (capability leaves) (formal-capability-entry type root))
      (and (not (set-empty? (capability-entry-keys capability)))
           (list root capability leaves))))
  (define formals
    (map (lambda (entry) (and entry (first entry))) entries))
  (define formal-fields
    (map (lambda (entry) (and entry (third entry))) entries))
  (define body-context
    (for/fold ([Λ_body (enter-child Λ 0)])
              ([name (in-list parameters)] [entry (in-list entries)]
               #:when entry)
      (define capability (second entry))
      (region-ctx-add-token Λ_body name
                            (capability-entry-keys capability)
                            #f #f
                            (capability-entry-fields capability)
                            (capability-entry-variants capability)
                            (capability-entry-borrowed-view? capability))))
  (values formals formal-fields body-context))

(define (formal-leaf-mode type path)
  (let walk ([current (normalize-type (peel-ty type))] [remaining path])
    (match current
      [`(Borrowed ,_ ,_) (and (null? remaining) 'shared)]
      [`(BorrowedMut ,_ ,_) (and (null? remaining) 'mut)]
      [`(Owned ,inner) (walk inner remaining)]
      [`(Untrusted ,inner) (walk inner remaining)]
      [`(Refined ,inner ,_) (walk inner remaining)]
      [`(Record ,row)
       (match remaining
         [(list (cons 'record-field label) rest ...)
          (define field
            (for/first ([candidate (in-list row)]
                        #:when (equal? (first candidate) label))
              candidate))
          (and field (walk (second field) rest))]
         [_ #f])]
      [`(Union ,_ ,_)
       (match remaining
         [(list member-type rest ...)
          (define normalized-member (normalize-type member-type))
          (and (member normalized-member
                       (map normalize-type (union-members current)) equal?)
               (walk normalized-member rest))]
         [_ #f])]
      [_
       (match remaining
         [(list (cons constructor (? exact-nonnegative-integer? index)) rest ...)
          (define schema (constructor-schema current))
          (define fields
            (and (list? schema)
                 (for/first ([candidate (in-list schema)]
                             #:when (equal? (first candidate) constructor))
                   (second candidate))))
          (and fields (< index (length fields))
               (walk (list-ref fields index) rest))]
         [_ #f])])))

(define (capability-entry-leaves entry [path '()])
  (define fields (capability-entry-fields entry))
  (if (hash? fields)
      (append-map
       (lambda (key)
         (capability-entry-leaves (hash-ref fields key) (append path (list key))))
       (hash-keys fields))
      (if (set-empty? (capability-entry-keys entry))
          '()
          (list (cons path entry)))))

(define (formal-destination-paths type alpha)
  (define-values (_entry leaves)
    (formal-capability-entry type '(formal-destination)))
  (remove-duplicates
   (for/list ([(path entry) (in-hash leaves)]
              #:when (and (capability-entry? entry)
                          (equal? (capability-entry-declared-lifetime entry)
                                  alpha)))
     path)
   equal?))

(define (record-leaf-exit! event root node fail)
  (match (deferred-leaf-exit-source event)
    [`(binder ,decomposition ,branch-index ,binder-index)
     (define info-table (branch-binder-event-info))
     (define info
       (and (hash? info-table)
            (hash-ref info-table
                      (list decomposition branch-index binder-index) #f)))
     (when info
       (define frame (first info))
       (define collector (template-frame-box frame))
       (unless (for/or ([previous (in-list (unbox collector))])
                 (and (deferred-leaf-exit? previous)
                      (equal? (leaf-exit-identity previous)
                              (leaf-exit-identity event))))
         (set-box! collector (cons event (unbox collector)))))]
    [_ (when (owning-frame root)
         (route-deferred! event root node fail))]))

(define (leaf-exit-destinations exit-kind destinations)
  (if (null? destinations)
      (list (list 'unclassified #f))
      (for/list ([destination (in-list destinations)])
        (list exit-kind destination))))

(define (mark-leaf-exit-incomplete!)
  (for ([frame (in-list (template-collectors))])
    (set-box! (template-frame-incomplete-box frame) #t)))

(define (record-formal-source-exits! Λ expression exit-kind destination-for fail)
  ;; capability 表の取得失敗は型検査を止めず、要約を不完全として残す。
  (define actual-entry
    (with-handlers ([exn:fail?
                     (lambda (_)
                       (mark-leaf-exit-incomplete!)
                       #f)])
      ((current-leaf-exit-capability-reader) Λ expression)))
  (when (capability-entry? actual-entry)
    (for* ([actual-leaf (in-list (capability-entry-leaves actual-entry))]
           [cap (in-set (capability-entry-keys (cdr actual-leaf)))]
           #:when (formal-key? (car cap)))
      (define root (car cap))
      (define frame (owning-frame root))
      (when frame
        (define index (fourth root))
        (define formal-fields (template-frame-formal-fields frame))
        (define leaves
          (and (< index (length formal-fields)) (list-ref formal-fields index)))
        (when (hash? leaves)
          (for ([(formal-path formal-entry) (in-hash leaves)]
                #:when (and (capability-entry? formal-entry)
                            (set-member? (capability-entry-keys formal-entry) cap)))
            (define mode
              (formal-leaf-mode
               (list-ref (template-frame-parameter-types frame) index)
               formal-path))
            (define alpha
              (capability-entry-declared-lifetime formal-entry))
            (when (and mode alpha)
              (for ([destination
                     (in-list
                      (leaf-exit-destinations
                       exit-kind
                       (destination-for (car actual-leaf) formal-path alpha)))])
                (record-leaf-exit!
                (deferred-leaf-exit
                  (list 'formal index formal-path) index formal-path '() mode alpha
                 (append (second root) '(0))
                  (first destination) (second destination))
                 root expression fail)))))))))

(define (record-binder-type-exits! type expression exit-kind destination-for fail)
  (define alphas (branch-binder-alphas))
  (define infos (branch-binder-event-info))
  (when (and (hash? alphas) (hash? infos))
    (define-values (_root leaves)
      (formal-capability-entry type '(binder-exit)))
    (for ([(path entry) (in-hash leaves)]
          #:when (and (capability-entry? entry)
                      (capability-entry-declared-lifetime entry)))
      (define source-alpha (capability-entry-declared-lifetime entry))
      (for ([(key alpha) (in-hash alphas)]
            #:when (set-member? (binder-alpha-origins source-alpha) alpha))
        (match (hash-ref infos key #f)
          [(list _frame formal-index parent-path parent-alpha mode ambiguous?)
           (define observed-kind (if ambiguous? 'unclassified exit-kind))
           (define destinations
             (if ambiguous?
                 (list (list 'unclassified #f))
                 (leaf-exit-destinations
                  exit-kind
                  (destination-for path parent-path parent-alpha))))
           (for ([destination (in-list destinations)])
             (record-leaf-exit!
              (deferred-leaf-exit
               (cons 'binder key) formal-index parent-path path mode alpha
               (first key) observed-kind (second destination))
              #f expression fail))]
          [_ (void)])))))

(define (binder-alpha-origins alpha)
  (define derived (branch-binder-alpha-sources))
  (let expand ([current alpha] [seen (set)])
    (cond
      [(not (lifetime-var? current)) (set)]
      [(set-member? seen current)
       (error 'binder-alpha-origins "binder α の対応が循環している: ~s" current)]
      [else
       (define next-seen (set-add seen current))
       (define derived-sources
         (and (hash? derived) (hash-ref derived current #f)))
       (define merged-sources
         (and (hash? (merge-alpha-sources))
              (hash-ref (merge-alpha-sources) current #f)))
       (define sources
         (or derived-sources
             (and merged-sources
                  (filter lifetime-var? (set->list merged-sources)))))
       (if sources
           (for/fold ([result (set)]) ([source (in-list (if (set? sources)
                                                            (set->list sources)
                                                            sources))])
             (set-union result (expand source next-seen)))
           (set current))])))

(define (record-binder-alpha-descendant! alpha parent)
  (define table (branch-binder-alpha-sources))
  (define binders (branch-binder-alphas))
  (when (and (hash? table) (hash? binders) (lifetime-var? parent))
    (define origins (binder-alpha-origins parent))
    (when (for/or ([binder-alpha (in-hash-values binders)])
            (set-member? origins binder-alpha))
      (hash-set! table alpha (set parent)))))

(define (record-binder-result-exits-in! core Λ result-type fail)
  (define term (peel-node core))
  (define head (and (pair? term) (car term)))
  (define child-indices
    (match term
      [`(Let ,_ ,_ ,_) '(1)]
      [`(Scope ,_ ,_) '(0)]
      [`(RegionLam ,_ ,_) '(0)]
      [`(Unsafe ,_) '(0)]
      [`(Suspend ,_) '(0)]
      [`(Discharge ,_ ,_) '(0)]
      [`(Recur ,_ ,_ ,_ ,_ ,_) '(1)]
      [`(RecurVal ,_ ,_ ,_ ,_) '(0)]
      [`(Eliminate ,_ ,branches) (range 1 (add1 (length branches)))]
      [`(EliminateAt ,_ ,branches) (range 1 (add1 (length branches)))]
      [`(UnionEliminate ,_ ,branches) (range 1 (add1 (length branches)))]
      [`(UnionEliminateAt ,_ ,branches) (range 1 (add1 (length branches)))]
      [_ '()]))
  (for ([index (in-list child-indices)])
    (define child (list-ref (core-children term) index))
    (when (and (positive? index)
               (memq head '(Eliminate EliminateAt
                            UnionEliminate UnionEliminateAt)))
      (record-binder-type-exits!
       (typing-child-type Λ index) child 'result
       (lambda (_actual-path _source-path parent-alpha)
         (formal-destination-paths result-type parent-alpha))
       fail))
    (record-binder-result-exits-in! child (enter-child Λ index)
                                    result-type fail)))

(define (record-formal-site-exits! core Λ child-index expression exit-kind
                                   destination-for fail)
  (define observed-kind (leaf-exit-kind-at core Λ child-index))
  (if (eq? observed-kind exit-kind)
      (record-formal-source-exits! (enter-child Λ child-index) expression
                                   exit-kind destination-for fail)
      (record-formal-source-exits!
       (enter-child Λ child-index) expression 'unclassified
       (lambda (_actual-path _source-path _alpha) (list #f)) fail)))

(define (record-formal-result-exits! Λ expression result-type fail)
  (record-formal-source-exits!
   Λ expression 'result
   (lambda (_actual-path _source-path alpha)
     (formal-destination-paths result-type alpha))
   fail)
  (match (typing-result-at Λ)
    [(list actual-type _normal-type _row _escapes)
     (record-binder-type-exits!
      actual-type expression 'result
      (lambda (_actual-path _source-path parent-alpha)
        (formal-destination-paths result-type parent-alpha))
      fail)]
    [_ (void)])
  (record-binder-result-exits-in! expression Λ result-type fail))

(define (record-formal-argument-exits! Λ expression parameter-index parameter-type fail)
  (record-formal-source-exits!
   Λ expression 'formal
   (lambda (_actual-path _source-path alpha)
     (for/list ([path (in-list (formal-destination-paths parameter-type alpha))])
       (list parameter-index path)))
   fail))

(define (formal-capability-type? type)
  (define-values (entry _leaves)
    (formal-capability-entry type '(formal-capability-probe)))
  (not (set-empty? (capability-entry-keys entry))))

(define (formal-leaf-info summary index path actual-entry)
  (unless (callable-summary? summary)
    (raise-argument-error 'formal-leaf-info "callable-summary?" summary))
  (unless (and (exact-nonnegative-integer? index)
               (< index (length (callable-summary-formal-fields summary))))
    (raise-arguments-error 'formal-leaf-info "formal index is out of range"
                           "index" index))
  (unless (capability-entry? actual-entry)
    (raise-argument-error 'formal-leaf-info "capability-entry?" actual-entry))
  (define leaves (list-ref (callable-summary-formal-fields summary) index))
  (define formal-entry (and (hash? leaves) (hash-ref leaves path #f)))
  (unless (and (capability-entry? formal-entry)
               (capability-entry-declared-lifetime formal-entry))
    (raise-arguments-error 'formal-leaf-info "formal leaf path is missing or ambiguous"
                           "index" index "path" path))
  (values (capability-entry-declared-lifetime formal-entry)
          (capability-entry-source-alphas actual-entry)))

(define (formal-key? w)
  (match w
    [(list 'formal _point _node (? exact-nonnegative-integer?)) #t]
    [_ #f]))

;; §5.4。雛形の収集器。関数の本体を型付けしているあいだだけ積みが伸びる。
;; 各段は自分が採った formal 鍵の集合と箱の対である。
;; 鍵の持ち主は最も内側から順に探す。積みの先頭へ無条件に入れてはならない。
;; 外側の仮引数を実引数として内側の呼出しへ渡すと、内側を実体化した結果が
;; 外側の鍵を持つ要求になる。その要求を受けるのは外側の段である。
(struct template-frame
  (formals box body parameters parameter-types return-type latent-row formal-fields
           incomplete-box)
  #:transparent)
(define template-collectors (make-parameter '()))

;; §4.2。再帰専用の重ね。template-collectors と同じ形の parameter である。
;; 要素は再帰の束縛の並び、借用の仮引数の位置ごとの鍵、転送候補の位置、
;; 雛形を集める箱、仮と確定のどちらかを示す印を持つ。
(struct recur-frame
  (bindings formals formal-fields result-index collector incomplete-box state)
  #:transparent)
(define recur-overlay (make-parameter '()))

;; §4.6。束縛の並びの長さは形ごとに決まる。形 i の Recur と RecurVal は 1、
;; 形 ii の Recur は 2 である。外れたら実装の誤りなので、黙って受理しない。
(define (make-recur-frame bindings formals result-index collector state expected
                          [formal-fields (make-list (length formals) #f)]
                          [incomplete-box (box #f)])
  (unless (= (length bindings) expected)
    (error 'make-recur-frame
           "束縛の並びの長さが ~a、期待は ~a" (length bindings) expected))
  (unless (= (length formals) (length formal-fields))
    (error 'make-recur-frame
           "formal の並びの長さが ~a、欄表の並びは ~a"
           (length formals) (length formal-fields)))
  (recur-frame bindings formals formal-fields result-index collector incomplete-box state))

;; §4.2。環境から引いた対が、重ねが保つ束縛の並びのいずれかと eq? で
;; 一致する枠を返す。名前で引くと、本体の中の Let が影にした同名の束縛を
;; 再帰呼出しと見なしてしまう。
(define (recur-frame-for binding)
  (and binding
       (for/first ([f (in-list (recur-overlay))]
                   #:when (memq binding (recur-frame-bindings f)))
         f)))

;; §4.2。仮の状態では雛形が揃っていないため、要約による照合はできない。
;; 借用の仮引数の位置ごとに、実引数の capability の根がその位置の鍵と
;; 一致することだけを課す。capability の要素は (cons root path) の組であり、
;; 直接の仮引数なら (set (cons w '())) となる。ここでは根だけを見て path は
;; 縛らない。同じ根を持つ射影と再借用は受理し、根が別の鍵になる入れ替えと
;; 根が解けない場合は落ちる。path を各回で縛らなくても、射影と再借用は根を
;; 変えず path だけを狭めるため、Ψ の単調な join がその path ごとの要求を
;; 次の fixpoint の巡へ運ぶ。収束後に新しい根が現れることはない。
(define (recur-check-roots frame argument-caps node fail)
  (define formals (recur-frame-formals frame))
  (unless (= (length formals) (length argument-caps))
    (fail 'parameter-arity-mismatch node
          (length formals) (length argument-caps)))
  (for ([w (in-list formals)] [caps (in-list argument-caps)] #:when w)
    (when (set-empty? caps)
      (fail 'unresolved-borrow-owner node))
    (for ([cap (in-set caps)])
      (unless (and (pair? cap) (equal? (car cap) w))
        (fail 'unresolved-borrow-owner node)))))

;; §4.2。収束した巡の箱を確定した要約へ写す。
;; 形 ii の RegionApp だけが実引数の region で置換するため、置換表は空で置く。
(define (recur-frame->summary frame)
  (callable-summary (recur-frame-formals frame)
                    (normalize-leaf-exits
                     (reverse (unbox (recur-frame-collector frame))))
                    (recur-frame-result-index frame)
                    (hash)
                    (recur-frame-formal-fields frame)
                    (unbox (recur-frame-incomplete-box frame))))

(define (owning-frame w)
  (for/first ([f (in-list (template-collectors))]
              #:when (set-member? (template-frame-formals f) w))
    f))

(define (point-prefix? prefix point)
  (and (<= (length prefix) (length point))
       (equal? prefix (take point (length prefix)))))

(define (template-relative-point w point)
  (define frame (owning-frame w))
  (match w
    [`(formal ,lambda-point ,_ ,_)
     (define body-root (append lambda-point '(0)))
     (and frame (point-prefix? body-root point)
          (drop point (length body-root)))]
    [_ point]))

(define (core-at-point core point)
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (for/fold ([node core]) ([index (in-list point)])
      (list-ref (core-children (peel-node node)) index))))

(define (scalar-window-type? type)
  (memq (normalize-type (peel-ty type)) '(Int Bool Unit String)))

(define (window-scope-safe? frame scope)
  (define (borrow-entry type)
    (match (normalize-type (peel-ty type))
      [`(Borrowed ,payload ,_)
       (and (scalar-window-type? payload) (list 'borrow payload))]
      [`(BorrowedMut ,payload ,_)
       (and (scalar-window-type? payload) (list 'borrow payload))]
      [_ #f]))
  (define parameters
    (for/hash ([name (in-list (template-frame-parameters frame))]
               [type (in-list (template-frame-parameter-types frame))]
               #:when (or (borrow-entry type) (scalar-window-type? type)))
      (values name (or (borrow-entry type) (list 'scalar type)))))
  (define (scalar-value? value)
    (or (exact-integer? value) (string? value)
        (memq value '(unit #t #f))))
  (define (safe-reborrow? place name borrowed mode env body)
    (define parent (hash-ref env (peel-node place) #f))
    (and (memq mode '(const let)) borrowed
         parent (eq? (first parent) 'borrow)
         (equal? (second parent) (second borrowed))
         (safe? body (hash-set env name borrowed))))
  (define (safe? term env)
    (match (peel-node term)
      [`(Scope ,_ ,body) (safe? body env)]
      [`(Let (,binder ,mode ,type) ,bound ,body)
       (define name (peel-bind binder))
       (define borrowed (borrow-entry type))
       (match (peel-node bound)
         [`(Reborrow ,place)
          (safe-reborrow? place name borrowed mode env body)]
         [`(ReborrowAt ,_ρ ,place)
          (safe-reborrow? place name borrowed mode env body)]
         [_
          (and (memq mode '(const let))
               (not borrowed) (scalar-window-type? type)
               (safe? bound env)
               (safe? body (hash-set env name (list 'scalar type))))])]
      [`(Read (Reborrow ,place))
       (define entry (hash-ref env (peel-node place) #f))
       (and entry (eq? (first entry) 'borrow)
            (scalar-window-type? (second entry)))]
      [`(Read ,place)
       (define entry (hash-ref env (peel-node place) #f))
       (and entry
            (or (eq? (first entry) 'scalar)
                (scalar-window-type? (second entry))))]
      [`(Assign ,place ,value)
       (define entry (hash-ref env (peel-node place) #f))
       (and entry (eq? (first entry) 'borrow) (scalar-value? value))]
      [value (scalar-value? value)]))
  ;; shortcut: scalar の読み書きだけ窓を付ける。escape を追跡できる段階で対象を広げる。
  (and (pair? (template-frame-parameter-types frame))
       (scalar-window-type? (template-frame-return-type frame))
       (not (borrowed-type-anywhere? (template-frame-return-type frame)))
       (not (borrowed-type-anywhere? (template-frame-latent-row frame)))
       (match (peel-node scope)
         [`(Scope ,_ ,body) (safe? body parameters)]
         [_ #f])))

(define (reborrow-window-point w point)
  (define frame (owning-frame w))
  (define relative (template-relative-point w point))
  (define window
    (and frame relative (template-frame-body frame)
         (let ([body (template-frame-body frame)])
           (define candidate
             (for/first ([length (in-range (length relative) -1 -1)]
                         #:do [(define prefix (take relative length))
                               (define term (core-at-point body prefix))]
                         #:when (match (peel-node term)
                                  [`(Scope ,_ ,_) #t]
                                  [_ #f]))
               (cons prefix term)))
           (and candidate
                (window-scope-safe? frame (cdr candidate))
                (append (append (second w) '(0)) (car candidate))))))
  window)

;; §5.4。要求と制約を出す唯一の窓口。formal 鍵が残っていれば、関数の本体を
;; 型付けしている最中である。そのまま出さず雛形として溜め、Apply が実引数の
;; capability と RegionApp が受けた region 項で置き換えてから出す。
;; 持ち主の段が積みに無い形は、実体化の経路が抜けているということなので
;; fail closed にする。
(define (route-deferred! item w node fail)
  (cond
    [(not (formal-key? w)) #f]
    [else
     (define f (owning-frame w))
     (unless f (fail 'unresolved-borrow-owner node))
     (define b (template-frame-box f))
     (if (deferred-leaf-exit? item)
         (unless (for/or ([previous (in-list (unbox b))])
                   (and (deferred-leaf-exit? previous)
                        (equal? (leaf-exit-identity previous)
                                (leaf-exit-identity item))))
           (set-box! b (cons item (unbox b))))
         (set-box! b (cons item (unbox b))))
     #t]))

(define (route-request! r node fail)
  (define w
    (if (borrow-request? r) (borrow-request-w r) (use-request-w r)))
  (define deferred-r
    (cond
      [(and (borrow-request? r) (formal-key? w))
       (struct-copy borrow-request r
                    [point (and (borrow-request-point r)
                                (template-relative-point
                                 w (borrow-request-point r)))])]
      [(and (use-request? r) (formal-key? w))
       (struct-copy use-request r
                    [point (and (use-request-point r)
                                (template-relative-point
                                 w (use-request-point r)))])]
      [else r]))
  (unless (route-deferred! deferred-r w node fail)
    (emit-request! r)))

;; 本体の Reborrow は親が (RParam rp) であり、呼出し位置で RegionApp が
;; 受けた region 項へ置き換わるまで具体の region へ落とせない。
(define (rparam-term? t)
  (match t [`(RParam ,_) #t] [_ #f]))

;; §5.4。region-constraint は所有者の designator を欄に持たない。
;; formal capability の欄 path は、呼出しで親と子の停止を結ぶため一緒に保持する。
(struct deferred-constraint (w constraint window-point parent-fp child-fp) #:transparent)

(define (route-constraint! c w node fail [window-point #f]
                           [parent-fp '()] [child-fp '()])
  (define deferred-c
    (if (formal-key? w)
        (struct-copy region-constraint c
                     [point (and (region-constraint-point c)
                                 (template-relative-point
                                  w (region-constraint-point c)))])
        c))
  (define deferred-window
    (and window-point (template-relative-point w window-point)))
  (unless (route-deferred!
           (deferred-constraint w deferred-c deferred-window
                                parent-fp child-fp)
           w node fail)
    (emit-constraint! c)))

;; Reborrow の token 集合は 1 つの収集先へしか送れない。formal 鍵と通常の
;; designator が混ざる形を任意の 1 要素で代表させると、制約の行き先が集合の
;; 反復順で変わる。formal 鍵どうしも別の frame に属するなら同じ問題なので、
;; その形を unresolved-borrow-owner で閉じる。
;; 同じ frame の formal が複数ある場合も、各鍵へ遅延制約を送る。
(define (uniform-token-designators tokens node fail)
  (define caps (set->list tokens))
  (define first-w (car (first caps)))
  (define first-frame (and (formal-key? first-w)
                           (owning-frame first-w)))
  (define uniform?
    (if (formal-key? first-w)
        (and first-frame
             (for/and ([cap (in-list caps)])
               (define w (car cap))
               (and (formal-key? w)
                    (eq? first-frame (owning-frame w)))))
        (for/and ([cap (in-list caps)])
          (not (formal-key? (car cap))))))
  (unless uniform?
    (fail 'unresolved-borrow-owner node))
  (sort (set->list (for/set ([cap (in-list caps)]) (car cap)))
        string<?
        #:key (lambda (w) (format "~s" w))))

;; §5.4。関数の出現ごとの要約。formals は仮引数の位置に対応する formal
;; designator の並びであり、借用でない位置は #f である。deferred は本体で
;; 集めた雛形、result-index は結果の借用を転送する候補位置の並び、
;; region-subst は RegionApp が解いた rp から ρ への写像である。
(struct callable-summary
  (formals deferred result-index region-subst formal-fields incomplete?)
  #:transparent)

(struct deferred-leaf-exit
  (source formal-index parent-path binder-path mode alpha body-point exit-kind destination)
  #:transparent)

;; 借用の起点と七種の行き先、または出口ではない通過位置。
;; descriptor は固定位置、(from k)、または descriptor の列である。
(define g2-only-leaf-exit-heads
  '(Absent RecRewriteOpen Borrow BorrowMut Reborrow ProjBorrow Read Assign Reassign
           RegionLam RegionApp AddressOf PtrOffset RawLoad RawStore FromRawPtr Unsafe
           MutSlot BorrowAt BorrowMutAt ReborrowAt ProjBorrowAt BorrowRef BorrowMutRef
           PtrVal))

(define leaf-exit-sites
  (let ([base
         (for/fold ([sites (for/hash ([row (in-list core-form-features)])
                             (values (first row) '()))])
                   ([head (in-list g2-only-leaf-exit-heads)])
           (hash-set sites head '()))])
  (for/fold ([sites base])
            ([(head entries)
              (in-hash
               (hash 'Apply (list (cons '(from 1) 'formal))
                     'Assign (list (cons 0 'local) (cons 1 'storage))
                     'AddressOf (list (cons 0 'yield))
                     'Construct (list (cons '(from 0) 'transit))
                     'Curry (list (cons 0 'transit) (cons 1 'capture))
                     'CurryVal (list (cons 0 'transit) (cons 1 'capture))
                     'Discharge (list (cons 0 'transit))
                     'Drop (list (cons 0 'local))
                     'Eliminate (list (cons 0 'transit) (cons '(from 1) 'transit))
                     'EliminateAt (list (cons 0 'transit) (cons '(from 1) 'transit))
                     'Handle (list (cons 0 'transit) (cons 1 'transit))
                     'Lam (list (cons 0 'transit))
                     'Let (list (cons 0 'transit) (cons 1 'transit))
                     'OwnLeaf (list (cons 0 'transit))
                     'OwnedLeaf (list (cons 0 'transit))
                     'OwnedTransit (list (cons 0 'transit))
                     'Perform (list (cons 0 'handle))
                     'Proj (list (cons 0 'transit))
                     'ProjBorrow (list (cons 0 'transit))
                     'ProjBorrowAt (list (cons 0 'transit))
                     'ProjOpt (list (cons 0 'transit))
                     'RVal (list (cons 0 'transit))
                     'Reborrow (list (cons 0 'transit))
                     'ReborrowAt (list (cons 0 'transit))
                     'Rec (list (cons '(from 0) 'transit))
                     'RecRewrite (list (cons 0 'transit) (cons '(from 1) 'transit))
                     'RecRewriteOpen (list (cons '(from 0) 'transit))
                     'Recur (list (cons 0 'transit) (cons 1 'transit))
                     'RecurVal (list (cons 0 'transit))
                     'Read (list (cons 0 'local))
                     'Reassign (list (cons 0 'storage))
                     'RegionApp (list (cons 0 'transit))
                     'RegionLam (list (cons 0 'transit))
                     'Scope (list (cons 0 'transit))
                     'Suspend (list (cons 0 'transit))
                     'UVal (list (cons 0 'transit))
                     'UnionEliminate (list (cons 0 'transit) (cons '(from 1) 'transit))
                     'UnionEliminateAt
                     (list (cons 0 'transit) (cons '(from 1) 'transit))
                     'UnionInject (list (cons 0 'transit))
                     'UnionVal (list (cons 0 'transit))
                     'Unsafe (list (cons 0 'transit))
                     'Yield (list (cons 0 'yield) (cons 1 'transit))))])
    (hash-set sites head entries))))

;; 試験で一覧から位置を除き、未分類出口の記録を検査する。
(define current-leaf-exit-sites (make-parameter leaf-exit-sites))

(define (site-position-matches? descriptor point)
  (define (match-segments segments remaining)
    (cond
      [(null? segments) #t]
      [(null? remaining) #f]
      [else
       (define segment (car segments))
       (define index (car remaining))
       (and (or (and (exact-nonnegative-integer? segment)
                     (= segment index))
                (match segment
                  [`(from ,(? exact-nonnegative-integer? start))
                   (>= index start)]
                  [_ #f]))
            (match-segments (cdr segments) (cdr remaining)))]))
  (match descriptor
    [(? exact-nonnegative-integer? index)
     (and (pair? point) (= index (car point)))]
    [`(from ,(? exact-nonnegative-integer? _))
     (match-segments (list descriptor) point)]
    [(list segments ...) (match-segments segments point)]
    [_ #f]))

(define (leaf-exit-kind-at core Λ child-index)
  (define point (region-ctx-point Λ))
  (define child-point (region-ctx-point (enter-child Λ child-index)))
  (define relative-point (list-tail child-point (length point)))
  (define head
    (match (peel-node core)
      [(list (? symbol? name) _ ...) name]
      [_ #f]))
  (for/first ([site (in-list (hash-ref (current-leaf-exit-sites) head '()))]
              #:when (site-position-matches? (car site) relative-point))
    (cdr site)))

(define (leaf-exit-identity event)
  (list (deferred-leaf-exit-source event)
        (deferred-leaf-exit-alpha event)
        (deferred-leaf-exit-exit-kind event)
        (deferred-leaf-exit-destination event)))

(define (normalize-leaf-exits deferred)
  (define events (filter deferred-leaf-exit? deferred))
  (define identities (make-hash))
  (define unique-events
    (for/list ([event (in-list events)]
               #:unless (hash-has-key? identities (leaf-exit-identity event)))
      (hash-set! identities (leaf-exit-identity event) #t)
      event))
  (append (filter (lambda (item) (not (deferred-leaf-exit? item))) deferred)
          (sort unique-events string<? #:key (lambda (event) (format "~s" event)))))

(define (callable-summary-leaf-exits summary)
  (filter deferred-leaf-exit? (callable-summary-deferred summary)))

(define (leaf-exit-key event)
  (list (deferred-leaf-exit-source event)
        (deferred-leaf-exit-alpha event)))

(define (classify-leaf-exits exits)
  (define grouped
    (for/fold ([groups (hash)]) ([event (in-list exits)])
      (hash-update groups (leaf-exit-key event)
                   (lambda (previous) (cons event previous)) '())))
  (for/hash ([(key events) (in-hash grouped)])
    (values key
            (if (andmap (lambda (event)
                          (eq? (deferred-leaf-exit-exit-kind event) 'local))
                        events)
                'local
                'fail-closed))))

(define (leaf-exit-local-safe? source exits result-type)
  (and (pair? exits)
       (andmap (lambda (event)
                 (and (deferred-leaf-exit? event)
                      (equal? (deferred-leaf-exit-source event) source)
                      (eq? (deferred-leaf-exit-exit-kind event) 'local)))
               exits)
       (match source
         [(list 'formal _ ...) #t]
         [(list 'binder _ ...)
          (define result-alphas (lifetime-vars-in result-type))
          (for/and ([event (in-list exits)])
            (not (set-member? result-alphas
                              (deferred-leaf-exit-alpha event))))]
         [_ #f])))

(define (local-exit-alpha-origins alpha)
  (define merged
    (if (lifetime-var? alpha) (alpha-set alpha) (set)))
  (define derived
    (if (lifetime-var? alpha) (binder-alpha-origins alpha) (set)))
  (set-add (set-union merged derived) alpha))

;; 要約を出現ごとに溜める表。既定の #f は「収集の外」であり、書き込みを
;; 黙って捨てる位置と区別する。typing の入口 2 つが parameterize する。
(define callable-summaries (make-parameter #f))

;; 鍵は point と node の対である。point だけでは足りない。同じ point へ別の
;; 節点が来る形が 2 つある。1 つは再推論であり、check-as が落ちた後に infer が
;; 同じ位置を測り直す。もう 1 つは入れ子であり、Task 4a の付け替えが同じ形の
;; 部分項を複製する。span の包みは剥がしてから鍵にする。
(define (summary-key Λ node)
  (cons (region-ctx-point Λ) (peel-node node)))

(define (record-callable-summary! Λ node summary fail)
  (define table (callable-summaries))
  (when table
    (define key (summary-key Λ node))
    (define previous (hash-ref table key #f))
    (cond
      [(not previous) (hash-set! table key summary)]
      ;; 同じ鍵へ同じ要約が来るのは再推論であり、正しい。
      [(equal? previous summary) (void)]
      ;; 別の要約が来たら鍵が出現を一意に指していない。黙って上書きすると、
      ;; 後から読む Apply が別の関数の雛形を実体化する。
      [else (fail 'unresolved-borrow-owner node)])))

(define (lookup-callable-summary Λ node)
  (define table (callable-summaries))
  (and table (hash-ref table (summary-key Λ node) #f)))

;; 借用型の region 欄を返す。借用型でなければ #f を返す。
(define (borrow-region type)
  (match (normalize-type type)
    [`(Borrowed ,_ ,ρ) ρ]
    [`(BorrowedMut ,_ ,ρ) ρ]
    [_ #f]))

;; 構成検査では具体化済みの region を境界で許し、自由な RParam は拒む。
(define (unbound-boundary-borrowed-type? type)
  (unbound-borrowed-type? type (bound-region-params)
                          #:concrete-regions-bound? (deriving-config?)))

;; 型木のどこかに借用があるかを、region の束縛状態に関係なく検出する。
;; 借用の所有者をこの型から復元できない位置で使う。
(define (borrowed-type-anywhere? type)
  (unbound-borrowed-type? type (set)))

(define (contains-omitted-region? type)
  (let walk ([value type])
    (match value
      [`(RParam %omitted) #t]
      [(? pair? values) (ormap walk values)]
      [_ #f])))

;; §5.4。定義時の formal region で、結果の借用と同じ region を持つ
;; 仮引数の位置を集める。RegionApp 後に数え直すと異なる formal が潰れる。
(define (forwarding-indices parameter-types return-type)
  (define ρ-result (borrow-region return-type))
  (if ρ-result
      (for/list ([τ (in-list parameter-types)]
                 [i (in-naturals)]
                 #:when (equal? (borrow-region τ) ρ-result))
        i)
      '()))

;; 要約の無い concrete function は候補が一つの場合だけ転送できる。
(define (forwarding-index parameter-types return-type)
  (match (forwarding-indices parameter-types return-type)
    [(list i) i]
    [_ #f]))

;; §5.4。署名の各 borrowed leaf について候補 (formal index . formal path) を作る。
(define (forwarding-leaf-candidates parameter-types return-type node fail)
  (define (checked-leaves type)
    (define-values (_root leaves)
      (formal-capability-entry type '(formal)))
    (for ([entry (in-hash-values leaves)])
      (unless (capability-entry? entry)
        (fail 'unresolved-borrow-owner node)))
    leaves)
  (define-values (_result-root result-leaves)
    (formal-capability-entry return-type '(result)))
  (define parameter-leaves
    (map checked-leaves parameter-types))
  (for/fold ([result (hash)])
            ([(result-path result-leaf) (in-hash result-leaves)])
    (unless (capability-entry? result-leaf)
      (fail 'unresolved-borrow-owner node))
    (define result-lifetime
      (capability-entry-declared-lifetime result-leaf))
    ;; 再帰 schema の打ち切り entry は leaf 寿命の無い上界候補であり、曖昧印ではない。
    ;; 実引数の上界は Apply の位置で組み立てる。
    (if result-lifetime
        (hash-set
         result result-path
         (append-map
          (lambda (index leaves)
            (for/list ([(formal-path formal-leaf) (in-hash leaves)]
                       #:when (and (capability-entry? formal-leaf)
                                   (capability-entry-declared-lifetime formal-leaf)
                                   (equal? result-lifetime
                                           (capability-entry-declared-lifetime
                                            formal-leaf))))
              (cons index formal-path)))
          (range (length parameter-leaves)) parameter-leaves))
        result)))

;; 要約がない関数値でも、署名が示す leaf の転送だけは照合できる。
(define (signature-forwarding-summary parameter-types return-type node fail)
  (callable-summary
   (make-list (length parameter-types) #f)
   '()
   (forwarding-leaf-candidates parameter-types return-type node fail)
   (hash)
   (for/list ([type (in-list parameter-types)])
     (define-values (_root leaves)
       (formal-capability-entry type '(formal)))
     leaves)
   ;; 本体を見ていない署名要約は出口イベントを欠くため、局所として扱わない。
   #t))

;; RegionApp が Union member を潰す場合だけ π の member segment を実体化後の
;; 鍵から除く。Record と constructor の segment は型引数を含まない。
(define (instantiate-capability-path type path region-subst)
  (let loop ([current type] [remaining path] [result '()])
    (define normalized (normalize-type (peel-ty current)))
    (cond
      [(null? remaining) result]
      [else
       (define segment (car remaining))
       (match normalized
         [`(Owned ,inner)
          (loop inner remaining result)]
         [`(Untrusted ,inner)
          (loop inner remaining result)]
         [`(Refined ,inner ,_)
          (loop inner remaining result)]
         [`(Record ,row)
          (match segment
            [(cons 'record-field label)
             (define field
               (for/first ([field (in-list row)]
                           #:when (equal? (first field) label))
                 field))
             (and field
                  (loop (second field) (cdr remaining)
                        (append result (list segment))))]
            [_ #f])]
         [`(Union ,_ ,_)
          (define member-type
            (normalize-type (subst-region-params segment region-subst)))
          (and (member member-type (union-members normalized) equal?)
               (loop member-type (cdr remaining)
                     (append result (list member-type))))]
         [_
          (cond
            [(and (pair? segment)
                  (not (eq? (car segment) 'record-field))
                  (exact-nonnegative-integer? (cdr segment)))
             (define constructor
               (for/first ([constructor (in-list (constructor-schema normalized))]
                           #:when (equal? (first constructor) (car segment)))
                 constructor))
             (define field-types (and constructor (second constructor)))
             (and field-types
                  (< (cdr segment) (length field-types))
                  (loop (list-ref field-types (cdr segment)) (cdr remaining)
                        (append result (list segment))))]
            [else
             ;; Union が member 1 個へ正規化された場合、その segment は消える。
             (define member-type
               (normalize-type (subst-region-params segment region-subst)))
             (and (equal? normalized member-type)
                  (loop normalized (cdr remaining) result))])])])))

(define (capability-entry-at-path entry path)
  (let loop ([current entry] [remaining path])
    (cond
      [(not current) #f]
      [(null? remaining) current]
      [else
       (define fields (capability-entry-fields current))
       (and (hash? fields)
            (loop (hash-ref fields (car remaining) #f) (cdr remaining)))])))

(define (actual-leaf-entry Λ expression actual-type actual-path fail)
  (define root-entry
    (typing-capability-of Λ expression #:fail fail #:allow-empty-keys? #t))
  (define root-entry*
    (struct-copy capability-entry root-entry
                 [borrowed-view? (borrow-typed? actual-type)]
                 [source-alphas (capability-source actual-type)]
                 [declared-lifetime (borrow-region actual-type)]))
  (define-values (_actual-root actual-leaves)
    (formal-capability-entry actual-type '(actual)))
  (define metadata (hash-ref actual-leaves actual-path #f))
  (define lifetime
    (and metadata (capability-entry-declared-lifetime metadata)))
  (unless lifetime (fail 'unresolved-borrow-owner expression))
  (define field-entry (capability-entry-at-path root-entry* actual-path))
  (when (and (pair? actual-path)
             (hash? (capability-entry-fields root-entry*))
             (not field-entry))
    (fail 'unresolved-borrow-owner expression))
  ;; 表が無い実引数は全体の capability を使うが、α は選んだ leaf の型だけから得る。
  (define selected (or field-entry root-entry*))
  (define sources
    (if field-entry
        (let ([existing (capability-entry-source-alphas field-entry)])
          (if (set-empty? existing)
              (capability-source `(Borrowed Unit ,lifetime))
              existing))
        (capability-source `(Borrowed Unit ,lifetime))))
  (struct-copy capability-entry selected
               [source-alphas sources]
               [declared-lifetime lifetime]))

(define (keyed-capability-leaf-entries entry fail node)
  (unless (capability-entry? entry)
    (fail 'unresolved-borrow-owner node))
  (define fields (capability-entry-fields entry))
  (if (hash? fields)
      (append-map (lambda (child) (keyed-capability-leaf-entries child fail node))
                  (hash-values fields))
      (if (set-empty? (capability-entry-keys entry))
          '()
          (list (struct-copy capability-entry entry
                             [fields #f]
                             [borrowed-view? #f])))))

(define (recursive-capability-leaf-candidates entry fail node)
  (define selected (keyed-capability-leaf-entries entry fail node))
  (when (null? selected) (fail 'unresolved-borrow-owner node))
  selected)

(define (result-capability-entry summary result-type arguments actuals Λ node fail)
  (define region-subst (callable-summary-region-subst summary))
  (define candidates-by-path
    (for/fold ([result (hash)])
              ([(path candidates)
                (in-hash (callable-summary-result-index summary))])
      (define actual-path
        (instantiate-capability-path result-type path region-subst))
      (unless actual-path (fail 'unresolved-borrow-owner node))
      (hash-update result actual-path
                   (lambda (previous) (append previous candidates))
                   candidates)))
  (define (leaf-entry type path lifetime)
    (define candidates (hash-ref candidates-by-path path '()))
    (unless (pair? candidates) (fail 'unresolved-borrow-owner node))
    (capability-entry-join
     (for/list ([candidate (in-list candidates)])
       (define index (car candidate))
       (define formal-path (cdr candidate))
       (define actual-type (list-ref actuals index))
       (define actual-path
         (instantiate-capability-path actual-type formal-path region-subst))
       (unless actual-path (fail 'unresolved-borrow-owner node))
       (define actual-entry
         (actual-leaf-entry (enter-child Λ (add1 index))
                            (list-ref arguments index) actual-type
                            actual-path fail))
       (define-values (_formal-lifetime sources)
         (with-handlers ([exn:fail?
                          (lambda (_error)
                            (fail 'unresolved-borrow-owner node))])
           (formal-leaf-info summary index formal-path actual-entry)))
       (when (set-empty? (capability-entry-keys actual-entry))
         (fail 'unresolved-borrow-owner node))
       (struct-copy capability-entry actual-entry
                    [fields #f]
                    [borrowed-view? #t]
                    [source-alphas sources]
                    [declared-lifetime lifetime]))))
  (define (aggregate fields)
    (define entries (hash-values fields))
    (capability-entry
     (for/fold ([keys (set)]) ([entry (in-list entries)])
       (set-union keys (capability-entry-keys entry)))
     (for/fold ([variants (set)]) ([entry (in-list entries)])
       (set-union variants (capability-entry-variants entry)))
     fields #f
     (for/fold ([sources (set)]) ([entry (in-list entries)])
       (set-union sources (capability-entry-source-alphas entry)))
     #f))
  (define (lifetimes-in type [seen (set)])
    (define normalized (normalize-type (peel-ty type)))
    (match normalized
      [`(Borrowed ,_ ,lifetime) (set lifetime)]
      [`(BorrowedMut ,_ ,lifetime) (set lifetime)]
      [`(Record ,row)
       (for/fold ([lifetimes (set)]) ([field (in-list row)])
         (set-union lifetimes (lifetimes-in (second field) seen)))]
      [`(Union ,_ ,_)
       (for/fold ([lifetimes (set)]) ([member (in-list (union-members normalized))])
         (set-union lifetimes (lifetimes-in member seen)))]
      [`(Owned ,inner) (lifetimes-in inner seen)]
      [`(Untrusted ,inner) (lifetimes-in inner seen)]
      [`(Refined ,inner ,_) (lifetimes-in inner seen)]
      [_
       (define schema (constructor-schema normalized))
       (if (or (not schema) (set-member? seen normalized))
           (set)
           (for*/fold ([lifetimes (set)])
                       ([constructor (in-list schema)]
                        [field-type (in-list (second constructor))])
             (set-union lifetimes
                        (lifetimes-in field-type
                                      (set-add seen normalized)))))]))
  (define (recursive-capability-upper-bound type)
    (define lifetimes (lifetimes-in type))
    (define-values (_root result-leaves)
      (formal-capability-entry result-type '(result)))
    (define candidate-lifetimes (make-hash))
    (for ([(formal-path candidates)
           (in-hash (callable-summary-result-index summary))])
      (define actual-path
        (instantiate-capability-path result-type formal-path region-subst))
      (unless actual-path (fail 'unresolved-borrow-owner node))
      (define result-leaf (hash-ref result-leaves actual-path #f))
      (unless (capability-entry? result-leaf)
        (fail 'unresolved-borrow-owner node))
      (define lifetime
        (subst-region-params
         (capability-entry-declared-lifetime result-leaf) region-subst))
      (when (and lifetime (set-member? lifetimes lifetime))
        (for ([candidate (in-list candidates)])
          (hash-update! candidate-lifetimes (car candidate)
                        (lambda (previous) (set-add previous lifetime))
                        (set)))))
    (when (zero? (hash-count candidate-lifetimes))
      (fail 'unresolved-borrow-owner node))
    (define candidates
      (append-map
       (lambda (index)
         (define actual-entry
           (typing-capability-of (enter-child Λ (add1 index))
                                 (list-ref arguments index)
                                 #:fail fail #:allow-empty-keys? #t))
         (recursive-capability-leaf-candidates
          actual-entry fail node))
       (hash-keys candidate-lifetimes)))
    (define joined
      (if (null? candidates)
          (capability-entry (set) (set) #f #f (set) #f)
          (capability-entry-join candidates)))
    (struct-copy capability-entry joined
                 [fields #f]
                 [borrowed-view? #f]
                 [declared-lifetime #f]))
  (define (walk type path seen)
    (define normalized (normalize-type (peel-ty type)))
    (match normalized
      [`(Borrowed ,_ ,lifetime) (leaf-entry normalized path lifetime)]
      [`(BorrowedMut ,_ ,lifetime) (leaf-entry normalized path lifetime)]
      [`(Record ,row)
       (aggregate
        (for/hash ([field (in-list row)])
          (define key (cons 'record-field (first field)))
          (values key (walk (second field) (append path (list key)) seen))))]
      [`(Union ,_ ,_)
       (aggregate
        (for/hash ([member (in-list (union-members normalized))])
          (values member (walk member (append path (list member)) seen))))]
      [`(Owned ,inner) (walk inner path seen)]
      [`(Untrusted ,inner) (walk inner path seen)]
      [`(Refined ,inner ,_) (walk inner path seen)]
      [_
       (define schema (constructor-schema normalized))
       (cond
         [(not schema) (capability-entry (set) (set) #f #f (set) #f)]
         [(and (set-member? seen normalized)
               (not (type-carries-capability? normalized)))
          (capability-entry (set) (set) #f #f (set) #f)]
         [(set-member? seen normalized)
          (recursive-capability-upper-bound normalized)]
         [else
          (aggregate
           (for/fold ([fields (hash)]) ([constructor (in-list schema)])
             (for/fold ([fields fields])
                       ([field-type (in-list (second constructor))]
                        [index (in-naturals)])
               (define key (cons (first constructor) index))
               (hash-set fields key
                         (walk field-type (append path (list key))
                               (set-add seen normalized))))))])]))
  (walk result-type '() (set)))

;; §5.4。呼出しの結果が運ぶ借用が、どの実引数の capability を指すのかを表す。
(struct forwarding-summary (index keys source fields variants) #:transparent)

;; §5.4。起点を解く 3 段。第 1 段は region-ctx の token を designator で引き、
;; 第 2 段は関数を通った結果に付く要約を引き、第 3 段は型が運ぶ capability を
;; 読む。Let の束縛位置と実引数の位置がこれを共有する。
(define (argument-source Λ core type index)
  (define designator (peel-node core))
  (define summary
    (or (lookup-forwarding-summary Λ core)
        (lookup-forwarding-summary (enter-child Λ index) core)))
  (or (and (borrow-designator? designator)
           (region-ctx-source Λ designator))
      (and summary (forwarding-summary-source summary))
      (capability-source type)))

;; §5.4。実引数が運ぶ capability。起点と同じ 3 段で引く。
(define (argument-capabilities Λ core index fail)
  (define summary
    (or (lookup-forwarding-summary Λ core)
        (lookup-forwarding-summary (enter-child Λ index) core)))
  (if summary
      (forwarding-summary-keys summary)
      (let ([entry
             (typing-capability-of
              (enter-child Λ index) core #:fail fail
              #:allow-empty-keys? #t)])
        (define (entry-keys entry)
          (if (capability-entry? entry)
              (set-union
               (capability-entry-keys entry)
               (for/fold ([keys (set)])
                         ([child (in-hash-values
                                  (or (capability-entry-fields entry) (hash)))])
                 (set-union keys (entry-keys child))))
              (if (set? entry) entry (set))))
        (define all-keys
          (set-union
           (capability-entry-keys entry)
           (if (hash? (capability-entry-fields entry))
               (for/fold ([all (set)])
                         ([entry (in-hash-values
                                  (capability-entry-fields entry))])
                 (set-union all (entry-keys entry)))
               (set))))
        (when (set-empty? all-keys)
          (fail 'unresolved-borrow-owner core))
        all-keys)))

;; §8.1。使用の要求へ載せる起点。使用の被演算子はいずれも 0 番目の子である。
(define (use-source Λ operand type)
  (argument-source Λ operand type 0))

;; §5.4。雛形の formal 鍵、region、局所 α を呼出し位置へ置き換えて要求を出す。
(define (instantiate-deferred! summary arguments actuals result-type
                               Λ node subst sources Ψ fail)
  (define region-subst (callable-summary-region-subst summary))
  (define deferred (callable-summary-deferred summary))
  (define exits (callable-summary-leaf-exits summary))
  (define exit-classifications (classify-leaf-exits exits))
  (define (event-group event)
    (filter (lambda (candidate)
              (equal? (leaf-exit-key candidate) (leaf-exit-key event)))
            exits))
  (define locals (make-hash))
  (define point (region-ctx-point Λ))
  (define ir (region-ctx-ir Λ))
  (define current-psi Ψ)
  (define (fresh-local α)
    (hash-ref! locals α (lambda () (fresh-local-lifetime!))))
  (define (subst-term t)
    (match t
      [`(RParam ,rp)
       (define mapped (hash-ref region-subst rp #f))
       (cond
         [mapped (subst-term mapped)]
         ;; 内側の Apply が外側の RegionLam の引数をまだ運ぶことがある。
         ;; 外側の雛形 frame に委ね、呼出し位置で実体化した後に収集器が
         ;; 無い場合は、写像の欠落として fail-closed にする。
         [(pair? (template-collectors)) `(RParam ,rp)]
         [else (fail 'unresolved-borrow-owner node)])]
      [_ (cond
           [(lifetime-var? t) (fresh-local t)]
           ;; 遅延した Reborrow の制約は region 項を使う一方、RegionApp の
           ;; 代入表は素の rho 整数を持つ。infer-reborrow と同じ IR ごとの
           ;; 橋を通して整数を戻してから制約を振り分ける。
           [(and ir (exact-nonnegative-integer? t)) (rho->region ir t)]
           [else t])]))
  (define (actual-caps w)
    (hash-ref subst w
              (lambda () (fail 'unresolved-borrow-owner node))))
  (define (reborrow-constraints w child-alpha child-fp)
    (for/list ([item (in-list deferred)]
               #:when (and (deferred-constraint? item)
                           (equal? (deferred-constraint-w item) w)
                           (eq? (region-constraint-kind
                                 (deferred-constraint-constraint item))
                                'reborrow)
                           (equal? (region-constraint-right
                                    (deferred-constraint-constraint item))
                                   child-alpha)
                           (equal? (deferred-constraint-child-fp item)
                                   child-fp)))
      item))
  ;; 遅延した共有借用は Reborrow から来ている。定義時の親は formal capability
  ;; なので通常の infer-reborrow 経路では呼出し側の可変借用をまだ停止できない。
  ;; formal 鍵を実体化した後、対応する遅延制約から親を復元する。
  ;; 遅延要求は呼出し位置の下に置く。関数本体の point はそのまま保つ。
  (define (deferred-point body-point)
    (append point
            (list (length (core-children (peel-node node))))
            body-point))
  (define (event-formal-index event)
    (match (deferred-leaf-exit-source event)
      [`(formal ,index ,_) index]
      [`(binder ,_ ...) (deferred-leaf-exit-formal-index event)]
      [_ #f]))
  (define (event-matches-cap? event cap index origins)
    (define event-index (event-formal-index event))
    (and (exact-nonnegative-integer? event-index)
         (= event-index index)
         (< index (length actuals))
         (let* ([formal-path (deferred-leaf-exit-parent-path event)]
                [actual-type (list-ref actuals index)]
                [actual-path
                 (instantiate-capability-path actual-type formal-path
                                               region-subst)])
           (and actual-path (equal? actual-path (cdr cap))
                (let ([actual-entry
                  (with-handlers ([exn:fail? (lambda (_) #f)])
                        (actual-leaf-entry
                          (enter-child Λ (add1 index))
                          (list-ref arguments index) actual-type actual-path fail))])
                  (and actual-entry
                       (let-values ([(declared-alpha source-alphas)
                                     (with-handlers ([exn:fail?
                                                      (lambda (_) (values #f #f))])
                                       (formal-leaf-info summary index formal-path
                                                        actual-entry))])
                          (cond
                            [(and declared-alpha (set? source-alphas)
                                  (not (set-empty? source-alphas))
                                  (set-member? origins declared-alpha)
                                  (match (deferred-leaf-exit-source event)
                                    [`(formal ,_ ,_)
                                     (equal? declared-alpha
                                            (deferred-leaf-exit-alpha event))]
                                    [`(binder ,_ ...) #t]
                                    [_ #f])
                                  source-alphas)
                             source-alphas]
                            [else #f]))))))))
  (define (local-exit-window cap index alpha)
    (define origins (local-exit-alpha-origins alpha))
    (define event
      (for/first ([event (in-list exits)]
                  #:when (let ([source-alphas
                                (event-matches-cap? event cap index origins)])
                           (and (set? source-alphas)
                                (not (callable-summary-incomplete? summary))
                                (eq? (hash-ref exit-classifications
                                               (leaf-exit-key event)
                                               'fail-closed)
                                     'local)
                                (leaf-exit-local-safe?
                                 (deferred-leaf-exit-source event)
                                 (event-group event) result-type))))
        event))
    (define window (and event (deferred-point '())))
    (define probe (current-local-exit-window-probe))
    (when probe
      (probe cap index alpha origins
             (and event (event-matches-cap? event cap index origins))
             window event))
    window)
  (for ([item (in-list deferred)])
    (cond
      [(borrow-request? item)
       (define w (borrow-request-w item))
       (define caps (actual-caps w))
       (define index (and (formal-key? w) (fourth w)))
       (define child-alpha (subst-term (borrow-request-alpha item)))
       (define reborrow-items
         (reborrow-constraints w (borrow-request-alpha item)
                               (borrow-request-fp item)))
       (for ([cap (in-set caps)])
         (define child-fp
           (append (cdr cap) (borrow-request-fp item)))
         (define local-window
           (and index
                (local-exit-window cap index
                                   (borrow-request-alpha item))))
         (route-request!
          (borrow-request (car cap)
                          child-fp
                          (borrow-request-mode item)
                          child-alpha
                          (borrow-request-rho-borrow item)
                          (borrow-request-node item)
                          (if local-window
                              local-window
                              (and (borrow-request-point item)
                                   (deferred-point
                                    (borrow-request-point item)))))
          node fail)
         (for ([reborrow-item (in-list reborrow-items)])
           (define constraint
             (deferred-constraint-constraint reborrow-item))
           (define parent-term
             (subst-term (region-constraint-left constraint)))
           (define parent-fp
             (append (cdr cap)
                     (deferred-constraint-parent-fp reborrow-item)))
           (define suspension-point
             (deferred-point (region-constraint-point constraint)))
           (define window-point
             (deferred-constraint-window-point reborrow-item))
           (define local-window
             (and index
                  (local-exit-window
                   cap index (region-constraint-left constraint))))
           (define suspension-window
             (or (and window-point (deferred-point window-point))
                 local-window))
           (define parent-alphas
             (for/list ([entry (in-set (psi-mut current-psi))]
                        #:when (and (equal? (first entry) (car cap))
                                    (equal? (second entry) parent-fp)))
               (third entry)))
           (when (null? parent-alphas)
             (set! current-psi
                   (psi-add-mut current-psi (car cap) parent-fp parent-term))
             (set! parent-alphas (list parent-term)))
           (for ([parent-alpha (in-list parent-alphas)])
             (set! current-psi
                   (psi-suspend current-psi
                                (car cap) child-fp
                                parent-alpha child-alpha
                                (borrow-request-mode item)
                                (borrow-request-node item)
                                suspension-point
                                suspension-window)))))]
      [(use-request? item)
       (define w (use-request-w item))
       ;; 遅延した Reborrow が作った局所 alpha を保つ。全ての use source を
       ;; 呼出し側の formal source に置き換えると、子借用の read が停止済みの
       ;; 親借用の read に戻る。雛形 source が空なら formal capability の直接使用
       ;; なので、呼出し側から与えた source へ戻す。
       (define template-source (use-request-source item))
       (define source
         (if (set-empty? template-source)
             (hash-ref sources w '())
             (for/set ([α (in-set template-source)])
               (if (lifetime-var? α) (fresh-local α) α))))
       (define mapped-caps
         (for/set ([cap (in-set (actual-caps w))])
           (cons (car cap) (append (cdr cap) (use-request-fp item)))))
       (when (eq? (use-request-operation item) 'assign)
         (reject-variant-view-write! Λ mapped-caps node fail))
       (for ([cap (in-set mapped-caps)])
          (route-request!
          (use-request (car cap) (cdr cap)
                       (use-request-operation item)
                       source
                       (region-at/branch (region-ctx-ir Λ) point)
                       (deferred-point (use-request-point item))
                       node
                       (use-request-kind item)
                       (use-request-otherwise item))
          node fail))]
      [(deferred-leaf-exit? item) (void)]
      [else
       (define w (deferred-constraint-w item))
       (define c (deferred-constraint-constraint item))
       (define index (and (formal-key? w) (fourth w)))
       (define c-new
         (if (eq? (region-constraint-kind c) 'contains)
             (region-constraint 'contains
                                (subst-term (region-constraint-left c))
                                (region-at (region-ctx-ir Λ) point)
                                point node)
             (region-constraint 'reborrow
                                (subst-term (region-constraint-left c))
                                (subst-term (region-constraint-right c))
                                point node)))
       (define window-point
         (deferred-constraint-window-point item))
       (for ([cap (in-set (actual-caps w))])
         (define local-window
           (and index
                (local-exit-window
                 cap index (region-constraint-left c))))
         (unless (and local-window
                      (eq? (region-constraint-kind c) 'contains))
           (route-constraint!
            c-new (car cap) node fail
            (or local-window
                (and window-point (deferred-point window-point)))
            (append (cdr cap)
                    (deferred-constraint-parent-fp item))
            (append (cdr cap)
                    (deferred-constraint-child-fp item)))))]))
  current-psi)

;; §5.5。呼出しの結果に付く要約を出現ごとに溜める表。
;; 既定の #f は「収集の外」であり、書き込みを黙って捨てる位置と区別する。
(define forwarding-summaries (make-parameter #f))

(define (record-forwarding-summary! Λ node summary fail)
  (define table (forwarding-summaries))
  (when table
    (define key (summary-key Λ node))
    (define previous (hash-ref table key #f))
    (cond
      [(not previous) (hash-set! table key summary)]
      [(equal? previous summary) (void)]
      [else (fail 'unresolved-borrow-owner node)])))

(define (lookup-forwarding-summary Λ node)
  (define table (forwarding-summaries))
  (and table (hash-ref table (summary-key Λ node) #f)))

(define (capability-of-typed-point Λ node)
  (define summary (lookup-forwarding-summary Λ node))
  (and summary
       (capability-entry
        (forwarding-summary-keys summary)
        (or (forwarding-summary-variants summary) (set))
        (forwarding-summary-fields summary)
        (hash-has-key? (forwarding-summary-index summary) '())
        (or (forwarding-summary-source summary) (set))
        #f)))

(define (typing-capability-of Λ core [locals (hash)]
                              #:fail [fail #f]
                              #:allow-empty-keys? [allow-empty-keys? #f])
  (capability-of Λ core locals #:fail fail
                 #:allow-empty-keys? allow-empty-keys?
                 #:apply-entry capability-of-typed-point))

(define current-leaf-exit-capability-reader (make-parameter typing-capability-of))

;; local 窓が実引数の α 起源へ対応したことを試験から確認する。
(define current-local-exit-window-probe (make-parameter #f))

(define (typing-borrow-token-key Λ core [locals (hash)] #:fail [fail #f])
  (borrow-token-key Λ core locals #:fail fail
                    #:apply-entry capability-of-typed-point))

(define (typing-capability-field-entries Λ core [locals (hash)] #:fail [fail #f])
  (capability-field-entries Λ core locals #:fail fail
                            #:apply-entry capability-of-typed-point))

(define (typing-capability-variant-views Λ core [locals (hash)])
  (capability-variant-views Λ core locals
                            #:apply-entry capability-of-typed-point))

;; §5.4。集めた要約の写し。要約は不変な構造体であり、雛形はその欄が持つ
;; 不変な並びである。可変の表そのものは外へ出さない。summary-key の文字列表現
;; で並べ、hash の走査順を外へ漏らさない。
;; 収集器の箱から読む形は採れない。箱は Lam の本体を出た時点で積みから
;; 外れており、入口まで戻ったときには空である。
(define (collected-callable-summaries)
  (define table (callable-summaries))
  (if table
      (map cdr
           (sort (hash->list table)
                 string<?
                 #:key (lambda (entry) (format "~s" (car entry)))))
      '()))

;; 使用の要求を立てる。ir が無い形では借用も無いので何もしない。
;; fp/operation/source/node/kind は要求の契約なので必須にする。
(define (emit-use-request! Λ w fp operation source node kind [otherwise #f]
                           [fail #f])
  (define ir (region-ctx-ir Λ))
  (when ir
    (define r
      (use-request w fp operation source
                   (region-at/branch ir (region-ctx-point Λ))
                   (region-ctx-point Λ) node kind otherwise))
    (if fail (route-request! r node fail) (emit-request! r))))

(define (binder-points+ names point)
  (for/fold ([points (binder-points)]) ([name (in-list names)]
                                         #:when (symbol? name))
    (hash-set points (peel-bind name) point)))

(define (with-binder-points names point thunk)
  (parameterize ([binder-points (binder-points+ names point)])
    (thunk)))

(define (lifetime-vars-in type)
  (let walk ([value type])
    (match value
      [`(RVar ,_) (set value)]
      [(? pair? pair)
       (set-union (walk (car pair)) (walk (cdr pair)))]
      [_ (set)])))

(define (tracked-child-alphas-in type)
  (define tracked (scrutinee-child-alphas))
  (if tracked
      (for*/set ([variable (in-set (lifetime-vars-in type))]
                 [alpha (in-set (alpha-set variable))]
                 #:when (set-member? tracked alpha))
        alpha)
      (set)))

(define (tracked-child-alpha? alpha)
  (define tracked (scrutinee-child-alphas))
  (and tracked
       (for/or ([member (in-set (alpha-set alpha))])
         (set-member? tracked member))))

(define (track-child-alpha! alpha)
  (define tracked (scrutinee-child-alphas))
  (when tracked
    (for ([member (in-set (alpha-set alpha))])
      (set-add! tracked member))))

(define (branch-region-enclosing? ir point)
  (and ir
       (let loop ([ρ (region-at/branch ir point)])
         (and ρ
              (or (branch-region? ir ρ)
                  (loop (region-parent ir ρ)))))))

(define (branch-binder-alpha! decomposition branch-index binder-index)
  (define table (branch-binder-alphas))
  (unless (hash? table)
    (error 'branch-binder-alpha! "型検査の binder alpha 表が無い"))
  (hash-ref! table (list decomposition branch-index binder-index)
             fresh-local-lifetime!))

(define (decomposition-outer-region ir decomposition)
  (region-parent ir (region-at/eliminate ir decomposition)))

(define (emit-decomposition-result! ir decomposition type node fail)
  (when ir
    (define outer (decomposition-outer-region ir decomposition))
    (for ([alpha (in-set (tracked-child-alphas-in type))])
      (emit-constraint!
       (region-constraint 'contains alpha outer decomposition node)))))

(define (emit-decomposition-exit! ir point dest type node fail)
  (when ir
    (for ([decomposition (in-list (region-enclosing-decompositions ir point))]
          #:unless (and dest (path-prefix? decomposition dest)))
      (define outer (decomposition-outer-region ir decomposition))
      (for ([alpha (in-set (tracked-child-alphas-in type))])
        (emit-constraint!
         (region-constraint 'contains alpha outer point node))))))

(define (return-handler-destination boundary type)
  (define operation (erase-core `(Return ,boundary ,type)))
  (for/first ([entry (in-list (return-handler-regions))]
              #:when (equal? operation (third entry)))
    (second entry)))

(define (emit-latent-decomposition-exits! ir point effects node fail)
  (for ([effect (in-list effects)])
    (match effect
      [`(Return ,boundary ,type)
       (emit-decomposition-exit!
        ir point (return-handler-destination boundary type) type node fail)]
      [`(Yield ,type)
       (emit-decomposition-exit! ir point #f type node fail)]
      [_ (void)])))

(define (assign-exit-destination target-capabilities environment)
  (define roots (remove-duplicates (map car (set->list target-capabilities))))
  (match roots
    [(list (? symbol? root))
     (define type (lookup environment root))
     (and type
          (not (borrow-typed? type))
          (hash-ref (binder-points) root #f))]
    [_ #f]))

(define (typing-child-type Λ index)
  (match (typing-child-result Λ index)
    [(list type _normal-type _row _escapes) type]
    [_ #f]))

(define (callable-latent-effects type)
  (match (normalize-type type)
    [`(Owned ,inner) (callable-latent-effects inner)]
    [`(ForallRegion (,_ ...) ,inner) (callable-latent-effects inner)]
    [`(NFn ,_ ,_ ,_ ,effects ,_ ,_) effects]
    [_ '()]))

(define (callable-type-parameter-types type)
  (let loop ([current (normalize-type (peel-ty type))])
    (match current
      [`(Owned ,inner) (loop inner)]
      [`(ForallRegion (,_ ...) ,inner) (loop inner)]
      [`(NFn ,parameters ,_ ,_ ,_ ,_ ,_) parameters]
      [_ '()])))

(define (emit-captured-decomposition-exits! ir point body bound-names
                                            environment node fail)
  (for ([name (in-set (set-subtract (core-free-vars body)
                                    (list->set bound-names)))])
    (define type (lookup environment name))
    (when type
      (emit-decomposition-exit! ir point #f type node fail))))

(define (record-captured-formal-exits! core Λ body bound-names environment fail)
  (for ([name (in-set (set-subtract (core-free-vars body)
                                    (list->set bound-names)))])
    (record-formal-source-exits!
     (enter-child Λ 0) name 'capture
     (lambda (_actual-path _source-path _alpha) (list (peel-node core)))
     fail)
    (define type (lookup environment name))
    (when type
      (record-binder-type-exits!
       type name 'capture
       (lambda (_actual-path _source-path _alpha) (list (peel-node core)))
       fail))))

(define (emit-expression-decomposition-exits! core Λ environment places
                                              callables result-type fail)
  (define ir (region-ctx-ir Λ))
  (when ir
    (define point (region-ctx-point Λ))
    (define (child-type index) (typing-child-type Λ index))
    (define head
      (match (peel-node core)
        [(list (? symbol? name) _ ...) name]
        [_ #f]))
    (define (record-unclassified! child-Λ child source-type)
      (record-formal-source-exits!
       child-Λ child 'unclassified
       (lambda (_actual-path _source-path _alpha) (list #f)) fail)
      (record-binder-type-exits!
       source-type child 'unclassified
       (lambda (_actual-path _source-path _alpha) (list #f)) fail))
    (for ([child (in-list (core-children (peel-node core)))]
          [index (in-naturals)])
      (define exit-kind (leaf-exit-kind-at core Λ index))
      (define child-Λ (enter-child Λ index))
      (cond
        [(eq? exit-kind 'transit) (void)]
        [exit-kind
          (cond
            [(and (eq? head 'Apply) (eq? exit-kind 'formal))
             (define parameter-types
               (callable-type-parameter-types (child-type 0)))
             (define parameter-index (sub1 index))
             (if (< parameter-index (length parameter-types))
                 (begin
                   (record-formal-argument-exits!
                    child-Λ child parameter-index
                    (list-ref parameter-types parameter-index) fail)
                   (record-binder-type-exits!
                    (child-type index) child exit-kind
                    (lambda (_actual _source parent-alpha)
                      (for/list
                          ([path (in-list
                                  (formal-destination-paths
                                   (list-ref parameter-types parameter-index)
                                   parent-alpha))])
                        (list parameter-index path)))
                    fail))
                 (record-unclassified! child-Λ child (child-type index)))]
            [(eq? exit-kind 'local)
             (record-formal-source-exits!
              child-Λ child exit-kind
              (lambda (_actual _source _alpha) (list #f)) fail)
             (record-binder-type-exits!
              (child-type index) child exit-kind
              (lambda (_actual _source _alpha) (list #f)) fail)]
            [(eq? exit-kind 'result)
             (record-formal-source-exits!
              child-Λ child exit-kind
              (lambda (_actual _source alpha)
                (formal-destination-paths result-type alpha))
              fail)
             (record-binder-type-exits!
              (child-type index) child exit-kind
              (lambda (_actual _source parent-alpha)
                (formal-destination-paths result-type parent-alpha))
              fail)]
            [(eq? exit-kind 'handle)
             (match (peel-node core)
               [`(Perform (Return ,_ ,payload-type) ,_)
                (record-formal-source-exits!
                 child-Λ child exit-kind
                 (lambda (_actual _source alpha)
                   (for/list ([path (in-list
                                     (formal-destination-paths payload-type alpha))])
                     (list 'Return path)))
                 fail)
                (record-binder-type-exits!
                 (child-type index) child exit-kind
                 (lambda (_actual _source parent-alpha)
                   (for/list ([path (in-list
                                     (formal-destination-paths payload-type
                                                               parent-alpha))])
                     (list 'Return path)))
                 fail)]
               [_ (record-unclassified! child-Λ child (child-type index))])]
            [else
             (record-formal-source-exits!
              child-Λ child exit-kind
              (lambda (_actual _source _alpha) (list (peel-node core)))
              fail)
             (record-binder-type-exits!
              (child-type index) child exit-kind
              (lambda (_actual _source _alpha) (list (peel-node core)))
              fail)])]
        [else (record-unclassified! child-Λ child (child-type index))]))
    (match (peel-node core)
      [`(Eliminate ,_ ,_)
       (emit-decomposition-result! ir point result-type core fail)]
      [`(EliminateAt ,_ ,_)
       (emit-decomposition-result! ir point result-type core fail)]
      [`(UnionEliminate ,_ ,_)
       (emit-decomposition-result! ir point result-type core fail)]
      [`(UnionEliminateAt ,_ ,_)
       (emit-decomposition-result! ir point result-type core fail)]
      [`(Perform (Return ,boundary ,type) ,_)
       (emit-decomposition-exit!
        ir point (return-handler-destination boundary type)
        (child-type 0) core fail)]
      [`(Yield ,_ ,_)
       (emit-decomposition-exit! ir point #f (child-type 0) core fail)]
      [`(Reassign ,target ,_ ,_)
       (emit-decomposition-exit!
        ir point (hash-ref (binder-points) (peel-bind target) #f)
        (child-type 0) core fail)]
      [`(Assign ,target ,_)
       (define caps
         (typing-borrow-token-key (enter-child Λ 0) target #:fail fail))
       (emit-decomposition-exit!
        ir point (assign-exit-destination caps environment)
        (child-type 1) core fail)]
      [`(AddressOf ,_)
       (emit-decomposition-exit! ir point #f (child-type 0) core fail)]
      [`(Curry ,_ ,_)
       (emit-decomposition-exit! ir point #f (child-type 1) core fail)]
      [`(Lam ,_ ,_ (,parameters ...) ,body)
       (emit-captured-decomposition-exits!
        ir point body parameters environment core fail)
       (record-captured-formal-exits! core Λ body parameters environment fail)]
      [`(RecurVal ,_ ,function (,parameters ...) ,body)
       (emit-captured-decomposition-exits!
        ir point body (cons function parameters) environment core fail)
       (record-captured-formal-exits!
        core Λ body (cons function parameters) environment fail)]
      [`(Recur ,_ ,function (,parameters ...) ,body ,_continuation)
       (record-captured-formal-exits!
        core Λ body (cons function parameters) environment fail)]
      [`(Apply ,function ,arguments ...)
       (define function-type (child-type 0))
       (emit-latent-decomposition-exits!
        ir point (callable-latent-effects function-type) core fail)
       (for ([index (in-range 1 (add1 (length arguments)))])
         (emit-decomposition-exit!
          ir point #f (child-type index) core fail))]
      [`(RegionApp ,_ ,_)
       (emit-latent-decomposition-exits!
        ir point (callable-latent-effects result-type) core fail)]
      [`(Recur ,callable ,_ ,_ ,_ ,_)
       (emit-latent-decomposition-exits!
        ir point (callable-latent-effects
                  (callable-signature callables callable))
        core fail)]
      [_ (void)])))

;; §3.2。親の書込みが variant segment より手前なら、その view が生きる間は拒む。
(define (reject-variant-view-write! Λ target-capabilities node fail)
  (when
      (for/or ([target-cap (in-set target-capabilities)])
        (for/or ([view (in-set (region-ctx-variant-views Λ))])
          (and (equal? (car target-cap) (car view))
               (path-prefix? (cdr target-cap) (cdr view))
               (not (equal? (cdr target-cap) (cdr view))))))
    (fail 'borrow-conflicting-use node)))

;; spec §5.6。RegionApp の実引数は借用の使用要求とは別に集め、段 3 で
;; σ を解いた後に生存を検査する。
(struct region-arg-request (rho point node bound) #:transparent)
(define region-arg-collector (make-parameter #f))

(define (emit-region-arg-request! rho point node)
  (define collector (region-arg-collector))
  (unless collector
    (error 'emit-region-arg-request!
           "region-arg-collector が parameterize されていない: ~s" node))
  ;; spec §5.6。束縛中かどうかは発行した時点で決まる。段 3 では
  ;; RegionLam を降りた文脈が残っていないので、ここで写しを採る。
  (set-box! collector
            (cons (region-arg-request rho point node (bound-region-params))
                  (unbox collector))))

(define (collected-region-args)
  (define collector (region-arg-collector))
  (if collector (reverse (unbox collector)) '()))

;; 段 3。実引数の region が適用位置で生きていることを確認する。
;; spec §5.6。実引数が束縛中の (RParam rp) である場合は判定を通さない。
;; rp を束縛する RegionLam の本体は、rp へ渡る具体的な region が生きて
;; いる位置でしか評価されない。適用位置はその内側なので生存は保たれる。
;; 外側の RegionApp が既に検査しているため、ここで再び呼ぶ必要はない。
(define (check-region-args ir sigma requests relation fail)
  (for ([request (in-list requests)])
    (define raw (region-arg-request-rho request))
    (define bound-here?
      (match raw
        [`(RParam ,rp)
         (set-member? (region-arg-request-bound request) rp)]
        [_ #f]))
    (unless bound-here?
      (cond
        ;; 構成検査は materialize 後の具体的な ρ を受け取るため、ir の
        ;; 無い状態から point の生存を再検査しない。
        [(and (deriving-config?) (not ir)) (void)]
        [(not ir)
         (fail 'region-arg-not-live (region-arg-request-node request))]
        [else
         (define rho (subst-type-regions raw sigma ir))
         (define at
           (region->rho ir
                        (region-at ir (region-arg-request-point request))))
         (unless (relation rho at)
           (fail 'region-arg-not-live (region-arg-request-node request)))]))))

;; 段 2。下限制約から σ を作る。spec §6.1。
;; ir が無い形では借用が立たないので、制約も空であり σ も空である。
(define (typing-solve ir constraints)
  (if ir
      (region-solve ir constraints)
      (list 'ok (hash))))

;; σ を読む唯一の窓口。寿命変数なら引き、具体的な region ならそのまま返す。
(define (sigma-ref σ t)
  (if (lifetime-var? t)
      (hash-ref σ (lifetime-var-index t))
      t))

;; 型が運び手である（spec §5.1）。
;; point π で推論した型の中に α が現れるなら region-at ir π は α の下限である。
;; 値の流れを別に追う解析を書くと、型の側と二重に管理することになる。
(define (collect-use-regions-at! type ir ρ point [scrutinee-child-ρ #f])
  (when (and ir ρ (lifetime-collector))
    (let walk ([t type])
      (match t
       [`(RVar ,k)
        (define alpha `(RVar ,k))
        (define lower-bound
          (if (tracked-child-alpha? alpha)
              (or scrutinee-child-ρ (region-at/branch ir point))
              ρ))
        (emit-constraint!
         (region-constraint 'contains alpha lower-bound point #f))]
        [(? list? ts) (for-each walk ts)]
        [_ (void)]))))

(define (collect-use-regions! type ir point)
  (collect-use-regions-at! type ir (and ir (region-at/branch ir point)) point
                           (and ir
                                (if (region-decomposition-scrutinee? ir point)
                                    (region-at/eliminate ir point)
                                    (region-at/branch ir point)))))

;; 寿命変数の採番（spec §3.2）。借用の項 1 つにつき 1 つ作る。
;; 番号は走査の順に依存するため、診断の本文へ番号を出してはならない
;; （region.md §2 の識別子の不透明性）。
(define lifetime-counter (make-parameter #f))
(define alpha-table (make-parameter #f))
(define mut-binding-types-table (make-parameter #f))
(define callable-contexts-table (make-parameter #f))
(define resource-place-set (make-parameter (set)))
(define resource-identity-transfers (make-parameter (set)))
(define declared-place-types (make-parameter '()))

(define (with-place-shadowing names thunk)
  (define shadowed (list->set names))
  (parameterize ([resource-place-set
                  (set-subtract (resource-place-set) shadowed)]
                 [resource-identity-transfers
                  (set-subtract (resource-identity-transfers) shadowed)])
    (thunk)))

(define (with-let-place name type thunk)
  (define outer (set-remove (resource-place-set) name))
  (parameterize ([resource-place-set
                  (if (resource-type? type) (set-add outer name) outer)]
                 [resource-identity-transfers
                  (set-remove (resource-identity-transfers) name)])
    (thunk)))

(define (with-resource-identity-transfers names thunk)
  (parameterize ([resource-identity-transfers
                  (set-union (resource-identity-transfers)
                             (list->set names))])
    (thunk)))

(define (with-identity-transfer name thunk)
  (with-resource-identity-transfers (list name) thunk))

(define (record-effective-let-type! Λ type [force? #f])
  (when (or force? (resource-type? type))
    (define table (mut-binding-types-table))
    (when table
      (define point (region-ctx-point Λ))
      ;; Recur の固定点や infer/check の再走査では同じ構文位置を複数回
      ;; 検査する。実行用注釈には最後に成功した走査の有効型を残す。
      (set-box! table (hash-set (unbox table) point type)))))

;; §5.4。alpha-table へ登録せずに寿命変数だけを採る。
(define (fresh-local-lifetime!)
  (define c (lifetime-counter))
  (define k (unbox c))
  (set-box! c (add1 k))
  `(RVar ,k))

(define (fresh-lifetime! point)
  (define table (alpha-table))
  (define merge-point? (and (pair? point) (eq? (car point) 'merge)))
  (define prior (and table (not merge-point?)
                     (hash-ref (unbox table) point #f)))
  (or prior
      (let ([α (fresh-local-lifetime!)])
        ;; 再走査は同じ AST point の借用を同じ寿命変数で表す。これにより
        ;; Recur の Ψ 固定点が検査のたびに新しい α を増やさず、alpha-table
        ;; が表す「構文位置ごとに一つの α」という契約も保つ。
        (unless merge-point?
          (when table (set-box! table (hash-set (unbox table) point α))))
        α)))

(define (lookup table key)
  (match (assoc key table)
    ;; P1c2b。環境 entry は mut のとき 3 要素になる。places の表は 2 要素の
    ;; ままであり、同じ形で両方から値を取る。
    [(list _ value _ ...) value]
    [_ #f]))

;; §4.6。lookup は assoc の結果から値だけを取り出すので、対の同一性が
;; 呼出し側へ届かない。重ねの照合はこの手続きだけを使う。包み直さない。
(define (lookup-binding table key)
  (assoc key table))

(define (record-type? type)
  (match type
    [`(Record ,_) #t]
    [_ #f]))

(define (row-union left right)
  (for/fold ([combined left])
            ([label (in-list right)])
    (if (for/or ([existing (in-list combined)]) (effect-equiv? existing label))
        combined
        (append combined (list label)))))

(define (rows-union rows)
  (for/fold ([combined '()])
            ([row (in-list rows)])
    (row-union combined row)))

(define (row-difference row removed)
  (for/list ([label (in-list row)]
             #:unless (for/or ([r (in-list removed)]) (effect-equiv? r label)))
    label))

(define (row-subset? left right)
  (for/and ([label (in-list left)])
    (for/or ([r (in-list right)]) (effect-equiv? r label))))

;; spec §4.3。引数の Effect のうち εin が受理するものを落とし、εout を足す。
(define (combine argument-row εin εout)
  (row-union (row-difference argument-row εin) εout))

(define (row=? left right)
  (row-equiv? left right))

;; VAR-001..003: checking は elaboration と同じ compat? を全型で共有する。
;; Never の bottom 受理は compat? の Never 分岐が担う。
;; RFN-003: discharge に使う文脈は大域の Γ_pc⁰ に限る。merge の W は渡さない。
;; region どうしの関係は current-region-relation から取る。既定は equal? で
;; あり、region 引数を書かない programme の判定は変わらない。
;; Union tag 保存互換で値の受け渡しを判定する。
(define (type-compatible? actual expected)
  (tag-compat? actual expected (current-Γ-pc0) (current-region-relation)))

(define (type? value)
  (and (redex-match? G2m τ value)
       (type-shape-ok? value)
       (type-normal? value)))

(define (row? value)
  (and (redex-match? G2m ε value)
       (effect-row-normal? value)))

(define (callable-id? value)
  (redex-match? G1 cid value))

(define (unique-table? table)
  (and (list? table)
       (andmap (λ (entry)
                 (and (list? entry) (= (length entry) 2)))
               table)
       (not (check-duplicates (map first table)))))

(define (unique-heap? heap)
  (and (list? heap)
       (not (check-duplicates (map first heap)))
       (for/and ([entry (in-list heap)])
         (match entry
           [(list _ _) #t]
           [(list _ _ `(declared ,type)) (type? type)]
           [_ #f]))))

(define (valid-places? places)
  (and (unique-table? places)
       (for/and ([entry (in-list places)])
         (match entry
           [(list (? exact-nonnegative-integer?) type)
            (type? type)]
           [_ #f]))))

;; 一番外の位置より内側に ForallRegion が現れないか。
;; type? は redex の τ を見るだけであり、ForallRegion をどの位置にも許す。
;; type-shape-ok? も ForallRegion の本体へ素通しで降りるだけである。
;; そのため入れ子を入口で落とすのはこの検査の仕事である。
(define (forall-region-free? type)
  (let walk ([type type] [visited (set)])
    (match type
      [`(ForallRegion ,_ ,_) #f]
      [`(Data ,name (,arguments ...))
       (define key (cons name arguments))
       (define schema (data-schema name arguments))
       (and schema
            (or (set-member? visited key)
                (for/and ([field (in-list (data-field-types name arguments))])
                  (walk field (set-add visited key)))))]
      [(? list? parts)
       (andmap (lambda (part) (walk part visited)) parts)]
      [_ #t])))

(define (valid-callables? callables)
  (and (unique-table? callables)
       (for/and ([entry (in-list callables)])
         (match entry
           [(list callable signature)
            (and (callable-id? callable)
                 (type? signature)
                 (match signature
                   [`(NFn ,_ ,_ ,_ ,_ ,_ ,_) (forall-region-free? signature)]
                   [`(ForallRegion (,rps ...) (NFn ,_ ,_ ,_ ,_ ,_ ,_))
                    (and (andmap symbol? rps)
                         (forall-region-free? (third signature)))]
                   [_ #f]))]
           [_ #f]))))

;; callables の署名から ForallRegion の包みを 1 段剥がす。
;; 剥がした本体の (RParam rp) は、context が渡した付け替え後の名前へ位置で
;; 対応させる。context が無い形と束縛の数が合わない形は #f を返す。
(define (unwrap-forall-region signature context)
  (match signature
    [`(ForallRegion (,rps ...) ,body)
     (and (list? context)
          (= (length rps) (length context))
          (subst-region-params
           body
           (for/hash ([rp (in-list rps)] [name (in-list context)])
             (values rp `(RParam ,name)))))]
    [_ #f]))

(define (valid-environment? environment)
  (and (list? environment)
       (for/and ([entry (in-list environment)])
         (match entry
           [(list (? symbol?) type) (type? type)]
           ;; P1c2b。mut を宣言した Let だけが 3 要素の entry を作る。
           [(list (? symbol?) type (? symbol? mode))
            (and (type? type) (memq mode '(const let mut)) #t)]
           [_ #f]))))

;; P1c2b。modes を渡すと (name type mode) の 3 要素 entry を作る。省略すると
;; 従来どおり 2 要素である。mut 以外の mode を運ぶ必要は無いので、呼出し側は
;; mut のときだけ modes を渡す。
(define (extend environment names types [modes #f])
  (append (if modes
              (map list names types modes)
              (map list names types))
          environment))

;; P1c2b。3 要素 entry の mode を返す。2 要素 entry と未束縛には #f を返す。
;; 呼出し側は #f を「再代入できない」として扱う。
(define (binding-mode-of environment name)
  (match (assoc name environment)
    [(list _ _ mode) mode]
    [_ #f]))

(define (without-owned environment)
  ;; OWN-009。高々一回の資源を運ぶ外側の値は、閉包や再帰関数へ
  ;; 暗黙に複製できない。仮引数として明示的に受け取る場合は呼出し側が
  ;; 供給するので、function-body-environment で後から追加する。
  (filter (λ (entry) (not (resource-type? (second entry))))
          environment))

;; G5c5b1 spec §7 と §8。本体の環境を作る。Owned<τ> の仮引数は payload の型
;; τ で束縛する。生名は本体から直接見えず、生成した Let が surface の名前へ
;; Owned<τ> を与えるためである。E-Var は Owned<_> の変数を裸で参照すること
;; を禁じており、生名を Owned<τ> で入れると Let の右辺の参照が落ちる。
;; 外側の環境から資源型の項目を落とす。資源型の捕捉は
;; elaborate が Curry の固定引数へ変換するため、この補助は外側の Owned を
;; 本体へ直接見せない。
(define (function-body-environment environment parameters parameter-types)
  (extend (without-owned environment)
          parameters
          (for/list ([type (in-list parameter-types)])
            (match type
              [`(Owned ,payload) payload]
              [_ type]))))

;; 項のどこかにその記号が現れるかを見る。束縛の位置も数える。
(define (core-mentions? core name)
  (let walk ([t (erase-core core)])
    (cond
      [(match t [`(RecurVal ,_ ,_ ,_ ,_) #t] [_ #f])
       ;; 展開後の再帰値は、その内部の lexical binder だけを除いて capture を数える。
       (set-member? (core-free-vars t) name)]
      [(eq? t name) #t]
      [(pair? t) (or (walk (car t)) (walk (cdr t)))]
      [else #f])))

;; G5c5b1 spec §8。資源型の仮引数を本体の形で符号化した Typed Core を
;; 検査する。parameters は Lam または Recur の仮引数列であり、資源型の位置
;; には生名が入っている。inner は本体を包む Scope の直下の計算である。
;;
;; 条件を満たさない Typed Core は拒否する。値の形から生名を推測して救う
;; ことはしない。手で書いた不正な Core をここで止める。
(define (resource-encoding-missing-key type)
  (if (owned-type? type)
      'owned-parameter-missing-binding
      'resource-binder-missing-binding))

(define (resource-encoding-raw-key type)
  (if (owned-type? type)
      'owned-raw-parameter-misuse
      'resource-binder-raw-misuse))

(define (resource-encoding-outer-missing-key parameter-types)
  (if (ormap (λ (type)
               (and (resource-type? type) (not (owned-type? type))))
             parameter-types)
      'resource-binder-missing-binding
      'owned-parameter-missing-binding))

(define (check-owned-encoding parameters parameter-types inner node fail
                              #:missing-key
                              [missing-key resource-encoding-missing-key]
                              #:raw-key
                              [raw-key resource-encoding-raw-key])
  (define resource-positions
    (for/list ([name (in-list parameters)]
               [type (in-list parameter-types)]
               #:when (resource-type? type))
      (list name type)))
  (define reserved (list->set parameters))
  (define body
    (let loop ([pending resource-positions] [core inner] [seen '()])
      (cond
        [(null? pending) core]
        [else
         (match-define (list raw declared) (first pending))
         (match (peel-node core)
           [`(Let (,binder-node ,binding-mode ,type-node) ,bound-node ,next)
            (define binder (peel-bind binder-node))
            ;; binder は仮引数のどの名前とも衝突せず、連なりの中で一意で
            ;; ある。衝突を許すと、生名を握り直す形や同じ名前を二度束縛
            ;; する形が通ってしまう。
            (unless (and (eq? (peel-node bound-node) raw)
                         (eq? binding-mode 'let)
                         (type-equiv? (peel-ty type-node) declared)
                         (not (set-member? reserved binder))
                         (not (memq binder seen)))
              (fail (missing-key declared) node))
            (loop (cdr pending) next (cons binder seen))]
           [_ (fail (missing-key declared) node)])])))
  ;; RecurVal 内では展開が同じ名前を埋め込むため、自身の lexical binder に
  ;; 束縛された出現を除き、それ以外では従来どおり束縛位置も数える。
  (for ([entry (in-list resource-positions)])
    (when (core-mentions? body (first entry))
      (fail (raw-key (second entry)) node)))
  body)

(define (forward-transfer-form? core mode)
  (match (peel-node core)
    [(? symbol?) #t]
    [`(Forward ,_) #t]
    [`(Discharge ,(app peel-node
                      `(ProofRep ,_ (RemainderSafelyDropped ,_ ,_))) ,inner)
     (forward-transfer-form? inner mode)]
    [`(Curry ,function ,argument)
     (and (match (peel-node function)
            [`(Lam ,_ ,_ ,_ ,_) #t]
            [_ #f])
          (not (forward-containing-now? function))
          (or (symbol? (peel-node argument))
              (and (eq? mode 'config)
                   (redex-match? G2m v (erase-core argument)))))]
    [`(UnionInject ,_ ,_ ,inner) (forward-transfer-form? inner mode)]
    [`(Rec ((,_ ,_ ,fields) ...))
     (andmap (lambda (field) (forward-transfer-form? field mode)) fields)]
    [`(Construct ,_ ,_ ,fields ...)
     (andmap (lambda (field) (forward-transfer-form? field mode)) fields)]
    [`(RecRewrite ,target (,entries ...))
     (and (forward-transfer-form? target mode)
          (andmap (lambda (entry)
                    (forward-transfer-form? (last entry) mode))
                  entries))]
    [`(RecRewriteOpen ,_)
     (eq? mode 'config)]
    [`(UnionEliminate ,scrutinee (,branches ...))
     (and (forward-transfer-form? scrutinee mode)
          (andmap (lambda (branch)
                    (match (peel-forward-union-branch branch)
                      [`(,_ ,_ -> ,body)
                       (forward-transfer-form? body mode)]
                      [_ #f]))
                  branches))]
    [`(UnionEliminateAt ,scrutinee (,branches ...))
     (define-values (plain-branches _regions)
       (peel-annotated-union-branches branches))
     (forward-transfer-form? `(UnionEliminate ,scrutinee ,plain-branches)
                             mode)]
    [`(Let (,_ let ,_) ,bound ,body)
     (and (forward-transfer-form? bound mode)
          (forward-transfer-form? body mode))]
    [`(Scope ,managed ,body)
     (and (list? managed)
          (or (eq? mode 'config) (null? managed))
          (forward-transfer-form? body mode))]
    [_ (redex-match? G2m v (erase-core core))]))

(define (peel-forward-union-branch branch)
  (match (peel-branch branch)
    [`(,member ,binder -> ,body)
     (list (peel-ty member) (peel-bind binder) '-> body)]
    [_ #f]))

(define (forward-containing-now? core)
  (match (peel-node core)
    [`(Forward ,_) #t]
    [`(Lam ,_ ,_ ,_ ,_) #f]
    [`(RecurVal ,_ ,_ ,_ ,_) #f]
    [`(RegionLam ,_ ,_) #f]
    [_ (for/or ([child (in-list (core-children (peel-node core)))])
         (forward-containing-now? child))]))

(define (callable-signature callables callable)
  (cond
    [(not (inst-cid? callable)) (lookup callables callable)]
    [(not (deriving-config?)) #f]
    [else
     (define pairs (cid-pairs callable))
     (define keys (map first pairs))
     (define raw (lookup callables (cid-base callable)))
     (and (not (check-duplicates keys))
          raw
          (let ([table
                 (for/hash ([pair (in-list pairs)])
                   (values (first pair) (second pair)))])
            (match* (raw (cid-poly callable))
              [(`(ForallRegion (,rps ...) ,body) 'Mono)
               (and (andmap (lambda (rp) (hash-has-key? table rp)) rps)
                    (subst-region-params body table))]
              [(`(ForallRegion (,rps ...) ,_) `(Poly (,own ...)))
               (and (equal? rps own)
                    (subst-region-params raw table))]
              [(_ 'Mono) (subst-region-params raw table)]
              [(_ _) #f])))]))

(define (callable-context raw-signature kind)
  (define-values (binders body)
    (match raw-signature
      [`(ForallRegion (,rps ...) ,inner) (values rps inner)]
      [_ (values '() raw-signature)]))
  (define forall?
    (match raw-signature [`(ForallRegion ,_ ,_) #t] [_ #f]))
  (define context (region-binder-context))
  (define bound
    (if (and (eq? kind 'lam) (pair? binders))
        (begin
          (unless (and (list? context) (= (length binders) (length context)))
            (error 'callable-context
                   "受理された Lam の region binder が一致しない: ~s ~s"
                   binders context))
          (map (lambda (rp name) (list rp `(RParam ,name))) binders context))
        '()))
  (define free
    (for/list ([rp (in-set (region-free-params body))]
               #:unless (memq rp binders))
      (list rp `(RParam ,(resolve-region-param rp)))))
  (values (append bound (sort free symbol<? #:key first))
          (if (and forall? (eq? kind 'recur))
              (list 'Poly binders)
              'Mono)))

(define (record-callable-context! Λ signature kind)
  (define box (callable-contexts-table))
  (when box
    (define-values (renamed-pairs poly) (callable-context signature kind))
    (define forall?
      (match signature [`(ForallRegion ,_ ,_) #t] [_ #f]))
    (when (or forall? (pair? renamed-pairs))
      (define source-pairs
        (for/list ([pair (in-list renamed-pairs)])
          (match pair
            [`(,rp (RParam ,fresh))
             (list rp `(RParam ,(region-param-origin fresh)))]
            [_ pair])))
      (define point (region-ctx-point Λ))
      (define entry (list renamed-pairs source-pairs poly))
      (define current (unbox box))
      (when (and (hash-has-key? current point)
                 (not (equal? (hash-ref current point) entry)))
        (error 'record-callable-context!
               "同じ callable 位置が異なる文脈で推論された: ~s" point))
      (set-box! box (hash-set current point entry)))))

(define (callable-parameter-types callables callable)
  (let loop ([signature (callable-signature callables callable)])
    (match signature
      [`(ForallRegion (,_ ...) ,body) (loop body)]
      [`(NFn (,parameters ...) ,_ ,_ ,_ ,_ ,_) parameters]
      [_ '()])))

(define (forward-transfer-binders parameters parameter-types body)
  (define pending
    (for/list ([parameter (in-list parameters)]
               [type (in-list parameter-types)]
               #:when (resource-type? type))
      parameter))
  (if (null? pending)
      '()
      (match (peel-node body)
        [`(Handle ,_ ,_ ,scope)
         (match (peel-node scope)
           [`(Scope () ,inner)
            (let loop ([names pending] [term inner])
              (cond
                [(null? names) '()]
                [else
                 (match (peel-node term)
                   [`(Let (,binder let ,_) ,_ ,next)
                    (cons (peel-bind binder)
                          (loop (cdr names) next))]
                   [_ '()])]))]
           [_ '()])]
        [_ '()])))

(define (identity-forward-handler? handler)
  (match (peel-branch handler)
    [`(,binder -> ,body)
     (equal? (peel-node body) (peel-bind binder))]
    [_ #f]))

;; Forward の局所的な条件は、型付けが通った項を一度走査して検査する。
;; usage は binder identity ごとの、その経路での最大 Forward 回数である。
(define (forward-invalid-node core callables [mode 'static] [states '()])
  (define invalid #f)
  (define (reject! node)
    (unless invalid (set! invalid node)))
  (define (bind env name identity)
    (cons (cons name identity)
          (filter (lambda (entry) (not (equal? name (car entry)))) env)))
  (define (usage-add left right node)
    (for/fold ([result left]) ([identity (in-list (hash-keys right))])
      (define previous (hash-ref result identity '(0 #f)))
      (define next (hash-ref right identity))
      (define count (+ (first previous) (first next)))
      (when (> count 1) (reject! node))
      (hash-set result identity
                (list count (or (second previous) (second next))))))
  (define (usage-max left right)
    (for/fold ([result left]) ([identity (in-list (hash-keys right))])
      (define previous (hash-ref result identity '(0 #f)))
      (define next (hash-ref right identity))
      (if (> (first next) (first previous))
          (hash-set result identity next)
          result)))
  (define (scan-sequential terms env allowed in-transfer?
                           local-lets? pending mode node)
    (for/fold ([usage (hash)]) ([term (in-list terms)])
      (usage-add usage
                 (scan term env allowed in-transfer? local-lets?
                       pending mode)
                 node)))
  (define (scan-result-tail term env allowed tail-allowed pending mode)
    (define node (peel-node term))
    (define result-allowed (set-union allowed tail-allowed))
    ;; 式全体が T なら、E_tail より先に一つの転送形として検査する。
    (if (and (forward-containing-now? node)
             (forward-transfer-form? node mode))
        (scan term env result-allowed #t #t pending mode)
        (match node
      [`(Handle ,_op ,handler ,body)
       (if (identity-forward-handler? handler)
           (usage-add
            (match (peel-branch handler)
              [`(,binder -> ,handler-body)
               (scan handler-body (bind env (peel-bind binder) #f)
                     allowed #f #t '() mode)]
              [_ (hash)])
            (scan-result-tail body env allowed tail-allowed pending mode)
            term)
           (scan term env allowed #f #f '() mode))]
      [`(Scope ,managed ,body)
       (if (and (list? managed)
                (or (eq? mode 'config) (null? managed)))
           (scan-result-tail body env allowed tail-allowed pending mode)
           (scan term env allowed #f #f '() mode))]
      [`(Let (,binder ,binding-mode ,type) ,bound ,body)
       (define name (peel-bind binder))
       (define declared (peel-ty type))
       (define transfer-binding?
         (and (pair? pending) (eq? name (first (first pending)))))
       (when (and (pair? pending) (not transfer-binding?))
         (reject! term))
       (define local-binding?
         (and (not transfer-binding?)
              (eq? binding-mode 'let)
              (resource-type? declared)))
       ;; config mode では β 簡約直後の値束縛が R-LetOwned 前に現れる。
       (define runtime-transfer-binding?
         (and (eq? mode 'config)
              (not transfer-binding?)
              (eq? binding-mode 'let)
              (resource-type? declared)
              (forward-containing-now? body)
              (redex-match? G2m v (erase-core bound))))
       (define identity
         (cond
           [transfer-binding? (second (first pending))]
           [runtime-transfer-binding? (gensym 'forward-runtime-result)]
           [local-binding? (gensym 'forward-result)]
           [else #f]))
       (define body-allowed
         (if runtime-transfer-binding?
             (set-add allowed identity)
             allowed))
       (define body-tail-allowed
         (if identity (set-add tail-allowed identity) tail-allowed))
      (usage-add
        ;; E_tail の binder は、その束縛式では通常の Forward 文脈に入らない。
        (scan bound env allowed #f #t '() mode)
        (scan-result-tail
         body (bind env name identity)
         body-allowed
         body-tail-allowed
         (if transfer-binding? (cdr pending) '()) mode)
        term)]
      [`(UnionEliminate ,scrutinee (,branches ...))
       (define branch-children (rest (core-children node)))
       (define branch-usages
         (for/list ([branch (in-list branches)]
                    [child (in-list branch-children)])
           (match (peel-forward-union-branch branch)
             [`(,_member ,binder -> ,body)
              (scan-result-tail body (bind env (peel-bind binder) #f)
                                allowed tail-allowed pending mode)]
             [_ (scan child env (set) #f #f '() mode)])))
       (usage-add
        ;; scrutinee は E_tail の binder 文脈から独立して走査する。
        (scan scrutinee env allowed #f #t '() mode)
        (for/fold ([usage (hash)]) ([branch (in-list branch-usages)])
          (usage-max usage branch))
        term)]
      [`(UnionEliminateAt ,scrutinee (,branches ...))
       (define-values (plain-branches _regions)
         (peel-annotated-union-branches branches))
       (scan-result-tail `(UnionEliminate ,scrutinee ,plain-branches)
                         env allowed tail-allowed pending mode)]
      [`(Apply ,_function ,_arguments ...)
       ;; Apply 自体が結果でも、Forward はその引数位置の条件で検査する。
       (scan term env result-allowed #f #t '() mode)]
       [_
        ;; 許可された E_tail から外れた式は通常走査へ戻す。
        ;; config では、その部分式の内側に別の関数境界が残ることがある。
        (when (pair? pending) (reject! term))
        (scan term env allowed #f #f '() mode)])))
  (define (scan term env allowed in-transfer? local-lets? pending mode
                [result-root? #f])
    (define node (peel-node term))
    (match node
      [`(Forward ,target)
       (cond
         [(not in-transfer?) (reject! term) (hash)]
         [(symbol? (peel-node target))
          (define identity (cdr (or (assoc (peel-node target) env)
                                    (cons #f #f))))
          (if (and identity (set-member? allowed identity))
              (hash identity (list 1 term))
              (begin (reject! term) (hash)))]
         [(and (eq? mode 'config)
               (exact-nonnegative-integer? (peel-node target))
               (eq? (second (or (assoc (peel-node target) states)
                                (list #f #f)))
                    'Available))
          (define identity
            (cdr (or (assoc (peel-node target) env) (cons #f #f))))
          (if (and identity (set-member? allowed identity))
              (hash identity (list 1 term))
              (begin (reject! term) (hash)))]
         [else (reject! term) (hash)])]
      [(? symbol? name)
       (define identity (cdr (or (assoc name env) (cons #f #f))))
       ;; T の外にある通常の資源読み取りは Forward の gate で制限しない。
       (when (and in-transfer? identity (set-member? allowed identity))
         (reject! term))
       (hash)]
      [`(Apply ,function ,arguments ...)
       (define has-forward?
         (ormap forward-containing-now? (cons function arguments)))
       (when (and has-forward?
                  (not (and (or (redex-match? G2 x (peel-node function))
                                (and (eq? mode 'config)
                                     (redex-match? G2m v
                                                   (erase-core function))))
                            (andmap (lambda (argument)
                                      (forward-transfer-form? argument mode))
                                    arguments))))
         (reject! term))
       (usage-add
        (scan function env allowed #f local-lets? '() mode)
        (scan-sequential arguments env allowed has-forward?
                         local-lets? '() mode term)
        term)]
      [`(Let (,binder ,binding-mode ,type) ,bound ,body)
       (define name (peel-bind binder))
       (define declared (peel-ty type))
       (define transfer-binding?
         (and (pair? pending) (eq? name (first (first pending)))))
       (when (and (pair? pending) (not transfer-binding?))
         (reject! term))
       (define local-binding?
         (and (not transfer-binding?)
              in-transfer?
              local-lets?
              (eq? binding-mode 'let)
              (resource-type? declared)))
       ;; R-Beta の直後から R-LetOwnedB までは、転送 Let の binder が
       ;; 一時的に変数として残る。値から新しい identity を作って検査する。
       (define runtime-transfer-binding?
         (and (eq? mode 'config)
              (not in-transfer?)
              (eq? binding-mode 'let)
              (resource-type? declared)
              (forward-containing-now? body)
              (redex-match? G2m v (erase-core bound))))
       (define identity
         (cond
           [transfer-binding? (second (first pending))]
           [local-binding? (gensym 'forward-local)]
           [runtime-transfer-binding? (gensym 'forward-runtime)]
           [else #f]))
       (define body-env (bind env name identity))
       (define body-allowed
         (if identity (set-add allowed identity) allowed))
       (usage-add
        (scan bound env allowed in-transfer? local-lets? '() mode)
        (scan body body-env body-allowed in-transfer? local-lets?
              (if transfer-binding? (cdr pending) '()) mode)
        term)]
      [`(Lam ,_ ,callable (,parameters ...) ,body)
       (define names (map peel-bind parameters))
       (define parameter-types (callable-parameter-types callables callable))
       (define owner? (ormap resource-type? parameter-types))
       (define transfer-names
         (forward-transfer-binders names parameter-types body))
       (define transfer-bindings
         (for/list ([name (in-list transfer-names)])
           (list name (gensym 'forward-owner))))
       (define body-env
         (for/fold ([result env]) ([name (in-list names)])
           (bind result name #f)))
       ;; 入れ子の Lam は外側の Forward 文脈を継承しない。
       (scan body
             body-env
             (list->set (map second transfer-bindings))
             #f owner? transfer-bindings mode #t)
       (hash)]
      [`(RecurVal ,_ ,function (,parameters ...) ,body)
       (define body-env
         (for/fold ([result env])
                   ([name (in-list (cons (peel-bind function)
                                         (map peel-bind parameters)))])
           (bind result name #f)))
       (scan body body-env (set) #f #f '() mode)
       (hash)]
      [`(RegionLam (,_ ...) ,body)
       (scan body env (set) #f #f '() mode)
       (hash)]
      [`(Recur ,_ ,function (,parameters ...) ,body ,continuation)
       (define body-env
         (for/fold ([result env])
                   ([name (in-list (cons (peel-bind function)
                                         (map peel-bind parameters)))])
           (bind result name #f)))
       (define continuation-env (bind env (peel-bind function) #f))
       (scan body body-env (set) #f #f '() mode)
       (scan continuation continuation-env (set) #f #f '() mode)]
      [`(UnionEliminate ,scrutinee (,branches ...))
       (define branch-children (rest (core-children node)))
       (define branch-usages
         (for/list ([branch (in-list branches)]
                    [child (in-list branch-children)])
           (match (peel-forward-union-branch branch)
             [`(,_member ,binder -> ,body)
              (scan body (bind env (peel-bind binder) #f)
                    allowed in-transfer? local-lets? '() mode)]
             [_
              ;; 枝の形を解釈できない場合も core-children の本文を走査する。
              (scan child env (set) in-transfer? local-lets? '() mode)])))
       (usage-add (scan scrutinee env allowed in-transfer? local-lets? '() mode)
                  (for/fold ([usage (hash)]) ([branch (in-list branch-usages)])
                    (usage-max usage branch))
                  term)]
      [`(UnionEliminateAt ,scrutinee (,branches ...))
       (define-values (plain-branches _regions)
         (peel-annotated-union-branches branches))
       (scan `(UnionEliminate ,scrutinee ,plain-branches)
             env allowed in-transfer? local-lets? pending mode result-root?)]
      [`(Eliminate ,scrutinee (,branches ...))
       (define branch-children (rest (core-children node)))
       (define branch-usages
         (for/list ([branch (in-list branches)]
                    [child (in-list branch-children)])
           (match (peel-branch branch)
             [`(,_constructor (,binders ...) -> ,body)
              (define branch-env
                (for/fold ([result env]) ([binder (in-list binders)])
                  (bind result (peel-bind binder) #f)))
              (scan body branch-env allowed in-transfer? local-lets? '() mode)]
             [_ (scan child env (set) in-transfer? local-lets? '() mode)])))
       (usage-add (scan scrutinee env allowed in-transfer? local-lets? '() mode)
                  (for/fold ([usage (hash)]) ([branch (in-list branch-usages)])
                    (usage-max usage branch))
                  term)]
      [`(EliminateAt ,scrutinee (,branches ...))
       (define-values (plain-branches _regions)
         (peel-annotated-data-branches branches))
       (scan `(Eliminate ,scrutinee ,plain-branches)
             env allowed in-transfer? local-lets? pending mode result-root?)]
      [`(RecRewrite ,input (,entries ...))
       (define entry-children (rest (core-children node)))
       (define entry-usage
         (for/fold ([usage (hash)])
                   ([entry (in-list entries)]
                    [child (in-list entry-children)])
           (define next
             (match (peel-node entry)
               [`(,_label ,binder ,_input-type ,_mode ,_output-type ,body)
                (scan body (bind env (peel-bind binder) #f)
                      allowed in-transfer? local-lets? '() mode)]
               [_ (scan child env (set) in-transfer? local-lets? '() mode)]))
           (usage-add usage next term)))
       (usage-add (scan input env allowed in-transfer? local-lets? '() mode)
                  entry-usage term)]
      [`(RecRewriteOpen (,fields ...))
       ;; Open の欄は閉じた RecRewrite entry から作られるため、外側の Forward
       ;; binder 文脈を引き継がず、欄ごとに独立して走査する。
       (for/fold ([usage (hash)]) ([field (in-list (map last fields))])
         (usage-add usage
                    (scan field '() (set) in-transfer? local-lets? '() mode)
                    term))]
      [`(Handle ,_op ,handler ,body)
       (define handler-body
         (match (peel-branch handler)
           [`(,binder -> ,handler-core)
            (scan handler-core (bind env (peel-bind binder) #f)
                  allowed in-transfer? local-lets? '() mode)]
           [_ (scan (first (core-children node)) env (set)
                    in-transfer? local-lets? '() mode)]))
       (define body-usage
         (if (and (identity-forward-handler? handler)
                  (or result-root? (eq? mode 'config)))
             (scan-result-tail body env allowed (set) pending mode)
             (scan body env allowed in-transfer? local-lets? pending mode)))
       (usage-add body-usage
                  handler-body term)]
      [`(Scope ,_ ,body)
       (scan body env allowed in-transfer? local-lets? pending mode)]
      [_
       (scan-sequential (core-children node) env allowed in-transfer?
                        local-lets? '() mode term)]))
  (define initial-env '())
  (define initial-allowed (set))
  (when (eq? mode 'config)
    (for ([entry (in-list states)] #:when (eq? (second entry) 'Available))
      (define identity (gensym 'forward-place))
      (set! initial-env (bind initial-env (first entry) identity))
      (set! initial-allowed (set-add initial-allowed identity))))
  (scan core initial-env initial-allowed #f (eq? mode 'config) '() mode)
  invalid)

(define (resource-binder-names binders types)
  (for/list ([binder (in-list binders)]
             [type (in-list types)]
             #:when (resource-type? type))
    (peel-bind binder)))

(define (resource-branch-binding-type type)
  (match type
    [`(Owned ,payload) payload]
    [_ type]))

(define (check-resource-branch-encoding binders declared-types body node fail)
  (define resource-binders
    (for/list ([binder (in-list binders)]
               [type (in-list declared-types)]
               #:when (resource-type? type))
      binder))
  (cond
    [(null? resource-binders) (values body #f '())]
    [else
     (match (peel-node body)
       [`(Scope ,managed ,inner)
        (unless (null? managed)
          (fail 'resource-binder-missing-binding node))
        (check-owned-encoding
         binders declared-types inner node fail
         #:missing-key (lambda (_) 'resource-binder-missing-binding)
         #:raw-key (lambda (_) 'resource-binder-raw-misuse))
        (values body #t resource-binders)]
       [_
        (for ([binder (in-list resource-binders)])
          (unless (linear-hole? body binder)
            (fail 'resource-binder-missing-binding node)))
        (values body #f resource-binders)])]))

(define (with-branch-context context thunk)
  (with-place-shadowing
   (fourth context)
   (lambda ()
     (parameterize
         ([resource-identity-transfers
           (set-union (resource-identity-transfers)
                     (list->set (fifth context)))])
       (with-binder-points
        (fourth context)
        (region-ctx-point (third context))
        thunk)))))

(define (check-many/full cores types Λ Ψ environment places callables node fail
                         [start-index 0]
                         #:adopt? [adopt? #t])
  (unless (= (length cores) (length types))
    (fail 'arity-mismatch node (length types) (length cores)))
  (let loop ([cores cores]
             [types types]
             [i start-index]
             [current-psi Ψ]
             [rows '()]
             [actuals '()])
    (if (null? cores)
        (list (reverse rows) current-psi (reverse actuals))
        (match (check-as/full (first cores)
                              (first types)
                              (enter-child Λ i)
                              current-psi
                              environment places callables fail
                              #:adopt? adopt?)
          [(list row next-psi actual)
           (loop (rest cores)
                 (rest types)
                 (add1 i)
                 next-psi
                 (cons row rows)
                 (cons actual actuals))]))))

;; 既存の呼び出しは実引数の型を要らない。第 3 要素を落として渡す。
(define (check-many cores types Λ Ψ environment places callables node fail
                    [start-index 0])
  (match (check-many/full cores types Λ Ψ environment places callables node fail
                          start-index)
    [(list rows psi _) (list rows psi)]))

;; config の型導出のときだけ、runtime の leaf をそのまま欄へ許す。
;; Rec の欄は既存の deriving-config? 節が同じ役目を別に持つ。
(define (config-runtime-leaf? core)
  (and (deriving-config?)
       (match (peel-node core)
         [`(OwnedLeaf ,_ ,_) #t]
         [`(OwnedTransit ,_ ,_) #t]
         [_ #f])))

(define (constructor-parameter-info data-type constructor)
  (match data-type
    [`(Option ,_) `(,(list 'A) ,(case constructor
                                  [(none) '()]
                                  [(some) '((Param A))]
                                  [else #f]))]
    [`(List ,_) `(,(list 'A) ,(case constructor
                                [(nil) '()]
                                [(cons) '((Param A) (List (Param A)))]
                                [else #f]))]
    [`(Result ,_ ,_) `(,(list 'A 'B) ,(case constructor
                                       [(ok) '((Param A))]
                                       [(ng) '((Param B))]
                                       [else #f]))]
    [`(Data ,name ,_)
     (match (data-decl name)
       [`(,_ (,parameters ...) (,constructors ...))
        (match (assoc constructor constructors)
          [(list _ field-types) (list parameters field-types)]
          [_ #f])]
       [_ #f])]
    [_ #f]))

(define (collect-constructor-parameter-types! template actual instances
                                              [invariant? #f])
  (unless (eq? actual 'Never)
    (match template
      [`(Param ,name)
       (hash-update! instances name
                     (lambda (types) (cons (list actual invariant?) types))
                     '())]
      [(? list? templates)
       (when (and (list? actual) (= (length templates) (length actual)))
         (for ([template-child (in-list templates)]
               [actual-child (in-list actual)]
               [index (in-naturals)])
           (collect-constructor-parameter-types!
            template-child actual-child instances
            (or invariant?
                (and (eq? (first templates) 'BorrowedMut)
                     (= index 1))))))]
      [_ (void)])))

(define (merge-constructor-parameter-types types node fail)
  (define normalized (map normalize-type types))
  (unless (andmap values normalized)
    (fail 'type-mismatch node (first types) (last types)))
  (match (first normalized)
    [`(Borrowed ,_ ,_)
     ;; 空の constructor が運ぶ Omitted は寿命の source ではない。
     (define sources
       (filter (lambda (type)
                 (not (match type
                        [`(Borrowed ,_ (RParam %omitted)) #t]
                        [_ #f])))
               normalized))
     (cond
       [(null? sources)
        (if (andmap (lambda (type) (type-equiv? type (first normalized)))
                    (rest normalized))
            (first normalized)
            (fail 'type-mismatch node (first types) (last types)))]
       [(ormap (lambda (type) (rparam-term? (third type))) sources)
        (if (andmap (lambda (type) (type-equiv? type (first sources)))
                    (rest sources))
            (first sources)
            (fail 'type-mismatch node (first types) (last types)))]
       [else
        (define unified (unify-borrow-lifetimes sources #:force? #t))
        (if (= (length unified) 1)
            (first unified)
            (fail 'type-mismatch node (first types) (last types)))])]
    [`(BorrowedMut ,_ ,_)
     ;; BorrowedMut's own lifetime may shorten; a parameter occurring in its
     ;; payload is kept invariant by collect-constructor-parameter-types!.
     (define sources
       (filter (lambda (type)
                 (not (match type
                        [`(BorrowedMut ,_ (RParam %omitted)) #t]
                        [_ #f])))
               normalized))
     (cond
       [(null? sources)
        (if (andmap (lambda (type) (type-equiv? type (first normalized)))
                    (rest normalized))
            (first normalized)
            (fail 'type-mismatch node (first types) (last types)))]
       [(ormap (lambda (type) (rparam-term? (third type))) sources)
        (if (andmap (lambda (type) (type-equiv? type (first sources)))
                    (rest sources))
            (first sources)
            (fail 'type-mismatch node (first types) (last types)))]
       [else
        (define unified (unify-borrow-lifetimes sources #:force? #t))
        (if (= (length unified) 1)
            (first unified)
            (fail 'type-mismatch node (first types) (last types)))])]
    [(? list? first-type)
     (unless (andmap (lambda (type)
                       (and (list? type)
                            (= (length type) (length first-type))))
                     (rest normalized))
       (fail 'type-mismatch node (first types) (last types)))
     (for/list ([index (in-range (length first-type))])
       (merge-constructor-parameter-types
        (map (lambda (type) (list-ref type index)) normalized) node fail))]
    [_
     (if (andmap (lambda (type) (type-equiv? type (first normalized)))
                 (rest normalized))
         (first normalized)
         (fail 'type-mismatch node (first types) (last types)))]))

(define (construct-result-type data-type constructor actual-field-types
                               Λ node fail)
  (match (constructor-parameter-info data-type constructor)
    [(list parameters template-field-types)
     (unless (= (length template-field-types) (length actual-field-types))
       (fail 'ill-typed node))
     (define instances (make-hash))
     (for ([template (in-list template-field-types)]
           [actual (in-list actual-field-types)])
       (collect-constructor-parameter-types! template actual instances))
     (define arguments
       (match data-type
         [`(List ,element) (list element)]
         [`(Option ,element) (list element)]
         [`(Result ,ok-type ,error-type) (list ok-type error-type)]
         [`(Data ,_ (,arguments ...)) arguments]
         [_ '()]))
     (define adopted-arguments
       (for/list ([parameter (in-list parameters)]
                  [declared (in-list arguments)])
         (define occurrences (reverse (hash-ref instances parameter '())))
         (define actuals (map first occurrences))
         (if (null? actuals)
             declared
             (let ([actual
                    (if (ormap second occurrences)
                        (if (andmap (lambda (type)
                                      (type-equiv? type (first actuals)))
                                    (rest actuals))
                            (first actuals)
                            (fail 'type-mismatch node (first actuals)
                                  (last actuals)))
                        (parameterize
                            ([merge-position
                              (list (region-ctx-ir Λ)
                                    (region-ctx-point Λ) node)])
                          (with-lifetime-unify
                           (lambda ()
                             (merge-constructor-parameter-types
                              actuals node fail)))))])
               (adopt-inferred-lifetimes declared actual)))))
     (match data-type
       [`(List ,_) `(List ,(first adopted-arguments))]
       [`(Option ,_) `(Option ,(first adopted-arguments))]
       [`(Result ,_ ,_) `(Result ,(first adopted-arguments)
                                  ,(second adopted-arguments))]
       [`(Data ,name ,_) `(Data ,name ,adopted-arguments)]
       [_ data-type])]
    [_ data-type]))

(define (check-construct constructor fields data-type
                         Λ Ψ environment places callables node fail)
  ;; 呼び出し側は G2+ の ts、つまり (#:ty τ s) を包みのまま渡す。
  ;; 剥がす位置をここに 1 つだけ置き、以降は実型だけを使う。
  (define actual-type (peel-ty data-type))
  (define schema (constructor-schema actual-type))
  (unless schema (fail 'unknown-data-type node actual-type))
  (define field-types (lookup schema constructor))
  (unless field-types (fail 'unknown-constructor node constructor))
  ;; Owned な欄は producer の根として OwnLeaf を必須にする。包んでいない欄は
  ;; 従来と同じ owned-constructor-field で落とす。config の runtime leaf だけは
  ;; deriving-config? の検査範囲で既に OwnedLeaf になっているため通す。
  (define permitted
    (for/list ([field-type (in-list field-types)]
               [field (in-list fields)]
               #:when (owned-type? field-type))
      (unless (config-runtime-leaf? field)
        (require-ownleaf-root field 'owned-constructor-field node fail))
      field))
  (match (parameterize ([ownleaf-permitted permitted])
           (check-many/full fields field-types Λ Ψ environment places callables
                            node fail))
    [(list rows next-psi actual-field-types)
     (list (rows-union rows) next-psi
           (construct-result-type actual-type constructor actual-field-types
                                  Λ node fail))]))

(define (type-with-branch-region type annotation)
  (if (or (not annotation) (eq? annotation '%parent))
      type
      (match type
        [`(Borrowed ,payload ,_) `(Borrowed ,payload ,annotation)]
        [`(BorrowedMut ,payload ,_) `(BorrowedMut ,payload ,annotation)]
        [_ type])))

(define (type-with-binder-alpha type alpha)
  (match type
    [`(BorrowedMut ,payload ,_) `(BorrowedMut ,payload ,alpha)]
    [_ type]))

(define (branch-binder-type+psi type region-mark capability parent-type
                                parent-caps ir decomposition branch-index
                                binder-index point Ψ node fail)
  (define marked-type (type-with-branch-region type region-mark))
  (define parent-alpha
    (match (normalize-type parent-type)
      [`(BorrowedMut ,_ ,alpha) alpha]
      [_ #f]))
  (define formal-parent?
    (and parent-caps
         (for/or ([cap (in-set parent-caps)])
           (formal-key? (car cap)))))
  (cond
    [(or (not parent-alpha)
         (not (match (normalize-type marked-type)
                [`(BorrowedMut ,_ ,_) #t]
                [_ #f]))
         (and region-mark (not (eq? region-mark '%parent)))
         (not (lexical-region-ir? ir)))
     (values marked-type Ψ)]
    [(or (not (set? parent-caps)) (set-empty? parent-caps))
     (fail 'unresolved-borrow-owner node)]
    [else
     (define alpha
       (branch-binder-alpha! decomposition branch-index binder-index))
     (when formal-parent?
       (define parent-keys (branch-binder-parent-keys))
       (unless (and parent-keys (set-mutable? parent-keys))
         (error 'branch-binder-type+psi "仮引数親 binder の鍵集合が無い"))
       (set-add! parent-keys (list decomposition branch-index binder-index)))
     (define event-info (branch-binder-event-info))
     (when (and (hash? event-info) (pair? (template-collectors)))
       (define parent-capabilities
         (sort (set->list parent-caps) string<? #:key (lambda (cap) (format "~s" cap))))
       (define source-cap
         (or (for/first ([cap (in-list parent-capabilities)]
                         #:when (formal-key? (car cap)))
               cap)
             (first parent-capabilities)))
       (define source-root (car source-cap))
       (define ambiguous-parent?
         (> (length parent-capabilities) 1))
       (define source-frame (and (formal-key? source-root)
                                 (owning-frame source-root)))
       (define source-fields
         (and source-frame
              (< (fourth source-root)
                 (length (template-frame-formal-fields source-frame)))
              (list-ref (template-frame-formal-fields source-frame)
                        (fourth source-root))))
       (define source-leaf
         (and (hash? source-fields)
              (for/fold ([best #f]) ([(path entry) (in-hash source-fields)])
                (define matching-paths
                  (if (capability-entry? entry)
                      (for/list ([cap (in-set (capability-entry-keys entry))]
                                 #:when (and (equal? (car cap) source-root)
                                             (path-prefix? (cdr cap)
                                                           (cdr source-cap))))
                        (cdr cap))
                      '()))
                (if (and (pair? matching-paths)
                         (or (not best)
                             (> (apply max (map length matching-paths))
                                (car best))))
                    (cons (apply max (map length matching-paths)) entry)
                    best))))
       (define event-parent-alpha
         (or (and source-leaf
                  (capability-entry-declared-lifetime (cdr source-leaf)))
             parent-alpha))
       (hash-set! event-info (list decomposition branch-index binder-index)
                  (list (first (template-collectors))
                        (if (formal-key? source-root) (fourth source-root) 'local)
                        (cdr source-cap) event-parent-alpha 'mut
                        ambiguous-parent?)))
     (define branch-region (branch-region-of ir decomposition branch-index))
     (define parent-term
       (if (or (lifetime-var? parent-alpha) (rparam-term? parent-alpha))
           parent-alpha
           (rho->region ir parent-alpha)))
     (define parent-sources (capability-source parent-type))
     (define (parent-terms cap)
       (define matches
         (for/list ([entry (in-set (psi-mut Ψ))]
                    #:when (and (equal? (first entry) (car cap))
                                (path-prefix? (second entry) (cdr cap))))
           (third entry)))
       (define exact (filter (lambda (term) (equal? term parent-term)) matches))
       (define sourced
         (if (set-empty? parent-sources)
             '()
             (filter (lambda (term) (set-member? parent-sources term)) matches)))
       (cond
         [(pair? exact) exact]
         [(pair? sourced) sourced]
         [(= (length matches) 1) matches]
         [else (list parent-term)]))
     (define child-caps
       (capability-entry-keys capability))
     (when (set-empty? child-caps)
       (fail 'unresolved-borrow-owner node))
     (define next-psi
       (for/fold ([current Ψ]) ([child-cap (in-set child-caps)])
         (define parents
           (for/list ([parent-cap (in-set parent-caps)]
                      #:when (and (equal? (car parent-cap) (car child-cap))
                                  (path-prefix? (cdr parent-cap)
                                                (cdr child-cap))))
             parent-cap))
         (when (null? parents)
           (fail 'unresolved-borrow-owner node))
         (define next
           (for/fold ([next current]) ([parent-cap (in-list parents)])
             (define w (car parent-cap))
             (define parent-fp (cdr parent-cap))
             (define child-fp (cdr child-cap))
             (route-constraint!
              (region-constraint 'contains alpha branch-region point node)
              w node fail)
             (for/fold ([next next])
                       ([α-parent (in-list (parent-terms parent-cap))])
               (route-constraint!
                (region-constraint 'reborrow α-parent alpha point node)
                w node fail #f parent-fp child-fp)
               (psi-suspend next w child-fp α-parent alpha 'mut node point))))
         (route-request!
          (borrow-request (car child-cap) (cdr child-cap) 'mut
                          alpha branch-region node point)
          node fail)
         next))
     (track-child-alpha! alpha)
     (values (type-with-binder-alpha marked-type alpha) next-psi)]))

(define (branch-contexts branches data-type Λ environment node scrutinee fail
                          [branch-regions #f] [Ψ (empty-psi)])
  (define-values (data-core rewrap) (peel-eliminate-wrapper data-type))
  (define schema-core (constructor-schema data-core))
  (unless schema-core (fail 'non-data-eliminate scrutinee))
  (define schema
    (for/list ([row (in-list schema-core)])
      (list (first row) (map rewrap (second row)))))
  (define borrowed-view?
    (match (normalize-type data-type)
      [`(Borrowed ,_ ,_) #t]
      [`(BorrowedMut ,_ ,_) #t]
      [_ #f]))
  (define variant-view? (and borrowed-view? (> (length schema) 1)))
  (define inherited-variants
    (typing-capability-variant-views (enter-child Λ 0) scrutinee))
  (unless (= (length branches) (length schema))
    (fail 'non-exhaustive-eliminate node))
  (define plain-branches (map peel-branch branches))
  (when (and branch-regions
             (or (not (= (length branch-regions) (length branches)))
                 (for/or ([branch (in-list plain-branches)]
                          [regions (in-list branch-regions)])
                   (match branch
                     [`(,_ (,binders ...) -> ,_)
                      (not (= (length binders) (length regions)))]
                     [_ #t]))))
    (fail 'ill-typed node))
  (for ([branch (in-list branches)]
        [plain (in-list plain-branches)]
        [regions (in-list (or branch-regions
                              (make-list (length branches) #f)))])
    ;; 枝の形だけを spanless な文法で検査し、本文は spanful のまま子へ渡す。
    ;; 本文までそのまま G2m へ照合すると、子の span が理由なく不一致になる。
    (unless (redex-match? G2m br (erase-core plain))
      (fail 'ill-typed branch)))
  (define expected-constructors (map first schema))
  (define actual-constructors (map first plain-branches))
  (when (check-duplicates actual-constructors)
    (fail 'duplicate-branch-constructor node))
  (for ([constructor (in-list expected-constructors)])
    (unless (member constructor actual-constructors)
      (fail 'non-exhaustive-eliminate node)))
  (for ([branch (in-list branches)]
        [plain (in-list plain-branches)])
    (match-define `(,constructor (,parameters ...) -> ,_) plain)
    (define field-types (lookup schema constructor))
    (unless field-types (fail 'unknown-constructor branch constructor))
    (unless (= (length parameters) (length field-types))
      (fail 'branch-binder-arity branch (length field-types) (length parameters)))
    (when (check-duplicates (map peel-bind parameters))
      (fail 'duplicate-branch-binder branch)))
  ;; scrutinee の型も schema の欄の型も capability を運ばないときは表を引かない。
  ;; いま通る programme はここを通る。
  (define carries?
    (or (type-carries-capability? data-type)
        (ormap type-carries-capability? (append* (map second schema)))))
  ;; capability を運ぶのに表が作れない scrutinee は所有者を辿れない。
  ;; 現行は infer-eliminate だけが capability-in-eliminate で落としており、
  ;; 期待型を与える check-eliminate は診断も受け渡しも無しに受理していた。
  ;; この 3 分岐を branch-contexts へ置くことで、その非対称が消える。
  (define field-table
    (and carries?
         (typing-capability-field-entries (enter-child Λ 0) scrutinee)))
  ;; 表が無い scrutinee でも、借用そのものが所有者を運んでいれば欄へ辿れる。
  ;; その場合は capability の path の末尾へ欄の位置を積む。
  (define scrutinee-ws
    (and carries? (not field-table)
         (typing-borrow-token-key (enter-child Λ 0) scrutinee)))
  (define parent-caps
    (and borrowed-view?
         (typing-borrow-token-key (enter-child Λ 0) scrutinee #:fail fail)))
  (when (and carries?
             (not field-table)
             (or (not scrutinee-ws) (set-empty? scrutinee-ws)))
    (fail 'unresolved-borrow-owner scrutinee))
  (for/list ([branch (in-list plain-branches)]
             [regions (in-list (or branch-regions
                                   (make-list (length branches) #f)))]
             [i (in-naturals 1)])
    (match-define `(,constructor (,parameters ...) -> ,body) branch)
    (define field-types (lookup schema constructor))
    (define binders (map peel-bind parameters))
    (define-values (checked-body encoded? identity-transfers)
      (check-resource-branch-encoding binders field-types body node fail))
    ;; 分配の規則は capability-of と共有する。鍵が表に無い分岐は
    ;; その label の値が来ないことを意味するため、空の token を張る。
    (define bindings
      (cond
        [field-table
         (capability-branch-bindings field-table constructor binders
                                     variant-view? borrowed-view? (set))]
         [carries?
         (capability-projection-bindings scrutinee-ws binders
                                         variant-view? borrowed-view?
                                         inherited-variants)]
        [else
         (capability-branch-bindings #f constructor binders
                                     variant-view? borrowed-view? (set))]))
    (define branch-point (region-ctx-point (enter-child Λ i)))
    (define-values (typed-field-types branch-psi)
      (for/fold ([types '()] [current-psi Ψ])
                ([type (in-list field-types)]
                 [ρm (in-list (or regions (make-list (length field-types) #f)))]
                 [capability (in-list bindings)]
                 [j (in-naturals)])
        (define-values (typed next-psi)
          (branch-binder-type+psi type ρm capability data-type parent-caps
                                  (region-ctx-ir Λ) (region-ctx-point Λ)
                                  (sub1 i) j
                                  branch-point current-psi node fail))
        (values (append types (list typed)) next-psi)))
    (define Λ_branch
      (for/fold ([Λ_acc Λ])
                ([x (in-list binders)] [τ (in-list typed-field-types)]
                 [entry (in-list bindings)])
        (region-ctx-add-token (register-owner Λ_acc x τ)
                              x
                              (capability-entry-keys entry)
                              #f
                              #f
                              (capability-entry-fields entry)
                              (capability-entry-variants entry)
                              (capability-entry-borrowed-view? entry))))
    (list checked-body
          (extend environment
                  binders
                  (if encoded?
                      (map resource-branch-binding-type typed-field-types)
                      typed-field-types))
          (enter-child Λ_branch i)
          binders
          identity-transfers
          branch-psi)))

;; flow は各式で局所の脱出を集め、子から戻るときに入口の脱出表へ足す。
(define (flow-clear-escapes Ψ)
  (struct-copy psi Ψ
               [flow (struct-copy flow-state (psi-flow Ψ) [escapes (hash)])]))

(define (flow-set-normal flow normal)
  (struct-copy flow-state flow [normal normal]))

(define (flow-join fail node left right)
  (cond
    [(eq? left 'bottom) right]
    [(eq? right 'bottom) left]
    [else
     (for/fold ([joined (hash)])
               ([key (in-list (filter (lambda (key) (hash-has-key? right key))
                                      (hash-keys left)))])
       (define a (hash-ref left key))
       (define b (hash-ref right key))
       (unless (and (type-equiv? (flow-entry-declared a)
                                 (flow-entry-declared b))
                    (type-equiv? (flow-entry-current a)
                                 (flow-entry-current b)))
         (fail 'reassign-type-mismatch node
               (flow-entry-current a) (flow-entry-current b)))
       (define pins-a (or (flow-entry-pins a) (set)))
       (define pins-b (or (flow-entry-pins b) (set)))
       (hash-set joined key
                 (flow-entry (flow-entry-declared a)
                             (flow-entry-current a)
                             (and (or (not (set-empty? pins-a))
                                      (not (set-empty? pins-b)))
                                  (set-union pins-a pins-b)))))]))

(define (escape-union fail node left right)
  (for/fold ([joined left]) ([(boundary state) (in-hash right)])
    (hash-set joined boundary
              (if (hash-has-key? joined boundary)
                  (flow-join fail node (hash-ref joined boundary) state)
                  state))))

(define (flow-join-state fail node left right)
  (flow-state (flow-join fail node
                         (flow-state-normal left) (flow-state-normal right))
              (escape-union fail node
                            (flow-state-escapes left)
                            (flow-state-escapes right))))

(define (psi-flow-branch-join fail node before branches)
  (define permissions
    (for/fold ([joined before]) ([branch (in-list branches)])
      (psi-join joined branch)))
  (define flow
    (for/fold ([joined #f]) ([branch (in-list branches)])
      (if joined
          (flow-join-state fail node joined (psi-flow branch))
          (psi-flow branch))))
  (struct-copy psi permissions [flow (or flow (psi-flow before))]))

(define (flow-exit-binder state name saved)
  (define (restore entries)
    (if (eq? saved #f)
        (hash-remove entries name)
        (hash-set entries name saved)))
  (flow-state (if (eq? (flow-state-normal state) 'bottom)
                  'bottom
                  (restore (flow-state-normal state)))
              (for/hash ([(boundary exits) (in-hash (flow-state-escapes state))])
                (values boundary
                        (if (eq? exits 'bottom) 'bottom (restore exits))))))

(define (flow-update Ψ key entry)
  (define state (psi-flow Ψ))
  (if (eq? (flow-state-normal state) 'bottom)
      Ψ
      (struct-copy psi Ψ
                   [flow (flow-set-normal
                          state
                          (hash-set (flow-state-normal state) key entry))])))

(define (flow-enter-let Ψ name mode declared current)
  (define state (psi-flow Ψ))
  (if (eq? (flow-state-normal state) 'bottom)
      (values Ψ #f)
      (let* ([normal (flow-state-normal state)]
             [saved (hash-ref normal name #f)]
             [masked (hash-remove normal name)]
             [next (if (eq? mode 'mut)
                       (hash-set masked name
                                 (flow-entry (if (deriving-config?) #f declared)
                                             current #f))
                       masked)])
        (values (struct-copy psi Ψ
                             [flow (flow-set-normal state next)])
                saved))))

(define (flow-leave-let bound-psi body-psi name saved fail node)
  (define body-state (flow-exit-binder (psi-flow body-psi) name saved))
  (define escapes
    (escape-union fail node
                  (flow-state-escapes (psi-flow bound-psi))
                  (flow-state-escapes body-state)))
  (struct-copy psi body-psi
               [flow (flow-state (flow-state-normal body-state) escapes)]))

(define (flow-record-escape Ψ operation fail node)
  (define state (psi-flow Ψ))
  (if (eq? (flow-state-normal state) 'bottom)
      Ψ
      (struct-copy psi Ψ
                   [flow (struct-copy flow-state state
                                      [escapes
                                       (escape-union
                                        fail node
                                        (flow-state-escapes state)
                                        (hash operation
                                              (flow-state-normal state)))])])))

(define (return-operation-key boundary type)
  (erase-core `(Return ,boundary ,(peel-ty type))))

(define (mut-slots-in core)
  (let walk ([term (peel-node core)])
    (match term
      [`(MutSlot ,(? exact-nonnegative-integer? place)) (set place)]
      [(? list? parts)
       (for/fold ([found (set)]) ([part (in-list parts)])
         (set-union found (walk part)))]
      [_ (set)])))

;; MutSlot は名前ではなく place 識別子なので、closure body の binder は
;; 捕捉走査で隠さない。Reassign の target も同じ走査に含める。
(define (captured-mut-slots value)
  (let walk ([term (peel-node value)])
    (match term
      [`(Lam ,_ ,_ ,_ ,body) (mut-slots-in body)]
      [`(RecurVal ,_ ,_ ,_ ,body) (mut-slots-in body)]
      [`(RegionLam (,_ ...) ,body) (mut-slots-in body)]
      [(? list? parts)
       (for/fold ([found (set)]) ([part (in-list parts)])
         (set-union found (walk part)))]
      [_ (set)])))

(define (flow-pin-mut-slots Ψ places)
  (define state (psi-flow Ψ))
  (if (eq? (flow-state-normal state) 'bottom)
      Ψ
      (let ([normal
             (for/fold ([entries (flow-state-normal state)])
                       ([place (in-set places)])
               (define key `(MutSlot ,place))
               (define entry (hash-ref entries key #f))
               (if entry
                   (let ([pins (or (flow-entry-pins entry) (set))])
                     (hash-set entries key
                               (flow-entry (flow-entry-declared entry)
                                           (flow-entry-current entry)
                                           (set-add pins
                                                    (flow-entry-current entry)))))
                   entries))])
        (struct-copy psi Ψ [flow (flow-set-normal state normal)]))))

(define (flow-pin-captures Ψ body environment [bound-names '()])
  (define state (psi-flow Ψ))
  (if (eq? (flow-state-normal state) 'bottom)
      Ψ
      (if (deriving-config?)
          (flow-pin-mut-slots Ψ (mut-slots-in body))
          (let* ([free (set-subtract (core-free-vars body)
                                    (list->set bound-names))]
                 [normal
                  (for/fold ([entries (flow-state-normal state)])
                            ([name (in-set free)]
                             #:when (eq? (binding-mode-of environment name) 'mut))
                    (define entry
                      (hash-ref entries name
                                (lambda ()
                                  (define type (lookup environment name))
                                  (flow-entry type type #f))))
                    (define pins (or (flow-entry-pins entry) (set)))
                    (hash-set entries name
                              (flow-entry (flow-entry-declared entry)
                                          (flow-entry-current entry)
                                          (set-add pins
                                                   (flow-entry-current entry)))))])
            (struct-copy psi Ψ
                         [flow (flow-set-normal state normal)])))))

(define (flow-check-backedge fail node entry output)
  ;; 通常の Recur では捕捉した外側の mut slot は pin され、Let の出口で局所 slot は除かれる。
  ;; したがって、この検査は将来の経路追加に備える防御的な確認である。
  (define input-normal (flow-state-normal (psi-flow entry)))
  (define output-normal (flow-state-normal (psi-flow output)))
  (when (and (hash? input-normal) (hash? output-normal))
    (unless (set=? (list->set (hash-keys input-normal))
                   (list->set (hash-keys output-normal)))
      (fail 'reassign-type-mismatch node input-normal output-normal))
    (for ([key (in-hash-keys input-normal)])
      (define before (hash-ref input-normal key))
      (define after (hash-ref output-normal key))
      (unless (and (type-equiv? (flow-entry-declared before)
                                (flow-entry-declared after))
                   (type-equiv? (flow-entry-current before)
                                (flow-entry-current after))
                   (set=? (or (flow-entry-pins before) (set))
                          (or (flow-entry-pins after) (set))))
        (fail 'reassign-type-mismatch node before after)))))

(define (flow-restore-output input output normal-type fail node)
  (define before (psi-flow input))
  (define after (psi-flow output))
  (define escapes
    (escape-union fail node
                  (flow-state-escapes before)
                  (flow-state-escapes after)))
  (struct-copy psi output
               [flow (flow-state
                      (if (or (eq? normal-type '⊥)
                              (eq? (flow-state-normal before) 'bottom))
                          'bottom
                          (flow-state-normal after))
                      escapes)]))

;; Union branch は成分型で束縛する。借用した Union だけは値を取り出さず、
;; 各枝の束縛子へ payload path を引き継ぐ。
(define (union-branch-contexts branches union-type wrapper Λ environment
                               node scrutinee fail [branch-regions #f]
                               [Ψ (empty-psi)])
  (define peeled-branches
    (for/list ([branch (in-list branches)])
      (match (peel-branch branch)
        [`(,type ,binder -> ,body)
         (list (peel-ty type) (peel-bind binder) '-> body)]
        [_ branch])))
  (when (and branch-regions
             (not (= (length branch-regions) (length peeled-branches))))
    (fail 'ill-typed node))
  (for ([branch (in-list peeled-branches)])
    (unless (redex-match? G2m ubr (erase-core branch))
      (fail 'ill-typed node)))
  (define members (union-members union-type))
  (define branch-members
    (for/list ([branch (in-list peeled-branches)])
      (match-define `(,declared ,_binder -> ,_) branch)
      (or (for/first ([member (in-list members)]
                      #:when (type-equiv? declared member))
            member)
          (and (contains-omitted-region? declared)
               (for/first ([member (in-list members)]
                           #:when
                           (type-equiv?
                            (normalize-type
                             (adopt-inferred-lifetimes declared member))
                            member))
                 member))
          declared)))
  (define plain-branches
    (for/list ([branch (in-list peeled-branches)]
               [member (in-list branch-members)])
      (match-define `(,_declared ,binder -> ,body) branch)
      (list member binder '-> body)))
  (define branch-types (map first plain-branches))
  (let check-duplicates ([remaining branch-types] [seen '()])
    (unless (null? remaining)
      (when (ormap (lambda (prior) (type-equiv? (first remaining) prior)) seen)
        (fail 'non-exhaustive-union-eliminate node))
      (check-duplicates (rest remaining) (cons (first remaining) seen))))
  (for ([member (in-list members)])
    (unless (= (for/sum ([type (in-list branch-types)]
                         #:when (type-equiv? type member))
                1)
               1)
      (fail 'non-exhaustive-union-eliminate node)))
  (define borrowed? (pair? wrapper))
  (define field-table
    (typing-capability-field-entries (enter-child Λ 0) scrutinee))
  (define parent-caps
    (and borrowed?
         (typing-borrow-token-key (enter-child Λ 0) scrutinee #:fail fail)))
  (define inherited-variants
    (typing-capability-variant-views (enter-child Λ 0) scrutinee))
  (define scrutinee-ws
    (and borrowed?
         (typing-borrow-token-key (enter-child Λ 0) scrutinee)))
  (when (and borrowed? (or (not scrutinee-ws) (set-empty? scrutinee-ws)))
    (fail 'unresolved-borrow-owner scrutinee))
  (define (member-capability member)
    (and (hash? field-table)
         (or (hash-ref field-table member #f)
             (for/first ([(key entry) (in-hash field-table)]
                         #:when
                         (and (contains-omitted-region? key)
                              (type-equiv?
                               (normalize-type
                                (adopt-inferred-lifetimes key member))
                               member)))
               entry))))
  (for/list ([branch (in-list plain-branches)]
             [region-mark (in-list (or branch-regions
                                       (make-list (length plain-branches) #f)))]
             [i (in-naturals 1)])
    (match-define `(,member ,binder -> ,body) branch)
    (define x (peel-bind binder))
    (define binding-type
      (if borrowed? `(,(first wrapper) ,member ,(second wrapper)) member))
    (define-values (checked-body encoded? identity-transfers)
      (if borrowed?
          (values body #f '())
          (check-resource-branch-encoding
           (list x) (list member) body node fail)))
    (define capability
      (capability-union-binding
       field-table member scrutinee-ws borrowed?
       (or (member-capability member)
           (and borrowed?
                (capability-union-binding #f member scrutinee-ws borrowed?
                                          #f borrowed? inherited-variants)))
       borrowed? inherited-variants))
    (define branch-point (region-ctx-point (enter-child Λ i)))
    (define parent-type
      (if borrowed?
          (list (first wrapper) union-type (second wrapper))
          union-type))
    (define-values (typed-binding-type branch-psi)
      (branch-binder-type+psi binding-type region-mark capability parent-type
                              parent-caps (region-ctx-ir Λ)
                              (region-ctx-point Λ) (sub1 i) 0
                              branch-point Ψ node fail))
    (define Λ_branch
      (region-ctx-add-token (register-owner Λ x typed-binding-type)
                            x
                            (capability-entry-keys capability)
                            #f #f
                            (capability-entry-fields capability)
                            (capability-entry-variants capability)
                            (capability-entry-borrowed-view? capability)))
    (list checked-body
          (extend environment
                  (list x)
                  (list (if borrowed?
                            typed-binding-type
                            (if encoded?
                                (resource-branch-binding-type typed-binding-type)
                                typed-binding-type))))
          (enter-child Λ_branch i)
          (list x)
          identity-transfers
          branch-psi)))

(define (union-eliminate-branches scrutinee-type branches Λ environment
                                  node scrutinee fail [branch-regions #f]
                                  [Ψ (empty-psi)])
  (match (normalize-type scrutinee-type)
    [`(Union ,_ ,_)
     (union-branch-contexts branches (normalize-type scrutinee-type) #f
                            Λ environment node scrutinee fail branch-regions Ψ)]
    [`(Owned (Union ,_ ,_))
     (union-branch-contexts branches
                            (second (normalize-type scrutinee-type)) #f
                            Λ environment node scrutinee fail branch-regions Ψ)]
    [`(Borrowed (Union ,_ ,_) ,ρ)
     (union-branch-contexts branches
                            (second (normalize-type scrutinee-type))
                            (list 'Borrowed ρ) Λ environment node scrutinee fail
                            branch-regions Ψ)]
    [`(BorrowedMut (Union ,_ ,_) ,ρ)
     (union-branch-contexts branches
                            (second (normalize-type scrutinee-type))
                            (list 'BorrowedMut ρ) Λ environment node scrutinee fail
                            branch-regions Ψ)]
    [_ (fail 'non-union-eliminate scrutinee)]))

(define (check-union-eliminate scrutinee branches expected
                               Λ Ψ environment places callables node fail
                               compatible? [branch-regions #f])
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define contexts
    (union-eliminate-branches
     (typing-normal-child-type node Λ 0 (first scrutinee-result))
     branches Λ environment node scrutinee fail branch-regions
     (third scrutinee-result)))
  (define branch-results
    (for/list ([context (in-list contexts)])
      (with-branch-context
       context
       (lambda ()
         (check-as/full (first context) expected (third context)
                        (sixth context) (second context)
                        places callables fail compatible?)))))
  (define branch-psi
    (psi-flow-branch-join fail node (third scrutinee-result)
                          (map second branch-results)))
  (define unified
    (parameterize ([merge-position
                    (list (region-ctx-ir Λ) (region-ctx-point Λ) node)])
      (with-lifetime-unify
       (lambda ()
         (unify-borrow-lifetimes
          (map (lambda (result) (normalize-type (third result)))
               branch-results))))))
  (define merged
    (cond
      ;; すべての枝が Never なら、寿命合流の形で期待型へ戻さない。
      [(andmap (lambda (result) (eq? (third result) 'Never)) branch-results)
       'Never]
      [(= (length unified) 1) (first unified)]
      [else expected]))
  (list (rows-union
         (cons (second scrutinee-result) (map first branch-results)))
        branch-psi
        merged))

(define (infer-union-eliminate scrutinee branches Λ Ψ environment
                               places callables node fail [branch-regions #f])
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define contexts
    (union-eliminate-branches
     (typing-normal-child-type node Λ 0 (first scrutinee-result))
     branches Λ environment node scrutinee fail branch-regions
     (third scrutinee-result)))
  (define attempts
    (for/list ([context (in-list contexts)])
      (with-branch-context
       context
       (lambda ()
         (infer (first context) (third context) (sixth context)
                (second context) places callables fail)))))
  (define non-never
    (filter (lambda (result) (not (eq? (first result) 'Never))) attempts))
  (define types (map first non-never))
  (define result-type
    (if (null? types)
        'Never
        (tagged-branch-upper-bound types Λ node fail)))
  (define branch-results
    (for/list ([context (in-list contexts)])
      (with-branch-context
       context
       (lambda ()
         (check-as/full (first context) result-type (third context)
                        (sixth context) (second context)
                        places callables fail type-compatible?)))))
  (define branch-psi
    (psi-flow-branch-join fail node (third scrutinee-result)
                          (map second branch-results)))
  (list result-type
        (rows-union (cons (second scrutinee-result)
                          (map first branch-results)))
        branch-psi))

(define (infer-union-inject union-type member-type payload Λ Ψ
                            environment places callables node fail)
  (define union-type* (normalize-type (peel-ty union-type)))
  (define member-type* (normalize-type (peel-ty member-type)))
  (unless (and union-type*
               (match union-type* [`(Union ,_ ,_) #t] [_ #f])
               member-type*
               (= (for/sum ([member (in-list (union-members union-type*))]
                            #:when (type-equiv? member member-type*))
                    1)
                  1))
    (fail 'union-inject-not-member node))
  (match (check-as/full payload member-type* (enter-child Λ 0) Ψ
                        environment places callables fail)
    [(list row next-psi actual)
     (define members (union-members union-type*))
     (define result-member
       (adopt-inferred-lifetimes member-type* actual))
     (define adopted-members
       (for/list ([member (in-list members)])
         (if (type-equiv? member member-type*) result-member member)))
     (define result-type
       (normalize-type
        (foldr (lambda (member tail) `(Union ,member ,tail))
               (last adopted-members)
               (drop-right adopted-members 1))))
     (list result-type row next-psi)]))

(define (infer-union-value union-type member-type payload Λ Ψ
                           environment places callables node fail)
  (define union-type* (normalize-type union-type))
  (define member-type* (normalize-type member-type))
  (unless (and (type-normal? union-type)
               (match union-type* [`(Union ,_ ,_) #t] [_ #f])
               (type-normal? member-type)
               (= (for/sum ([member (in-list (union-members union-type*))]
                            #:when (type-equiv? member member-type*))
                    1)
                  1))
    (fail 'ill-typed node))
  (match (infer payload (enter-child Λ 0) Ψ
                environment places callables fail)
    [(list payload-type row next-psi)
     (define adopted-member
       (adopt-retained-lifetimes member-type* payload-type))
     (unless (tag-compat? payload-type adopted-member
                          (current-Γ-pc0) (current-region-relation))
       (fail 'ill-typed node))
     (check-borrow-hiding! payload-type member-type* node fail)
     (define result-type
       (normalize-type
        (foldr (lambda (member tail)
                 (if tail `(Union ,member ,tail) member))
               #f
               (for/list ([member (in-list (union-members union-type*))])
                 (if (type-equiv? member member-type*)
                     adopted-member
                     member)))))
     (list result-type row next-psi)]))

(define (check-eliminate scrutinee branches expected
                         Λ Ψ environment places callables node fail
                         [compatible? type-compatible?]
                         [branch-regions #f])
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define data-type
    (typing-normal-child-type node Λ 0 (first scrutinee-result)))
  (define contexts
    (branch-contexts branches data-type Λ environment node scrutinee fail
                     branch-regions (third scrutinee-result)))
  (define branch-results
    (for/list ([context (in-list contexts)])
      (with-branch-context
       context
       (lambda ()
         (check-as/full (first context)
                        expected
                        (third context)
                        (sixth context)
                        (second context)
                        places
                        callables
                        fail
                        compatible?)))))
  (define branch-psi
    (psi-flow-branch-join fail node (third scrutinee-result)
                          (map second branch-results)))
  ;; 分岐ごとに別の α を持つ借用を 1 本へ合流する。合流しなかったときは
  ;; expected を返し、分岐 0 の型を根拠なく選ばない。
  (define unified
    (parameterize ([merge-position
                    (list (region-ctx-ir Λ) (region-ctx-point Λ) node)])
      (with-lifetime-unify
       (lambda ()
         (unify-borrow-lifetimes
          (map (lambda (result) (normalize-type (third result)))
               branch-results))))))
  (define merged
    (cond
      [(andmap (lambda (result) (eq? (third result) 'Never)) branch-results)
       'Never]
      [(= (length unified) 1) (first unified)]
      [else expected]))
  (list (rows-union
         (cons (second scrutinee-result)
               (map first branch-results)))
        branch-psi
        merged))

;; §2.8。既に tag を持つ値の型だけを合わせ、tag の無い値から Union を作らない。
(define (tag-upper-bound left right)
  (define l (normalize-type left))
  (define r (normalize-type right))
  (and l r
       (match* (l r)
         [('Never _) r]
         [(_ 'Never) l]
         [(`(Union ,_ ,_) `(Union ,_ ,_)) (normalize-type `(Union ,l ,r))]
         [(`(Union ,_ ,_) _) #f]
         [(_ `(Union ,_ ,_)) #f]
         [(`(Record ,_) `(Record ,_))
          (tag-merge-record-types l r)]
         [(`(Owned ,l-payload) `(Owned ,r-payload))
          ;; c2b1 spec §4.2。payload の上界へ両方が tag-narrowing? で
          ;; 狭められる場合だけ Owned で包む。幅を落とす Record の候補は拒否する。
          (define candidate (tag-upper-bound l-payload r-payload))
          (and candidate
               (tag-narrowing? l-payload candidate)
               (tag-narrowing? r-payload candidate)
               `(Owned ,candidate))]
         [(_ _) (and (type-equiv? l r) l)])))

(struct tag-bound-failure (reason details) #:transparent)

(define (tag-types-upper-bound types)
  (cond
    [(andmap record-type? types)
     ;; 全ての枝を一度に渡す。2 つずつ畳み込むと witness と合流の規則がずれる。
     (define-values (merged _witnesses)
       (merge-record-types/impl types tag-upper-bound))
     (or merged (tag-bound-failure 'unmergeable-branch-records '()))]
    [(ormap record-type? types)
     (tag-bound-failure 'incompatible-branch-types '())]
    [else
     (let loop ([upper (first types)] [remaining (rest types)])
       (cond
         [(null? remaining) upper]
         [(tag-upper-bound upper (first remaining))
          => (lambda (next) (loop next (rest remaining)))]
         [else (tag-bound-failure 'type-mismatch
                                  (list upper (first remaining)))]))]))

(define (branch-types-upper-bound types)
  (when (ormap contains-lifetime-var? types)
    (error 'branch-types-upper-bound
           "Λ なしの合流は寿命変数を含む型を受けない: ~s" types))
  (branch-types-upper-bound/in-context types))

(define (branch-types-upper-bound/in-context types)
  (if (ormap record-type? types)
      (tag-types-upper-bound types)
      (with-lifetime-unify
       (lambda () (tag-types-upper-bound (unify-borrow-lifetimes types))))))

(define (tagged-branch-upper-bound types Λ node fail)
  (parameterize ([merge-position
                  (list (region-ctx-ir Λ) (region-ctx-point Λ) node)])
    (match (branch-types-upper-bound/in-context types)
      [(tag-bound-failure reason details)
       (apply fail reason node details)]
      [upper upper])))

(define (tag-merge-record-types left right)
  (define-values (merged _witnesses)
    (merge-record-types/impl (list left right) tag-upper-bound))
  merged)

;; §10.1。合流の memo。merge-record-types/impl が 1 回の合流につき 1 つ張る。
;; merge-fields と merge-witness-context が同じ型の並びへ同じ α_m を得るための共有である。
(define lifetime-unify-context (make-parameter #f))

;; 合流の制約の診断位置。分岐を型付けする側が張る（§10.2）。
;; 値は `(list ir point node)` か `#f` である。
;; `#f` のときは制約を立てない。span を引けない節点で診断を出さないためである。
;; ir を持つのは、α_m の下限に合流位置の region を置くためである。
(define merge-position (make-parameter #f))

;; §8.1。合流した α から、その合流が受け取った分岐の ρ の集合への対応。
;; lifetime-counter や alpha-table と同じく、寿命を 1 つの typing の文脈に限る。
(define merge-alpha-sources (make-parameter #f))

(define (with-lifetime-unify thunk)
  (parameterize ([lifetime-unify-context (box (hash))]) (thunk)))

;; 借用の寿命だけを合流する。payload が一致する借用が 2 つ以上あるときに働く。
;; 文脈が無いとき（合流の外から呼ばれたとき）は何もしない。
(define (unify-borrow-lifetimes types #:force? [force? #f])
  (define memo (lifetime-unify-context))
  (define key (list force? types))
  (cond
    [(not memo) types]
    [(hash-ref (unbox memo) key #f) => values]
    [else
     (define result (unify-borrow-lifetimes/fresh types force?))
     (set-box! memo (hash-set (unbox memo) key result))
     result]))

(define (borrow-shape t)
  (match t
    [`(Borrowed ,payload ,ρ) (list 'Borrowed payload ρ)]
    [`(BorrowedMut ,payload ,ρ) (list 'BorrowedMut payload ρ)]
    [_ #f]))

(define (nested-type-arguments type)
  (match type
    [`(Option ,element) (list 'Option (list element))]
    [`(List ,element) (list 'List (list element))]
    [`(Result ,ok ,error) (list 'Result (list ok error))]
    [`(Data ,name (,arguments ...)) (list (list 'Data name) arguments)]
    [_ #f]))

(define (rebuild-nested-type constructor arguments)
  (match constructor
    ['Option `(Option ,(first arguments))]
    ['List `(List ,(first arguments))]
    ['Result `(Result ,(first arguments) ,(second arguments))]
    [(list 'Data name) `(Data ,name ,arguments)]))

(define (unify-nested-borrow-lifetimes types)
  (define decomposed (map nested-type-arguments types))
  (and (andmap values decomposed)
       (andmap (lambda (parts)
                 (equal? (first parts) (first (first decomposed))))
               (rest decomposed))
       (let* ([arguments (map second decomposed)]
              [merged-arguments
               (for/list ([index (in-range (length (first arguments)))])
                 (define candidates
                   (map (lambda (args) (list-ref args index)) arguments))
                 (define unified (unify-borrow-lifetimes candidates))
                 (cond
                   [(= (length unified) 1) (first unified)]
                   [(andmap (lambda (type)
                              (type-equiv? type (first candidates)))
                            (rest candidates))
                    (first candidates)]
                   [else #f]))])
         (and (andmap values merged-arguments)
              (list (rebuild-nested-type (first (first decomposed))
                                         merged-arguments))))))

(define (unify-borrow-lifetimes/fresh types [force? #f])
  (define shapes (map borrow-shape types))
  (cond
    ;; 全てが借用であり、構築子と payload が一致し、
    ;; かつ少なくとも 1 つの枝が寿命変数を持つときだけ合流する。
    ;; 全ての枝が具体的な region のときは G5b のままにする（§3.1）。
    [(and (andmap values shapes)
          (or force? (> (length shapes) 1))
          (for/and ([s (in-list (rest shapes))])
            (and (eq? (first s) (first (first shapes)))
                 (equal? (second s) (second (first shapes)))))
          (or force?
              (for/or ([s (in-list shapes)]) (lifetime-var? (third s)))))
     (define ctor (first (first shapes)))
     (define payload (second (first shapes)))
     (define α_m (fresh-lifetime! (list 'merge (length shapes))))
     ;; §8.1。合流した α が受け取った分岐の ρ を記録する。
     ;; capability-source はこれを葉まで展開する。
     (hash-set! (merge-alpha-sources) α_m
                (for/set ([s (in-list shapes)]) (third s)))
     (define pos (merge-position))
     ;; 位置が無い呼び出しでは制約を立てない。§10.2。
     (when (and pos (first pos))
       (define ir (first pos))
       (define point (second pos))
       (define node (third pos))
       ;; α_m の下限を必ず 1 本立てる。合流した値は合流位置で生きている。
       (emit-constraint!
        (region-constraint 'contains α_m (region-at ir point) point node))
       (for ([s (in-list shapes)])
         (define ρ (third s))
         (cond
           [(lifetime-var? ρ)
            ;; 合流した値は両分岐の寿命に収まる。§10.1。
            (emit-constraint!
             (region-constraint 'merge ρ α_m point node))]
           [(rparam-term? ρ)
            ;; 仮引数の寿命は呼出し位置で実体化するため、定義時 IR では解決しない。
            (void)]
           [else
            ;; 具体の側は下限である。§3.1。
            (emit-constraint!
             (region-constraint 'contains α_m (rho->region ir ρ)
                                point node))])))
     (list (list ctor payload α_m))]
    [(unify-nested-borrow-lifetimes types) => values]
    [else types]))

;; CMP-001/ROW-005: 同じ label を持つ field を合わせる。
;; 異型があれば可変性を保ったまま Union join する。
;; 可変性が枝の間で食い違う field だけを imm へ落とす。
(define (merge-field left right)
  (merge-fields (list left right)))

(define (presence-binding-name label)
  (string->symbol (format "presence-~a" label)))

(define (field-type-binding-name label index)
  (string->symbol (format "field-type-~a-~a" label index)))

(define (merge-witness-binding name proposition)
  (list name
        (list proposition '(Reserved o-merge)
              name 'root 'default '())))

;; branch 型を正規化し、Union 正規化と同じ順序・同値判定で重複を畳む。
(define (distinct-normal-types types)
  (define normalized (map normalize-type types))
  (and (andmap values normalized)
       (unify-borrow-lifetimes (sort-then-dedup normalized))))

;; RFN-002/CMP-001: merge が立てる局所 witness 文脈。
;; 各 field の Presence に加え、異型 join には branch 型ごとの FieldType を置く。
(define (merge-witness-context types merged-row)
  (append-map
   (lambda (field)
     (define label (first field))
     (define branch-types
       (for/list ([type (in-list types)])
         (first (field-row-lookup (second type) label))))
     (define distinct-types (distinct-normal-types branch-types))
     (define presence-name (presence-binding-name label))
     (append
      (if (field-optional? field)
          '()
          (list (merge-witness-binding presence-name `(Presence ,label))))
      (if (> (length distinct-types) 1)
          (for/list ([type (in-list distinct-types)]
                     [index (in-naturals)])
            (define name (field-type-binding-name label index))
            (merge-witness-binding name `(FieldType ,label ,type)))
          '())))
   merged-row))

(define (merge-fields fields [join-type tag-upper-bound])
  (define first-field (first fields))
  (define label (first first-field))
  ;; 全枝が mut のときにだけ mut を保つ。1 枝でも imm なら、書き込みが
  ;; imm 枝の不変性を破りうるため imm へ落とす。
  (define all-mutable?
    (for/and ([field (in-list fields)]) (eq? (third field) 'mut)))
  (define any-optional?
    (for/or ([field (in-list fields)]) (field-optional? field)))
  (define types (distinct-normal-types (map second fields)))
  (define (make-field type mutability)
    (if any-optional?
        (list label type mutability 'opt)
        (list label type mutability)))
  (and
   (for/and ([field (in-list fields)])
     (eq? (first field) label))
   types
   (cond
     [(null? (rest types))
      (make-field (first types) (if all-mutable? 'mut 'imm))]
     ;; 既に Union tag を持つ型どうしだけが上界へ合流する。
     [else
      (define joined
        (for/fold ([joined (first types)])
                  ([type (in-list (rest types))])
          (and joined (join-type joined type))))
      (and joined (make-field joined (if all-mutable? 'mut 'imm)))])))

;; ROW-005: 返り値は 3 状態である。field 行なら合流成功、'absent は「どれかの
;; branch にこの field が無い」正常な脱落、#f は正規化または join の失敗であり
;; merge 全体の fail-closed へ伝播する。
;; 両者を #f で兼ねると、失敗が脱落として黙って握り潰される。
(define (merge-common-field types first-field join-type)
  (define label (first first-field))
  (define fields
    (for/list ([type (in-list types)])
      (assoc label (second type))))
  (if (andmap values fields)
      (merge-fields fields join-type)
      'absent))

;; RFN-002/CMP-001/ROW-005: 全 branch に常在する field を合わせる。異型は
;; 可変性を保ったまま Union join する。どれかの branch に無い field だけが落ちる。
;; types は空でないことを呼び出し側が保証する。
(define (merge-record-types/impl types [join-type tag-upper-bound])
  (with-lifetime-unify
   (lambda ()
     (define merged-fields
       (for/list ([field (in-list (second (first types)))])
         (merge-common-field types field join-type)))
     (cond
       [(memq #f merged-fields) (values #f '())]
       [else
        (define merged-row
          (filter (lambda (field) (not (eq? field 'absent))) merged-fields))
        (define merged-type (normalize-type `(Record ,merged-row)))
        (if merged-type
            (values merged-type
                    (merge-witness-context types (second merged-type)))
            (values #f '()))]))))

;; POL-002/ROW-004: 合流 row の label は一意で昇順、witness 列は wf-context? を
;; 満たし束縛名が重複しない。#f だけが fail-closed 返却である。(Record ()) は
;; 共通 field が残らない正常な合流であり、成功返却として不変条件を適用する。
;; 両者を同じ形と見なすと、正規化失敗が「空 row の合流に成功した」として素通り
;; する。
;; ROW-005 以降、#f は merge-common-field から伝播した正規化・join の失敗と、
;; 合流 row 自身の正規化失敗の 2 経路で立つ。
(define (check-merge-return args returns)
  (match returns
    [(list #f '()) #t]
    [(list `(Record ,row) witnesses)
     (define labels (map first row))
     (define names (map first witnesses))
     (and (field-row-unique? row)
          (equal? labels (sort labels symbol<?))
          (wf-context? witnesses)
          (= (length names) (length (remove-duplicates names))))]
    [_ #f]))

(define merge-record-types
  (policy-wrap 'RowPolicy 'merge-record-types
               merge-record-types/impl
               check-merge-return))

;; RFN-002: merge の局所検査。その merge が立てた W だけを候補文脈として、
;; 要求された常在性の義務が充足できるかを見る。型付けの受理条件ではなく、
;; merge ごとに成り立つ性質として検査する。
(define (merge-witnesses-dischargeable? types obligations)
  (define-values (merged witnesses) (merge-record-types/impl types))
  (and merged
       (obligations-dischargeable? obligations witnesses)))

(define (infer-eliminate scrutinee branches Λ Ψ environment places callables node fail
                         [branch-regions #f])
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define data-type
    (typing-normal-child-type node Λ 0 (first scrutinee-result)))
  (define contexts
    (branch-contexts branches data-type Λ environment node scrutinee fail
                     branch-regions (third scrutinee-result)))
  (define attempts
    (for/list ([context (in-list contexts)])
      (with-branch-context
       context
       (lambda ()
         (infer (first context)
                (third context)
                (sixth context)
                (second context)
                places
                callables
                fail)))))
  (define non-never
    (filter (lambda (result)
              (not (eq? (first result) 'Never)))
            attempts))
  (define types (map first non-never))
  (define result-type
    (if (null? types)
        'Never
        (tagged-branch-upper-bound types Λ node fail)))
  (define branch-rows
    (for/list ([context (in-list contexts)])
      (with-branch-context
       context
       (lambda ()
         (check-as (first context)
                   result-type
                   (third context)
                   (sixth context)
                   (second context)
                   places
                   callables
                   fail
                   type-compatible?)))))
  (define branch-psi
    (psi-flow-branch-join fail node (third scrutinee-result)
                          (map second branch-rows)))
  (list result-type
        (rows-union
         (cons (second scrutinee-result)
               (map first branch-rows)))
        branch-psi))

;; [REQ: BOR-001] spec §14。関数境界で Borrowed と BorrowedMut を禁じる。
;; 仮引数、結果、証明義務の Q、捕捉を同じ入口で検査する。
(define (check-function-boundary parameter-types return-type obligations body
                                 bound-names environment node fail)
  (when (ormap unbound-boundary-borrowed-type? parameter-types)
    (fail 'borrowed-function-parameter node))
  (when (unbound-boundary-borrowed-type? return-type)
    (fail 'borrowed-function-result node))
  (when (unbound-boundary-borrowed-type? obligations)
    (fail 'borrowed-function-result node obligations))
  ;; 関数自身の束縛子は同名の外側の項目を遮蔽するため、自由変数から引く。
  (define free
    (set-subtract (core-free-vars body) (list->set bound-names)))
  ;; environment は連想リストであり、前方の項目が遮蔽後の有効な項目である。
  (define visible
    (for/fold ([entries '()]) ([entry (in-list environment)])
      (if (assoc (first entry) entries)
          entries
          (cons entry entries))))
  ;; ForallRegion の binder は、外側の lexical region ではなく callable 自身の
  ;; 抽象 region である。環境の polymorphic callable を捕捉するときは、その
  ;; binder を bound-region-params へ一時的に加えて payload の借用を調べる。
  (define (captured-borrowed? type)
    (match type
      [`(ForallRegion (,rps ...) ,body)
       (unbound-borrowed-type?
        body
        (set-union (bound-region-params) (list->set rps)))]
      [_ (unbound-borrowed-type? type)]))
  (for ([entry (in-list visible)])
    (when (and (captured-borrowed? (second entry))
               (set-member? free (first entry)))
      (fail 'borrowed-function-capture node))))

;; 関数本体の借用要求は外側で解決するため、停止集合だけを外へ返す。
(define (psi-with-suspended base body)
  (struct-copy psi base
               [suspended (set-union (psi-suspended base)
                                     (psi-suspended body))]))

(define (infer-lam callable parameters body Λ Ψ
                   environment places callables node fail)
  (define raw-signature (callable-signature callables callable))
  (unless raw-signature (fail 'unknown-callable node))
  ;; callables は入力側の名前を保持する。core の RegionLam は入口で fresh 名へ
  ;; 付け替えるため、署名の RParam だけ同じ対応表で型検査側へ写す。
  (define signature (resolve-region-params raw-signature))
  ;; ForallRegion は直上の RegionLam が渡した binder 文脈で 1 段だけ剥がす。
  ;; 文脈が無い形や束縛数が合わない形は下の既存の fail-closed へ落とす。
  (define expanded
    (or (unwrap-forall-region signature (region-binder-context)) signature))
  (match expanded
    [`(NFn ,parameter-types ,return-type ,_latent-in ,latent-row ,obligations ,_origin)
     (record-callable-context! Λ raw-signature 'lam)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates parameters)
       (fail 'duplicate-parameter node))
     ;; 境界では、この callable の署名に現れる region parameter だけを使う。
     ;; とくに内側の素の Lam は、捕捉検査で外側の RegionLam の parameter を
     ;; 引き継いではならない。
     (define signature-region-params
       (set-intersect (bound-region-params)
                      (region-free-params expanded)))
     (parameterize ([bound-region-params signature-region-params])
       (check-function-boundary parameter-types return-type obligations
                                body parameters environment node fail))
     ;; 署名が資源型の仮引数を持つなら、本体は生名と Let の連なりで
     ;; 符号化されている。仮引数の位置ではなく本体の形で検査する。
     (when (ormap resource-type? parameter-types)
       (match (peel-node body)
         [`(Handle ,_ ,_ ,scope)
          (match (peel-node scope)
            [`(Scope () ,inner)
             (check-owned-encoding parameters parameter-types inner node fail)]
            [_ (fail (resource-encoding-outer-missing-key parameter-types)
                     node)])]
         [_ (fail (resource-encoding-outer-missing-key parameter-types)
                  node)]))
     (define body-environment
       (function-body-environment environment parameters parameter-types))
     ;; §5.4。借用の仮引数の位置ごとに文脈局所の formal 鍵を採る。
     ;; 借用でない位置は #f を置き、位置の対応を崩さない。
     (define-values (formals formal-fields body-context)
       (formal-parameter-context Λ node parameters parameter-types))
     ;; formal 鍵は token へ登録する。本体の Reborrow と使用はこの登録を
     ;; 通じて親を引く。普通の借用の要求へは入れない。仮引数は呼出し側の
     ;; 借用の別名であり、定義位置で新しい借用を立てるわけではない。
     (define closure-psi
       (flow-pin-captures Ψ body body-environment parameters))
     (define collector (box '()))
     (define incomplete-box (box #f))
     (define frame
       (template-frame (for/set ([w (in-list formals)] #:when w) w)
                       collector body parameters parameter-types return-type
                       latent-row formal-fields incomplete-box))
     ;; Lam が転送できるのは自身の署名に自由に現れる region parameter だけ。
     ;; 外側の callable にしか属さない parameter を境界の外へ出すと、閉包の
     ;; ような Lam が証明の終わった lexical region を保持できてしまう。
     ;; expanded は外側の ForallRegion を 1 段剥がした NFn なので、
     ;; region-free-params が署名の自由な RParam だけを返す。
     (define body-result
       (parameterize ([region-binder-context #f]
                      ;; 閉包本体は定義位置で検査し、外側 Handle の捕捉境界を引き継がない。
                      [return-handler-regions '()]
                      ;; formal の RParam はこの Lam の境界に属する。
                      ;; 内側の Lam が外側の RegionLam の束縛をそのまま
                      ;; 引き継ぐと、formal 借用の capture を見逃す。
                      [bound-region-params signature-region-params]
                      [template-collectors
                       (cons frame (template-collectors))]
                      [scrutinee-child-alphas (mutable-set)]
                      [binder-points
                       (binder-points+ parameters
                                       (region-ctx-point body-context))])
         (with-place-shadowing
          parameters
             (lambda ()
               (with-resource-identity-transfers
                (resource-binder-names parameters parameter-types)
                (lambda ()
                  (define result
                    (check-as body return-type body-context closure-psi body-environment
                              places callables fail))
                  (record-formal-result-exits! body-context body return-type fail)
                  result))))))
     (unless (row-subset? (first body-result) latent-row)
       (fail 'undeclared-function-effect body latent-row (first body-result)))
     ;; §5.4。出現局所の要約を登録する。Apply はこの要約を引いて実体化する。
     (record-callable-summary!
      Λ node
      (callable-summary formals (normalize-leaf-exits (reverse (unbox collector)))
                        (forwarding-leaf-candidates parameter-types return-type
                                                     node fail)
                        (hash) formal-fields (unbox incomplete-box))
      fail)
     (list expanded '() (psi-with-suspended closure-psi (second body-result)))]
    ;; 表の行が ForallRegion に包まれた署名で、binder 文脈が無い形はここへ来る。
    ;; 囲う RegionLam があるはずという仮定を置かず、表に無い場合と key を
    ;; 共有して fail-closed にする（spec §5.7）。
    [_ (fail 'unknown-callable node)]))

(struct recur-prelude
  (signature body-signature binder-params region-params
   parameter-types return-type latent-row obligations)
  #:transparent)

(define (recur-signature-prelude callable function parameters body
                                 Λ environment callables node fail)
  (define raw-signature (callable-signature callables callable))
  (unless raw-signature (fail 'unknown-callable node))
  ;; callables は入力側の名前を保持する。core の RegionLam は入口で fresh 名へ
  ;; 付け替えるため、署名の RParam だけ同じ対応表で型検査側へ写す。
  (define signature (resolve-region-params raw-signature))
  (define-values (body-signature binder-params)
    (match signature
      [`(ForallRegion (,rps ...) ,inner) (values inner rps)]
      [_ (values signature '())]))
  (match body-signature
    [`(NFn ,parameter-types ,return-type ,_latent-in ,latent-row ,obligations ,_origin)
     (record-callable-context! Λ raw-signature 'recur)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates (cons function parameters))
       (fail 'duplicate-parameter node))
     ;; §4.4。境界では、ForallRegion の binder と、この callable の署名に
     ;; 現れる外側の region parameter だけを使う。
     (define region-params
       (set-union (list->set binder-params)
                  (set-intersect (bound-region-params)
                                 (region-free-params body-signature))))
     (parameterize ([bound-region-params region-params])
       (check-function-boundary parameter-types return-type obligations
                                body (cons function parameters)
                                environment node fail))
     (when (ormap resource-type? parameter-types)
       (match (peel-node body)
         [`(Scope () ,inner)
          (check-owned-encoding parameters parameter-types inner node fail)]
         [_ (fail (resource-encoding-outer-missing-key parameter-types)
                  node)]))
     (recur-prelude signature body-signature binder-params region-params
                    parameter-types return-type latent-row obligations)]
    ;; 表の行が NFn でない場合は fail-closed にする。
    [_ (fail 'unknown-callable node)]))

(define (infer-recur-value callable function parameters body Λ Ψ
                           environment places callables node fail)
  (match-define
    (recur-prelude signature body-signature binder-params region-params
                   parameter-types return-type latent-row _obligations)
    (recur-signature-prelude callable function parameters body
                             Λ environment callables node fail))
  (define function-environment
    (extend environment
            (list function)
            (list signature)))
  (define body-function-environment
    (if (null? binder-params)
        function-environment
        (extend environment
                (list function)
                (list body-signature))))
  (define body-environment
    (function-body-environment body-function-environment
                                parameters parameter-types))
  (define closure-psi
    (flow-pin-captures Ψ body body-environment (cons function parameters)))
  ;; §4.2。借用の仮引数の位置ごとの鍵。
  (define-values (formals formal-fields body-context)
    (formal-parameter-context Λ node parameters parameter-types))
  (define recur-binding (lookup-binding body-function-environment function))
  (define (fixpoint Ψ_in [previous-exits '()] [previous-incomplete? #f])
    (define collector (box previous-exits))
    (define incomplete-box (box previous-incomplete?))
    (define tentative
      (make-recur-frame (list recur-binding) formals
                        (forwarding-leaf-candidates parameter-types return-type
                                                     node fail)
                        collector 'tentative 1 formal-fields incomplete-box))
    (define template
      (template-frame (for/set ([w (in-list formals)] #:when w) w)
                      collector body parameters parameter-types return-type
                      latent-row formal-fields incomplete-box))
    (match (parameterize ([region-binder-context #f]
                          [return-handler-regions '()]
                          ;; RecurVal の本体も呼出しまで遅延する。
                          [bound-region-params region-params]
                          [template-collectors
                           (cons template (template-collectors))]
                          [recur-overlay
                           (cons tentative (recur-overlay))]
                          [scrutinee-child-alphas (mutable-set)]
                          [binder-points
                           (binder-points+ (cons function parameters)
                                           (region-ctx-point body-context))])
              (with-place-shadowing
              (cons function parameters)
              (lambda ()
                (with-resource-identity-transfers
                 (resource-binder-names parameters parameter-types)
                 (lambda ()
                   (define result
                     (check-as body return-type body-context Ψ_in body-environment
                               places callables fail))
                   (record-formal-result-exits! body-context body return-type fail)
                   result)))))
      [(list body-row Ψ_1)
       (flow-check-backedge fail body Ψ_in Ψ_1)
       (define Ψ_next (psi-join Ψ_in Ψ_1))
       (define exits
         (filter deferred-leaf-exit? (unbox collector)))
       (define exits-unchanged?
         (set=? (list->set (map leaf-exit-identity exits))
                (list->set (map leaf-exit-identity previous-exits))))
       (if (and (equal? Ψ_next Ψ_in) exits-unchanged?)
           (list body-row Ψ_next
                 (struct-copy recur-frame tentative [state 'final]))
           (fixpoint Ψ_next exits (unbox incomplete-box)))]))
  (match-define (list body-row Ψ_body frame) (fixpoint closure-psi))
  (unless (row-subset? body-row latent-row)
    (fail 'undeclared-function-effect body latent-row body-row))
  ;; §4.4。RecurVal は継続を持たないので、剥がした本体の要約を自身の
  ;; 出現へ登録する。RegionApp がこの節点を直接参照できるようにする。
  (record-callable-summary! Λ node (recur-frame->summary frame) fail)
  (list signature '() (psi-with-suspended closure-psi Ψ_body)))

(define (recur-context callable function parameters body Λ Ψ
                       environment places callables node fail)
  (match-define
    (recur-prelude signature body-signature binder-params region-params
                   parameter-types return-type latent-row _obligations)
    (recur-signature-prelude callable function parameters body
                             Λ environment callables node fail))
  (define function-environment
    (extend environment
            (list function)
            (list signature)))
  ;; §4.4。本体は剥がした NFn、継続は元の ForallRegion を見る。形 i は
  ;; 包みが無いので同じ環境の対を共有し、形 ii だけ本体側を別に作る。
  (define body-function-environment
    (if (null? binder-params)
        function-environment
        (extend environment
                (list function)
                (list body-signature))))
  (define body-environment
    (function-body-environment body-function-environment
                               parameters parameter-types))
  (define closure-psi
    (flow-pin-captures Ψ body body-environment (cons function parameters)))
  ;; §4.2。借用の仮引数の位置ごとの鍵。
  (define-values (formals formal-fields body-context)
    (formal-parameter-context Λ node parameters parameter-types))
  (define bindings
    (if (null? binder-params)
        (list (lookup-binding function-environment function))
        (list (lookup-binding body-function-environment function)
              (lookup-binding function-environment function))))
  ;; 本体を Ψ が動かなくなるまで解析し直す。集合は単調に増えるため停止する。
  (define (fixpoint Ψ_in [previous-exits '()] [previous-incomplete? #f])
    (define collector (box previous-exits))
    (define incomplete-box (box previous-incomplete?))
    (define tentative
      (make-recur-frame bindings formals
                        (forwarding-leaf-candidates parameter-types return-type
                                                     node fail)
                        collector 'tentative
                        (if (null? binder-params) 1 2)
                        formal-fields incomplete-box))
    (define template
      (template-frame (for/set ([w (in-list formals)] #:when w) w)
                      collector body parameters parameter-types return-type
                      latent-row formal-fields incomplete-box))
    (match (parameterize ([region-binder-context #f]
                          [return-handler-regions '()]
                          ;; Recur の定義本体は呼出しまで遅延する。
                          [bound-region-params region-params]
                          [template-collectors
                           (cons template (template-collectors))]
                          [recur-overlay
                           (cons tentative (recur-overlay))]
                          [scrutinee-child-alphas (mutable-set)]
                          [binder-points
                           (binder-points+ (cons function parameters)
                                           (region-ctx-point body-context))])
            (with-place-shadowing
             (cons function parameters)
             (lambda ()
                (with-resource-identity-transfers
                (resource-binder-names parameters parameter-types)
                (lambda ()
                  (define result
                    (check-as body return-type body-context Ψ_in body-environment
                              places callables fail))
                  (record-formal-result-exits! body-context body return-type fail)
                  result)))))
      [(list body-row Ψ_1)
       (flow-check-backedge fail body Ψ_in Ψ_1)
       (define Ψ_next (psi-join Ψ_in Ψ_1))
       (define exits
         (filter deferred-leaf-exit? (unbox collector)))
       (define exits-unchanged?
         (set=? (list->set (map leaf-exit-identity exits))
                (list->set (map leaf-exit-identity previous-exits))))
       (if (and (equal? Ψ_next Ψ_in) exits-unchanged?)
           (list body-row Ψ_next
                 (struct-copy recur-frame tentative [state 'final]))
           (fixpoint Ψ_next exits (unbox incomplete-box)))]))
  (match-define (list body-row Ψ_body frame) (fixpoint closure-psi))
  (unless (row-subset? body-row latent-row)
    (fail 'undeclared-function-effect body latent-row body-row))
  (list function-environment Ψ_body frame))

;; spec §3.1。宣言型の借用の region 欄は書き手が書いた起点であり、
;; 推論した型のそれは寿命である。語彙が違うので照合しない。
;; config の BorrowedMut は不変なので、具体化済みの期待 region を実行値で上書きしない。
;; 両方が同じ構成子の借用である位置だけ、宣言型の欄を推論した欄へ写す。
;; 形が食い違う位置は宣言型のまま残し、後段の type-compatible? に落とさせる。
(define (adopt-inferred-lifetimes declared actual)
  (define (adopt-region declared-region actual-region)
    (if (and (deriving-config?)
             (not (contains-omitted-region? declared-region))
             (not (lifetime-var? declared-region))
             (not (rparam-term? declared-region)))
        declared-region
        actual-region))
  (match* (declared actual)
    [(`(Borrowed ,d-payload ,_) `(Borrowed ,a-payload ,a-rho))
     `(Borrowed ,(adopt-inferred-lifetimes d-payload a-payload) ,a-rho)]
    [(`(BorrowedMut ,d-payload ,d-rho) `(BorrowedMut ,a-payload ,a-rho))
     `(BorrowedMut ,(adopt-inferred-lifetimes d-payload a-payload)
                   ,(adopt-region d-rho a-rho))]
    [(`(Record ,declared-row) `(Record ,actual-row))
     `(Record
       ,(for/list ([field (in-list declared-row)])
          (define actual-field (field-row-lookup actual-row (first field)))
          (if actual-field
              (list* (first field)
                     (adopt-inferred-lifetimes (second field)
                                               (first actual-field))
                     (cddr field))
              field)))]
    [((? list?) (? list?))
     #:when (= (length declared) (length actual))
     (for/list ([d (in-list declared)] [a (in-list actual)])
       (adopt-inferred-lifetimes d a))]
    [(_ _) declared]))

;; §12。宣言型が Owned のときだけ使う比較。推論した型が Owned でなければ
;; Owned で包んでから比べる。包んで比べる形を type-compatible? そのものへ
;; 入れない。入れると、関数の実引数や分岐の合流でも暗黙の持ち上げが起きる。
(define (owned-lift-compatible? actual expected)
  (or (type-compatible? actual expected)
      (and (not (owned-type? actual))
           (type-compatible? `(Owned ,actual) expected))))

;; 固定引数と関数のどちらかが Owned なら、結果の関数型も Owned で包む。
;; 包んだ型は Move を経由してのみ関数の位置へ置ける（§5.4）。
(define (curry-result-type remaining-types return-type latent-in latent-out
                           obligations new-origin owned?)
  (define bare `(NFn ,remaining-types ,return-type ,latent-in ,latent-out
                     ,obligations ,new-origin))
  (if owned? `(Owned ,bare) bare))

;; spec §6.2。O の比較キーを作る。(Curry #:erased) は step ではないため、
;; 戻り値は Redex の O ではなく Racket 側の比較キーである。
(define (curry-payload-erase origin)
  (match origin
    [`(Derived ,inner (Curry ,_))
     `(Derived ,(curry-payload-erase inner) (Curry #:erased))]
    [`(Derived ,inner (Compose ,nm ,left ,right))
     `(Derived ,(curry-payload-erase inner)
               (Compose ,nm ,(curry-payload-erase left) ,(curry-payload-erase right)))]
    [`(Derived ,inner ,step) `(Derived ,(curry-payload-erase inner) ,step)]
    [_ origin]))

;; 関数の位置に置かれた Owned<NFn ...> を一段だけ剥がす。
;; Move と CurryVal は place を経由するため許し、それ以外の根は拒む。
(define owned-function-roots '(Move CurryVal OwnedTransit))

(define (owned-function-type? type)
  (match type
    [`(Owned (NFn ,_ ...)) #t]
    [_ #f]))

(define (peel-owned-function type core fail)
  (cond
    [(not (owned-function-type? type)) (values type #f)]
    [else
     (define worn (peel-node core))
     (unless (and (pair? worn)
                  (memq (car worn) owned-function-roots))
       (fail 'owned-function-requires-move core))
     (values (second type) #t)]))

(define (mut-slot-type-supported? type)
  (and (owned-free? type)
       (not (borrowed-type-anywhere? type))))

;; ROW-001 / OWN-009 / BOR-001。config の再型付けだけで使う view の互換。
(define (config-view-compatible? actual view)
  (or (type-equiv? actual view)
      (and (eq? (owned-narrowing-kind actual view type-compatible?) 'ok)
           (eq? (borrow-hiding-kind actual view type-compatible?) 'ok)
           (match* (actual view)
             [(`(Record ,_) `(Record ,_))
              (rsd-proof-pair-ok? actual view type-compatible?)]
             [(_ _) (type-compatible? actual view)]))))

;; BOR-001 / OWN-004。余剰の借用を型 view から隠すには、明示的な RSD が要る。
(define (check-borrow-hiding! actual expected node fail
                              [compatible? type-compatible?])
  (unless (eq? (borrow-hiding-kind actual expected compatible?) 'ok)
    (fail 'borrow-hidden-by-narrowing node)))

(define (binding-context binding-mode declared-type bound Λ Ψ
                         environment places callables node fail)
  (when (and (eq? binding-mode 'mut)
             (not (mut-slot-type-supported? declared-type)))
    ;; 宣言型だけで明らかな affine/borrowed binding は bound を推論する前に
    ;; 拒む。これにより借用の所有者検査より mut の契約を先に報告できる。
    (fail 'mut-binding-unsupported-type node))
  (match declared-type
    [`(Record ,_declared-row)
     (match (infer bound (enter-child Λ 0) Ψ environment places callables fail)
       [(list 'Never bound-row bound-psi)
        (list bound-row declared-type bound-psi #t)]
       [(list `(Record ,actual-row) bound-row bound-psi)
        ;; 束縛の型には推論した寿命を持つ宣言型を使う。宣言型を先に比較すると、
        ;; 借用欄の (RParam %omitted) と実際の region が異なるため拒否される。
        (define adopted-type
          (adopt-inferred-lifetimes declared-type `(Record ,actual-row)))
        (define adopted-row (second adopted-type))
        (unless (tag-compat? `(Record ,actual-row) adopted-type
                             (current-Γ-pc0)
                             (current-region-relation))
          (fail 'record-binding-incompatible bound))
        (define residual
          (field-row-residual actual-row adopted-row))
        (define binding-row
          (case binding-mode
            [(const)
             (if (or (null? residual)
                     (and (deriving-config?)
                          (config-view-compatible? `(Record ,actual-row)
                                                   adopted-type)))
                 adopted-row
                 (fail 'const-record-residual bound residual))]
            ;; P1c2b。mut は残余を落とさない。落とすと const と同じ制約になる。
            [(let)
             (field-row-⊕ adopted-row residual)]
            [(mut)
             ;; mut の再代入は古い値を捨てるため、affine な値と借用を
             ;; mutable な環境へ入れない。既存の再帰的な述語で欄の内側も見る。
             (define row (field-row-⊕ adopted-row residual))
             (for ([field (in-list row)])
               (define type (second field))
               (when (not (mut-slot-type-supported? type))
                 (fail 'mut-binding-unsupported-type node)))
             row]
            [else (fail 'ill-typed node)]))
        ;; field-row-residual は adopted-row のラベルを除いた残余を返すため、
        ;; field-row-⊕ の重複検査はここでは破れない。表の整合を保つため、
        ;; 到達しないこの位置は先の compat? 検査と key を共有する。
        (unless binding-row (fail 'record-binding-incompatible bound))
        (define narrowing-row binding-row)
        (check-borrow-hiding!
         `(Record ,actual-row) `(Record ,narrowing-row) bound fail
         (lambda (actual expected)
           (compat? actual expected (current-Γ-pc0)
                    (current-region-relation))))
        ;; OWN-004。binding-row の宣言欄と残余欄を保って narrowing を検査する。
        (match (owned-narrowing-kind
                `(Record ,actual-row)
                `(Record ,narrowing-row)
                (lambda (actual expected)
                  (compat? actual expected (current-Γ-pc0)
                           (current-region-relation))))
          ['ok
           (void)]
          [`(drop-obligation ,_ ,_)
           (fail 'owned-narrowing-needs-proof bound
                 `(Record ,binding-row)
                 `(Record ,actual-row))]
          [_
           (fail 'owned-narrowing-rejected bound
                 `(Record ,binding-row)
                 `(Record ,actual-row))])
        (list bound-row `(Record ,binding-row) bound-psi #f)]
       [(list actual-type _ _)
        (fail 'type-mismatch bound declared-type actual-type)])]
    [`(Owned ,payload)
     ;; §12。計算した値を Owned へ載せる経路。宣言型が Owned のとき、
     ;; bound が計算した値をそのまま place へ載せる。
     ;; resource と Move が作った値は最初の比較で通るため、既存の経路は変わらない。
     ;; payload に借用が入る形は落とす。place へ載せた後は借用の所有者が
     ;; どこにいるのかを追う手立てが無く、所有者より長生きする借用を作れる。
     ;; 束縛の集合は空にする。この位置では region 多相の束縛の下でも、
     ;; 借用そのものを payload に置けない。
     (when (borrowed-type-anywhere? payload)
       (fail 'own-binding-borrowed-payload node))
     (match (check-as/full bound declared-type (enter-child Λ 0)
                           Ψ environment places callables fail
                           owned-lift-compatible?)
       [(list row bound-psi actual)
        ;; 宣言型をそのまま束縛の型にする。payload に借用が無いことを
        ;; 直前に確かめたので、寿命を写す先が無い。
        (list row declared-type bound-psi (eq? actual 'Never))])]
    [_
     (match (check-as/full bound declared-type (enter-child Λ 0)
                           Ψ environment places callables fail)
       [(list row bound-psi actual)
        (when (and (eq? binding-mode 'mut)
                   (not (mut-slot-type-supported? actual)))
          ;; Record 以外の mut binding も同じ契約を受ける。ここは宣言型の
          ;; match の外側なので Borrowed/Owned の non-record root を拾う。
          (fail 'mut-binding-unsupported-type node))
        ;; 束縛の型には推論した寿命を持つ側を置く。
        ;; 宣言型を置くと spec §5.1 の下限収集が (RVar k) を見つけられず、
        ;; 束縛した名前を使う位置の region が σ に入らない。
        (list row (adopt-inferred-lifetimes declared-type actual) bound-psi
              (eq? actual 'Never))])]))

;; PRF-004: Discharge の連なりを外側から剥がし、(φ 列, 基底) を返す。
;; 型付けを連なりの全体で見るため、節の側では再帰しない。
(define (peel-discharge core)
  (let loop ([core core] [propositions '()])
    (match (peel-node core)
      [`(Discharge ,proof-rep ,inner)
       (match (peel-node proof-rep)
         [`(ProofRep ,_ ,phi)
          (loop inner (cons phi propositions))]
         [_ (values (reverse propositions) core)])]
      [_ (values (reverse propositions) core)])))

;; spec §6: 失敗は返り値ではなく脱出継続で運ぶ。struct を返すと真値になり、
;; 既存の and と andmap と for/and の短絡が失敗を成功として通す。
;; lowering.rkt:88 の with-diagnostics と同じ機構である。
;; 局所回復の callback も同じ検査を通すため、key 検査を単独の手続きにする。
;; callback の中へ書き写すと、片方だけ直したときに未登録 key が素通りする。
(define (assert-typing-key key)
  (unless (diagnostic-code-of 'typing key)
    (error 'fail "registry に無い typing の key である: ~s" key)))

(define (with-typing proc)
  (let/ec escape
    (define (fail key node . details)
      (assert-typing-key key)
      (escape (list 'fail key node details)))
    (list 'ok (proc fail))))

;; 脱出を捕まえて従来の #f へ潰す。core-check-row と config-ok? が使う。
;; spec §4.1。段 1 だけでなく段 3 まで通す。段 2 と段 3 の fail も #f へ潰す。
;; 返り値は成功時の段 1 の row を σ で解決したものであり、σ 自体は外へ出さない。
;; 段 1 の fail は with-typing の脱出で段 2 へ進まないため、段 1 で棄却した形が
;; 制約違反として報告されることはない。type-of/raw* と同じ契約である。
(define (check-as/boolean core expected environment places callables
                          [Λ (empty-region-ctx)]
                          #:compatible? [compatible? type-compatible?]
                          #:initial-psi [initial-psi (empty-psi)])
  (define cs (box '()))
  (define rs (box '()))
  (define ras (box '()))
  (define origins (make-hash))
  (define ir (region-ctx-ir Λ))
  (define erased-core (erase-core core))
  (define config-place-points
    (and (deriving-config?)
         (let walk ([node erased-core])
           (or (match node [`(ProjBorrowAt ,_ ,_ ,_) #t] [_ #f])
               (for/or ([child (in-list (core-children node))])
                 (walk child))))
         (lexical-region-ir-projborrow-place-points
          (build-region-ir erased-core))))
  (match (parameterize ([lifetime-collector cs]
                        [request-collector rs]
                        [region-arg-collector ras]
                        [lifetime-counter (box 0)]
                        [region-param-origins origins]
                        [region-binder-renamings '()]
                        [alpha-table (box (hash))]
                        [branch-binder-alphas (make-hash)]
                        [branch-binder-parent-keys (mutable-set)]
                        [branch-binder-event-info (make-hash)]
                        [branch-binder-alpha-sources (make-hash)]
                        [resource-place-set (set)]
                        [resource-identity-transfers (set)]
        [merge-alpha-sources (make-hash)]
        [callable-summaries (make-hash)]
        [forwarding-summaries (make-hash)]
        [template-collectors '()]
        [recur-overlay '()]
        [scrutinee-child-alphas (mutable-set)]
        [binder-points (hash)]
        [config-projborrow-place-points config-place-points])
           (with-typing
            (lambda (fail)
              ;; 束縛名を入口で 1 度だけ付け替える。関係の表も同じ項から作る。
              (define renamed
                (call-with-region-params
                 (lambda () (alpha-rename-all-region-lams core))))
              (define relation
                (if ir (make-region-relation ir (erase-core renamed)) equal?))
              (parameterize ([current-region-relation relation])
                ;; 段 1。
                (match-define (list row Ψ)
                  (check-as renamed expected Λ initial-psi
                            environment places callables fail
                            compatible?))
                ;; 段 2。
                (match (typing-solve ir (reverse (unbox cs)))
                  [(list 'error broken)
                   (define c (first broken))
                   (fail (constraint-key c) (constraint-node c))]
                  [(list 'ok σ)
                   ;; 段 3。ir が無い Λ では emit-use-request! が要求を作らない
                   ;; ため、届くのは RegionApp の要求だけである。
                   (check-region-args ir σ (collected-region-args) relation fail)
                   (check-borrows ir σ Ψ (reverse (unbox rs)) sigma-ref fail)
                   (subst-type-regions row σ ir)])))))
    [(list 'ok row) row]
    [_ #f]))

;; spec §3.7。root Owned の binder は従来どおり owner とする。
;; 集約資源型は P に入る Let の変数だけを owner にする。
;; data constructor の Eliminate 枝と UnionEliminate の枝、関数仮引数は
;; c1c1 では P の外であり、c1c2 で仮引数を P へ入れる段階に借用の owner 登録も広げる。
;; Let の各節点では本体の with-let-place より先に呼ぶため、P への所属は
;; Let 専用の引数で渡す。branch の呼出しは既定値のままとする。
;; ρ は束縛子の節点で有効な region である。Λ.point がその節点を指すため、
;; enter-child を掛ける前の Λ をここへ渡す。
;; ir が無い Λ、すなわち公開入口の既定の空 Λ では何もしない。
(define (register-owner Λ w binding-type #:let-place? [let-place? #f])
  (define ir (region-ctx-ir Λ))
  (define normalized (normalize-type binding-type))
  (define resource-let?
    (and let-place?
         (resource-type? normalized)))
  (cond
    [(not ir) Λ]
    [(or (match normalized [`(Owned ,_) #t] [_ #f])
         resource-let?)
     (region-ctx-add-owner
      Λ w
      (if resource-let?
          (owner-let-body-region ir (region-ctx-point Λ))
          (region-at ir (region-ctx-point Λ))))]
    [else Λ]))

;; 借用の対象の payload を引く。p は places が直接 τ を与え、
;; root Owned の x は payload τ を、P の集約資源型の x は宣言型全体を与える。
(define (borrow-target-payload w environment places node fail)
  (cond
    [(exact-nonnegative-integer? w)
     (define type (lookup places w))
     (unless type (fail 'unknown-place node))
     type]
    [else
     (define type (lookup environment (peel-node w)))
     (unless type (fail 'unbound-variable node))
     (match type
       [`(Owned ,payload) payload]
       [_ (if (and (set-member? (resource-place-set) (peel-node w))
                   (resource-type? type))
              type
              (fail 'borrow-non-owned node))])]))

;; [REQ: BOR-001] 借用の region は owner の region に含まれていなければならない。
;; [REQ: BOR-002] 可変借用の有効期間中、競合する alias を作れない。
;;
;; G5c1 では判定を行わない。α を作り、制約と判定の要求だけを記録する。
;; 判定は解決の後、検査の段が行う（spec §7.3）。
(define (infer-borrow core w mutable? Λ Ψ environment places callables fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-unknown-owner-region core))
  (define payload (borrow-target-payload w environment places core fail))
  (define key (if (exact-nonnegative-integer? w) w (peel-node w)))
  (define ρ_owner (region-ctx-owner Λ key))
  ;; 所有者の region が引けないのは制約の違反ではなく入力の情報不足である。
  ;; 解決を待つ理由が無いため、ここで落とす（spec §8.1）。
  (unless ρ_owner (fail 'borrow-unknown-owner-region core))
  (define point (region-ctx-point Λ))
  (define branch-born? (branch-region-enclosing? ir point))
  (define ρ_borrow
    (if branch-born? (region-at/branch ir point) (region-at ir point)))
  (define α (fresh-lifetime! point))
  (when branch-born? (track-child-alpha! α))
  ;; 借用の起点は α の下限である。使わない借用の解はこの 1 本で決まり、
  ;; G5b の ρ_borrow と一致する（spec §5.3）。
  (emit-constraint!
   (region-constraint 'contains α ρ_borrow point #f))
  ;; BOR-001 は上限制約になる（spec §8.1）。
  (emit-constraint!
   (region-constraint 'outlives ρ_owner α point core))
  (emit-request!
   (borrow-request key '() (if mutable? 'mut 'shared)
                   α ρ_borrow core point))
  (define Ψ_out
    (if mutable?
        (psi-add-mut Ψ key '() α)
        (psi-add-shared Ψ key '() α)))
  (list (list (if mutable? 'BorrowedMut 'Borrowed)
              payload
              α)
        '()
        Ψ_out))

;; 構成検査では materialize 後の注釈 ρ が実行時の寿命である。
;; source 型付けが既に検査した衝突、outlives、borrow request は再計算しない。
(define (infer-borrow/config core w mutable? ρ environment places Ψ fail)
  (define payload (borrow-target-payload w environment places core fail))
  (list (list (if mutable? 'BorrowedMut 'Borrowed) payload ρ)
        '()
        Ψ))

;; [REQ: BOR-002] Reborrow は可変借用を子 region の共有借用へ落とし、
;; 親 capability を子の生存期間だけ停止する。判定は段 3 で行う。
(define (infer-reborrow core operand Λ Ψ environment places callables fail)
  (define operand-Λ (enter-child Λ 0))
  (define operand-result
    (infer operand operand-Λ Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-unknown-owner-region core))
  (match (normalize-type τ_operand)
    [`(BorrowedMut ,τ ,α_parent)
     (define point (region-ctx-point Λ))
     (define α_child (fresh-lifetime! point))
     (record-binder-alpha-descendant! α_child α_parent)
     ;; 型の region 欄は未解決の RVar または concrete な ρ を運ぶ。
     ;; RVar はそのまま制約へ渡し、concrete な欄だけ per-IR bridge で
     ;; region 項へ戻して、制約の寿命項の表現を揃える。
     (define parent-term
       (if (or (lifetime-var? α_parent) (rparam-term? α_parent))
           α_parent
           (rho->region ir α_parent)))
     (define derived? (tracked-child-alpha? α_parent))
     (define branch-born? (branch-region-enclosing? ir point))
     (define ρ_child
       (if (or derived? branch-born?)
           (region-at/branch ir point)
           (region-at ir point)))
     (when (or derived? branch-born?) (track-child-alpha! α_child))
     (define tokens
       (typing-borrow-token-key (enter-child Λ 0) operand #:fail fail))
     (when (set-empty? tokens)
       (error 'infer-reborrow
              "親の token を特定できない operand: ~s"
              operand))
     (define parent-designators
       (uniform-token-designators tokens core fail))
     ;; 合流後は operand の全実起点だけを停止し、同じ capability の古い要求を拾わない。
     (define parent-sources (capability-source τ_operand))
     ;; Reborrow 自体も親可変 capability の使用である。二つ目の Reborrow が
     ;; 窓の中で親を使うことを、停止中の親への通常の使用として判定する。
     ;; 窓なしの経路は従来どおり σ だけで判定する。
     (define (existing-mut cap)
       (define matches
         (for/list ([entry (in-set (psi-mut Ψ_1))]
                    #:when (and (equal? (first entry) (car cap))
                                (path-prefix? (second entry) (cdr cap))))
           entry))
       (define exact
         ;; ρ の親は IR region term へ変換済みなので Ψ と同じ表現で照合する。
         (filter (lambda (entry) (equal? (third entry) parent-term)) matches))
       (cond
         [(pair? exact) exact]
         [(not (set-empty? parent-sources))
          (filter (lambda (entry)
                    (set-member? parent-sources (third entry)))
                  matches)]
         [(= (length matches) 1) matches]
         [else '()]))
     (define parent-terms
       (for/hash ([cap (in-set tokens)])
         (define existing (existing-mut cap))
         (values cap
                 (if (pair? existing)
                     (map third existing)
                     (list parent-term)))))
     (for ([w (in-list parent-designators)])
       (route-constraint!
        (region-constraint 'contains α_child ρ_child point core)
        w core fail))
     (for ([cap (in-set tokens)])
       (define w (car cap))
       (define fp (cdr cap))
       (define reborrow-window (reborrow-window-point w point))
       (when reborrow-window
         ;; operand は Reborrow の停止開始より先に評価される。
         (emit-use-request! operand-Λ w fp 'read parent-sources
                           core 'borrow-conflicting-use #f fail))
       (for ([α_parent (in-list (hash-ref parent-terms cap))])
         (route-constraint!
          (region-constraint 'reborrow α_parent α_child point core)
          w core fail reborrow-window fp fp))
       ;; 外部から渡された concrete な可変借用は、借用要求を core 内で
       ;; 生成していない。各 token を親の要求として記録し、境界の先でも
       ;; Move/Drop の判定へ届かせる。core 内ですでに Ψ にある要求は
       ;; synthetic request を重ねない。
       (unless (or (lifetime-var? α_parent)
                   (rparam-term? α_parent)
                   (pair? (existing-mut cap)))
         (route-request! (borrow-request w fp 'mut parent-term parent-term
                                         core point)
                         core fail)))
     ;; Reborrow の結果そのものも共有借用として判定要求へ記録する。
     ;; 親を停止窓から除いたあとも、子と別の可変借用との衝突は残す必要がある。
     (for ([cap (in-set tokens)])
       (define w (car cap))
       (define fp (cdr cap))
       (route-request! (borrow-request w fp 'shared α_child
                                       ρ_child
                                       core point)
                       core fail))
     ;; concrete な親は Ψ に元の mut 項目が無い環境由来の借用である。
     ;; synthetic request と親子除外を同じ規則へ揃えるため、判定用の
     ;; suspension tuple だけは実在する mut capability として張る。
     (define Ψ_seed
       (if (or (lifetime-var? α_parent)
               (rparam-term? α_parent))
           Ψ_1
           (for/fold ([Ψ_acc Ψ_1]) ([cap (in-set tokens)])
             (if (pair? (existing-mut cap))
                 Ψ_acc
                 (psi-add-mut Ψ_acc (car cap) (cdr cap) parent-term)))))
     (define Ψ_2
       (for/fold ([Ψ_acc Ψ_seed]) ([cap (in-set tokens)])
         (for/fold ([Ψ_inner Ψ_acc])
                   ([α_parent (in-list (hash-ref parent-terms cap))])
           (psi-suspend Ψ_inner
                        (car cap)
                        (cdr cap)
                        α_parent
                        α_child
                        'shared
                        core
                        point))))
     (list `(Borrowed ,τ ,α_child) ε_operand Ψ_2)]
    [_ (fail 'reborrow-non-mutable core)]))

;; 構成検査では入力の実行時借用値から capability を得て、注釈 ρ の共有借用へ落とす。
(define (infer-reborrow/config core operand ρ Λ Ψ environment
                               places callables fail)
  (define operand-result
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (match (normalize-type τ_operand)
    [`(BorrowedMut ,τ ,_ρ_parent)
     (define tokens
       (typing-borrow-token-key (enter-child Λ 0) operand #:fail fail))
     (when (set-empty? tokens)
       (fail 'unresolved-borrow-owner core))
     (list `(Borrowed ,τ ,ρ) ε_operand Ψ_1)]
    [_ (fail 'reborrow-non-mutable core)]))

;; §8.1。合流した α を、借用の項が直接採番した α だけの集合へ展開する。
;; 中間の合流 α を残してはならない。循環は不変条件の破れとして error にする。
(define (alpha-set ρ)
  (cond
    [(not (lifetime-var? ρ)) (set)]
    [else
     (let expand ([α ρ] [seen (set)])
       (cond
         [(set-member? seen α)
          (error 'alpha-set "合流した α の対応が循環している: ~s" α)]
         [(hash-ref (merge-alpha-sources) α #f)
          => (lambda (branches)
               (for/fold ([acc (set)]) ([β (in-set branches)])
                 (if (lifetime-var? β)
                     (set-union acc (expand β (set-add seen α)))
                     acc)))]
         [else (set α)]))]))

;; §8.1。capability の起点となる借用の α の集合を返す。
;; 具体的な ρ と借用でない型は起点の寿命を運ばないので空集合である。
(define (capability-source type)
  (match (normalize-type type)
    [`(Borrowed ,_ ,ρ) (alpha-set ρ)]
    [`(BorrowedMut ,_ ,ρ) (alpha-set ρ)]
    [_ (set)]))

;; [REQ: BOR-004] 値位置の可変親射影は新しい α と停止を作る。
;; Read/Assign の place 位置と共有親射影は親の α を使う（spec §3.1, §3.7）。
(define (infer-projborrow core operand label Λ Ψ environment places callables fail)
  (define field-label (peel-lbl label))
  (define point (region-ctx-point Λ))
  (define ir (region-ctx-ir Λ))
  (define place?
    (cond
      [ir (region-projborrow-place? ir point)]
      [(deriving-config?)
       (set-member? (or (config-projborrow-place-points) (set)) point)]
      [else #f]))
  (define operand-result
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (define-values (m_parent τ_inner α)
    (match (normalize-type τ_operand)
      [`(Borrowed ,τ ,α) (values 'Borrowed τ α)]
      [`(BorrowedMut ,τ ,α) (values 'BorrowedMut τ α)]
      [_ (fail 'projborrow-non-record core)]))
  (define row
    (match (normalize-type τ_inner)
      [`(Record ,r) r]
      [_ (fail 'projborrow-non-record core)]))
  (define field
    (or (assoc field-label row)
        (fail 'projborrow-unknown-field core)))
  (when (field-optional? field)
    (fail 'projborrow-optional-field core))
  (match-define (list _ τ_f m_f) field)
  ;; spec §5.4 の例外。直接の Owned payload は Borrowed の禁止形になる。
  (when (match (normalize-type τ_f) [`(Owned ,_) #t] [_ #f])
    (fail 'borrowed-owned-payload core))
  (define source (use-source Λ operand τ_operand))
  (define tokens
    (typing-borrow-token-key (enter-child Λ 0) operand #:fail fail))
  (for ([cap (in-set tokens)])
    (emit-use-request! Λ (car cap) (append (cdr cap) (list field-label)) 'read source
                       core 'borrow-conflicting-use #f fail))
  (define projected-name (proj-borrow-mode m_parent m_f))
  (define child-mode (if (eq? projected-name 'BorrowedMut) 'mut 'shared))
  (cond
    [(deriving-config?)
     ;; 現在の machine 値は注釈 ρ を持つ一時 view である。place mark はこの
     ;; 節点を source 型検査の place/value 分岐へ誤って流さないために読む。
     (define ρ
       (match (peel-node core)
         [`(ProjBorrowAt ,annotated-ρ ,_ ,_) annotated-ρ]
         [_ (fail 'ill-typed core)]))
     (list `(,projected-name ,τ_f ,ρ) ε_operand Ψ_1)]
    [(and ir
          (eq? m_parent 'BorrowedMut)
          (not place?)
          (for/or ([cap (in-set tokens)]) (formal-key? (car cap))))
     (define parent-designators (uniform-token-designators tokens core fail))
     (define α_child (fresh-lifetime! point))
     (record-binder-alpha-descendant! α_child α)
     (define branch-born? (branch-region-enclosing? ir point))
     (define ρ_child
       (if branch-born?
           (region-at/branch ir point)
           (region-at ir point)))
     (when branch-born? (track-child-alpha! α_child))
     (define parent-term
       (if (or (lifetime-var? α) (rparam-term? α))
           α
           (rho->region ir α)))
     (for ([w (in-list parent-designators)])
       (route-constraint!
        (region-constraint 'contains α_child ρ_child point core)
        w core fail))
     (for ([cap (in-set tokens)])
       (define w (car cap))
       (define parent-fp (cdr cap))
       (define child-fp (append parent-fp (list field-label)))
       (route-constraint!
        (region-constraint 'reborrow parent-term α_child point core)
        w core fail #f parent-fp child-fp)
       (route-request!
        (borrow-request w child-fp child-mode α_child ρ_child core point)
        core fail))
     (list `(,projected-name ,τ_f ,α_child) ε_operand Ψ_1)]
    [(and ir
          (eq? m_parent 'BorrowedMut)
          (not place?)
          (not (for/or ([cap (in-set tokens)]) (formal-key? (car cap)))))
     (when (set-empty? tokens) (fail 'unresolved-borrow-owner core))
     (define parent-designators (uniform-token-designators tokens core fail))
     (define α_child (fresh-lifetime! point))
     (record-binder-alpha-descendant! α_child α)
     (define scrutinee-child?
       (region-decomposition-scrutinee? ir point))
     (define derived? (tracked-child-alpha? α))
     (define branch-born? (branch-region-enclosing? ir point))
     (define ρ_child
       (cond
         [scrutinee-child? (region-at/eliminate ir point)]
         [(or derived? branch-born?) (region-at/branch ir point)]
         [else (region-at ir point)]))
     (when (or scrutinee-child? derived? branch-born?)
       (track-child-alpha! α_child))
     (define parent-term
       (if (or (lifetime-var? α) (rparam-term? α))
           α
           (rho->region ir α)))
     (define parent-sources (capability-source τ_operand))
     (define (existing-mut cap)
       (define matches
         (for/list ([entry (in-set (psi-mut Ψ_1))]
                    #:when (and (equal? (first entry) (car cap))
                                (path-prefix? (second entry) (cdr cap))))
           entry))
       (define exact
         (filter (lambda (entry) (equal? (third entry) parent-term)) matches))
       (cond
         [(pair? exact) exact]
         [(not (set-empty? parent-sources))
          (filter (lambda (entry)
                    (set-member? parent-sources (third entry)))
                  matches)]
         [else '()]))
     (define parent-terms
       (for/hash ([cap (in-set tokens)])
         (define existing (existing-mut cap))
         (values cap (if (pair? existing)
                         (map third existing)
                         (list parent-term)))))
     (for ([w (in-list parent-designators)])
       (route-constraint!
        (region-constraint 'contains α_child ρ_child point core)
        w core fail))
     (for ([cap (in-set tokens)])
       (define w (car cap))
       (define fp (cdr cap))
       (for ([α_parent (in-list (hash-ref parent-terms cap))])
         (route-constraint!
          (region-constraint 'reborrow α_parent α_child point core)
          w core fail))
       (unless (or (lifetime-var? α)
                   (rparam-term? α)
                   (pair? (existing-mut cap)))
         (route-request!
          (borrow-request w fp 'mut parent-term parent-term core point)
          core fail)))
     (for ([cap (in-set tokens)])
       (route-request!
        (borrow-request (car cap)
                        (append (cdr cap) (list field-label))
                        child-mode α_child ρ_child core point)
        core fail))
     (define Ψ_seed
       (for/fold ([Ψ_acc Ψ_1]) ([cap (in-set tokens)])
         (if (pair? (existing-mut cap))
             Ψ_acc
             ;; 内側の Reborrow が除いた親項目を戻し、次の停止関係を記録する。
             (psi-add-mut Ψ_acc (car cap) (cdr cap) parent-term))))
     (define Ψ_child
       (for/fold ([Ψ_acc Ψ_seed]) ([cap (in-set tokens)])
         (for/fold ([Ψ_inner Ψ_acc])
                   ([α_parent (in-list (hash-ref parent-terms cap))])
           (psi-suspend Ψ_inner
                        (car cap)
                        (append (cdr cap) (list field-label))
                        α_parent α_child child-mode core point))))
     (list `(,projected-name ,τ_f ,α_child) ε_operand Ψ_child)]
    [else (list `(,projected-name ,τ_f ,α) ε_operand Ψ_1)]))

;; spec §4 分岐 2。α から所有者の region を引く。
;; 借用の生成は BOR-001 の上限制約 (outlives ρ_owner α) を必ず出すため、
;; 収集器の中に α を右辺とする outlives があれば、その左辺が所有者の region である。
(define (lifetime-owner-region alpha)
  (for/first ([c (in-list (collected-constraints))]
              #:when (and (eq? (region-constraint-kind c) 'outlives)
                          (equal? (region-constraint-right c) alpha)))
    (region-constraint-left c)))

;; Read には内側の可変 loan を再借用する規則がなく、複製は排他参照を二つにする。
(define (borrow-payload-borrow-free? type #:reject-borrowed-mut? [reject-borrowed-mut? #t])
  (let walk ([t type] [visited (set)])
    (match t
      [`(Borrowed ,payload ,_) (not (borrowed-type-anywhere? payload))]
      [`(BorrowedMut ,payload ,_)
       (and (not reject-borrowed-mut?)
            (not (borrowed-type-anywhere? payload)))]
      [`(Data ,name (,arguments ...))
       (define key (cons name arguments))
       (define schema (data-schema name arguments))
       (and schema
            (or (set-member? visited key)
                (for/and ([field (in-list (data-field-types name arguments))])
                  (walk field (set-add visited key)))))]
      [(? list? terms)
       (andmap (lambda (term) (walk term visited)) terms)]
      [_ #t])))

;; 型の中の借用がすべて所有者を追えることを確かめ、α の列を返す。
;; 借用以外の複製できない構成子は reason で落とす。
;; 所有者が引けない借用は関数の境界を越えて入ってきたものであり、
;; borrow.md 14 節 1 項により本サイクルでは受け取らない。
(define (payload-borrows-traceable? type reason core fail
                                    #:reject-borrowed-mut? [reject-borrowed-mut? #t])
  (define scanned (copy-out-scan type))
  (unless scanned (fail reason core))
  (unless (borrow-payload-borrow-free?
           type #:reject-borrowed-mut? reject-borrowed-mut?)
    (fail reason core))
  (for ([alpha (in-list scanned)])
    (unless (lifetime-owner-region alpha)
      (fail 'borrow-unknown-owner-region core)))
  scanned)

;; [REQ: BOR-005] 借用が指す先の値を複製する。結果は借用でも所有値でもない。
;; ρ は結果の型に現れない（spec §6.1）。
(define (infer-read core operand Λ Ψ environment places callables fail)
  (define operand-result
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (define-values (τ_payload α_view)
    (match (normalize-type τ_operand)
      [`(Borrowed ,τ ,α) (values τ α)]
      [`(BorrowedMut ,τ ,α) (values τ α)]
      [_ (fail 'read-non-borrow core)]))
  (define α_inner
    (payload-borrows-traceable? τ_payload 'read-uncopyable-payload core fail))
  ;; borrow.md §12。読み出した値の中の借用は view の region を超えない。
  ;; BOR-001 と同じ形の上限制約であり、違反は borrow-escapes-owner で報告される。
  (for ([α (in-list α_inner)])
    (emit-constraint!
     (region-constraint 'outlives α_view α (region-ctx-point Λ) core)))
  (define source (use-source Λ operand τ_operand))
  (for ([cap (in-set
              (typing-borrow-token-key (enter-child Λ 0) operand #:fail fail))])
    (emit-use-request! Λ (car cap) (cdr cap) 'read source
                       core 'borrow-conflicting-use #f fail))
  (list τ_payload ε_operand Ψ_1))

;; [REQ: BOR-004] 可変借用 capability を通じた代入だけを許す。
;; Union payload は値全体の tag 保存互換で照合する。
(define (infer-assign core target value Λ Ψ environment places callables fail)
  (define target-result
    (infer target (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_target
    (typing-normal-child-type core Λ 0 (first target-result)))
  (define ε_target (second target-result))
  (define Ψ_1 (third target-result))
  (define τ_target* (normalize-type τ_target))
  (define-values (τ_payload α_target)
    (match τ_target*
      [`(BorrowedMut ,τ ,α) (values τ α)]
      [`(Borrowed ,_ ,_) (fail 'assign-through-shared core)]
      [_ (fail 'assign-non-borrow core)]))
  ;; Assign は lifetime を追跡するが、Read の copy-out 判定は適用しない。
  (payload-borrows-traceable? τ_payload 'assign-owned-payload core fail
                               #:reject-borrowed-mut? #f)
  (match-define (list τ_value ε_value Ψ_2)
    (infer value (enter-child Λ 1) Ψ_1 environment places callables fail))
  ;; 書き込む値の借用は、書き込み先の view より長く生きなければならない。
  ;; 短ければ view を通じて解放済みの借用を読み出せる。
  (define α_value
    (payload-borrows-traceable? τ_value 'assign-owned-payload core fail
                                 #:reject-borrowed-mut? #f))
  (for ([α (in-list α_value)])
    (emit-constraint!
     (region-constraint 'outlives α α_target (region-ctx-point Λ) core)))
  (unless (type-compatible? τ_value τ_payload)
    (fail 'assign-union-variant core))
  (check-borrow-hiding! τ_value τ_payload core fail)
  (unless (storage-ok? τ_payload)
    (fail 'mutable-callable-storage-requires-partial core τ_payload))
  (define source (use-source Λ target τ_target))
  (define target-capabilities
    (typing-borrow-token-key (enter-child Λ 0) target #:fail fail))
  (reject-variant-view-write! Λ target-capabilities core fail)
  (for ([cap (in-set target-capabilities)])
    (emit-use-request! Λ (car cap) (cdr cap) 'assign source
                       core 'borrow-conflicting-use #f fail))
  (list 'Unit (rows-union (list ε_target ε_value '(Mutation))) Ψ_2))

;; spec §7.1 §7.2。Reassign は固定された slot の中身を差し替える。slot の型は
;; binding の宣言で決まり、再代入で変わらない。imm 欄への mut 欄の代入を許す
;; reassign-narrowing? で値を照合する。
;; 一般の compat? は余剰 Owned を落としうる。
(define (infer-reassign core target flow-type value Λ Ψ
                        environment places callables fail)
  (define τ_slot
    (match target
      ;; 実行時の形。R-LetMutB が置いた mut の slot である。
      [`(MutSlot ,place)
       (define type (lookup places place))
       (unless type (fail 'unknown-place core))
       type]
      [(? exact-nonnegative-integer?)
       ;; 裸の place は R-LetOwnedB が置いた形であり、再代入の対象ではない。
       (fail 'immutable-binding core)]
      [_
       (define name (peel-node target))
       (define type (lookup environment name))
       (unless type (fail 'unbound-variable core))
       (unless (eq? (binding-mode-of environment name) 'mut)
         (fail 'immutable-binding core))
       type]))
  (define τ_flow (peel-ty flow-type))
  (match-define (list τ_value ε_value Ψ_1)
    (infer value (enter-child Λ 0) Ψ environment places callables fail))
  (cond
    [(eq? τ_value 'Never) (list 'Never ε_value Ψ_1)]
    [else
     (define key
       (match target
         [`(MutSlot ,place) `(MutSlot ,place)]
         [_ (peel-node target)]))
     (define current-state (flow-state-normal (psi-flow Ψ_1)))
     (define flow-entry*
       (and (hash? current-state) (hash-ref current-state key #f)))
     (define declared
       (if flow-entry*
           (flow-entry-declared flow-entry*)
           (and (not (deriving-config?)) τ_slot)))
     ;; config の許容は、静的に型付けされた Core の RSD が除去後に残した
     ;; 非資源・非借用の物理的な余剰欄を再型付けするときに限る。
     (unless (or (reassign-narrowing? τ_value τ_flow)
                 (and (deriving-config?)
                      (mut-slot-type-supported? τ_value)
                      (config-view-compatible? τ_value τ_flow)))
       (fail 'reassign-type-mismatch core τ_flow τ_value))
     (check-borrow-hiding! τ_value τ_flow core fail reassign-narrowing?)
     (when (and declared
                (not (tag-compat? τ_flow declared
                                  (current-Γ-pc0) (current-region-relation))))
       (fail 'reassign-type-mismatch core declared τ_flow))
     (when (not (mut-slot-type-supported? τ_flow))
       (fail 'mut-binding-unsupported-type core τ_flow))
     (unless (storage-ok? τ_flow)
       (fail 'mutable-callable-storage-requires-partial core τ_flow))
     (define pins (and flow-entry* (flow-entry-pins flow-entry*)))
     (when (and pins
                (for/or ([pin (in-set pins)])
                  (not (type-equiv? τ_flow pin))))
       (fail 'reassign-type-mismatch core pins τ_flow))
     (define next-entry
       (flow-entry declared τ_flow pins))
     (list 'Unit (rows-union (list ε_value '(Mutation)))
           (if (and (hash? current-state)
                    (or flow-entry* (not (deriving-config?))))
               (flow-update Ψ_1 key next-entry)
               Ψ_1))]))

;; unsafe.md §2.2。pointer の型成分を検査し、成分の並びを返す。
(define (pointer-parts core type fail)
  (define normalized (normalize-type type))
  (match normalized
    [`(RawPtr ,τ ,ptrmut ,nul ,align ,as ,prov)
     ;; unsafe.md §3.1。5 成分の許可集合は validators.rkt の
     ;; raw-ptr-components-ok?（G5c7a1 Task 3）に閉じてある。
     ;; type-shape-ok? と同じ helper を通し、判定の分岐を作らない。
     (unless (raw-ptr-components-ok? normalized)
       (unless (addr-space-ok? as) (fail 'invalid-address-space core))
       (unless (prov-ok? prov) (fail 'invalid-provenance core))
       (fail 'ptr-malformed core))
     (list τ ptrmut nul align as prov)]
    [_ (fail 'ptr-non-pointer core)]))

;; unsafe.md §2.2。store 先が Mut の pointer であることを検査する。
;; fail を引数で受ける形は payload-borrows-traceable?（typing.rkt:2005）の
;; 先例に揃える。Const の pointer を作る項が本サイクルに無いため、
;; 単体で呼べる形へ切り出す。
(define (raw-store-target-check type fail)
  (match (normalize-type type)
    [`(RawPtr ,_ Mut ,_ ,_ ,_ ,_) type]
    [`(RawPtr ,_ ,_ ,_ ,_ ,_ ,_) (fail 'rawstore-const-pointer type)]
    [_ (fail 'ptr-non-pointer type)]))

;; unsafe.md §4.1。(Unsafe c) の内側だけ、未解決の PtrProp を許可する。
;; ownleaf-permitted と同じく、包む構成子が本体の検査を parameterize する形を
;; 採る（typing.rkt:2612 の Yield が先例）。
(define unsafe-permitted (make-parameter #f))

(define (raw-load-obligation-ids)
  '(AliveAllocation NonNull Aligned Initialized Readable InBounds))

;; store は未初期化の領域を初期化する操作でもあるため Initialized を要求しない。
(define (raw-store-obligation-ids)
  '(AliveAllocation NonNull Aligned Writable InBounds))

(define (ptr-offset-obligation-ids)
  '(AliveAllocation InBounds))

(define (raw-obligations ids type)
  (for/list ([id (in-list ids)]) `(PtrProp ,id ,type)))

;; unsafe.md §4.1。obligation が Γ-pc0 から暗黙充足できないとき、Unsafe
;; boundary の内側でだけ未解決を許可する。PtrProp は validator 表に無いため、
;; 実際には boundary の内側であることが条件になる。
(define (check-raw-obligations! core ids pointee fail)
  (unless (or (unsafe-permitted)
              (obligations-dischargeable? (raw-obligations ids pointee)
                                          (current-Γ-pc0)))
    (fail 'unsafe-outside-boundary core)))

;; unsafe.md §2.2。生きた可変借用から native の owned pointer を作る。
;; 6 引数はすべて生成源の値へ固定し、書き手に選ばせない。
;; AddressOf 自身は H を触らないため Unsafe を row へ載せない。
(define (infer-address-of core operand Λ Ψ environment places callables fail)
  (define operand-result
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (define τ_payload
    (match (normalize-type τ_operand)
      [`(BorrowedMut ,τ ,_) τ]
      [_ (fail 'address-of-non-mut-borrow core)]))
  (list `(RawPtr ,τ_payload Mut NonNull (Align 1)
                 (AddrSpace native) (Prov owned))
        ε_operand
        Ψ_1))

;; unsafe.md §2.2。offset の結果が非 null である保証は無いため
;; nul を Nullable へ落とす。ptrmut と align と as と prov は保つ。
(define (infer-ptr-offset core operand offset Λ Ψ environment places callables fail)
  (define operand-result
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (match-define (list τ_offset ε_offset Ψ_2)
    (infer offset (enter-child Λ 1) Ψ_1 environment places callables fail))
  (unless (type-compatible? (normalize-type τ_offset) 'Int)
    (fail 'ptr-offset-non-int core))
  (match-define (list τ_payload ptrmut _nul align as prov)
    (pointer-parts core τ_operand fail))
  (check-raw-obligations! core (ptr-offset-obligation-ids) τ_payload fail)
  (record-ptr-request! 'ptr-offset core (ptr-offset-obligation-ids))
  (list `(RawPtr ,τ_payload ,ptrmut Nullable ,align ,as ,prov)
        (rows-union (list ε_operand ε_offset '(Unsafe)))
        Ψ_2))

(define (infer-raw-load core operand Λ Ψ environment places callables fail)
  (define operand-result
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (match-define (list τ_payload _ptrmut _nul _align _as _prov)
    (pointer-parts core τ_operand fail))
  (check-raw-obligations! core (raw-load-obligation-ids) τ_payload fail)
  (record-ptr-request! 'raw-load core (raw-load-obligation-ids))
  (list τ_payload (row-union ε_operand '(Unsafe)) Ψ_1))

(define (infer-raw-store core target value Λ Ψ environment places callables fail)
  (define target-result
    (infer target (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_target
    (typing-normal-child-type core Λ 0 (first target-result)))
  (define ε_target (second target-result))
  (define Ψ_1 (third target-result))
  ;; 失敗記号の details を core へ揃えるため、fail を包み直して渡す。
  (raw-store-target-check τ_target (lambda (key _node) (fail key core)))
  (match-define (list τ_value ε_value Ψ_2)
    (infer value (enter-child Λ 1) Ψ_1 environment places callables fail))
  (match-define (list τ_payload _ptrmut _nul _align _as _prov)
    (pointer-parts core τ_target fail))
  (unless (type-compatible? τ_value τ_payload)
    (fail 'rawstore-type-mismatch core))
  (check-borrow-hiding! τ_value τ_payload core fail)
  (check-raw-obligations! core (raw-store-obligation-ids) τ_payload fail)
  (unless (storage-ok? τ_payload)
    (fail 'mutable-callable-storage-requires-partial core τ_payload))
  (record-ptr-request! 'raw-store core (raw-store-obligation-ids))
  (list 'Unit (rows-union (list ε_target ε_value '(Unsafe Mutation))) Ψ_2))

;; unsafe.md §3.3。lifetime、alignment、validity の Proof を要求する。
(define (from-raw-ptr-obligation-ids)
  '(LifetimeValid Aligned Initialized AliveAllocation NonNull))

;; unsafe.md §3.3。借用台帳が追跡できる pointer に限る。(Prov foreign) と
;; (Prov unknown) は H の place を指すとは限らない。native 以外の address
;; space も同じ理由で落とす。ptrmut で借用の種を分ける。
(define (from-raw-ptr-result-type type region fail)
  (match (normalize-type type)
    [`(RawPtr ,τ ,ptrmut ,_nul ,_align ,as ,prov)
     ;; 現在は pointer-parts が先に address space と provenance を閉じるため、
     ;; この二つの枝へ到達しない。§11 で非 native/foreign pointer を開くときに使う。
     (unless (equal? as '(AddrSpace native))
       (fail 'from-raw-ptr-non-native type))
     (unless (equal? prov '(Prov owned))
       (fail 'from-raw-ptr-non-owned type))
     (case ptrmut
       [(Const) `(Borrowed ,τ ,region)]
       [(Mut) `(BorrowedMut ,τ ,region)]
       [else (fail 'ptr-non-pointer type)])]
    [_ (fail 'ptr-non-pointer type)]))

(define (infer-from-raw-ptr core operand region Λ Ψ environment
                            places callables fail)
  ;; unsafe.md §3.3。ρ の束縛は既存の region well-formedness と同じ層で見る。
  (unless (deriving-config?)
    (check-region-annotation Λ region core fail))
  (define operand-result
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_operand
    (typing-normal-child-type core Λ 0 (first operand-result)))
  (define ε_operand (second operand-result))
  (define Ψ_1 (third operand-result))
  (match-define (list τ_payload _ptrmut _nul _align _as _prov)
    (pointer-parts core τ_operand fail))
  (check-raw-obligations! core (from-raw-ptr-obligation-ids) τ_payload fail)
  (record-ptr-request! 'from-raw-ptr core (from-raw-ptr-obligation-ids))
  (define result
    (from-raw-ptr-result-type τ_operand region
                              (lambda (key _node) (fail key core))))
  (list result (row-union ε_operand '(Unsafe)) Ψ_1))

;; unsafe.md §4.1、§4.3。境界の外へ Unsafe と未解決 obligation と
;; raw pointer のいずれも出さない。
(define (infer-unsafe core body Λ Ψ environment places callables fail)
  (match-define (list τ_body ε_body Ψ_1)
    (parameterize ([unsafe-permitted #t])
      (infer body (enter-child Λ 0) Ψ environment places callables fail)))
  (when (leaks-rawptr? τ_body)
    (fail 'rawptr-escapes-unsafe core))
  (when (effect-leaks-rawptr? ε_body)
    (fail 'rawptr-escapes-unsafe core))
  (list τ_body (row-difference ε_body '(Unsafe)) Ψ_1))

;; 資源型の Let 変数から欄を読むときは、変数全体を裸で複製せず、
;; 非資源型の欄だけを読む。使用要求には欄の label を capability path として
;; 積むため、同じ欄への可変借用とだけ競合する。
(define (projection-prefix core)
  (match (peel-node core)
    [(? symbol? name) (list name '())]
    [(? exact-nonnegative-integer? place) (list place '())]
    [`(Proj ,record ,label)
     (match (projection-prefix record)
       [(list root path) (list root (append path (list (peel-lbl label))))]
       [_ #f])]
    [_ #f]))

(define (place-projection-info core)
  (match (peel-node core)
    [`(Proj ,record ,label)
     (match (projection-prefix record)
       [(list root path)
        (list root (append path (list (peel-lbl label))) #f)]
       [_ #f])]
    [`(ProjOpt ,type ,record ,label)
     (match (projection-prefix record)
       [(list root path)
        (list root (append path (list (peel-lbl label))) (peel-ty type))]
       [_ #f])]
    [_ #f]))

(define (infer-place-projection core root path optional-type
                                Λ Ψ environment places fail)
  (define root-type
    (if (symbol? root)
        (lookup environment root)
        (lookup places root)))
  (unless root-type (fail 'project-non-record core))
  (define result-type
    (let walk ([type (normalize-type root-type)] [labels path])
      (match type
        [`(Record ,row)
         (define field (assoc (first labels) row))
         (unless field (fail 'unknown-record-label core))
         (define field-type (second field))
         (if (null? (rest labels))
             (begin
               (when (resource-type? field-type)
                 (fail 'owned-variable-requires-move core))
               (cond
                 [(and (not optional-type) (field-optional? field))
                  (fail 'project-optional-field core)]
                 [(and optional-type
                       (not (type-compatible? field-type optional-type)))
                  (fail 'projopt-invalid-field core)])
               (when optional-type
                 (check-borrow-hiding! field-type optional-type core fail))
               (if optional-type `(Option ,optional-type) field-type))
             (if (field-optional? field)
                 (fail 'project-optional-field core)
                 (walk (normalize-type field-type) (rest labels))))]
        [_ (fail 'project-non-record core)])))
  (emit-use-request! Λ root path 'read (set) core
                     'borrow-conflicting-use #f fail)
  (list result-type '() Ψ))

(define (place-projection-root? root places)
  (or (and (symbol? root)
           (set-member? (resource-place-set) root))
      (and (exact-nonnegative-integer? root)
           (lookup places root))))

;; G1/G2 の E に現れる正格な子と、通常の規則がその型を使う位置をまとめる。
;; 共通の infer/check wrapper がこの表を参照して Never を親へ伝えるため、
;; 個別の infer 節が参照しない Perform の項も評価文脈の網羅表として必要である。
;; 子の添字は region.rkt の core-children と同じである。
(define typing-evaluation-contexts
  '((Apply all (0))
    (Let (0) ())
    (Construct all ())
    (Eliminate (0) (0))
    (Perform (0) ())
    (Drop (0) (0))
    (Yield (0) (0))
    (Curry all (0))
    (Scope (0) ())
    (Handle handle-body ())
    (OwnLeaf (0) ())
    (Rec record-fields record-fields)
    (Discharge (0) (0))
    (UnionInject (0) ())
    (UnionEliminate (0) (0))
    (RecRewrite (0) (0))
    (RecRewriteOpen open-fields unannotated-open-fields)
    (Proj (0) (0))
    (ProjOpt (0) (0))
    (ReborrowAt (0) (0))
    (ProjBorrowAt (0) (0))
    (Read (0) (0))
    (Assign all (0))
    (Reassign (0) ())
    (RegionApp (0) (0))
    (AddressOf (0) (0))
    (PtrOffset all (0))
    (RawLoad (0) (0))
    (RawStore all (0))
    (FromRawPtr (0) (0))
    (Unsafe (0) ())))

(define typing-normal-results (make-parameter #f))

(define (typing-context-rule core)
  (define term (peel-node core))
  (and (pair? term) (assq (car term) typing-evaluation-contexts)))

(define (typing-context-indices core selector)
  (define children (core-children (peel-node core)))
  (cond
    [(eq? selector 'all) (range (length children))]
    [(eq? selector 'handle-body) '(1)]
    [(eq? selector 'record-fields)
     (for/list ([field (in-list (second (peel-node core)))]
                [index (in-naturals)]
                #:unless (match (peel-node (third field))
                           [`(Absent ,_) #t]
                           [_ #f]))
       index)]
    [(eq? selector 'open-fields)
     (for/list ([field (in-list (second (peel-node core)))]
                [index (in-naturals)]
                #:unless (match (peel-node (last field))
                           [`(Absent ,_) #t]
                           [_ #f]))
       index)]
    [(eq? selector 'unannotated-open-fields)
     (for/list ([field (in-list (second (peel-node core)))]
                [index (in-naturals)]
                #:when (and (= (length field) 3)
                            (not (match (peel-node (last field))
                                   [`(Absent ,_) #t]
                                   [_ #f]))))
       index)]
    [(list? selector) selector]
    [else '()]))

(define (typing-result-at Λ)
  (define table (typing-normal-results))
  (and table (hash-ref table (region-ctx-point Λ) #f)))

(define (typing-child-result Λ index)
  (typing-result-at (enter-child Λ index)))

(define (typing-child-normal-type Λ index)
  (match (typing-child-result Λ index)
    [(list _ normal-type _ _) normal-type]
    [_ #f]))

(define (typing-normal-child-type core Λ index actual-type)
  (define rule (typing-context-rule core))
  (define required
    (and rule
         (member index (typing-context-indices core (third rule)))))
  (if (and required (eq? actual-type 'Never))
      (let ([normal-type (typing-child-normal-type Λ index)])
        (if (and normal-type (not (eq? normal-type '⊥)))
            normal-type
            actual-type))
      actual-type))

(define (typing-context-never? core Λ)
  (define rule (typing-context-rule core))
  (and rule
       (not (eq? (first rule) 'Handle))
       (let ([indices (typing-context-indices core (second rule))])
         (for/or ([index (in-list indices)])
           (match (typing-child-result Λ index)
           [(list 'Never _ _ _) #t]
            [_ #f])))))

(define (typing-normal-from-let Λ)
  (match* ((typing-child-result Λ 0) (typing-child-result Λ 1))
    [((list bound-type _ _ _) (list body-type body-normal _ _))
     (if (eq? bound-type 'Never)
         (if (eq? body-type 'Never) '⊥ body-normal)
         body-normal)]
    [(_ _) '⊥]))

(define (typing-handle-propagates-never? core Λ)
  (match (peel-node core)
    [`(Handle (Return ,boundary ,type) ,_ ,_)
     (define operation (return-operation-key boundary type))
     (match (typing-child-result Λ 1)
       ;; E は latent row の上界なので、operation 鍵の不在だけを Never 判定に使う。
       [(list 'Never _ _ escape-operations)
        (not (member operation escape-operations equal?))]
       [_ #f])]
    [`(Handle ,operation ,_ ,_)
     (match (typing-child-result Λ 1)
       [(list 'Never _ body-row _)
        (not (member operation body-row effect-equiv?))]
       [_ #f])]
    [_ #f]))

(define (typing-result-never? core Λ raw-type)
  (or (eq? raw-type 'Never)
      (typing-context-never? core Λ)
      (typing-handle-propagates-never? core Λ)))

(define (typing-normal-from-infer core Λ raw-type)
  (define term (peel-node core))
  (cond
    [(and (match term [`(Handle ,_ ,_ ,_) #t] [_ #f])
          (typing-handle-propagates-never? core Λ))
     (or (typing-child-normal-type Λ 1) '⊥)]
    [(not (eq? raw-type 'Never)) raw-type]
    [else
     (match term
       [`(Let ,_ ,_ ,_)
        (typing-normal-from-let Λ)]
       [`(Suspend ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Scope ,_ ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(OwnLeaf ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(OwnedLeaf ,_ ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Unsafe ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Discharge ,_ ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Yield ,_ ,_) (or (typing-child-normal-type Λ 1) '⊥)]
       [`(Recur ,_ ,_ ,_ ,_ ,_)
        (or (typing-child-normal-type Λ 1) '⊥)]
       [`(Handle ,_ ,_ ,_)
        (if (typing-handle-propagates-never? core Λ)
            (or (typing-child-normal-type Λ 1) '⊥)
            '⊥)]
       [_ '⊥])]))

(define (typing-normal-from-check core Λ expected actual-type)
  (cond
    [(typing-result-at Λ)
     => (lambda (result) (second result))]
    [(and (match (peel-node core) [`(Handle ,_ ,_ ,_) #t] [_ #f])
          (typing-handle-propagates-never? core Λ))
     (or (typing-child-normal-type Λ 1) '⊥)]
    [(not (eq? actual-type 'Never)) actual-type]
    [else
     (match (peel-node core)
       [`(Let ,_ ,_ ,_)
        (typing-normal-from-let Λ)]
       [`(Suspend ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Scope ,_ ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(OwnLeaf ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Unsafe ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Discharge ,_ ,_) (or (typing-child-normal-type Λ 0) '⊥)]
       [`(Yield ,_ ,_) (or (typing-child-normal-type Λ 1) '⊥)]
       [`(Recur ,_ ,_ ,_ ,_ ,_)
        (or (typing-child-normal-type Λ 1) '⊥)]
       [`(Handle ,_ ,_ ,_)
        (if (typing-handle-propagates-never? core Λ)
            (or (typing-child-normal-type Λ 1) '⊥)
            expected)]
       [_ '⊥])]))

(define (record-typing-result! Λ actual-type normal-type row escape-operations)
  (define table (typing-normal-results))
  (when table
    (hash-set! table (region-ctx-point Λ)
               (list actual-type normal-type row escape-operations))))

(define (psi-escape-operations Ψ)
  ;; wrapper は入口で E を消すため、restore 前の Ψ に局所 E だけが残る。
  (hash-keys (flow-state-escapes (psi-flow Ψ))))

(define (infer core Λ Ψ environment places callables fail)
  (if (not (typing-normal-results))
      (parameterize ([typing-normal-results (make-hash)])
        (infer core Λ Ψ environment places callables fail))
      (let* ([input-psi Ψ]
             [local-psi (flow-clear-escapes Ψ)]
             [raw-result
              (infer/body core Λ local-psi environment places callables fail)]
             [raw-type (first raw-result)]
             [normal-type (typing-normal-from-infer core Λ raw-type)]
             [result-type
              (if (typing-result-never? core Λ raw-type) 'Never raw-type)]
             [result-psi (flow-restore-output input-psi (third raw-result)
                                              normal-type fail core)]
             [result (list result-type (second raw-result) result-psi)])
        ((typing-point-probe) (region-ctx-point Λ))
        (record-typing-result! Λ result-type normal-type (second result)
                               (psi-escape-operations (third raw-result)))
        (emit-expression-decomposition-exits!
         core Λ environment places callables normal-type fail)
        (collect-use-regions! result-type
                              (region-ctx-ir Λ)
                              (region-ctx-point Λ))
        result)))

;; producer 位置から入ったときだけ OwnLeaf を許す。許可は節点そのものを
;; memq で保持するため、兄弟の位置へ漏れない。既定は拒否である。
(define ownleaf-permitted (make-parameter '()))

;; span 付きの core も受けるため peel-node を通す。
(define (ownleaf-root? core)
  (match (peel-node core)
    [`(OwnLeaf ,_) #t]
    [_ #f]))

;; producer 位置の共通 gate。追跡されていない raw Owned payload を通さない
;; ため、根の OwnLeaf を必須にする。診断 key は producer ごとに異なるため
;; 引数で受ける。
(define (require-ownleaf-root core key node fail)
  (unless (ownleaf-root? core)
    (fail key node)))

;; 資源を持つ binder は、token を結果へ一度だけ運べる文脈の穴にだけ置く。
;; siblings は binder-aware な自由変数集合で個別に検査する。
(define (linear-hole? core name)
  (define term (erase-core core))
  (define (free-under-binding? binder body)
    (and (not (eq? (peel-bind binder) name))
         (set-member? (core-free-vars body) name)))
  (define (one-child-hole? children)
    (for/or ([hole (in-list children)]
             [hole-index (in-naturals)])
      (and
       (linear-hole? hole name)
       (for/and ([sibling (in-list children)]
                 [sibling-index (in-naturals)]
                 #:unless (= hole-index sibling-index))
         (not (set-member? (core-free-vars sibling) name))))))
  (match term
    [(? symbol? variable)
     (and (eq? variable name) (redex-match? G2 x variable))]
    [`(UnionInject ,_ ,_ ,payload) (linear-hole? payload name)]
    [`(Discharge ,(app peel-node
                      `(ProofRep ,_ (RemainderSafelyDropped ,_ ,_))) ,inner)
     (linear-hole? inner name)]
    [`(Rec ,_) (one-child-hole? (core-children term))]
    [`(Construct ,_ ,_ ,_ ...) (one-child-hole? (core-children term))]
    [`(RecRewrite ,input (,entries ...))
     (and (linear-hole? input name)
          (for/and ([entry (in-list entries)])
            (match entry
              [`(,_ ,binder ,_ ,_ ,_ ,body)
               (not (free-under-binding? binder body))])))]
    [`(Let (,binder ,mode ,_) ,bound ,body)
     (and (memq mode '(const let))
          (not (eq? (peel-bind binder) name))
          (eq? (peel-node body) (peel-bind binder))
          (linear-hole? bound name))]
    [`(UnionEliminate ,scrutinee (,branches ...))
     (and (linear-hole? scrutinee name)
          (for/and ([branch (in-list branches)])
            (match branch
              [`(,branch-type ,binder -> ,body)
               (and (not (free-under-binding? binder body))
                    (or (not (resource-type? (peel-ty branch-type)))
                        (linear-hole? body (peel-bind binder))))])))]
    [_ #f]))

(define (core-contains-ownleaf? core)
  (let walk ([term (erase-core core)])
    (match term
      [`(OwnLeaf ,_) #t]
      [_ (for/or ([child (in-list (core-children term))])
           (walk child))])))

(define (retained-lifetime-shape type)
  (define (walk type)
    (match type
      [`(Borrowed ,payload ,_) `(Borrowed ,(walk payload) retained-region)]
      [`(BorrowedMut ,payload ,_) `(BorrowedMut ,(walk payload) retained-region)]
      [(? list?) (map walk type)]
      [_ type]))
  (normalize-type (walk type)))

(define (adopt-retained-union-lifetimes expected actual)
  (define expected-members (union-members expected))
  (define actual-members (union-members actual))
  (define expected-shapes (map retained-lifetime-shape expected-members))
  (define actual-shapes (map retained-lifetime-shape actual-members))
  (define adopted
    (for/list ([member (in-list expected-members)]
               [shape (in-list expected-shapes)])
      (define expected-matches
        (for/list ([candidate (in-list expected-members)]
                   [candidate-shape (in-list expected-shapes)]
                   #:when (and shape candidate-shape
                               (type-equiv? shape candidate-shape)))
          candidate))
      (define actual-matches
        (for/list ([candidate (in-list actual-members)]
                   [candidate-shape (in-list actual-shapes)]
                   #:when (and shape candidate-shape
                               (type-equiv? shape candidate-shape)))
          candidate))
      (if (and (= (length expected-matches) 1)
               (= (length actual-matches) 1))
          (adopt-retained-lifetimes member (car actual-matches))
          member)))
  (normalize-type
   (foldr (lambda (member rest)
            (if rest `(Union ,member ,rest) member))
          #f adopted)))

(define (adopt-retained-lifetimes expected actual)
  (match* (expected actual)
    [(`(Union ,_ ,_) _)
     (or (adopt-retained-union-lifetimes expected actual) expected)]
    [(`(Borrowed ,expected-payload ,expected-region)
      `(Borrowed ,actual-payload ,actual-region))
     `(Borrowed ,(adopt-retained-lifetimes expected-payload actual-payload)
                ,(if (equal? expected-region '(RParam %omitted))
                     actual-region
                     expected-region))]
    [(`(BorrowedMut ,expected-payload ,expected-region)
      `(BorrowedMut ,actual-payload ,actual-region))
     `(BorrowedMut ,(adopt-retained-lifetimes expected-payload actual-payload)
                   ,(if (equal? expected-region '(RParam %omitted))
                        actual-region
                        expected-region))]
    [(`(Record ,expected-row) `(Record ,actual-row))
     `(Record
       ,(for/list ([field (in-list expected-row)])
          (define actual-field (field-row-lookup actual-row (first field)))
          (if actual-field
              (list* (first field)
                     (adopt-retained-lifetimes (second field)
                                               (first actual-field))
                     (cddr field))
              field)))]
    [(`(Option ,expected-payload) `(Option ,actual-payload))
     `(Option ,(adopt-retained-lifetimes expected-payload actual-payload))]
    [(`(List ,expected-payload) `(List ,actual-payload))
     `(List ,(adopt-retained-lifetimes expected-payload actual-payload))]
    [(`(Owned ,expected-payload) `(Owned ,actual-payload))
     `(Owned ,(adopt-retained-lifetimes expected-payload actual-payload))]
    [(`(Untrusted ,expected-payload) `(Untrusted ,actual-payload))
     `(Untrusted ,(adopt-retained-lifetimes expected-payload actual-payload))]
    [(`(Refined ,expected-payload ,proposition)
      `(Refined ,actual-payload ,_))
     `(Refined ,(adopt-retained-lifetimes expected-payload actual-payload)
               ,proposition)]
    [(`(Result ,expected-ok ,expected-error)
      `(Result ,actual-ok ,actual-error))
     `(Result ,(adopt-retained-lifetimes expected-ok actual-ok)
              ,(adopt-retained-lifetimes expected-error actual-error))]
    [(`(Data ,name (,expected-arguments ...))
      `(Data ,name (,actual-arguments ...)))
     #:when (= (length expected-arguments) (length actual-arguments))
     `(Data ,name
            ,(for/list ([expected-argument (in-list expected-arguments)]
                        [actual-argument (in-list actual-arguments)])
               (adopt-retained-lifetimes expected-argument actual-argument)))]
    ;; Union/Intersection の成員順や NFn の row 順は寿命の対応を表さない。
    [(_ _) expected]))

(define (infer-remainder-discharge core phi base base-Λ Ψ
                                  environment places callables fail)
  (define origin
    (match (peel-node core)
      [`(Discharge ,proof-rep ,_)
       (match (peel-node proof-rep)
         [`(ProofRep ,o ,_) o])]))
  (match phi
    [`(RemainderSafelyDropped ,tau-actual ,tau-expected)
     (unless (proof-issuer-ok? (current-R0) origin phi)
       (fail 'discharge-proof-issuer core))
     (when (eq? (borrow-hiding-kind tau-actual tau-expected
                                    type-compatible?)
                'reject)
       (fail 'borrow-hidden-by-narrowing core))
     (match (owned-narrowing-kind tau-actual tau-expected type-compatible?)
       ['reject
        (fail 'owned-narrowing-rejected core tau-expected tau-actual)]
       [_
        (match (check-as/full base tau-actual base-Λ
                              Ψ environment places callables fail)
          [(list row result-psi actual*)
           (unless (rsd-proof-pair-ok? tau-actual tau-expected
                                       type-compatible?)
             (define target-type
               (remainder-target-type tau-actual tau-expected))
             (if (and target-type
                      (not (eq? (borrow-hiding-kind target-type tau-expected
                                                   type-compatible?)
                                'ok)))
                 (fail 'borrow-hidden-by-narrowing core)
                 (fail 'owned-narrowing-rejected core
                       tau-expected tau-actual)))
           ;; 証明の row 形は保ち、残る欄の寿命だけを推論結果から採る。
           (list (adopt-retained-lifetimes tau-expected actual*) row result-psi)])])]))

(define (infer-rec-rewrite core input entries Λ Ψ environment places callables fail)
  (define input-result
    (infer input (enter-child Λ 0) Ψ environment places callables fail))
  (match (cons (typing-normal-child-type core Λ 0 (first input-result))
               (rest input-result))
    [(list `(Record ,row) input-row input-psi)
     (define labels
       (for/list ([entry (in-list entries)]) (peel-lbl (first entry))))
     (when (check-duplicates labels)
       (fail 'duplicate-record-label core))
     (define normalized-entries
       (for/list ([entry (in-list entries)])
         (match-define (list label binder tau output-mode output-type body) entry)
         (list (peel-lbl label) (peel-bind binder) (peel-ty tau)
               output-mode (peel-ty output-type) body)))
     (define replacements '())
     (define final-psi
       (for/fold ([current-psi input-psi])
                 ([entry (in-list normalized-entries)]
                  [index (in-naturals)])
         (match-define (list label binder tau output-mode output-type body) entry)
         (define field (assoc label row))
         (unless field (fail 'unknown-record-label core))
         (match-define (list input-type input-mode)
           (field-row-lookup row label))
         (unless (and (or (type-equiv? tau input-type)
                          (and (deriving-config?)
                               (not (owned-type? tau))
                               (config-view-compatible? input-type tau)))
                      (memq output-mode '(imm mut))
                      (or (eq? output-mode input-mode)
                          (eq? output-mode 'imm)))
           (fail 'ill-typed core))
         (cond
           [(owned-type? tau)
            (unless (and (type-equiv? tau output-type)
                         (eq? (peel-node body) binder))
              (fail 'ill-typed core))
            (set! replacements
                  (append replacements
                          (list (list label output-type output-mode))))
           current-psi]
           [else
            (when (and (resource-type? tau)
                       (not (linear-hole? body binder)))
              (fail 'ill-typed core))
            (when (core-contains-ownleaf? body)
              (fail 'ill-typed core))
            (define body-result
              (with-place-shadowing
               (list binder)
               (lambda ()
                 (if (resource-type? tau)
                     (with-identity-transfer
                      binder
                      (lambda ()
                        (check-as/full body output-type
                                       (enter-child Λ (add1 index))
                                       current-psi
                                       (extend '() (list binder) (list tau))
                                       places callables fail)))
                     (check-as/full body output-type
                                    (enter-child Λ (add1 index))
                                    current-psi
                                    (extend '() (list binder) (list tau))
                                    places callables fail)))))
            (match body-result
              [(list body-row body-psi _)
               (unless (row=? body-row '())
                 (fail 'ill-typed core))
               (set! replacements
                     (append replacements
                             (list (list label output-type output-mode))))
               body-psi])])))
     (define result-type
       `(Record
         ,(for/list ([field (in-list row)])
            (match (assoc (first field) replacements)
              [(list _ output-type output-mode)
               (append (list (first field) output-type output-mode)
                       (drop field 3))]
              [_ field]))))
     (list result-type input-row final-psi)]
    [_ (fail 'ill-typed core)]))

(define (infer-rec-rewrite-open core fields Λ Ψ environment places callables fail)
  (define plain-fields
    (for/list ([field (in-list fields)])
      (match field
        [(list label mode work)
         (list (peel-lbl label) mode #f work)]
        [(list label mode output-type work)
         (list (peel-lbl label) mode (peel-ty output-type) work)]
        [_ (fail 'ill-typed core)])))
  (unless (and (field-row-unique? plain-fields)
               (andmap (lambda (field) (memq (second field) '(imm mut)))
                       plain-fields))
    (fail 'ill-typed core))
  (define-values (typed-fields field-rows final-psi)
    (for/fold ([typed-fields '()] [field-rows '()] [current-psi Ψ])
              ([field (in-list plain-fields)] [index (in-naturals)])
      (define output-type (third field))
      (define work (fourth field))
      (define absent? (match (peel-node work) [`(Absent ,_) #t] [_ #f]))
      (define result
        (cond
          [(and output-type absent?)
           (define absent-type (peel-ty (second (peel-node work))))
           (unless (type-equiv? absent-type output-type)
             (fail 'type-mismatch work output-type absent-type))
           (list output-type '() current-psi)]
          [output-type
           (match (check-as/full work output-type (enter-child Λ index)
                                 current-psi environment places callables fail)
             [(list row next-psi _actual)
              (list output-type row next-psi)])]
          [absent?
           (list (peel-ty (second (peel-node work))) '() current-psi)]
          [else
           (define inferred
             (infer work (enter-child Λ index) current-psi
                    environment places callables fail))
           (define field-type
             (typing-normal-child-type core Λ index (first inferred)))
           (cons field-type (rest inferred))]))
      (define row-field
        (if absent?
            (list (first field) (first result) (second field) 'opt)
            (list (first field) (first result) (second field))))
      (values (append typed-fields (list row-field))
              (append field-rows (list (second result)))
              (third result))))
  (list (if (ormap (lambda (field) (eq? (second field) 'Never))
                   typed-fields)
            'Never
            `(Record ,typed-fields))
        (rows-union field-rows) final-psi))

(define (infer/body core Λ Ψ environment places callables fail)
  (match (peel-node core)
    [(? integer?) (list 'Int '() Ψ)]
    [(? string?) (list 'String '() Ψ)]
    ['unit (list 'Unit '() Ψ)]

    [`(Lam ,_ ,callable (,parameters ...) ,body)
     (infer-lam callable (map peel-bind parameters) body Λ
                Ψ
                environment places callables core fail)]

    [`(RegionLam (,rps ...) ,body)
     (define free (core-free-vars body))
     (define visible
       (for/fold ([entries '()]) ([entry (in-list environment)])
         (if (assoc (first entry) entries)
             entries
             (cons entry entries))))
     (for ([entry (in-list visible)]
           #:when (set-member? free (first entry)))
       (define type (second entry))
       (define hidden?
         (match type
           [`(ForallRegion (,bound ...) ,body-type)
            (unbound-borrowed-type?
             body-type
             (set-union (list->set rps) (list->set bound)))]
           [_ (unbound-borrowed-type? type (list->set rps))]))
       (when hidden?
         (fail 'borrow-hidden-by-narrowing core)))
     (define closure-psi (flow-pin-captures Ψ body environment))
     (match-define (list body-type body-row body-psi)
       (parameterize (;; RegionLam の本体は RegionApp まで遅延する。
                      [region-binder-context rps]
                      [region-binder-renamings
                       (cons (for/hash ([fresh (in-list rps)])
                               (values (region-param-origin fresh) fresh))
                             (region-binder-renamings))]
                      [bound-region-params
                       (set-union (bound-region-params) (list->set rps))])
         (infer body (enter-child Λ 0) closure-psi
                (without-owned environment) places callables fail)))
     (list `(ForallRegion ,rps ,body-type) body-row
           (psi-with-suspended closure-psi body-psi))]

    [`(PrimVal ,_ ,name)
     (match (assoc name (current-Γ0))
       [(list _ (list type canonical-value))
        (unless (equal? canonical-value (peel-node core))
          (fail 'non-canonical-primitive core))
        (list type '() Ψ)]
       [_ (fail 'unknown-primitive core)])]

    [`(CurryVal ,_ ,function ,argument)
     (match-define (list function-type function-row function-psi)
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (define-values (peeled function-owned?)
       (peel-owned-function function-type function fail))
     (match (list peeled function-row function-psi)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-in ,latent-out ,obligations ,origin)
              _ _)
        (define summary
          (or (lookup-callable-summary (enter-child Λ 0) function)
              (let ([w (peel-node function)])
                (and (borrow-designator? w)
                     (region-ctx-summary Λ w)))))
        (define borrowed-parameter?
          (or (borrowed-type-anywhere? first-type)
              (ormap borrowed-type-anywhere? remaining-types)))
        (define borrowed-result?
          (borrowed-type-anywhere? return-type))
        (define borrowed-obligations?
          (borrowed-type-anywhere? obligations))
        (cond
          [(and summary
                (or borrowed-parameter? borrowed-result?
                    borrowed-obligations?))
           (fail 'unresolved-borrow-owner function)]
          [borrowed-parameter?
           ;; 具体 NFn の従来の診断を保つ。summary が無い場合でも、部分適用
           ;; は型木の内側にある借用の provenance を運べないため落とす。
           (fail 'borrowed-function-parameter function)]
          [borrowed-result?
           (fail 'borrowed-function-result function)]
          [borrowed-obligations?
           (fail 'borrowed-function-result function obligations)])
        (unless (null? function-row)
          (fail 'effectful-curry-operand function))
        (when (and (owned-type? first-type)
                   (not (config-runtime-leaf? argument)))
          (require-ownleaf-root argument 'missing-ownleaf-root argument fail))
        (define argument-row
          (parameterize ([ownleaf-permitted
                          (if (owned-type? first-type) (list argument) '())])
            (check-as argument first-type (enter-child Λ 1)
                      function-psi
                      environment places callables fail
                      (if (owned-type? first-type)
                          owned-lift-compatible?
                          type-compatible?))))
        (unless (null? (first argument-row))
          (fail 'effectful-curry-operand argument))
        (define new-origin
          `(Derived ,origin (Curry ,(erase-origin-core argument))))
        (list (curry-result-type remaining-types return-type latent-in latent-out
                                 obligations new-origin
                                 (or function-owned? (resource-type? first-type)))
              (row-union function-row (first argument-row))
              (second argument-row))]
       [_ (fail 'curry-non-function function)])]

    [`(RecurVal ,callable ,function (,parameters ...) ,body)
     (infer-recur-value callable (peel-bind function)
                        (map peel-bind parameters) body Λ
                        Ψ
                        environment places callables core fail)]

    [`(TypeRep ,_ ,_ ,kind)
     (list `(TypeInfo ,kind) '() Ψ)]

    [`(ProofRep ,_ ,proposition)
     (list `(Proof ,proposition) '() Ψ)]

    [`(UnionInject ,union-type ,member-type ,payload)
     (infer-union-inject union-type member-type payload Λ Ψ
                         environment places callables core fail)]

    [`(UnionVal ,union-type ,member-type ,payload)
     (infer-union-value union-type member-type payload Λ Ψ
                        environment places callables core fail)]

    [`(Construct ,data-type ,constructor ,fields ...)
     (define result
       (check-construct constructor fields data-type Λ
                        Ψ
                        environment places callables core fail))
     (list (third result) (first result) (second result))]

    ;; Move 後に H に残る値を宣言型 Owned τ と結び付ける構成専用の印である。
    [`(OwnedTransit ,place ,payload)
     (unless (deriving-config?)
       (fail 'ill-typed core))
     (define declared (assoc place (declared-place-types)))
     (define state (and (forward-config-states)
                        (assoc place (forward-config-states))))
     (unless (and state
                  (eq? (second state) 'Moved)
                  declared
                  (owned-type? (second declared))
                  (not (owned-leaf? (peel-node payload)))
                  (not (owned-transit? payload)))
       (fail 'ill-typed core))
     (match-define (list payload-type payload-row payload-psi)
       (infer payload (enter-child Λ 0) Ψ environment places callables fail))
     (unless (owned-lift-compatible? payload-type (second declared))
       (fail 'ill-typed core))
     (list (second declared) payload-row payload-psi)]

    ;; unsafe.md §2.3。PtrVal は実行時構成だけで埋め込み型を持つ。
    ;; 到達先の状態と型は使用規則の guard が検査する。
    [`(PtrVal ,place ,_path ,type)
     (unless (and (deriving-config?)
                  (raw-ptr-components-ok? type)
                  (assoc place places))
       (fail 'ill-typed core))
     (list type '() Ψ)]

    [`(resource ,_) (list '(Owned Res) '() Ψ)]

    ;; producer 位置から入ったときだけ OwnLeaf を許す。payload の再帰は
    ;; 通常の infer へ戻すため、入れ子の producer は親位置で個別に許可される。
    [`(OwnLeaf ,payload)
     (unless (or (memq core (ownleaf-permitted))
                 (and (deriving-config?)
                      (match (peel-node payload)
                        [`(resource ,_) #t]
                        [`(OwnedLeaf ,_ ,_) #t]
                        [`(OwnedTransit ,_ ,_) #t]
                        [_ #f])))
       (fail 'unexpected-ownleaf core))
     (parameterize ([ownleaf-permitted '()])
       (infer payload (enter-child Λ 0)
              Ψ environment places callables fail))]

    [`(OwnedLeaf ,_tk ,payload)
     (when (owned-transit? payload)
       (fail 'ill-typed core))
     (match-define (list payload-type payload-row payload-psi)
       (infer payload (enter-child Λ 0) Ψ environment places callables fail))
     (unless (owned-type? payload-type)
       (fail 'ill-typed core))
     (list payload-type payload-row payload-psi)]

    [`(RecRewrite ,input (,entries ...))
     (infer-rec-rewrite core input entries Λ Ψ
                        environment places callables fail)]

    [`(RecRewriteOpen (,fields ...))
     (infer-rec-rewrite-open core fields Λ Ψ
                             environment places callables fail)]

    [`(Rec (,fields ...))
     (define plain-fields
       (for/list ([field (in-list fields)])
         (list (peel-lbl (first field))
               (second field)
               (third field))))
     (unless (field-row-unique? plain-fields)
       (fail 'duplicate-record-label core))
     (define-values (results final-psi)
       (for/fold ([results '()] [current-psi Ψ])
                 ([field (in-list plain-fields)]
                  [i (in-naturals)])
         (define result
           (match (peel-node (third field))
             [`(Absent ,type) (list (peel-ty type) '() current-psi)]
             [_ (infer (third field) (enter-child Λ i)
                       current-psi environment places callables fail)]))
         (define field-type
           (typing-normal-child-type core Λ i (first result)))
         (values (append results
                         (list (cons field-type (rest result))))
                 (third result))))
     (for ([field (in-list plain-fields)]
           [result (in-list results)])
       (when (and (not (eq? (first result) 'Never))
                  (owned-type? (first result))
                  (not (match (peel-node (third field))
                         [`(Absent ,_) #t]
                         [_ #f]))
                  (not (and (deriving-config?)
                            (match (peel-node (third field))
                              [`(OwnedLeaf ,_ ,_) #t]
                              [`(OwnedTransit ,_ ,_) #t]
                              [_ #f]))))
         (fail 'owned-record-field (third field))))
     (list
      (if (ormap (lambda (result) (eq? (first result) 'Never)) results)
          'Never
          `(Record
            ,(for/list ([field (in-list plain-fields)]
                        [result (in-list results)])
               (if (match (peel-node (third field)) [`(Absent ,_) #t] [_ #f])
                   `(,(first field) ,(first result) ,(second field) opt)
                   `(,(first field) ,(first result) ,(second field))))))
      (rows-union (map second results))
      final-psi)]

    ;; RFN-001: 未検証の値。ペイロードの型をそのまま Untrusted で包む。
    ;; effect row はペイロードのものを引き継ぐ。
    [`(UVal ,value)
     (match (infer value (enter-child Λ 0)
                    Ψ
                    environment places callables fail)
       [(list value-type value-row value-psi)
        (unless (owned-free? value-type)
          (fail 'owned-untrusted-payload value))
        (list `(Untrusted ,value-type) value-row value-psi)])]

    ;; RFN-001: 検証済みの値。witness の命題を型へ持ち上げる。発行者が正当か
    ;; どうかは成果物検証（verify-origins）の担当であり、ここでは見ない。
    [`(RVal ,proof-rep ,value)
     (match (peel-node proof-rep)
       [`(ProofRep ,_ ,proposition)
        (match (infer value (enter-child Λ 0)
                       Ψ
                       environment places callables fail)
          [(list value-type value-row value-psi)
           (unless (owned-free? value-type)
             (fail 'owned-refined-payload value))
           (list `(Refined ,value-type ,proposition) value-row value-psi)])]
       [_ (fail 'ill-typed core)])]

    [`(Proj ,record ,label)
     (define projection (place-projection-info core))
     (if (and projection
              (not (third projection))
              (place-projection-root? (first projection) places))
         (infer-place-projection core (first projection) (second projection)
                                 #f Λ Ψ environment places fail)
         (let ([record-result
                (infer record (enter-child Λ 0)
                       Ψ environment places callables fail)])
           (match (cons (typing-normal-child-type core Λ 0
                                                 (first record-result))
                        (rest record-result))
             [(list 'Never record-row record-psi)
              (list 'Never record-row record-psi)]
             [(list `(Record ,row) record-row record-psi)
              (define field (assoc (peel-lbl label) row))
              (cond
                [(not field) (fail 'unknown-record-label core)]
                [(field-optional? field) (fail 'project-optional-field core)]
                [else
                 (match (field-row-lookup row (peel-lbl label))
                   [(list field-type _) (list field-type record-row record-psi)]
                   [_ (fail 'unknown-record-label core)])])]
             [_ (fail 'project-non-record record)])))]

    [`(ProjOpt ,τ ,record ,label)
     (define type (peel-ty τ))
     (define projection (place-projection-info core))
     (if (and projection
              (third projection)
              (place-projection-root? (first projection) places))
         (infer-place-projection core (first projection) (second projection)
                                 (third projection) Λ Ψ environment places fail)
         (let ([record-result
                (infer record (enter-child Λ 0)
                       Ψ environment places callables fail)])
           (match (cons (typing-normal-child-type core Λ 0
                                                 (first record-result))
                        (rest record-result))
             [(list 'Never record-row record-psi)
              (list 'Never record-row record-psi)]
             [(list `(Record ,row) record-row record-psi)
              (define field (assoc (peel-lbl label) row))
              (cond
                [(not field) (fail 'unknown-record-label core)]
                [(type-compatible? (second field) type)
                 (check-borrow-hiding! (second field) type core fail)
                 (list `(Option ,type) record-row record-psi)]
                [else (fail 'projopt-invalid-field core)])]
             [_ (fail 'project-non-record record)])))]

    [`(RegionApp ,function (,rhos ...))
     (define function-result
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (define function-type
       (typing-normal-child-type core Λ 0 (first function-result)))
     (define function-row (second function-result))
     (define function-psi (third function-result))
     (match function-type
       [`(ForallRegion (,rps ...) ,body-type)
        (unless (= (length rps) (length rhos))
          (fail 'region-app-arity core (length rps) (length rhos)))
        (for ([rho (in-list rhos)])
          (emit-region-arg-request! rho (region-ctx-point Λ) core))
        ;; subst-region-params は capture-avoiding ではない。両入口で infer の
        ;; 前に alpha-rename-all-region-lams を通すため、全 binder 名が一意になり、
        ;; region-param.rkt の前提 (2) をここでも満たす。
        (define actual-regions
          (for/hash ([rp (in-list rps)] [rho (in-list rhos)])
            (values rp rho)))
        (define substituted-body
          (subst-region-params body-type actual-regions))
        ;; §5.4。点と節点は同じ規約で動かす。RegionLam のときだけ包みを
        ;; 1 段余計に降り、そうでないときは Apply と同じ規約にする。
        (define-values (inner-point inner-node)
          (match (peel-node function)
            [`(RegionLam ,_ ,body)
             (values (enter-child (enter-child Λ 0) 0) body)]
            [_ (values (enter-child Λ 0) function)]))
        (define function-name (peel-node function))
        ;; Recur の継続は元の ForallRegion を環境に持つため、素の名前の
        ;; RegionApp は再帰の重ねから確定要約を複製する。
        (define frame
          (and (symbol? function-name)
               (recur-frame-for (lookup-binding environment function-name))))
        (define inner
          (or (lookup-callable-summary inner-point inner-node)
              (and frame
                   (eq? (recur-frame-state frame) 'final)
                   (recur-frame->summary frame))))
        (when inner
          (record-callable-summary!
           Λ core
           (struct-copy callable-summary inner
                        [region-subst actual-regions])
           fail))
        (list substituted-body function-row function-psi)]
       [_ (fail 'region-app-non-forall core function-type)])]

    [`(Apply ,function ,arguments ...)
     (define function-result
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (define function-type
       (typing-normal-child-type core Λ 0 (first function-result)))
     (define function-row (second function-result))
     (define function-psi (third function-result))
     (define-values (peeled _function-owned?)
       (peel-owned-function function-type function fail))
     (match (list peeled function-row function-psi)
       [(list `(NFn ,parameter-types
                    ,return-type ,latent-in ,latent-out ,obligations ,function-origin)
              _ _)
        (unless (valid-origin? (current-R0) function-origin)
          (fail 'type-origin-invalid function))
        ;; §4.2。再帰の束縛は、環境から引いた対の同一性で判別する。名前で
        ;; 引くと、本体の中の Let が影にした同名の束縛を再帰と見なす。
        (define function-name (peel-node function))
        (define frame
          (and (symbol? function-name)
               (recur-frame-for (lookup-binding environment function-name))))
        (define summary
          (or (and frame
                   (eq? (recur-frame-state frame) 'final)
                   (recur-frame->summary frame))
              (lookup-callable-summary (enter-child Λ 0) function)
              (let ([w (peel-node function)])
                (and (borrow-designator? w)
                     (region-ctx-summary Λ w)))))
        ;; 義務は呼出しの出現へ provenance を結び付けられるため、束縛済みの
        ;; RParam は呼出し側で運べる。ここでは既定の bound-region-params を
        ;; 尊重し、未束縛の借用だけを借用結果として拒む。
        (when (unbound-boundary-borrowed-type? obligations)
          (fail 'borrowed-function-result function obligations))
        ;; summary の無い concrete NFn は、従来の関数境界の診断を引数の
        ;; 照合より先に返す。summary のある callable だけ実体化へ進む。
        (when (and (not summary)
                   (not frame)
                   (ormap unbound-boundary-borrowed-type? parameter-types))
          (fail 'borrowed-function-parameter function))
        (when (and (not summary)
                   (not frame)
                   (unbound-boundary-borrowed-type? return-type))
          (fail 'borrowed-function-result function))
        (define argument-result
          (check-many/full arguments parameter-types Λ function-psi
                           environment places callables core fail 1
                           #:adopt? #f))
        (define actuals (third argument-result))
        (define borrow-parameters?
          (ormap formal-capability-type? parameter-types))
        ;; 既存の concrete NFn は本体の出現要約を持たないため、従来の
        ;; unbound 診断を保つ。ForallRegion の要約欠落だけを fail-closed にする。
        (when (and (not summary) (not frame) borrow-parameters?)
          (unless (or (not (borrow-region return-type))
                      (forwarding-index parameter-types return-type))
            (fail 'unresolved-borrow-owner core)))
        (define argument-caps
          (for/list ([a (in-list arguments)]
                     [τ (in-list parameter-types)]
                     [i (in-naturals 1)])
            (if (formal-capability-type? τ)
                (argument-capabilities Λ a i fail)
                (set))))
        ;; §4.2。仮の状態の再帰呼出しは、雛形の実体化ではなく根の制約で受ける。
        (when (and frame (eq? (recur-frame-state frame) 'tentative))
          (recur-check-roots frame argument-caps core fail))
        (define next-psi (second argument-result))
        (define call-psi
          (for/fold ([state next-psi]) ([effect (in-list latent-out)])
            (match effect
              [`(Return ,boundary ,type)
               (flow-record-escape state
                                   (return-operation-key boundary type)
                                   fail core)]
              [_ state])))
        (when summary
          (define formals (callable-summary-formals summary))
          (define subst
            (for/hash ([w (in-list formals)] [caps (in-list argument-caps)]
                       #:when w)
              (when (set-empty? caps)
                (fail 'unresolved-borrow-owner core))
              (values w caps)))
          (define sources
            (for/hash ([w (in-list formals)]
                       [a (in-list arguments)]
                       [τ (in-list actuals)]
                       [i (in-naturals 1)]
                       #:when w)
              (values w (argument-source Λ a τ i))))
          (set! next-psi
                (instantiate-deferred! summary arguments actuals return-type
                                        Λ core subst sources call-psi fail)))
        (unless summary (set! next-psi call-psi))
        (when (formal-capability-type? return-type)
          (define result-summary
            (or summary
                (and frame (recur-frame->summary frame))
                (and (not (borrow-region return-type))
                     (signature-forwarding-summary parameter-types
                                                   return-type core fail))))
          (define result-entry
            (cond
              [result-summary
               (result-capability-entry result-summary return-type arguments
                                        actuals Λ core fail)]
              [(borrow-region return-type)
               (define index (forwarding-index parameter-types return-type))
               (unless index (fail 'unresolved-borrow-owner core))
               (define actual-type (list-ref actuals index))
               (define entry
               (actual-leaf-entry (enter-child Λ (add1 index))
                                  (list-ref arguments index) actual-type
                                  '() fail))
               (when (set-empty? (capability-entry-keys entry))
                 (fail 'unresolved-borrow-owner core))
               (struct-copy capability-entry entry
                            [borrowed-view? #t]
                            [declared-lifetime (borrow-region return-type)])]
              [else (fail 'unresolved-borrow-owner core)]))
          (record-forwarding-summary!
           Λ core
           (forwarding-summary
            (if result-summary
                (callable-summary-result-index result-summary)
                (hash '() (list (cons (forwarding-index parameter-types
                                                        return-type)
                                      '()))))
            (capability-entry-keys result-entry)
            (capability-entry-source-alphas result-entry)
            (capability-entry-fields result-entry)
            (capability-entry-variants result-entry))
           fail))
        (unless (obligations-dischargeable? obligations (current-Γ-pc0))
          (fail 'unsatisfied-proof-obligation core))
        (define argument-rows-union (rows-union (first argument-result)))
        (list return-type
              (row-union function-row
                         (combine argument-rows-union latent-in latent-out))
              next-psi)]
       [_ (fail 'apply-non-function function)])]

    [`(Discharge ,_ ,_)
     ;; 包み先を直接の Apply に限る形は採れない。複数義務では外側の Discharge
     ;; の包み先が Discharge になり、生成する形を自分で拒否してしまう。
     ;; 素通しの規則も採れない。当該の Apply と無関係な正当な ProofRep を手書き
     ;; で包んだ項が検証を通る。PRF-004 が要求するのは選択した Proof の
     ;; provenance であるから、φ 列と義務列の対応をここで固定する。
     (define-values (propositions base) (peel-discharge core))
     (define base-Λ
       (let loop ([node (peel-node core)] [ctx Λ])
         ;; Discharge の proof 欄は子ではないが、各包みの inner は child 0
         ;; である。base へ跳ぶ前に中間層も観測して point 集合を欠かさない。
         ((typing-point-probe) (region-ctx-point ctx))
         (match node
           [`(Discharge ,_ ,inner)
            (loop (peel-node inner) (enter-child ctx 0))]
           [_ ctx])))
     (define (remainder-phi? phi)
       (match phi [`(RemainderSafelyDropped ,_ ,_) #t] [_ #f]))
     (define remainder-count
       (for/sum ([phi (in-list propositions)]) (if (remainder-phi? phi) 1 0)))
     (define (ensure-base-normal result)
       (when (match (typing-result-at base-Λ)
               [(list 'Never '⊥ _ _) #t]
               [_ #f])
         ;; Discharge は被演算子が Never でも正常型 ⊥ では通常規則を適用できない。
         (fail 'ill-typed base))
       result)
     (cond
       [(zero? remainder-count)
        (match (peel-node base)
          [`(Apply ,function ,_ ...)
           (define function-result
             (infer function (enter-child base-Λ 0)
                    Ψ environment places callables fail))
           (define function-type
             (typing-normal-child-type base base-Λ 0
                                       (first function-result)))
           (match (list function-type (second function-result)
                        (third function-result))
             [(list `(NFn ,_ ,_ ,_ ,_ ,obligations ,_) _ function-psi)
              (unless (= (length propositions) (length obligations))
                (fail 'discharge-obligation-count core))
              (for ([phi (in-list propositions)]
                    [obligation (in-list obligations)])
                (unless (proposition-equiv? phi obligation)
                  (fail 'discharge-proposition-mismatch core)))
              ;; 型と Effect 行は基底の Apply のものを返す。
              (ensure-base-normal
               (infer base base-Λ function-psi
                      environment places callables fail))]
             [_ (fail 'apply-non-function function)])]
          [_ (fail 'discharge-target-not-apply base)])]
       [(< remainder-count (length propositions))
        ;; 残余 drop の義務と他の義務は、渡し方が違う。混ぜた形は受理しない。
        (fail 'discharge-mixed-obligation core)]
       [else
        (unless (= remainder-count 1)
          ;; 残余 drop は 1 段で完結する。2 段目の τ_actual は 1 段目の
          ;; τ_expected と等しく、同じ判定を繰り返すだけである。
          (fail 'discharge-remainder-chain core))
        ;; remainder-count が 1 で propositions も 1 要素なので、ここでは
        ;; RemainderSafelyDropped の単一義務を処理する。
        (ensure-base-normal
         (infer-remainder-discharge core (first propositions) base base-Λ
                                    Ψ environment places callables fail))])]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound Λ
                             Ψ environment places callables core fail)
       [(list bound-row binding-type bound-psi bound-never?)
        (define x (peel-bind name))
        (define Λ_owner (register-owner Λ x binding-type #:let-place? #t))
        (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
        (define callable (lookup-callable-summary (enter-child Λ 0) bound))
        (define borrowed? (borrow-typed? (normalize-type binding-type)))
        (define token
          (cond
            [(not borrowed?) (set)]
            [summary (forwarding-summary-keys summary)]
            [else (typing-borrow-token-key (enter-child Λ 0) bound
                                            #:fail fail)]))
        (when (and summary borrowed? (set-empty? token))
          (fail 'unresolved-borrow-owner bound))
        ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
        ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
        ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
        ;; ため、表の側で fail を落としても未知の designator を見逃さない。
        (define fields
          (or (and summary (forwarding-summary-fields summary))
              (typing-capability-field-entries (enter-child Λ 0) bound)))
        (define Λ_token
          (region-ctx-add-token Λ_owner x token
                                (and summary (forwarding-summary-source summary))
                                callable
                                fields
                                (or (and summary
                                         (forwarding-summary-variants summary))
                                    (typing-capability-variant-views
                                     (enter-child Λ 0) bound))
                                borrowed?))
        (define Λ_body (enter-child Λ_token 1))
        (define-values (body-psi saved-flow)
          (flow-enter-let bound-psi x binding-mode (peel-ty type) binding-type))
        (set! body-psi (flow-clear-escapes body-psi))
        (define identity? (eq? (peel-node body) x))
        (define body-result
          (with-binder-points
           (list x) (region-ctx-point Λ_body)
           (lambda ()
             (with-let-place
              x binding-type
              (lambda ()
                (if identity?
                    (with-identity-transfer
                     x
                     (lambda ()
                       (infer body
                              Λ_body
                              body-psi
                              (extend environment (list x)
                                      (list binding-type)
                                      (and (eq? binding-mode 'mut) '(mut)))
                              places callables fail)))
                   (infer body
                          Λ_body
                          body-psi
                          (extend environment (list x)
                                  (list binding-type)
                                  (and (eq? binding-mode 'mut) '(mut)))
                          places callables fail)))))))
        (record-effective-let-type! Λ binding-type (eq? binding-mode 'mut))
        (match body-result
          [(list body-type body-row body-psi)
           (list (if bound-never? 'Never body-type)
                 (row-union bound-row body-row)
                 (flow-leave-let bound-psi body-psi x saved-flow fail core))])])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-result
       (check-as/full bound (peel-ty type) (enter-child Λ 0)
                      Ψ environment places callables fail))
     (define bound-never? (eq? (third bound-result) 'Never))
     (define x (peel-bind name))
     (define binding-type (peel-ty type))
     (define Λ_owner (register-owner Λ x binding-type #:let-place? #t))
     (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
     (define callable (lookup-callable-summary (enter-child Λ 0) bound))
     (define borrowed? (borrow-typed? (normalize-type binding-type)))
     (define token
       (cond
         [(not borrowed?) (set)]
         [summary (forwarding-summary-keys summary)]
         [else (typing-borrow-token-key (enter-child Λ 0) bound
                                        #:fail fail)]))
     (when (and summary borrowed? (set-empty? token))
       (fail 'unresolved-borrow-owner bound))
     ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
     ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
     ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
     ;; ため、表の側で fail を落としても未知の designator を見逃さない。
     (define fields
       (or (and summary (forwarding-summary-fields summary))
           (typing-capability-field-entries (enter-child Λ 0) bound)))
     (define Λ_token
       (region-ctx-add-token Λ_owner x token
                             (and summary (forwarding-summary-source summary))
                             callable
                             fields
                             (or (and summary
                                      (forwarding-summary-variants summary))
                                      (typing-capability-variant-views
                                       (enter-child Λ 0) bound))
                             borrowed?))
     (define Λ_body (enter-child Λ_token 1))
     (define-values (body-psi saved-flow)
       (flow-enter-let (second bound-result) x 'let binding-type binding-type))
     (set! body-psi (flow-clear-escapes body-psi))
     (define identity? (eq? (peel-node body) x))
     (define body-result
       (with-binder-points
        (list x) (region-ctx-point Λ_body)
        (lambda ()
          (with-let-place
           x binding-type
           (lambda ()
             (if (and identity? (resource-type? binding-type))
                 (with-identity-transfer
                  x
                  (lambda ()
                    (infer body Λ_body body-psi
                           (extend environment (list x) (list binding-type))
                           places callables fail)))
                 (infer body Λ_body body-psi
                        (extend environment (list x) (list binding-type))
                        places callables fail)))))))
     (record-effective-let-type! Λ binding-type)
     (match body-result
        [(list body-type body-row body-psi)
        (list (if bound-never? 'Never body-type)
              (row-union (first bound-result) body-row)
              (flow-leave-let (second bound-result) body-psi
                              x saved-flow fail core))])]

    [`(Eliminate ,scrutinee (,branches ...))
     (infer-eliminate scrutinee branches Λ
                      Ψ
                      environment places callables core fail)]

    [`(EliminateAt ,scrutinee (,branches ...))
     (define-values (plain-branches branch-regions)
       (peel-annotated-data-branches branches))
     (infer-eliminate scrutinee plain-branches Λ Ψ
                      environment places callables core fail branch-regions)]

    [`(UnionEliminate ,scrutinee (,branches ...))
     (infer-union-eliminate scrutinee branches Λ Ψ
                             environment places callables core fail)]

    [`(UnionEliminateAt ,scrutinee (,branches ...))
     (define-values (plain-branches branch-regions)
       (peel-annotated-union-branches branches))
     (infer-union-eliminate scrutinee plain-branches Λ Ψ
                            environment places callables core fail branch-regions)]

    [`(Perform (Return ,boundary ,type) ,argument)
     (define type* (peel-ty type))
     (define operation* (erase-core `(Return ,boundary ,type*)))
     (define argument-result
       (check-as/full argument type* (enter-child Λ 0)
                      Ψ environment places callables fail))
     (define ir (region-ctx-ir Λ))
     (define handler-entry
       (for/first ([entry (in-list (return-handler-regions))]
                   #:when (equal? operation* (third entry)))
         entry))
     (define handler-point (and handler-entry (second handler-entry)))
     (when (and ir handler-point)
       (collect-use-regions-at!
        (third argument-result) ir (region-at ir handler-point)
        (region-ctx-point Λ)
        (region-at/branch ir handler-point)))
     (when (and handler-entry (not (eq? (third argument-result) 'Never)))
       (define payload-types (fourth handler-entry))
       (set-box! payload-types
                 (cons (third argument-result) (unbox payload-types))))
     (define argument-psi (second argument-result))
     (list 'Never
           (row-union (first argument-result)
              `((Return ,boundary ,type*)))
           (flow-record-escape argument-psi operation* fail core))]

    [`(Handle (Return ,boundary ,type) ,handler-clause ,body)
     (define type* (peel-ty type))
     (define operation* (erase-core `(Return ,boundary ,type*)))
     (define captured-types-box (box '()))
     (define body-result
       (parameterize
           ([return-handler-regions
             (cons (list boundary (region-ctx-point Λ)
                         operation* captured-types-box)
                   (return-handler-regions))])
         (check-as/full body type* (enter-child Λ 1)
                        Ψ environment places callables fail)))
     (define body-psi (second body-result))
     (define body-flow (psi-flow body-psi))
     (define caught-state
       (hash-ref (flow-state-escapes body-flow) operation* #f))
     (define captured-types (remove-duplicates (unbox captured-types-box)))
     (define handler-payload-type
       (cond
         [(or (null? captured-types)
              (not (borrowed-type-anywhere? type*)))
          type*]
         [(null? (rest captured-types)) (first captured-types)]
         [else
          (tagged-branch-upper-bound captured-types
                                     (enter-child Λ 0) core fail)]))
     (define handler-base
       (psi-join Ψ body-psi))
     (define handler-input
       (struct-copy psi handler-base
                    [flow (flow-state
                           (or caught-state
                               (flow-state-normal (psi-flow Ψ)))
                           (hash))]))
     (define handler-binder
       (match (peel-branch handler-clause)
         [`(,name -> ,_) (peel-bind name)]
         [_ #f]))
     (define captured-capability
       (handle-return-capability
        (capability-flow-of (enter-child Λ 1) body
                            #:apply-entry capability-of-typed-point)
        operation*))
     (define handler-Λ
       (region-ctx-add-token
        (enter-child Λ 0) handler-binder
        (capability-entry-keys captured-capability)
        (capability-source handler-payload-type)
        #f
        (capability-entry-fields captured-capability)
        (capability-entry-variants captured-capability)
        (borrow-typed? (normalize-type handler-payload-type))))
     (define handler-result
       (match (peel-branch handler-clause)
         [`(,name -> ,handler)
          #:when (eq? (match handler
                        [(? symbol? x) x]
                        [`(#:var ,x ,_) x]
                        [_ #f])
                      (peel-bind name))
          (list '() handler-input handler-payload-type)]
         [`(,name -> ,handler)
          #:when (resource-type? type*)
          (define binder (peel-bind name))
          (define missing-key
            (if (owned-type? type*)
                (lambda (_) 'owned-return-binder-misuse)
                (lambda (_) 'resource-binder-missing-binding)))
          (define raw-key
            (if (owned-type? type*)
                (lambda (_) 'owned-return-binder-misuse)
                (lambda (_) 'resource-binder-raw-misuse)))
          (match (peel-node handler)
            [`(Scope ,managed ,inner)
             (unless (null? managed)
               (fail (missing-key type*) core))
             (check-owned-encoding
              (list binder) (list type*) inner core fail
              #:missing-key missing-key
              #:raw-key raw-key)]
            [_ (fail (missing-key type*) core)])
          (with-binder-points
           (list binder) (region-ctx-point handler-Λ)
           (lambda ()
             (with-place-shadowing
              (list binder)
              (lambda ()
                (with-identity-transfer
                 binder
                 (lambda ()
                   (check-as/full handler
                                  type*
                                  handler-Λ
                                  handler-input
                                  (extend environment
                                          (list binder)
                                          (list (resource-branch-binding-type type*)))
                                  places
                                  callables
                                  fail)))))))]
         [`(,name -> ,handler)
          (with-binder-points
           (list (peel-bind name)) (region-ctx-point handler-Λ)
           (lambda ()
             (with-place-shadowing
              (list (peel-bind name))
              (lambda ()
                (check-as/full handler
                               type*
                               handler-Λ
                               handler-input
                               (extend environment
                                       (list (peel-bind name))
                                       (list handler-payload-type))
                               places
                               callables
                               fail)))))]
         [_ (fail 'ill-typed core)]))
     (define handler-psi (second handler-result))
     (define handler-row (first handler-result))
     (define handler-flow (psi-flow handler-psi))
     (define body-escapes (flow-state-escapes body-flow))
     (define output-escapes
       (escape-union fail core
                     (hash-remove body-escapes operation*)
                     (if caught-state
                         (flow-state-escapes handler-flow)
                         (hash))))
     (define output-normal
       (if caught-state
           (flow-join fail core
                      (flow-state-normal body-flow)
                      (flow-state-normal handler-flow))
           (flow-state-normal body-flow)))
     (define output-psi
       (struct-copy psi (psi-join body-psi handler-psi)
                    [flow (flow-state output-normal output-escapes)]))
     (define normal-result-type
       (and (not (eq? (flow-state-normal body-flow) 'bottom))
            (third body-result)))
     (define handled-result-type
       (and caught-state (third handler-result)))
     (define result-types
       (filter values (list normal-result-type handled-result-type)))
     (define merge-anchor
       (for/first ([result-type (in-list result-types)]
                   #:unless (contains-omitted-region? result-type))
         result-type))
     (define merge-types
       (cond
         [(and merge-anchor
               (ormap contains-omitted-region? result-types))
          (map (lambda (result-type)
                 (if (contains-omitted-region? result-type)
                     (adopt-inferred-lifetimes result-type merge-anchor)
                     result-type))
               result-types)]
         [(and (pair? result-types)
               (andmap contains-omitted-region? result-types))
          (list type*)]
         [else result-types]))
     (define result-type
       (if (borrowed-type-anywhere? type*)
           (match merge-types
             ['() type*]
             [(list only-type) only-type]
             [multiple-types
              (tagged-branch-upper-bound multiple-types Λ core fail)])
           type*))
     (list result-type
           (row-union
            (row-difference (first body-result)
                            `((Return ,boundary ,type*)))
            handler-row)
           output-psi)]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (define point (region-ctx-point Λ))
     (define ir (region-ctx-ir Λ))
     (define body-result
       (infer body (enter-child Λ 0) Ψ environment places callables fail))
     (when ir
       (collect-use-regions-at!
        (first body-result) ir
        (region-parent ir (region-at ir point)) point
        (region-parent ir (region-at/branch ir point))))
     body-result]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      Λ
                      Ψ
                      environment places callables core fail))
     ;; §4.6。recur-context は継続を検査する前に返るので、枠を受け取って
     ;; 継続の検査全体をここで包む。
     (parameterize ([recur-overlay
                     (cons (third continuation-environment)
                           (recur-overlay))]
                    [binder-points
                     (binder-points+
                      (list (peel-bind function))
                      (region-ctx-point (enter-child Λ 1)))])
       (with-place-shadowing
        (list (peel-bind function))
        (lambda ()
          (infer continuation (enter-child Λ 1)
                (second continuation-environment)
                (first continuation-environment)
                places callables fail))))]

    [`(Yield ,observed ,next)
      (define observed-result
       (parameterize ([ownleaf-permitted (list observed)])
         (infer observed (enter-child Λ 0)
               Ψ environment places callables fail)))
      (define observed-type
        (typing-normal-child-type core Λ 0 (first observed-result)))
      (when (eq? observed-type 'Never)
        (fail 'ill-typed observed))
      (define observed-owned? (owned-type? observed-type))
      (cond
        [(and observed-owned?
              (not (ownleaf-root? observed))
              (not (config-runtime-leaf? observed)))
         (fail 'missing-ownleaf-root observed)]
        [(and (not observed-owned?) (ownleaf-root? observed))
         (fail 'unexpected-ownleaf observed)])
      (define next-result
       (infer next (enter-child Λ 1)
             (third observed-result)
             environment places callables fail))
     (list (first next-result)
           (rows-union
            (list (second observed-result)
                  (second next-result)
                  `((Yield ,observed-type))))
           (third next-result))]

    [`(Suspend ,body)
     (define result (infer body (enter-child Λ 0)
                               Ψ
                               environment places callables fail))
     (list (first result) (row-union (second result) '(Suspend))
           (third result))]

    [`(MutSlot ,place)
     (define state (flow-state-normal (psi-flow Ψ)))
     (define entry
       (and (hash? state) (hash-ref state `(MutSlot ,place) #f)))
     (define type
       (or (and entry (flow-entry-current entry))
           (lookup places place)))
     (unless type (fail 'unknown-place core))
     (list type '() Ψ)]

    [`(Move ,place)
     #:when (exact-nonnegative-integer? place)
     (define type (lookup places place))
     (unless type (fail 'unknown-place core))
     (emit-use-request! Λ place '() 'move (set) core 'move-borrowed)
     (define declared (assoc place (declared-place-types)))
     (define moved-type
       (if (and declared (not (owned-type? (second declared))))
           (second declared)
           `(Owned ,type)))
     (list moved-type '(Own) Ψ)]

    [`(Move ,name)
     (define w (peel-node name))
     (define type (lookup environment w))
     (unless type (fail 'unbound-variable core))
     (emit-use-request! Λ w '() 'move (set) core 'move-borrowed)
     (when (borrow-typed? type) (fail 'move-borrowed core))
     (match type
       [`(Owned ,inner-type) (list `(Owned ,inner-type) '(Own) Ψ)]
       [_ (if (and (resource-type? type)
                   (set-member? (resource-place-set) w))
              (list type '(Own) Ψ)
              (fail 'move-non-owned core))])]

    [`(Forward ,target)
     (define w (peel-node target))
     (cond
       [(exact-nonnegative-integer? w)
        (define type (lookup places w))
        (unless type (fail 'unknown-place core))
        (emit-use-request! Λ w '() 'move (set) core 'move-borrowed)
        (define declared (assoc w (declared-place-types)))
        (define moved-type
          (if (and declared (not (owned-type? (second declared))))
              (second declared)
              `(Owned ,type)))
        (list moved-type '() Ψ)]
       [else
        (define type (lookup environment w))
        (unless type (fail 'unbound-variable core))
        (emit-use-request! Λ w '() 'move (set) core 'move-borrowed)
        (when (borrow-typed? type) (fail 'move-borrowed core))
        (match type
          [`(Owned ,inner-type) (list `(Owned ,inner-type) '() Ψ)]
          [_ (if (and (resource-type? type)
                      (set-member? (resource-place-set) w))
                 (list type '() Ψ)
                 (fail 'move-non-owned core))])])]

    [`(Drop ,argument)
     (define dropped
       (match (peel-node argument)
         [`(Move ,w) (peel-node w)]
         [(? symbol? w) w]
         [_ #f]))
     ;; spec §7.5。Move を通さない裸の名前で、型が Owned のとき、
     ;; 段 1 は答えを決められない。借用が生きていれば drop-borrowed、
     ;; 生きていなければ owned-variable-requires-move である。
     ;; 段 1 で後者を出すと段 3 の判定を潰すので、両方を段 3 へ渡す。
     ;; ir が無いときは借用が無いので答えが段 1 で確定する。
     ;; そのとき渡してしまうと要求が記録されず、どちらも出ずに受理してしまう。
     (define dropped-type (and dropped (lookup environment dropped)))
     (define bare-resource?
       (and dropped
            (region-ctx-ir Λ)
            (symbol? (peel-node argument))
            dropped-type
            (resource-type? dropped-type)
            (or (owned-type? dropped-type)
                (set-member? (resource-place-set) dropped))))
     (when dropped
       (emit-use-request! Λ dropped '() 'move (set) argument 'drop-borrowed
                          (and bare-resource? 'owned-variable-requires-move)))
     (when (and dropped
                (borrow-typed? (or (lookup environment dropped) '())))
       (fail 'drop-borrowed argument))
     (define argument-Λ (enter-child Λ 0))
     (define argument-result
       (if bare-resource?
           (list dropped-type '() Ψ)
           (let/ec recover
             (infer argument argument-Λ Ψ environment places callables
                    (lambda (key node . details)
                      (assert-typing-key key)
                      (recover #f))))))
     (when argument-result
       (define argument-type
         (typing-normal-child-type core Λ 0 (first argument-result)))
       (when (eq? argument-type 'Never)
         (fail 'drop-non-owned argument))
       (set! argument-result
             (cons argument-type (rest argument-result))))
     (cond
       [(and argument-result
             (resource-type? (first argument-result)))
        (list 'Unit
              (row-union (second argument-result) '(Own))
              (third argument-result))]
       [else
        (define argument-row
          (check-as argument '(Owned Res) argument-Λ
                    Ψ
                    environment places callables
                    (lambda (key node . details)
                      (assert-typing-key key)
                      (if (and (eq? key 'type-mismatch)
                               (eq? node argument))
                          (fail 'drop-non-owned argument)
                          (apply fail key node details)))))
        (list 'Unit (row-union (first argument-row) '(Own))
              (second argument-row))])]

    [`(Curry ,function ,argument)
     (define function-result
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (define function-type
       (typing-normal-child-type core Λ 0 (first function-result)))
     (define function-row (second function-result))
     (define function-psi (third function-result))
     (define-values (peeled function-owned?)
       (peel-owned-function function-type function fail))
     (match (list peeled function-row function-psi)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-in ,latent-out ,obligations ,origin)
              _ _)
        (define summary
          (or (lookup-callable-summary (enter-child Λ 0) function)
              (let ([w (peel-node function)])
                (and (borrow-designator? w)
                     (region-ctx-summary Λ w)))))
        (define borrowed-parameter?
          (or (borrowed-type-anywhere? first-type)
              (ormap borrowed-type-anywhere? remaining-types)))
        (define borrowed-result?
          (borrowed-type-anywhere? return-type))
        (define borrowed-obligations?
          (borrowed-type-anywhere? obligations))
        (cond
          [(and summary
                (or borrowed-parameter? borrowed-result?
                    borrowed-obligations?))
           (fail 'unresolved-borrow-owner function)]
          [borrowed-parameter?
           (fail 'borrowed-function-parameter function)]
          [borrowed-result?
           (fail 'borrowed-function-result function)]
          [borrowed-obligations?
           (fail 'borrowed-function-result function obligations)])
        (when (and (owned-type? first-type)
                   (not (config-runtime-leaf? argument)))
          (require-ownleaf-root argument 'missing-ownleaf-root argument fail))
        (define argument-row
          (parameterize ([ownleaf-permitted
                          (if (owned-type? first-type) (list argument) '())])
            (check-as argument first-type (enter-child Λ 1)
                      function-psi
                      environment places callables fail)))
        (define new-origin
          `(Derived ,origin (Curry ,(erase-origin-core argument))))
        (list (curry-result-type remaining-types return-type latent-in latent-out
                                 obligations new-origin
                                 (or function-owned? (resource-type? first-type)))
              (row-union function-row (first argument-row))
              (second argument-row))]
       [_ (fail 'curry-non-function function)])]

    [`(Error ,_) (fail 'error-needs-expected-type core)]

    [(? symbol? name)
     (define type (lookup environment name))
     (unless type (fail 'unbound-variable core))
     (define state (psi-flow Ψ))
     (define flow-entry*
       (and (hash? (flow-state-normal state))
            (hash-ref (flow-state-normal state) name #f)))
     ;; flow entry を作るのは Let mut だけで、内側の Let mut は entry を上書きする。
     ;; 仮引数や枝・handler の binder が同じ名前を隠す場合は外側の entry を使わない。
     (define visible-type
       (if (and flow-entry* (eq? (binding-mode-of environment name) 'mut))
           (flow-entry-current flow-entry*)
           type))
     (when (and (resource-type? type)
                (not (set-member? (resource-identity-transfers) name)))
       (fail 'owned-variable-requires-move core))
     (list visible-type '() Ψ)]

    [`(Borrow ,w)
     (infer-borrow core w #f Λ Ψ environment places callables fail)]
    [`(BorrowMut ,w)
     (infer-borrow core w #t Λ Ψ environment places callables fail)]
    [`(BorrowAt ,ρ ,_ ,w)
     (if (deriving-config?)
         (infer-borrow/config core w #f ρ environment places Ψ fail)
         (begin
           (check-region-annotation Λ ρ core fail)
           (infer-borrow core w #f Λ Ψ environment places callables fail)))]
    [`(BorrowMutAt ,ρ ,_ ,w)
     (if (deriving-config?)
         (infer-borrow/config core w #t ρ environment places Ψ fail)
         (begin
           (check-region-annotation Λ ρ core fail)
           (infer-borrow core w #t Λ Ψ environment places callables fail)))]
    [`(BorrowRef ,_ ,_ ,_)
     #:when (and (deriving-config?) (config-runtime-borrow-types))
     (define type
       (hash-ref (config-runtime-borrow-types) (peel-node core) #f))
     (if type (list type '() Ψ) (fail 'ill-typed core))]
    [`(BorrowMutRef ,_ ,_ ,_)
     #:when (and (deriving-config?) (config-runtime-borrow-types))
     (define type
       (hash-ref (config-runtime-borrow-types) (peel-node core) #f))
     (if type (list type '() Ψ) (fail 'ill-typed core))]
    [`(Reborrow ,c_operand)
     (infer-reborrow core c_operand Λ Ψ environment places callables fail)]
    [`(ReborrowAt ,ρ ,c_operand)
     (if (deriving-config?)
         (infer-reborrow/config core c_operand ρ
                                Λ Ψ environment places callables fail)
         (begin
           (check-region-annotation Λ ρ core fail)
           (infer-reborrow core c_operand Λ Ψ environment places callables fail)))]
    [`(ProjBorrowAt ,_ ,operand ,label)
     (infer-projborrow core operand label Λ Ψ environment places callables fail)]
    [`(Read ,operand)
     (infer-read core operand Λ Ψ environment places callables fail)]
    [`(Assign ,target ,value)
     (infer-assign core target value Λ Ψ environment places callables fail)]
    [`(Reassign ,target ,flow-type ,value)
     (infer-reassign core target flow-type value Λ Ψ
                     environment places callables fail)]
    [`(AddressOf ,operand)
     (infer-address-of core operand Λ Ψ environment places callables fail)]
    [`(PtrOffset ,operand ,offset)
     (infer-ptr-offset core operand offset Λ Ψ environment places callables fail)]
    [`(RawLoad ,operand)
     (infer-raw-load core operand Λ Ψ environment places callables fail)]
    [`(RawStore ,target ,value)
     (infer-raw-store core target value Λ Ψ environment places callables fail)]
    [`(FromRawPtr ,operand ,region)
     (infer-from-raw-ptr core operand region Λ Ψ environment places callables fail)]
    [`(Unsafe ,body)
     (infer-unsafe core body Λ Ψ environment places callables fail)]

    [_ (fail 'ill-typed core)]))

;; 段 1 だけを走らせる。試験と、Task 7 の解決の段が使う。
;; with-typing は成功を (list 'ok <本体の返り値>) で包むので、ここで剥がす。
;; 返すのは裸の 6 つ組で、末尾は RegionApp の実引数要求と callable 要約である。
;; 段 1 で棄却されたときは error を上げる。
(define (typing-inference core-in places callables [environment '()]
                          [Λ (empty-region-ctx)]
                          #:forwarding-summaries [forwarding-summaries-box #f])
  (when forwarding-summaries-box
    (unless (box? forwarding-summaries-box)
      (raise-argument-error 'typing-inference "box?" forwarding-summaries-box))
    (set-box! forwarding-summaries-box (hash)))
  (define cs (box '()))
  (define rs (box '()))
  (define ras (box '()))
  (define tbl (box (hash)))
  (define forwarding-table (make-hash))
  (define origins (make-hash))
  (define ir (region-ctx-ir Λ))
  (define result
    (parameterize ([lifetime-collector cs]
                   [request-collector rs]
                   [region-arg-collector ras]
                   [lifetime-counter (box 0)]
                   [region-param-origins origins]
                   [region-binder-renamings '()]
                   [alpha-table tbl]
                   [branch-binder-alphas (make-hash)]
                   [branch-binder-parent-keys (mutable-set)]
                   [branch-binder-event-info (make-hash)]
                   [branch-binder-alpha-sources (make-hash)]
                   [merge-alpha-sources (make-hash)]
                   [callable-summaries (make-hash)]
                   [forwarding-summaries forwarding-table]
                   [template-collectors '()]
                   [recur-overlay '()]
                   [scrutinee-child-alphas (mutable-set)]
                   [binder-points (hash)])
      (with-typing
       (lambda (fail)
         (define renamed
           (call-with-region-params
            (lambda () (alpha-rename-all-region-lams core-in))))
         (parameterize ([current-region-relation
                         (if ir
                             (make-region-relation ir (erase-core renamed))
                             equal?)])
           (match-define (list type _row _Ψ)
             (infer renamed Λ (empty-psi) environment places callables fail))
           (list type (unbox tbl) (reverse (unbox cs)) (reverse (unbox rs))
                 (collected-region-args)
                 (collected-callable-summaries)))))))
  (match result
    [(list 'ok value)
     (when forwarding-summaries-box
       (set-box! forwarding-summaries-box (hash-copy forwarding-table)))
     value]
    [(list 'fail key _node details)
     (error 'typing-inference "段 1 が棄却した: ~a ~a" key details)]))

;; 呼出し位置の実引数を照合する。借用の region 欄は、宣言側では呼出しの
;; 起点、推論側では寿命を表すため、その欄同士を adopt で一致させない。
;; まず実引数の capability を use-source と同じ起点解決で取り、各 owner の
;; region が宣言側の region と一致することを確認する。その後は region 欄を
;; 推論側へ揃えた一時型で payload と mode だけを比較する。owner が解けない
;; 形は type-mismatch ではなく unresolved-borrow-owner で閉じる。
(define (argument-owner-rhos Λ core fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'unresolved-borrow-owner core))
  (define caps (argument-capabilities Λ core 0 fail))
  (for/list ([cap (in-set caps)])
    (define owner (region-ctx-owner Λ (car cap)))
    (unless owner (fail 'unresolved-borrow-owner core))
    (region->rho ir owner)))

(define (call-argument-compatible? actual expected core Λ compatible? fail)
  (define actual* (normalize-type actual))
  (define expected* (normalize-type expected))
  (match* (actual* expected*)
    [((list ctor actual-payload actual-rho)
      (list same-ctor _ expected-rho))
     #:when (and (memq ctor '(Borrowed BorrowedMut))
                 (eq? ctor same-ctor))
     (if (equal? actual-rho expected-rho)
         (compatible? actual expected)
         (and (or (and (deriving-config?) (not (region-ctx-ir Λ)))
                  (for/or ([owner-rho
                            (in-list (argument-owner-rhos Λ core fail))])
                    (equal? owner-rho expected-rho)))
              (compatible? actual
                           (adopt-inferred-lifetimes expected actual))))]
    [(_ _) (compatible? actual expected)]))

(define (check-as/full/body core expected Λ Ψ environment places callables fail
                            [compatible? type-compatible?]
                            #:adopt? [adopt? #t])
  ((typing-point-probe) (region-ctx-point Λ))
  (match (peel-node core)
    [`(Construct ,data-type ,constructor ,fields ...)
     (define actual (peel-ty data-type))
     ;; Construct は payload の実際の借用から結果寿命を推論するため、
     ;; 型注釈の寿命だけを check 位置の期待型へ採る。
     (define expected* (adopt-inferred-lifetimes expected actual))
     (unless (compatible? actual expected*)
       (fail 'type-mismatch core expected actual))
     (check-borrow-hiding! actual expected* core fail compatible?)
     ;; OWN-004。互換だと判断した組に対してだけ narrowing の損失を見る。
     (match (owned-narrowing-kind actual expected* compatible?)
       ['ok (void)]
       [`(drop-obligation ,_ ,_)
        (fail 'owned-narrowing-needs-proof core expected* actual)]
       [_ (fail 'owned-narrowing-rejected core expected* actual)])
     (match (check-construct constructor fields data-type
                              Λ
                              Ψ
                              environment places callables core fail)
       [(list row psi constructed-type)
        (list row psi constructed-type)])]

    [`(Rec ,fields)
     #:when (match (normalize-type (peel-ty expected))
              [`(Record ,_) #t]
              [_ #f])
     (define expected-row (second (normalize-type (peel-ty expected))))
     (define plain-fields
       (for/list ([field (in-list fields)])
         (match field
           [(list label mode expression)
            (list (peel-lbl label) mode expression)]
           [_ (fail 'ill-typed core)])))
     (unless (field-row-unique? plain-fields)
       (fail 'duplicate-record-label core))
     (define-values (actual-row effect-rows next-psi)
       (for/fold ([row '()] [rows '()] [current-psi Ψ])
                 ([field (in-list plain-fields)] [index (in-naturals)])
         (define label (first field))
         (define mode (second field))
         (define expression (third field))
         (define expected-field (assoc label expected-row))
         (define absent?
           (match (peel-node expression) [`(Absent ,_) #t] [_ #f]))
         (define result
           (cond
             [absent?
             (list (peel-ty (second (peel-node expression))) '() current-psi)]
             [expected-field
              (match (check-as/full expression (second expected-field)
                                     (enter-child Λ index) current-psi
                                     environment places callables fail
                                     compatible?)
                [(list field-row field-psi actual-type)
                 (list actual-type field-row field-psi)])]
             [else
              (define inferred
                (infer expression (enter-child Λ index) current-psi
                       environment places callables fail))
              (list (first inferred) (second inferred) (third inferred))]))
         (define result-type
           (if (and (not absent?) (eq? (first result) 'Never))
               (if expected-field
                   (second expected-field)
                   (typing-normal-child-type core Λ index (first result)))
               (first result)))
         (define bottom-field?
           (and (not absent?)
                (eq? (first result) 'Never)
                (eq? (typing-child-normal-type Λ index) '⊥)))
         (define omit-bottom-extra?
           (and (not expected-field) bottom-field?))
         (when (and (eq? result-type 'Never)
                    (not omit-bottom-extra?))
           (fail 'ill-typed expression))
         (when (and (not bottom-field?)
                    (owned-type? result-type)
                    (not absent?)
                    (not (config-runtime-leaf? expression)))
           (fail 'owned-record-field expression))
         (values (if omit-bottom-extra?
                    row
                    (append row
                            (list (if absent?
                                      (list label result-type mode 'opt)
                                      (list label result-type mode)))))
                 (append rows (list (second result)))
                 (third result))))
     (define actual `(Record ,actual-row))
     (define expected*
       (if adopt? (adopt-inferred-lifetimes expected actual) expected))
     (unless (compatible? actual expected*)
       (fail 'type-mismatch core expected actual))
     (check-borrow-hiding! actual expected* core fail compatible?)
     (match (owned-narrowing-kind actual expected* compatible?)
       ['ok (void)]
       [`(drop-obligation ,_ ,_)
        (fail 'owned-narrowing-needs-proof core expected actual)]
       [_ (fail 'owned-narrowing-rejected core expected actual)])
     (list (rows-union effect-rows) next-psi actual)]

    [`(Error ,place)
     (unless (and (exact-nonnegative-integer? place)
                  (assoc place places))
       (fail 'unknown-place core))
     (list '() Ψ expected)]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound
                             Λ
                             Ψ environment places callables core fail)
       [(list bound-row binding-type bound-psi bound-never?)
        (define x (peel-bind name))
        (define Λ_owner (register-owner Λ x binding-type #:let-place? #t))
        (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
        (define callable (lookup-callable-summary (enter-child Λ 0) bound))
        (define borrowed? (borrow-typed? (normalize-type binding-type)))
        (define token
          (cond
            [(not borrowed?) (set)]
            [summary (forwarding-summary-keys summary)]
            [else (typing-borrow-token-key (enter-child Λ 0) bound
                                            #:fail fail)]))
        (when (and summary borrowed? (set-empty? token))
          (fail 'unresolved-borrow-owner bound))
        ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
        ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
        ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
        ;; ため、表の側で fail を落としても未知の designator を見逃さない。
        (define fields
          (or (and summary (forwarding-summary-fields summary))
              (typing-capability-field-entries (enter-child Λ 0) bound)))
        (define Λ_token
          (region-ctx-add-token Λ_owner x token
                                (and summary (forwarding-summary-source summary))
                                callable
                                fields
                                (or (and summary
                                         (forwarding-summary-variants summary))
                                    (typing-capability-variant-views
                                     (enter-child Λ 0) bound))
                                borrowed?))
        (define Λ_body (enter-child Λ_token 1))
        (define-values (body-psi saved-flow)
          (flow-enter-let bound-psi x binding-mode (peel-ty type) binding-type))
        (set! body-psi (flow-clear-escapes body-psi))
        (define identity? (eq? (peel-node body) x))
        (define body-environment
          (extend environment (list x) (list binding-type)
                  (and (eq? binding-mode 'mut) '(mut))))
        (define body-result
          (with-let-place
           x binding-type
           (lambda ()
            (define (infer-body)
               (infer body Λ_body body-psi body-environment
                      places callables fail))
            (define (check-body)
               (check-as/full body expected Λ_body body-psi body-environment
                              places callables fail compatible?))
             (if identity?
                 (with-identity-transfer
                  x (lambda () (if bound-never? (infer-body) (check-body))))
                 (if bound-never? (infer-body) (check-body))))))
        (record-effective-let-type! Λ binding-type (eq? binding-mode 'mut))
        (if bound-never?
            (list (row-union bound-row (second body-result))
                  (flow-leave-let bound-psi (third body-result)
                                  x saved-flow fail core)
                  'Never)
            (list (row-union bound-row (first body-result))
                  (flow-leave-let bound-psi (second body-result)
                                  x saved-flow fail core)
                  (third body-result)))])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-result
       (check-as/full bound (peel-ty type) (enter-child Λ 0)
                      Ψ environment places callables fail compatible?))
     (define bound-never? (eq? (third bound-result) 'Never))
     (define x (peel-bind name))
     (define binding-type (peel-ty type))
     (define Λ_owner (register-owner Λ x binding-type #:let-place? #t))
     (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
     (define callable (lookup-callable-summary (enter-child Λ 0) bound))
     (define borrowed? (borrow-typed? (normalize-type binding-type)))
     (define token
       (cond
         [(not borrowed?) (set)]
         [summary (forwarding-summary-keys summary)]
         [else (typing-borrow-token-key (enter-child Λ 0) bound
                                        #:fail fail)]))
     (when (and summary borrowed? (set-empty? token))
       (fail 'unresolved-borrow-owner bound))
     ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
     ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
     ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
     ;; ため、表の側で fail を落としても未知の designator を見逃さない。
     (define fields
       (or (and summary (forwarding-summary-fields summary))
           (typing-capability-field-entries (enter-child Λ 0) bound)))
     (define Λ_token
       (region-ctx-add-token Λ_owner x token
                             (and summary (forwarding-summary-source summary))
                             callable
                             fields
                             (or (and summary
                                      (forwarding-summary-variants summary))
                                      (typing-capability-variant-views
                                       (enter-child Λ 0) bound))
                             borrowed?))
     (define Λ_body (enter-child Λ_token 1))
     (define-values (body-psi saved-flow)
       (flow-enter-let (second bound-result) x 'let binding-type binding-type))
     (set! body-psi (flow-clear-escapes body-psi))
     (define identity? (eq? (peel-node body) x))
     (define body-environment
       (extend environment (list x) (list binding-type)))
     (define body-result
       (with-let-place
        x binding-type
        (lambda ()
          (if (and identity? (resource-type? binding-type))
              (with-identity-transfer
               x
               (lambda ()
                 (if bound-never?
                     (infer body Λ_body body-psi
                            body-environment places callables fail)
                     (check-as/full body expected Λ_body body-psi
                                    body-environment places callables fail
                                    compatible?))))
              (if bound-never?
                  (infer body Λ_body body-psi
                         body-environment places callables fail)
                  (check-as/full body expected Λ_body body-psi
                                 body-environment places callables fail
                                 compatible?))))))
     (record-effective-let-type! Λ binding-type)
     (if bound-never?
         (list (row-union (first bound-result) (second body-result))
               (flow-leave-let (second bound-result) (third body-result)
                               x saved-flow fail core)
               'Never)
         (list (row-union (first bound-result) (first body-result))
               (flow-leave-let (second bound-result) (second body-result)
                               x saved-flow fail core)
               (third body-result)))]

    [`(UnionEliminate ,scrutinee (,branches ...))
     (check-union-eliminate scrutinee branches expected Λ Ψ
                            environment places callables core fail compatible?)]

    [`(UnionEliminateAt ,scrutinee (,branches ...))
     (define-values (plain-branches branch-regions)
       (peel-annotated-union-branches branches))
     (check-union-eliminate scrutinee plain-branches expected Λ Ψ
                            environment places callables core fail
                            compatible? branch-regions)]

    [`(Eliminate ,scrutinee (,branches ...))
     (check-eliminate scrutinee branches expected
                      Λ
                      Ψ
                      environment places callables core fail
                      compatible?)]

    [`(EliminateAt ,scrutinee (,branches ...))
     (define-values (plain-branches branch-regions)
       (peel-annotated-data-branches branches))
     (check-eliminate scrutinee plain-branches expected
                      Λ Ψ environment places callables core fail
                      compatible? branch-regions)]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (define point (region-ctx-point Λ))
     (define ir (region-ctx-ir Λ))
     (define body-result
       (check-as/full body expected (enter-child Λ 0)
                      Ψ environment places callables fail compatible?))
     (when ir
       (collect-use-regions-at!
        (third body-result) ir
        (region-parent ir (region-at ir point)) point
        (region-parent ir (region-at/branch ir point))))
     body-result]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      Λ
                      Ψ
                      environment places callables core fail))
     (parameterize ([recur-overlay
                     (cons (third continuation-environment)
                           (recur-overlay))]
                    [binder-points
                     (binder-points+
                      (list (peel-bind function))
                      (region-ctx-point (enter-child Λ 1)))])
       (check-as/full continuation
                      expected
                      (enter-child Λ 1)
                      (second continuation-environment)
                      (first continuation-environment)
                      places
                      callables
                      fail
                      compatible?))]

    [`(Yield ,observed ,next)
      (define observed-result
       (parameterize ([ownleaf-permitted (list observed)])
         (infer observed (enter-child Λ 0)
               Ψ environment places callables fail)))
      (define observed-type
        (typing-normal-child-type core Λ 0 (first observed-result)))
      (when (eq? observed-type 'Never)
        (fail 'ill-typed observed))
      (define observed-owned? (owned-type? observed-type))
      (cond
        [(and observed-owned?
              (not (ownleaf-root? observed))
              (not (config-runtime-leaf? observed)))
         (fail 'missing-ownleaf-root observed)]
        [(and (not observed-owned?) (ownleaf-root? observed))
         (fail 'unexpected-ownleaf observed)])
      (define next-result
       (check-as/full next expected (enter-child Λ 1)
                      (third observed-result)
                      environment places callables fail compatible?))
     (list (rows-union
            (list (second observed-result)
                  (first next-result)
                  `((Yield ,observed-type))))
           (second next-result)
           (third next-result))]

    [`(Suspend ,body)
     (define body-result
       (check-as/full body expected (enter-child Λ 0)
                      Ψ environment places callables fail compatible?))
     (list (row-union (first body-result) '(Suspend))
           (second body-result)
           (third body-result))]

    [_
     (match (infer core Λ Ψ environment places callables fail)
       [(list actual row result-psi)
        ;; OWN-004。narrowing の検査は互換性の判定に渡したのと同じ型を使う。
        ;; adopt? の真偽で expected の実体が変わるため、ここで一度束縛する。
        (define expected*
          (if adopt? (adopt-inferred-lifetimes expected actual) expected))
        (unless (if adopt?
                   (compatible? actual expected*)
                   (call-argument-compatible? actual expected core Λ
                                              compatible? fail))
          (fail 'type-mismatch core expected actual))
        (check-borrow-hiding! actual expected* core fail compatible?)
        (match (owned-narrowing-kind actual expected* compatible?)
          ['ok (void)]
          [`(drop-obligation ,_ ,_)
           (fail 'owned-narrowing-needs-proof core expected actual)]
          [_ (fail 'owned-narrowing-rejected core expected actual)])
        (list row result-psi actual)])]))

(define (check-as/full core expected Λ Ψ environment places callables fail
                       [compatible? type-compatible?]
                       #:adopt? [adopt? #t])
  (if (not (typing-normal-results))
      (parameterize ([typing-normal-results (make-hash)])
        (check-as/full core expected Λ Ψ environment places callables fail
                       compatible? #:adopt? adopt?))
      (let* ([input-psi Ψ]
             [local-psi (flow-clear-escapes Ψ)]
             [raw-result
              (check-as/full/body core expected Λ local-psi environment places callables
                                  fail compatible? #:adopt? adopt?)]
             [row (first raw-result)]
             [raw-psi (second raw-result)]
             [raw-type (third raw-result)]
             [normal-type (typing-normal-from-check core Λ expected raw-type)]
             [result-type
              (if (typing-result-never? core Λ raw-type) 'Never raw-type)]
             [psi (flow-restore-output input-psi raw-psi normal-type fail core)])
        (record-typing-result! Λ result-type normal-type row
                               (psi-escape-operations raw-psi))
        (emit-expression-decomposition-exits!
         core Λ environment places callables normal-type fail)
        (collect-use-regions! result-type
                              (region-ctx-ir Λ)
                              (region-ctx-point Λ))
        (list row psi result-type))))

;; 既存の呼び出しは結果の型を要らない。第 3 要素を落として渡す。
(define (check-as core expected Λ Ψ environment places callables fail
                  [compatible? type-compatible?]
                  #:adopt? [adopt? #t])
  (match (check-as/full core expected Λ Ψ environment places callables fail
                        compatible?
                        #:adopt? adopt?)
    [(list row psi _) (list row psi)]))

;; 入口検査は type-of/raw と core-check-row が共有する。片方だけ直す事故を
;; 避けるため、検査の順と key をここへ寄せる。
;; core は投影済みの項を受け取る。返り値は最初に破れた検査の
;; (list key details ...) か、すべて通ったときの #f である。
(define (borrowed-owned-payload-type subject)
  ;; core の型注釈を走査し、Borrowed または BorrowedMut の payload が直接
  ;; Owned である最初の型を返す。無ければ #f。
  (let search ([t subject])
    (match t
      [`(Borrowed (Owned ,_) ,_) t]
      [`(BorrowedMut (Owned ,_) ,_) t]
      [(? list?) (for/or ([e (in-list t)]) (search e))]
      [_ #f])))

(define (entry-violation core places callables environment)
  (cond
    [(not (redex-match? G2m c core)) '(not-core-term)]
    [(own-annotation-violation core)
     => (lambda (found) (list 'own-designator-mismatch found))]
    [(borrowed-owned-payload-type core)
     => (lambda (found) (list 'borrowed-owned-payload found))]
    [(ormap owned-union-member? (list core places callables environment))
     '(owned-union-member)]
    [(not (core-types-normal? core)) '(non-normal-type)]
    [(not (valid-environment? environment))
     (list 'invalid-environment environment)]
    [(not (valid-places? places)) (list 'invalid-places places)]
    [(not (valid-callables? callables)) (list 'invalid-callables callables)]
    [else #f]))

(define (type-of/raw* core-in places callables environment Λ
                      #:sidecar [sidecar-box #f]
                      #:ptr-sidecar [ptr-box #f]
                      #:binder-alphas [binder-alphas-box #f]
                      #:binder-parent-keys [binder-parent-keys-box #f]
                      #:mut-types [mut-types-box #f]
                      #:callable-contexts [callable-contexts-box #f]
                      #:normal-type [normal-type-box #f])
  (when mut-types-box
    (unless (box? mut-types-box)
      (raise-argument-error 'type-of/raw* "box?" mut-types-box))
    (set-box! mut-types-box (hash)))
  (when callable-contexts-box
    (unless (box? callable-contexts-box)
      (raise-argument-error 'type-of/raw* "box?" callable-contexts-box))
    (set-box! callable-contexts-box (hash)))
  (when binder-parent-keys-box
    (unless (box? binder-parent-keys-box)
      (raise-argument-error 'type-of/raw* "box?" binder-parent-keys-box))
    (set-box! binder-parent-keys-box (set)))
  (when normal-type-box
    (unless (box? normal-type-box)
      (raise-argument-error 'type-of/raw* "box?" normal-type-box))
    (set-box! normal-type-box #f))
  (define collected-mut-types (and mut-types-box (box (hash))))
  (define collected-callable-contexts
    (and callable-contexts-box (box (hash))))
  (define resolved-mut-types (box (hash)))
  (define collected-binder-alphas (box (hash)))
  (define collected-binder-parent-keys (box (set)))
  (define cs (box '()))
  (define rs (box '()))
  (define ptr-rs (box '()))
  (define ras (box '()))
  (define tbl (box (hash)))
  (define origins (make-hash))
  (define normal-results (make-hash))
  (define ir (region-ctx-ir Λ))
  (define result
    (parameterize ([typing-normal-results normal-results]
                   [lifetime-collector cs]
                   [request-collector rs]
                   [ptr-request-collector (and ptr-box ptr-rs)]
                   [region-arg-collector ras]
                   [lifetime-counter (box 0)]
                   [region-param-origins origins]
                   [region-binder-renamings '()]
                   [alpha-table tbl]
                   [branch-binder-alphas (make-hash)]
                   [branch-binder-parent-keys (mutable-set)]
                   [branch-binder-event-info (make-hash)]
                   [branch-binder-alpha-sources (make-hash)]
                   [mut-binding-types-table collected-mut-types]
                   [callable-contexts-table collected-callable-contexts]
                   [resource-place-set (set)]
                   [resource-identity-transfers (set)]
                   [merge-alpha-sources (make-hash)]
                   [callable-summaries (make-hash)]
                   [forwarding-summaries (make-hash)]
                   [template-collectors '()]
                   [recur-overlay '()]
                   [scrutinee-child-alphas (mutable-set)]
                   [binder-points (hash)])
      (with-typing
       (lambda (fail)
         ;; span.md §7.3: 入口検査だけ投影し、走査は spanful な項へ行う。
         (require-expanded! 'type-of/raw core-in)
         (define core (erase-core core-in))
         (define violation (entry-violation core places callables environment))
         (when violation
           (apply fail (first violation) core-in (rest violation)))
         ;; 束縛名を入口で 1 度だけ付け替える。関係の表も同じ core から作る。
         (define renamed
           (call-with-region-params
            (lambda () (alpha-rename-all-region-lams core-in))))
         (define relation
           (if ir (make-region-relation ir (erase-core renamed)) equal?))
         (parameterize ([current-region-relation relation])
           ;; 段 1。
           (match-define (list type row Ψ)
             (infer renamed Λ (empty-psi) environment places callables fail))
           ;; 段 2。
           (define solved (typing-solve ir (reverse (unbox cs))))
           (match solved
             [(list 'error broken)
              (define c (first broken))
              (fail (constraint-key c) (constraint-node c))]
             [(list 'ok σ)
              ;; 段 3。
              (check-region-args ir σ (collected-region-args) relation fail)
              (check-borrows ir σ Ψ (reverse (unbox rs)) sigma-ref fail)
              ;; spec §4.4。段 3 が受理した時点の要求と σ を一度だけ写し取る。
              ;; infer-eliminate は attempts と check-as の双方で枝を走査する
              ;; ため同じ要求が重複する。check-borrows と同じ remove-duplicates
              ;; を掛け、順序は入力のまま保つ。
              (when sidecar-box
                (set-box! sidecar-box
                          (borrow-sidecar
                           (remove-duplicates
                            (filter borrow-request? (reverse (unbox rs))))
                           σ)))
              (when ptr-box
                (set-box! ptr-box
                          (ptr-sidecar
                           (remove-duplicates (reverse (unbox ptr-rs))))))
              ;; 型の中の α を σ で解いてから正規化する。materialize が core の
              ;; 注釈へ行う置換と同じ σ を、型の側へも行う（spec §6.3）。
              ;; 置換を正規化より先に置くのは、Union の重複除去が置換の後で
              ;; なければ効かないためである。σ(α_1) と σ(α_2) が同じ region に
              ;; なる形では、正規化を先に置くと正規形の不変が破れる。
              (define substituted (subst-type-regions type σ ir))
              (define normalized (normalize-type substituted))
              (unless normalized
                (fail 'non-normalizable-result-type core-in substituted))
              (define root-result
                (hash-ref normal-results (region-ctx-point Λ) #f))
              (unless root-result
                (error 'type-of/raw*
                       "正常型の記録が見つからない: ~s"
                       (region-ctx-point Λ)))
              (define raw-normal (second root-result))
              (define normalized-normal
                (if (eq? raw-normal '⊥)
                    '⊥
                    (let ([normal
                           (normalize-type
                            (subst-type-regions raw-normal σ ir))])
                      (unless normal
                        (fail 'non-normalizable-result-type core-in raw-normal))
                      normal)))
              (when normal-type-box
                (set-box! normal-type-box normalized-normal))
              (define states (forward-config-states))
              (define invalid-forward
                (forward-invalid-node renamed callables
                                      (if states 'config 'static)
                                      (or states '())))
              (when invalid-forward
                (fail 'forward-invalid-context invalid-forward))
              (define effective-mut-types
                (if collected-mut-types
                    (for/hash ([(point effective-type)
                                (in-hash (unbox collected-mut-types))])
                  (define substituted-effective
                    (subst-type-regions effective-type σ ir))
                  (define normalized-effective
                    (normalize-type substituted-effective))
                  (unless normalized-effective
                    (error 'type-of/raw*
                           "有効型の領域置換後の正規化に失敗した: ~s: ~s"
                           point substituted-effective))
                  (values point normalized-effective))
                    (hash)))
              (set-box! resolved-mut-types effective-mut-types)
              (set-box! collected-binder-alphas
                        (branch-binder-alphas))
              (set-box! collected-binder-parent-keys
                        (for/set ([key (in-set (branch-binder-parent-keys))])
                          key))
              ;; row も同じ σ で解く。Yield は観測値の型を (Yield τ) として、
              ;; Perform は (Return boundary τ) として row へ入れるため、
              ;; 借用をこれらで返すと row が α を運ぶ。
              (list normalized
                    (subst-type-regions row σ ir)
                    (unbox tbl)
                    σ
                    renamed)]))))))
  ;; 失敗の details も同じ σ の下へ置く。段 1 の fail は脱出継続で
  ;; with-typing の外へ出るため、σ を掛ける位置はここしかない。
  (define completed
    (materialize-fail-result (region-ctx-ir Λ) (reverse (unbox cs)) result))
  (when (and mut-types-box
             (match completed [`(ok ,_) #t] [_ #f]))
    (set-box! mut-types-box (unbox resolved-mut-types)))
  (when (and callable-contexts-box
             (match completed [`(ok ,_) #t] [_ #f]))
    (set-box! callable-contexts-box (unbox collected-callable-contexts)))
  (when (and binder-alphas-box
             (match completed [`(ok ,_) #t] [_ #f]))
    (unless (box? binder-alphas-box)
      (raise-argument-error 'type-of/raw* "box?" binder-alphas-box))
    (set-box! binder-alphas-box (unbox collected-binder-alphas)))
  (when (and binder-parent-keys-box
             (match completed [`(ok ,_) #t] [_ #f]))
    (set-box! binder-parent-keys-box
              (unbox collected-binder-parent-keys)))
  completed)

;; 既存の呼び出しは結果の型を要らない。第 3 要素以降を落として渡す。
(define (type-of/raw core-in places callables [environment '()]
                     [Λ (empty-region-ctx)]
                     #:mut-types [mut-types-box #f]
                     #:callable-contexts [callable-contexts-box #f])
  (match (type-of/raw* core-in places callables environment Λ
                       #:mut-types mut-types-box
                       #:callable-contexts callable-contexts-box)
    [(list 'ok (list type row _table _σ _renamed)) (list 'ok (list type row))]
    [other other]))

(define (type-of/raw*+normal core-in places callables [environment '()]
                             [Λ (empty-region-ctx)])
  (define normal-type (box #f))
  (match (type-of/raw* core-in places callables environment Λ
                       #:normal-type normal-type)
    [(list 'ok (list type row table σ renamed))
     (list 'ok (list type row table σ renamed (unbox normal-type)))]
    [other other]))

;; spec §4.4。性質 8 の bounded 検査だけが使う入口。
;; 既存の type-of/raw* の返り値と既存の 2 箇所の呼び出しは変えず、成功結果の末尾へ sidecar を足す。
(define (type-of/raw*+borrows core-in places callables [environment '()]
                              [Λ (empty-region-ctx)]
                              #:mut-types [mut-types-box #f]
                              #:callable-contexts [callable-contexts-box #f]
                              #:binder-alphas [binder-alphas-box #f]
                              #:binder-parent-keys [binder-parent-keys-box #f])
  (define sidecar-box (box #f))
  (match (type-of/raw* core-in places callables environment Λ
                       #:sidecar sidecar-box
                       #:mut-types mut-types-box
                       #:callable-contexts callable-contexts-box
                       #:binder-alphas binder-alphas-box
                       #:binder-parent-keys binder-parent-keys-box)
    [(list 'ok (list type row table σ renamed))
     (list 'ok (list type row table σ renamed (unbox sidecar-box)))]
    [other other]))

;; unsafe.md §5.2。既存の type-of/raw* の返り値を変えず、raw 操作の
;; sidecar を返す入口を足す。
(define (type-of/raw*+ptr core-in places callables [environment '()]
                          [Λ (empty-region-ctx)]
                          #:mut-types [mut-types-box #f]
                          #:callable-contexts [callable-contexts-box #f])
  (define ptr-box (box #f))
  (match (type-of/raw* core-in places callables environment Λ
                       #:ptr-sidecar ptr-box
                       #:mut-types mut-types-box
                       #:callable-contexts callable-contexts-box)
    [(list 'ok (list type row _table _σ _renamed))
     (list 'ok (list type row (unbox ptr-box)))]
    [other other]))

;; machine へ入れる前に、型付けが記録した mut binding の有効型を
;; Let の型欄へ反映する。位置は region walker と同じ core-children の添字である。
;; alpha-rename-all-region-lams は領域名だけを変え、束縛子と型注釈は
;; core-children の子に数えないため、型付け側の renamed と位置列が一致する。
;; span を持つ項も erase-core の前後で木の形を保つ。
(define (annotate-mut-binding-types core table)
  (unless (hash? table)
    (raise-argument-error 'annotate-mut-binding-types "hash?" table))
  (define spanless (erase-core/region-annotations core))
  (define (walk node point)
    (define replaced
      (match node
        [`(Let (,name ,mode ,declared) ,bound ,body)
         `(Let (,name ,mode ,(hash-ref table point (lambda () declared)))
            ,bound ,body)]
        [`(Let (,name ,declared) ,bound ,body)
         `(Let (,name ,(hash-ref table point (lambda () declared)))
            ,bound ,body)]
        [_ node]))
    (define children (core-children replaced))
    (if (null? children)
        replaced
        (core-with-children
         replaced
         (for/list ([child (in-list children)] [index (in-naturals)])
           (walk child (append point (list index)))))))
  (walk spanless '()))

(define (annotate-callable-contexts core table namespace)
  (unless (hash? table)
    (raise-argument-error 'annotate-callable-contexts "hash?" table))
  (unless (memq namespace '(renamed source))
    (raise-argument-error 'annotate-callable-contexts
                          "'renamed or 'source" namespace))
  (define spanless (erase-core/region-annotations core))
  (define (instantiated-cid cid point)
    (match (hash-ref table point #f)
      [(list renamed-pairs source-pairs poly)
       (when (match cid [`(Inst ,_ ,_ ,_) #t] [_ #f])
         (error 'annotate-callable-contexts "Inst cid を二重に付ける: ~s" cid))
       `(Inst ,cid ,(if (eq? namespace 'renamed)
                        renamed-pairs
                        source-pairs)
              ,poly)]
      [_ cid]))
  (define (walk node point)
    (define replaced
      (match node
        [`(Lam ,origin ,cid (,parameters ...) ,body)
         `(Lam ,origin ,(instantiated-cid cid point) ,parameters ,body)]
        [`(Recur ,cid ,function (,parameters ...) ,body ,next)
         `(Recur ,(instantiated-cid cid point) ,function ,parameters ,body ,next)]
        [_ node]))
    (define children (core-children replaced))
    (if (null? children)
        replaced
        (core-with-children
         replaced
         (for/list ([child (in-list children)] [index (in-naturals)])
           (walk child (append point (list index)))))))
  (walk spanless '()))

;; machine と lowering へ渡す Core は、型付け時に得た有効な束縛型を持つ。
;; 型欄を置き換えた結果は再型検査しない。OWN-004 の判定には元の宣言型が要る。
(define (execution-core core callables)
  (define effective-types (box (hash)))
  (define contexts (box (hash)))
  (match (type-of/raw core '() callables '()
                      #:mut-types effective-types
                      #:callable-contexts contexts)
    [(list 'ok _)
     (annotate-callable-contexts
      (annotate-mut-binding-types core (unbox effective-types))
      (unbox contexts) 'source)]
    [failure
     (error 'execution-core "型検査に失敗した Core: ~s" failure)]))

(struct region-typed (type row ir table σ renamed sidecar mut-types callable-contexts
                           binder-alphas binder-parent-keys)
  #:transparent)

(define region-bearing-forms
  '(Borrow BorrowMut Reborrow ProjBorrow Read Assign
    BorrowAt BorrowMutAt ReborrowAt ProjBorrowAt BorrowRef BorrowMutRef
    Borrowed BorrowedMut))

(define (borrow-bearing-core? core)
  (let walk ([node (erase-core core)])
    (or (and (pair? node) (memq (first node) region-bearing-forms) #t)
        (and (list? node) (ormap walk node)))))

(define (core-type-of/regions core places callables [environment '()]
                              #:expansion-context [expansion-context (hash)]
                              #:ir [provided-ir #f])
  ;; placeholder を埋めた caller は、その同じ IR で型付けする。
  (define ir (or provided-ir (build-region-ir core)))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
  (define annotated (annotate-regions core ir))
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (define binder-alphas (box (hash)))
  (define binder-parent-keys (box (set)))
  (match (type-of/raw*+borrows
          annotated places callables environment
          (region-ctx ir '() owners (hash))
          #:mut-types mut-types
          #:callable-contexts callable-contexts
          #:binder-alphas binder-alphas
          #:binder-parent-keys binder-parent-keys)
    [(list 'ok (list type row table σ renamed sidecar))
     (region-typed type row ir table σ renamed sidecar
                   (unbox mut-types) (unbox callable-contexts)
                   (unbox binder-alphas) (unbox binder-parent-keys))]
    [(list 'fail key node details)
     (typing-diagnostic key node details expansion-context)]
    [other (error 'core-type-of/regions "typing の結果が不正である: ~s" other)]))

(define (region-execution-core typed)
  (unless (region-typed? typed)
    (raise-argument-error 'region-execution-core "region-typed?" typed))
  (define core
    (materialize-regions (region-typed-ir typed)
                         (erase-core/region-annotations
                          (region-typed-renamed typed))
                         (region-typed-table typed)
                         (region-typed-σ typed)
                         (region-typed-binder-alphas typed)
                         (region-typed-binder-parent-keys typed)))
  (annotate-callable-contexts
   (annotate-mut-binding-types core (region-typed-mut-types typed))
   (region-typed-callable-contexts typed)
   'renamed))

;; 機械へ渡すため、型付けと同じ σ で core の注釈を materialize する。
(define (core-type-of/materialized core-in places callables
                                   [environment '()]
                                   [Λ (empty-region-ctx)])
  (define contexts (box (hash)))
  (define binder-alphas (box (hash)))
  (define binder-parent-keys (box (set)))
  (match (type-of/raw* core-in places callables environment Λ
                       #:callable-contexts contexts
                       #:binder-alphas binder-alphas
                       #:binder-parent-keys binder-parent-keys)
    [(list 'ok (list type _row table σ renamed))
     (define ir (region-ctx-ir Λ))
     (define materialized
       (if ir
           (materialize-regions ir renamed table σ
                                (unbox binder-alphas)
                                (unbox binder-parent-keys))
           renamed))
     (list 'ok type
           (annotate-callable-contexts materialized
                                       (unbox contexts) 'renamed))]
    [other other]))

;; 失敗の details は、型と effect row に続く 3 つ目の σ の経路である（spec §6.3）。
;; 段 1 の fail は推論の途中の型を details へ入れる。typing.rkt:1346 の
;; typing-expected/found がそれを diagnostic-of の expected と found へ
;; そのまま渡すので、α が残ると Task 3 の寿命変数の検査が型検査を
;; 異常終了させる。返す前に必ず解くか捨てるかする。
(define (materialize-fail-result ir cs result)
  (match result
    [(list 'fail key node details)
     (match (and ir (pair? cs) (typing-solve ir cs))
       [(list 'ok σ)
        (list 'fail key node
              (map (lambda (d) (subst-type-regions d σ ir)) details))]
       ;; ir が無い形と制約が空の形では α を採らない。details はそのままでよい。
       [#f result]
       ;; 段 1 が棄却した時点の制約集合は不完全である。出口の下限が欠けると
       ;; σ(α) は本来より狭くなり、α を左辺に持つ Reborrow と分岐合流の制約が
       ;; 偽に破れる。左辺が具体的な region の BOR-001 だけは向きが逆になるが、
       ;; 制約の種別で健全性が変わる規則は置かない。段 1 の key と node を保ち、
       ;; 解けない details だけを捨てる。失われるのは expected と found であり、
       ;; 診断の分類と位置は残る（spec §6.3）。
       [_ (list 'fail key node '())])]
    [_ result]))

;; 破れた上限制約から診断の key と節点を引く。
;; Task 12 が合流の制約を足すとき、ここに 1 行足せば済む形にする。
(define (constraint-key c)
  (case (region-constraint-kind c)
    [(outlives) 'borrow-escapes-owner]
    [(reborrow) 'reborrow-region-escapes]
    [else
     (error 'constraint-key "未知の region constraint kind: ~s"
            (region-constraint-kind c))]))

(define (constraint-node c) (region-constraint-node c))

;; 型の中の `(RVar k)` を σ の解へ置き換える（spec §6.3）。
;; α が現れるのは借用の 3 つ目の欄だけだが、Union や Record や NFn の中へ
;; 入れ子になるため木全体を歩く。
;; これを通さないと、`type-of` の返り値に α が残り、spec §11 の不変性が破れる。
;; effect row も同じ関数で解く。row の要素は (Return boundary τ) と (Yield τ) と
;; 記号であり、型を運ぶ欄はこの走査で覆える。validators.rkt の owned-free? 内部も
;; 同じ 2 形から型を取り出して走査する。
(define (subst-type-regions t σ ir)
  (match t
    [`(RVar ,_) (region->rho ir (sigma-ref σ t))]
    [(? list? ts) (map (lambda (x) (subst-type-regions x σ ir)) ts)]
    [_ t]))

;; 段 3 の出口で α が残っていないことを試験が見るための述語。
(define (contains-lifetime-var? t)
  (cond
    [(lifetime-var? t) #t]
    [(list? t) (ormap contains-lifetime-var? t)]
    [else #f]))

;; 段 1 の試験専用。typing の走査が訪れた point を集める。
;; 型検査の成否は問わず、走査の網羅だけを観測する。
(define (typing-visited-points core places callables [environment '()])
  (define seen (box '()))
  (parameterize ([typing-point-probe
                  (lambda (point)
                    (set-box! seen (cons point (unbox seen))))])
    (with-typing
     (lambda (fail)
       (infer core (empty-region-ctx) (empty-psi)
              environment places callables fail))))
  (unbox seen))

(define (core-type-of core-in places callables [environment '()]
                      [Λ (empty-region-ctx)])
  (match (type-of/raw core-in places callables environment Λ)
    [(list 'ok result) result]
    [_ 'ill-typed]))

(define (core-type-of/normal core-in places callables [environment '()]
                             [Λ (empty-region-ctx)])
  (match (type-of/raw*+normal core-in places callables environment Λ)
    [(list 'ok (list type row _table _σ _renamed normal-type))
     (list type row normal-type)]
    [_ 'ill-typed]))

;; spec §8: Diagnostic を組む位置はここ 1 箇所だけである。
;; producer は details の先頭へ expected、次へ actual を渡す
;; （G4e2 spec §3）。elaborate.rkt の distribute-details と同じ規則である。
;; key の allowlist は残す。表に無い key の details 2 件は
;; expected と actual の対ではない。
(define (typing-expected/found key details)
  (match* (key details)
    [('forward-invalid-context '()) (values #f #f)]
    [((or 'type-mismatch
          'arity-mismatch
          'parameter-arity-mismatch
          'branch-binder-arity
          'undeclared-function-effect
          'owned-narrowing-rejected
          'owned-narrowing-needs-proof
          'reassign-type-mismatch)
      (list expected actual))
     (values expected actual)]
    [(_ '()) (values #f #f)]
    [(_ (list only)) (values #f only)]
    [(_ _) (values #f details)]))

(define (typing-diagnostic key node details [expansion-context (hash)])
  (define-values (expected found) (typing-expected/found key details))
  (diagnostic-of 'typing key
                #:primary-span (entry-span node)
                #:expected expected
                #:found found
                #:expansion-context expansion-context))

;; spec §3: G4d2 の公開 Diagnostic 境界はこの adapter である。
;; core-type-of は 'ill-typed を返す低レベルの判定として残し、判定 API と診断 API
;; を混ぜない。
;; primary-span は fail が運ぶ棄却節点から取る。entry-span が span を取れないときだけ
;; synthetic fallback へ落ちる。
(define (core-type-of/diagnostic core-in places callables [environment '()]
                                 [Λ (empty-region-ctx)]
                                 #:expansion-context [expansion-context (hash)])
  (match (type-of/raw core-in places callables environment Λ)
    [(list 'ok (list type row)) (list type row)]
    [(list 'fail key node details)
     (typing-diagnostic key node details expansion-context)]))

(define (core-check-row core-in places callables expected [environment '()]
                        [Λ (empty-region-ctx)]
                        #:declared [declared '()]
                        #:states [states #f]
                        #:heap [heap #f])
  ;; span.md §7.3: core-type-of と同じく、既存の型走査へ渡す前に投影する。
  (require-expanded! 'core-check-row core-in)
  (define core (erase-core core-in))
  (define initial-psi
    (and heap states
         (config-initial-psi core heap states places declared)))
  (and (not (entry-violation core places callables environment))
       (type? expected)
       (let ([row
              (parameterize ([declared-place-types declared]
                             [forward-config-states states])
                (check-as/boolean core-in expected environment places callables Λ
                                  #:initial-psi (or initial-psi (empty-psi))))])
         (and row
              (not (forward-invalid-node
                    core-in callables
                    (if states 'config 'static)
                    (or states '())))
              row))))

(define (core-check core places callables expected row [environment '()]
                    [Λ (empty-region-ctx)])
  (and (row? row)
       (let ([actual-row
              (core-check-row core places callables expected environment Λ)])
         (and actual-row (row=? actual-row row)))))

;; Ξ の第 1 段。derive-places は heap 値から型を得るため、BorrowRef と
;; BorrowMutRef を含む値は通常の type-of/raw が拒否する。config-ok? は place
;; を導出した後の再型付けに限り、これらの実行時値を別に型回復する。OwnedLeaf を
;; 含む Rec 欄は config 専用の with-config-typing でだけ許されるが、heap を
;; place の番号順に畳み込むため、前方参照を含む値は依然として拒否される。
;; 閉包の捕捉先もこの順序に従うため、R-Assign の後に再検査しても前方参照の
;; 拒否は同じように効く。
;; H の entry の並びは規定されないため、先に番号で整列する。
(define (derive-places heap callables #:declared [declared '()])
  (for/fold ([acc '()] #:result (and acc (reverse acc)))
            ([entry (in-list (sort heap < #:key first))])
    #:break (not acc)
    (define recorded (assoc (first entry) declared))
    (if recorded
        (cons (list (first entry) (strip-owned (second recorded))) acc)
        (match (type-of/raw (second entry) (reverse acc) callables)
          [(list 'ok (list type _row))
           (cons (list (first entry) (strip-owned type)) acc)]
          [_ #f]))))

(define (config-declared-types configuration)
  (match configuration
    [`(cfg ,_ ,heap ,_ ,_ ,_)
     (for/list ([entry (in-list heap)]
                #:when (match entry
                         [`(,_ ,_ (declared ,_)) #t]
                         [_ #f]))
       (list (first entry) (second (third entry))))]
    [_ '()]))

;; Ξ は place の指す値そのものの型を持ち、Owned の包みは place 側が担う。
;; heap の値の型が常に Owned で始まるとは仮定しない。
(define (strip-owned type)
  (match type
    [`(Owned ,inner) inner]
    [_ type]))

;; Ω[p]=Available の root の値だけを live 集合へ入れる。Moved root の H entry
;; は R-Move 後も stale value を保持するため、ここへ含めない。
(define (available-root-values heap states)
  (map second (available-place-values heap states)))

(define (available-place-values heap states)
  (for/list ([entry (in-list heap)]
             #:when (match (assoc (first entry) states)
                       [(list _ 'Available) #t]
                       [_ #f]))
    (list (first entry) (second entry))))

(define (config-owned-place? place declared)
  ;; Owned の declared metadata は R-LetOwnedB 由来で、mut binder ではない。
  (match (assoc place declared)
    [(list _ `(Owned ,_)) #t]
    [_ #f]))

(define (config-initial-psi core heap states places [declared '()])
  (define values (available-root-values heap states))
  (define captured
    (for/fold ([found (set)]) ([value (in-list values)])
      (set-union found (captured-mut-slots value))))
  (define places-in-scope
    (for/fold ([found (mut-slots-in core)]) ([value (in-list values)])
      (set-union found (mut-slots-in value))))
  (define normal
    (for/fold ([entries (hash)]) ([place (in-set places-in-scope)]
                                 #:when (and (assoc place places)
                                             (not (config-owned-place?
                                                   place declared))))
      (define view (second (assoc place places)))
      (hash-set entries `(MutSlot ,place)
                (flow-entry #f view
                            (and (set-member? captured place)
                                 (set view))))))
  (psi (set) (set) (set) (flow-state normal (hash))))

(define (config-mut-views-supported? core heap states places declared)
  (define live-places
    (for/fold ([found (mut-slots-in core)])
              ([value (in-list (available-root-values heap states))])
      (set-union found (mut-slots-in value))))
  (for/and ([place (in-set live-places)])
    (if (config-owned-place? place declared)
        #t
        (match (assoc place places)
          [(list _ view) (mut-slot-type-supported? view)]
          [_ #f]))))

;; θ の (obs v) の payload を出現順に返す。観測は履歴であるが、観測した値
;; そのものは回収前の live な値として残るため、token 検査の対象に含める。
(define (observed-values trace)
  (for/list ([event (in-list trace)]
             #:when (match event
                      [`(obs ,_) #t]
                      [_ #f]))
    (second event)))

;; 制御項と Available な root の値から到達する token。Moved/Dropped の root の
;; heap entry は R-Move 後の stale value なので含めない。
(define (structural-tokens core heap states)
  (append-map collect-tokens
              (cons core (available-root-values heap states))))

;; trace の obs payload から到達する token。観測済みの leaf は root から
;; 切り離されているため、構造側とは別に数える。
(define (observed-tokens trace)
  (append-map collect-tokens (observed-values trace)))

;; 値である最大の部分項へ leaf 位置検査を課し、値でない構成子はその子を透過して見る。
;; config の制御根と Perform payload は根 leaf を許し、heap の根は呼び出し側で厳格に検査する。
(define (control-leaf-positions-ok? core [allow-root-leaf? #f])
  (define (value-position-ok? candidate)
    (if (redex-match? G2m v candidate)
        (observed-leaf-positions-ok? candidate)
        (control-leaf-positions-ok? candidate)))
  (define (transit-position-ok? candidate)
    (if (owned-transit? candidate)
        (observed-leaf-positions-ok? candidate)
        (control-leaf-positions-ok? candidate)))
  (define (deferred-code-ok? candidate)
    (not (or (contains-owned-leaf? candidate)
             (contains-owned-transit? candidate))))
  (match (peel-node core)
    ;; R-OwnLeafPass は既に token を持つ producer の直前を通過する。
    [`(OwnLeaf ,payload) (value-position-ok? payload)]
    ;; Yield の観測 payload と Curry の固定引数は producer が作る値位置
    ;; なので、根の leaf を許しつつ値内部の走査規則を適用する。
    [`(Yield ,observed ,continuation)
     (and (value-position-ok? observed)
          (control-leaf-positions-ok? continuation))]
    ;; Perform の payload は handler escape 後も外へ運ぶ値である。
    [`(Perform ,_operation ,payload) (value-position-ok? payload)]
    [`(Curry ,function ,argument)
     (and (transit-position-ok? function)
          (value-position-ok? argument))]
    ;; CurryVal の固定引数は β 縮約で Apply の実引数や Drop の引数へ
    ;; 移るため、評価途中のこれらの値位置では根 leaf を許す。
    [`(Apply ,function ,arguments ...)
     (and (transit-position-ok? function)
          (andmap value-position-ok? arguments))]
    [`(Let ,_binding ,bound ,body)
     (and (value-position-ok? bound)
          (control-leaf-positions-ok? body))]
    [`(Construct ,_type ,_constructor ,fields ...)
     (andmap value-position-ok? fields)]
    [`(MutSlot ,_) #t]
    [`(Drop ,argument)
     (value-position-ok? argument)]
    [`(Handle ,_operation ,handler ,body)
     (and (deferred-code-ok? handler)
          (value-position-ok? body))]
    [`(Unsafe ,body)
     (value-position-ok? body)]
    [`(Scope ,_places ,body)
     (value-position-ok? body)]
    [`(Eliminate ,scrutinee (,branches ...))
     (and (transit-position-ok? scrutinee)
          (andmap (lambda (branch)
                    (match branch
                      [`(,_constructor (,_names ...) -> ,body)
                       (deferred-code-ok? body)]
                      ;; 文法上は br 形しか来ないが、未知の枝も厳格側へ落とす。
                      [_ (control-leaf-positions-ok? branch)]))
                  branches))]
    [`(EliminateAt ,scrutinee (,branches ...))
     (and (transit-position-ok? scrutinee)
          (andmap (lambda (branch)
                    (match (peel-branch branch)
                      [`(,_constructor (,_names ...) (,_regions ...) -> ,body)
                       (deferred-code-ok? body)]
                      [_ #f]))
                  branches))]
    [`(UnionEliminate ,scrutinee (,branches ...))
     (and (transit-position-ok? scrutinee)
          (andmap (lambda (branch)
                    (match (erase-core branch)
                      [`(,_member ,_binder -> ,body)
                       (deferred-code-ok? body)]
                      [_ (control-leaf-positions-ok? branch)]))
                  branches))]
    [`(UnionEliminateAt ,scrutinee (,branches ...))
     (and (transit-position-ok? scrutinee)
          (andmap (lambda (branch)
                    (match (peel-branch branch)
                      [`(,_member ,_binder ,_region -> ,body)
                       (deferred-code-ok? body)]
                      [_ #f]))
                  branches))]
    [`(Recur ,_id ,_function (,_arguments ...) ,body ,next)
     (and (deferred-code-ok? body)
          (control-leaf-positions-ok? next))]
    [`(RecRewrite ,input (,entries ...))
     (and (control-leaf-positions-ok? input)
          (andmap (lambda (entry)
                    (match (erase-core entry)
                      [`(,_label ,_binder ,_input-type ,_mark ,_output-type ,body)
                       (deferred-code-ok? body)]
                      [_ #f]))
                  entries))]
    [`(RecRewriteOpen (,fields ...))
     (andmap value-position-ok? (map last fields))]
    [_
     (cond
       [(redex-match? G2m v core)
        (if allow-root-leaf?
            (observed-leaf-positions-ok? core)
            (leaf-positions-ok? core))]
       [(list? core) (andmap control-leaf-positions-ok? core)]
       [else #t])]))

(define (resource-producer-positions-ok? core [allow-root? #f])
  (define (resource-literal? term)
    (match (peel-node term)
      [`(resource ,_) #t]
      [_ #f]))
  (let walk ([term core] [allow? allow-root?])
    (match (peel-node term)
      [`(resource ,_) allow?]
      [`(OwnLeaf ,payload)
       (walk payload (resource-literal? payload))]
      [`(OwnedLeaf ,_ ,payload)
       (walk payload (resource-literal? payload))]
      [_
       (if (list? term)
           (andmap (lambda (child) (walk child #f)) term)
           #t)])))

;; finLeaf は所有値の走査が作る owner path を記録する。Construct の欄は
;; positional segment を使うため、空 path だけを拒否する。
(define (trace-paths-ok? trace)
  (andmap
   (lambda (event)
     (match event
       [`(finLeaf ,_ ,fp) (and (pair? fp) (owner-path? fp))]
       [_ #t]))
   trace))

;; config-ok? と runtime-row が共有する実行時の借用型を place と path から復元する。
(define (recover-runtime-borrow-types core heap states places)
  (define recovered (make-hash))
  (define valid? #t)
  (define (path-type place path)
    (and (match (assoc place states)
           [(list _ 'Available) #t]
           [_ #f])
         (let ([place-entry (assoc place places)])
           (and place-entry
                (heap-path-type heap place (second place-entry) path)))))
  (define (record-borrow! node place path region mutable?)
    (define payload-type (path-type place path))
    (if payload-type
        (hash-set! recovered node
                   (list (if mutable? 'BorrowedMut 'Borrowed)
                         payload-type region))
        (set! valid? #f)))
  (define (visit term)
    (match (peel-node term)
      [`(BorrowRef ,place ,path ,region)
       (record-borrow! (peel-node term) place path region #f)]
      [`(BorrowMutRef ,place ,path ,region)
       (record-borrow! (peel-node term) place path region #t)]
      [_
       (when (list? term)
         (for-each visit term))]))
  (visit core)
  (for ([entry (in-list heap)])
    (visit (second entry)))
  (and valid? recovered))

(define (elimination-annotations-well-formed? core)
  (letrec ([walk
            (lambda (term)
              (define node (peel-node term))
              (match node
                [`(EliminateAt ,scrutinee (,branches ...))
                 (and (walk scrutinee)
                      (andmap
                       (lambda (branch)
                         (match (peel-branch branch)
                           [`(,_ (,binders ...) (,regions ...) -> ,body)
                            (and (= (length binders) (length regions))
                                 (andmap (lambda (region)
                                           (redex-match? G2m ρm region))
                                         regions)
                                 (walk body))]
                           [_ #f]))
                       branches))]
                [`(UnionEliminateAt ,scrutinee (,branches ...))
                 (and (walk scrutinee)
                      (andmap
                       (lambda (branch)
                         (match (peel-branch branch)
                           [`(,member ,binder ,region -> ,body)
                            (and (redex-match? G2m τ (peel-ty member))
                                 (redex-match? G2m x (peel-bind binder))
                                 (redex-match? G2m ρm region)
                                 (walk body))]
                           [_ #f]))
                       branches))]
                [(? pair?)
                 #:when (memq (first node) '(EliminateAt UnionEliminateAt))
                 #f]
                [(? list? terms) (andmap walk terms)]
                [_ #t]))])
    (walk core)))

(define (config-ok? configuration callables expected row)
  ;; entry-violation と共通の型・形状検査に加え、config-ok? は構成固有の
  ;; root/leaf 位置と token 状態も検査する。places は heap から導出するが、
  ;; own 注釈の整合は entry-violation と同じ検査で確かめる。
  (with-config-typing (lambda ()
    (and (redex-match? G2m config configuration)
         (core-types-normal? configuration)
         (valid-callables? callables)
         (type? expected)
         (row? row)
         (match configuration
           [`(cfg ,core ,heap ,states ,token-states ,trace)
         (and (not (own-annotation-violation core))
                 (elimination-annotations-well-formed?
                  (list core heap callables))
                 (unique-heap? heap)
                 (unique-table? states)
                 (equal? (sort (map first heap) <)
                         (sort (map first states) <))
                 (unique-table? token-states)
                 (trace-paths-ok? trace)
                 ;; G5 derives Ξ from each heap value rather than assuming Res.
                 (let* ([declared-types (config-declared-types configuration)]
                        [places (derive-places heap callables
                                               #:declared declared-types)])
                   (and
                    places
                    (let ([borrow-types
                           (recover-runtime-borrow-types
                            core heap states places)])
                      (and
                       borrow-types
                       (let ([initial-psi
                              (config-initial-psi
                               core heap states places declared-types)])
                         (parameterize ([config-runtime-borrow-types borrow-types])
                           (and
                            (config-mut-views-supported?
                             core heap states places declared-types)
                            (for/and ([entry (in-list heap)])
                              (define declared
                                (second (assoc (first entry) places)))
                              (define declared-entry
                                (assoc (first entry) declared-types))
                              (define declared-root-owned?
                                (and declared-entry
                                     (owned-type? (second declared-entry))))
                              (define value (second entry))
                              (define expected-value-type
                                (if (or declared-root-owned?
                                        (not declared-entry))
                                    `(Owned ,declared)
                                    declared))
                              (define compatible?
                                (if (or declared-root-owned?
                                        (and (not declared-entry)
                                             (contains-owned-leaf? value)))
                                    owned-lift-compatible?
                                    type-compatible?))
                              ;; root Owned の place だけ payload を Owned へ持ち上げる。
                              ;; 内側に Owned leaf を持つ Record は宣言型の row のまま
                              ;; 照合し、欄の互換性と token 検査をそれぞれ保つ。
                              (define value-row
                                (parameterize
                                    ([declared-place-types declared-types]
                                     [forward-config-states states])
                                  (check-as/boolean value
                                                    expected-value-type
                                                    '()
                                                    places
                                                    callables
                                                    #:compatible? compatible?
                                                    #:initial-psi initial-psi)))
                              (and value-row (null? value-row)))
                            (let ([actual-row
                                   (parameterize
                                     ([declared-place-types declared-types]
                                      [forward-config-states states])
                                     (check-as/boolean core expected '()
                                                       places callables
                                                       #:initial-psi initial-psi))])
                              (and actual-row
                                   (row=? actual-row row)
                                   (not (forward-invalid-node core callables
                                                              'config states))
                                 ;; 識別の無い resource は producer の直下に限る。
                                 (resource-producer-positions-ok? core)
                                 (andmap (lambda (entry)
                                           (resource-producer-positions-ok?
                                            (second entry) #t))
                                         heap)
                                 ;; H の leaf は走査で辿れる位置に限る。
                                 (andmap (lambda (entry)
                                           (leaf-positions-ok? (second entry)))
                                         heap)
                                 ;; 移送 marker は制御項と Available place の値で数える。
                                 ;; Moved/Dropped の heap 値は stale なので数えず、θ も履歴として数えない。
                                 (let ([transits
                                        (append
                                         (transit-places core)
                                         (append-map
                                          transit-places
                                          (available-root-values heap states)))])
                                   (= (length transits)
                                      (length (remove-duplicates transits))))
                                 (andmap observed-leaf-positions-ok?
                                         (observed-values trace))
                                 (control-leaf-positions-ok? core #t)
                                 ;; token の構造側・観測側の出現と Λtok の状態を
                                 ;; 突き合わせる。
                                 (let ([structural
                                        (structural-tokens core heap states)]
                                       [observed (observed-tokens trace)])
                                   (and
                                    (= (length structural)
                                       (length (remove-duplicates structural)))
                                    (= (length observed)
                                       (length (remove-duplicates observed)))
                                    (not (ormap (lambda (tk)
                                                  (member tk observed))
                                                structural))
                                    (for/and ([tk (in-list (append structural
                                                                    observed))])
                                      (assoc tk token-states))
                                    (for/and ([entry (in-list token-states)])
                                      (define (count tokens)
                                        (length
                                         (filter (lambda (tk)
                                                   (equal? tk (first entry)))
                                                 tokens)))
                                      (define s (count structural))
                                      (define o (count observed))
                                      (case (second entry)
                                        [(Available Moved) (and (= s 1) (= o 0))]
                                        [(Observed) (and (= s 0) (= o 1))]
                                        [(Dropped) (and (= s 0) (<= o 1))]
                                        [else #f]))))))))))))))]
           [_ #f])))))

(module+ test
  (require rackunit)

(test-case "再帰上界は寿命の一致に関係なく全 keyed leaf を選ぶ"
    (define actual-entry
      (capability-entry
       (set '(owner first) '(owner second)) (set)
       (hash
        'first (capability-entry (set '(owner first)) (set) #f #f
                                 (set '(RVar 3)) '(RVar 3))
        'second (capability-entry (set '(owner second)) (set) #f #f
                                  (set '(RVar 0)) '(RVar 0)))
       #f (set) #f))
    (define (probe-fail key node)
      (error 'recursive-capability-leaf-candidates "~a at ~s" key node))
    (define selected
      (recursive-capability-leaf-candidates actual-entry probe-fail 'probe))
    (check-equal?
     (list->set (map capability-entry-keys selected))
     (set (set '(owner first)) (set '(owner second))))
    (check-equal?
     (list->set (map capability-entry-source-alphas selected))
     (set (set '(RVar 3)) (set '(RVar 0))))
    (check-exn
     #rx"unresolved-borrow-owner"
     (lambda ()
       (recursive-capability-leaf-candidates
        (capability-entry (set) (set) #f #f (set) #f)
        probe-fail 'probe))))

  ;; fail は key ill-typed を未登録として error にしない。
  (check-equal? (with-typing (lambda (fail) (fail 'ill-typed 1)))
                '(fail ill-typed 1 ()))

  ;; registry に無い key は error になる。
  (check-exn #px"registry に無い typing の key"
             (lambda ()
               (with-typing (lambda (fail) (fail 'no-such-key 1)))))

  ;; Curry は Lam の閉包を変数か config 上の値に固定する形だけを T に含める。
  (check-true
   (forward-transfer-form?
    '(Curry (Lam User callable (fixed next) unit) captured)
    'static))
  (check-true
   (forward-transfer-form?
    '(Curry (Lam User callable (fixed next) unit)
            (Lam User fixed-value () unit))
    'config))
  (check-false
   (forward-transfer-form?
    '(Curry (Lam User callable (fixed next) unit)
            (Lam User fixed-value () unit))
    'static))
  (check-false
   (forward-transfer-form?
    '(Curry (Lam User callable (fixed next) unit) (Forward captured))
    'static))
  (check-false
   (forward-transfer-form? '(Curry callable captured) 'static))

  (check-true
   (type-equiv?
    (adopt-retained-lifetimes
     '(Union (Borrowed Int (RParam %omitted))
             (Borrowed Bool (RParam %omitted)))
     '(Union (Borrowed Bool ρ-bool)
             (Borrowed Int ρ-int)))
    '(Union (Borrowed Int ρ-int)
            (Borrowed Bool ρ-bool))))
  (check-true
   (type-equiv?
    (adopt-retained-lifetimes
     '(Union (Borrowed Int (RParam %omitted))
             (Borrowed Bool (RParam %omitted)))
     '(Borrowed Int ρ-int))
    '(Union (Borrowed Int ρ-int)
            (Borrowed Bool (RParam %omitted)))))
  (define ambiguous-expected
    '(Union (Borrowed Int (RParam omitted-a))
            (Borrowed Int (RParam omitted-b))))
  (check-equal?
   (adopt-retained-lifetimes
    ambiguous-expected
    '(Union (Borrowed Int ρ-a) (Borrowed Int ρ-b)))
   ambiguous-expected))

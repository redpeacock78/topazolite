#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "annotate.rkt"
         "borrow.rkt"
         "classify.rkt"
         "compat.rkt"
         "diagnostic.rkt"
         "data-env.rkt"
         "erase.rkt"
         "lang.rkt"
         "origins.rkt"
         "ownership.rkt"
         "resource-type.rkt"
         "rows.rkt"
         "schema.rkt"
         "search.rkt"
         "span-core.rkt"
         "span-subst.rkt"
         "type-equiv.rkt"
         "type-shape.rkt"
         "uniquify.rkt"
         "ucore.rkt"
         (only-in "typing.rkt"
                  tag-upper-bound
                  tag-types-upper-bound
                  tag-bound-failure?
                  branch-types-upper-bound
                  merge-record-types/impl
                  core-type-of
                  core-type-of/diagnostic)
         "validators.rkt")

(provide UCore
         elab
         current-trait-providers
         mentions-return?
         identity-conversion?
         ;; c2b1 spec §4.1 の欄の型の合流とその単体試験に使う。
         row005-join
         flow-join-type
         flow-join-decision
         loop-join
         (struct-out loop-excess-key)
         loop-excess-fields
         loop-type-depth
         loop-widen
         loop-cycle?)

(struct judgment (core type row core-type normal-type)
  #:transparent
  #:constructor-name make-judgment/raw
  #:omit-define-syntaxes)

(define (default-normal-type type)
  (if (eq? type 'Never) '⊥ type))

;; IfSome が解決した型を Surface 注釈の再解決へ戻さず constructor へ渡す。
(struct resolved-type-argument (type) #:transparent)

(define current-when-arm-fallthroughs (make-parameter #f))
(define current-deferred-when-fallthroughs (make-parameter #f))
(define current-trait-providers (make-parameter (hasheq)))

;; 既存の三引数の構築は judgment の型を Core の型として使う。
;; check の一部だけ、実際に生成した Core の型を明示する。
(define judgment
  (case-lambda
    [(core type row)
     (make-judgment/raw core type row type (default-normal-type type))]
    [(core type row core-type)
     (make-judgment/raw core type row core-type (default-normal-type type))]
    [(core type row core-type normal-type)
     (make-judgment/raw core type row core-type normal-type)]))
(struct exn:fail:elab exn:fail (primary-span phase reason details related) #:transparent)
(define current-failure-returns (make-parameter #f))

;; primary-span は第 1 引数であり既定値を持たない。既定値を持たせると渡し忘れ
;; が黙って通り、DIA-002 の契約が静かに崩れる。span-ok? と registry の検査で
;; 渡し忘れ、引数の逆順、registry に無い reason を実行時に落とす。
(define (reject primary-span reason #:phase [phase 'elaborate]
                #:related [related '()] . details)
  (unless (span-ok? primary-span)
    (error 'reject "span として妥当でない値を primary-span に受けた: ~s"
           primary-span))
  (unless (diagnostic-code-of phase reason)
    (error 'reject "registry に無い reason である: ~s" reason))
  (raise
   (exn:fail:elab
    (format "elaboration failed: ~a" reason)
    (current-continuation-marks)
    primary-span
    phase
    reason
    details
    related)))

;; c2b1 spec §4.1。欄の型を ROW-005 の規則で合流する。
(define (row005-field-join left right)
  (define bound (tag-upper-bound left right))
  (cond
    [bound bound]
    [(or (owned-type? left) (owned-type? right)) #f]
    [else
     (define union (normalize-type `(Union ,left ,right)))
     (and union (not (owned-union-member? union)) union)]))

(define (row005-join types)
  (define-values (merged _witnesses)
    (merge-record-types/impl types row005-field-join))
  merged)

;; SUR-014c0b1b spec §5.1。枝の view を T の下で合流する。
(define (flow-join-type branch-types declared-type propositions)
  (define types (map normalize-type branch-types))
  (define target (normalize-type declared-type))
  (define context (initial-candidate-context propositions))
  (cond
    [(null? types) (values target 'fallback)]
    [(andmap (λ (type) (type-equiv? type (first types))) types)
      (values (first types) 'equiv)]
    [(and (andmap (λ (type) (match type [`(Record ,_) #t] [_ #f])) types)
          (row005-join types))
     => (λ (joined)
          (define corrected
            (match* (joined target)
              [(`(Record ,joined-row) `(Record ,target-row))
               (define corrected-row
                 (for/list ([field (in-list joined-row)])
                   (define target-field (assq (first field) target-row))
                   (if (and target-field
                            (not (tag-compat? (second field)
                                              (second target-field)
                                              context)))
                       target-field
                       field)))
               (define missing-target-fields
                 (filter (λ (field)
                           (not (assq (first field) corrected-row)))
                         target-row))
               (normalize-type `(Record ,(append corrected-row
                                                  missing-target-fields)))]
              [(_ _) joined]))
          (values (and (tag-compat? corrected target context) corrected)
                  'merge))]
    [else (values target 'fallback)]))

;; SUR-014c0b1b spec §5.2。pin があればそれを選び、各枝をそこへ作り直せるか判定する。
(define (flow-join-decision branch-types pins declared-type propositions rebuildable?)
  (define pin-types (append* pins))
  (define target
    (cond
      [(pair? pin-types)
       (and (andmap (λ (type) (type-equiv? type (first pin-types))) pin-types)
            (normalize-type (first pin-types)))]
      [else
       (define-values (joined _path)
         (flow-join-type branch-types declared-type propositions))
       joined]))
  (if (and target
           (= (length branch-types) (length pins))
           (andmap (λ (type) (rebuildable? type target)) branch-types))
      target
      'reassign-type-mismatch))

(struct loop-excess-key (path correspondence field) #:transparent)

(define (loop-join inputs declared-type propositions fits?)
  (define-values (candidate _path)
    (flow-join-type inputs declared-type propositions))
  (define target (normalize-type declared-type))
  (if (and candidate
           (andmap (λ (input) (fits? input candidate)) inputs))
      candidate
      target))

(define (loop-type-depth type)
  (define (depths types)
    (if (null? types) 0 (apply max (map loop-type-depth types))))
  (define (plus children) (add1 (depths children)))
  (match type
    [`(Record ,row) (if (null? row) 1 (add1 (depths (map second row))))]
    [`(Union ,_ ,_) (depths (union-members type))]
    [`(Intersection ,left ,right) (plus (list left right))]
    [`(List ,element) (plus (list element))]
    [`(Option ,element) (plus (list element))]
    [`(Result ,ok-type ,error-type) (plus (list ok-type error-type))]
    [`(Owned ,inner) (plus (list inner))]
    [`(Borrowed ,payload ,_) (plus (list payload))]
    [`(BorrowedMut ,payload ,_) (plus (list payload))]
    [`(RawPtr ,payload ,_ ,_ ,_ ,_ ,_) (plus (list payload))]
    [`(Untrusted ,payload) (plus (list payload))]
    [`(Refined ,payload ,_) (plus (list payload))]
    [`(Data ,_ (,arguments ...)) (plus arguments)]
    [`(NFn ,parameters ,return-type ,_ ,_ ,_ ,_)
     (plus (cons return-type parameters))]
    [`(ForallRegion (,_ ...) ,body) (plus (list body))]
    [`(TypeInfo ,_) 1]
    [`(Proof ,_) 1]
    [_ 0]))

(define (loop-expand-targets targets)
  (append-map
   (λ (target)
     (match-define (list path type) target)
     (match type
       [`(Union ,_ ,_)
        (for/list ([member (in-list (union-members type))]
                   [index (in-naturals)])
          (list (append path (list `(union ,index))) member))]
       [_ (list target)]))
   targets))

(define (loop-compatible-records view targets)
  (for/list ([target (in-list (loop-expand-targets targets))]
             #:when (match (second target)
                      [`(Record ,_)
                       ;; 直下の Record は親位置として保持し、Union 成員だけ tag で選ぶ。
                       (or (not (ormap (λ (part)
                                         (match part [`(union ,_) #t] [_ #f]))
                                       (first target)))
                           (tag-compat? view (second target)))]
                      [_ #f]))
    target))

(define (loop-correspondence records)
  (sort (remove-duplicates (map first records) equal?)
        string<? #:key (λ (path) (format "~s" path))))

(define (loop-target-fields records label)
  (for/list ([record (in-list records)]
             #:do [(match-define (list path `(Record ,row)) record)
                   (define field (assq label row))]
             #:when field)
    (list (append path (list `(field ,label))) (second field))))

(define (loop-payload-targets targets constructor payload-index path-token)
  (for/list ([target (in-list (loop-expand-targets targets))]
             #:do [(match-define (list path type) target)]
             #:when (and (list? type) (eq? (first type) constructor)))
    (list (append path (list path-token))
          (list-ref type payload-index))))

(define (loop-excess-field-entries view declared-type)
  (define normalized-view (normalize-type view))
  (define normalized-declared (normalize-type declared-type))
  (define (walk view targets path)
    (match view
      [`(Union ,_ ,_)
       (append-map (λ (member) (walk member targets path))
                   (union-members view))]
      [`(Record ,row)
       (define records (loop-compatible-records view targets))
       (define correspondence (loop-correspondence records))
       (append-map
        (λ (field)
          (define label (first field))
          (define common?
            (and (pair? records)
                 (for/and ([record (in-list records)])
                   (assq label (second (second record))))))
          (if common?
              (walk (second field)
                    (loop-target-fields records label)
                    (append path (list `(field ,label))))
              (list (cons (loop-excess-key path correspondence label)
                          (second field)))))
        row)]
      [`(Owned ,payload)
       (walk payload (loop-payload-targets targets 'Owned 1 '(Owned-payload))
             (append path '((Owned-payload))))]
      [`(Untrusted ,payload)
       (walk payload (loop-payload-targets targets 'Untrusted 1 '(Untrusted-payload))
             (append path '((Untrusted-payload))))]
      [`(Refined ,payload ,_)
       (walk payload (loop-payload-targets targets 'Refined 1 '(Refined-payload))
             (append path '((Refined-payload))))]
      [`(Borrowed ,payload ,_)
       (walk payload (loop-payload-targets targets 'Borrowed 1 '(Borrowed-payload))
             (append path '((Borrowed-payload))))]
      [`(BorrowedMut ,payload ,_)
       (walk payload (loop-payload-targets targets 'BorrowedMut 1 '(BorrowedMut-payload))
             (append path '((BorrowedMut-payload))))]
      [`(NFn ,_ ,return-type ,_ ,_ ,_ ,_)
       (walk return-type (loop-payload-targets targets 'NFn 2 '(nfn-return))
             (append path '((nfn-return))))]
      [_ '()]))
  (if (and normalized-view normalized-declared)
      (walk normalized-view (list (list '() normalized-declared)) '())
      '()))

(define (loop-excess-fields view declared-type)
  (remove-duplicates (map car (loop-excess-field-entries view declared-type)) equal?))

(define (loop-remove-excess view declared-type removed)
  (define (walk view targets path)
    (match view
      [`(Union ,left ,right)
       (normalize-type `(Union ,(walk left targets path)
                               ,(walk right targets path)))]
      [`(Record ,row)
       (define records (loop-compatible-records view targets))
       (define correspondence (loop-correspondence records))
       (define new-row
         (append-map
          (λ (field)
            (define label (first field))
            (define common?
              (and (pair? records)
                   (for/and ([record (in-list records)])
                     (assq label (second (second record))))))
            (define key (loop-excess-key path correspondence label))
            (cond
              [(set-member? removed key) '()]
              [common?
               (define child-path (append path (list `(field ,label))))
               (define child-targets (loop-target-fields records label))
               (list (field-with-type
                      field (walk (second field) child-targets child-path)))]
              [else (list field)]))
          row))
       `(Record ,new-row)]
      [`(Owned ,payload)
       `(Owned ,(walk payload (loop-payload-targets targets 'Owned 1 '(Owned-payload))
                      (append path '((Owned-payload)))))]
      [`(Untrusted ,payload)
       `(Untrusted ,(walk payload (loop-payload-targets targets 'Untrusted 1 '(Untrusted-payload))
                          (append path '((Untrusted-payload)))))]
      [`(Refined ,payload ,proposition)
       `(Refined ,(walk payload (loop-payload-targets targets 'Refined 1 '(Refined-payload))
                        (append path '((Refined-payload)))) ,proposition)]
      [`(Borrowed ,payload ,region)
       `(Borrowed ,(walk payload (loop-payload-targets targets 'Borrowed 1 '(Borrowed-payload))
                         (append path '((Borrowed-payload)))) ,region)]
      [`(BorrowedMut ,payload ,region)
       `(BorrowedMut ,(walk payload (loop-payload-targets targets 'BorrowedMut 1 '(BorrowedMut-payload))
                            (append path '((BorrowedMut-payload)))) ,region)]
      [`(NFn ,parameters ,return-type ,in-row ,out-row ,obligations ,origin)
       `(NFn ,parameters
             ,(walk return-type (loop-payload-targets targets 'NFn 2 '(nfn-return))
                   (append path '((nfn-return))))
             ,in-row ,out-row ,obligations ,origin)]
      [_ view]))
  (normalize-type
   (walk view (list (list '() (normalize-type declared-type))) '())))

(define (loop-widen previous next declared-type removed)
  (define target (normalize-type declared-type))
  (define normalized-previous (normalize-type previous))
  (define normalized-next (normalize-type next))
  (define already-pruned
    (loop-remove-excess normalized-next target removed))
  (define previous-depths
    (for/fold ([depths (hash)])
              ([entry (in-list (loop-excess-field-entries normalized-previous target))])
      (define key (car entry))
      (hash-set depths key
                (max (hash-ref depths key 0)
                     (loop-type-depth (cdr entry))))))
  (define next-depths
    (for/fold ([depths (hash)])
              ([entry (in-list (loop-excess-field-entries already-pruned target))])
      (define key (car entry))
      (hash-set depths key
                (max (hash-ref depths key 0)
                     (loop-type-depth (cdr entry))))))
  (define removed*
    (for/fold ([keys removed]) ([(key depth) (in-hash next-depths)])
      (if (> depth (hash-ref previous-depths key 0))
          (set-add keys key)
          keys)))
  (define widened (loop-remove-excess already-pruned target removed*))
  (if (and widened (tag-compat? widened target))
      (values widened removed*)
      (values target removed*)))

(define (loop-cycle? view history)
  (define normalized-view (normalize-type view))
  (and normalized-view
       (for/or ([previous (in-list history)])
         (define normalized-previous (normalize-type previous))
         (and normalized-previous
              (type-equiv? normalized-view normalized-previous)))))

;; §6: details を expected と found へ配る。既定は件数だけで決まり、意味を
;; 推測しない。producer は details の先頭へ expected、次へ actual を渡す
;; （G4e2 spec §3）。この順は Diagnostic の欄順および renderer の表示順と
;; 一致する。
;; key の allowlist は残す。表に無い key でも details を 2 件渡す site が
;; あり（unsaturated-type、invalid-type-application、kind-mismatch、
;; constructor-type-arity）、その 2 件は expected と actual の対ではない。
;; ambiguous-union-member は expected、actual、候補列を渡し、Diagnostic の
;; expected と found には expected と (actual candidates) を置く。
;; 例外表の reason でも details の長さが合わなければ既定へ落ちる。
(define (distribute-details reason details)
  (match* (reason details)
    [('ambiguous-union-member (list expected actual candidates))
     (values expected (list actual candidates))]
    [((or 'type-mismatch
          'arity-mismatch
          'constructor-type-mismatch
          'undeclared-function-effect
          'undeclared-recur-effect
          'owned-narrowing-rejected
          'owned-narrowing-needs-proof
          'reassign-type-mismatch
          'try-bind-boundary-mismatch)
      (list expected actual))
     (values expected actual)]
    [('try-bind-non-adt (list actual))
     (values #f actual)]
    [('when-arm-missing-return '()) (values #f #f)]
    [(_ '()) (values #f #f)]
    [(_ (list only)) (values #f only)]
    [(_ _) (values #f details)]))

(define (lookup table key)
  (match (assoc key table)
    ;; P1c2b。環境 entry は mut のとき 3 要素になる。
    [(list _ value _ ...) value]
    [_ #f]))

;; span.md §7.4: Γ0 の値は表の項であり span を持たない。参照した位置の
;; span を head の直後へ付け、G1+ の値へ戻す。
(define (attach-span value s)
  (match value
    [(list head rest ...) (list* head s rest)]
    [_ (error 'attach-span "Γ0 の値が項ではない: ~s" value)]))

;; 包みが span を持つならそれを、持たないなら親から引き継いだ span を返す。
;; wrapper-span は span を持たない包みで error を出すため、形の判定を先に行う。
(define (nearest-span t inherited)
  (match t
    [(list (or '#:ty '#:bind '#:lbl '#:ef) _ (and s (list '#:span _ _ _))) s]
    [_ inherited]))

;; span.md §3: 文法は startByte <= endByte を書けない。UCore+ に属する項でも
;; 座標が逆順なら span として妥当でない。入口で一度だけ再帰的に検査する。
;; 判定は span-core.rkt の span-ok? が持ち、ここは走査だけを行う。
(define (spans-ok? t)
  (cond
    [(and (pair? t) (eq? (car t) '#:span)) (span-ok? t)]
    [(list? t) (andmap spans-ok? t)]
    [else #t]))

;; SCP-002。識別子の区切り記号は source の束縛子へ持ち込ませない。
;; UCore と UCore+ の両方を入口で受けるため、未注釈の記号と #:bind 包みを
;; 同じ走査で扱う。型や label の記号は束縛子位置として調べない。
(define reserved-binder-mark-rx #px"[⟨⟩]")

(define (reserved-binder-symbol? value)
  (and (symbol? value)
       (regexp-match? reserved-binder-mark-rx (symbol->string value))))

(define (binder-name value)
  (match value
    [`(#:bind ,name ,_) name]
    [`((#:bind ,name ,_) ,_ ...) name]
    [`(,(? symbol? name) ,_ ...) name]
    [(? symbol? name) name]
    [_ #f]))

(define (reserved-name value)
  (define name (binder-name value))
  (and (reserved-binder-symbol? name) name))

(define (reserved-binder-in term)
  (define (first-reserved values)
    (for/first ([value (in-list values)]
                #:when (reserved-binder-symbol? value))
      value))
  (define (parameter-name parameter)
    (binder-name parameter))
  (define (branch-reserved branch)
    (match branch
      [`(,_ ,(? symbol? binder) -> ,_)
       (reserved-name binder)]
      [`(,_ ,parameters -> ,_)
       (and (list? parameters)
            (first-reserved (map parameter-name parameters)))]
      [_ #f]))
  (define (walk value)
    (match value
      [`(#:bind ,name ,_)
       (and (reserved-binder-symbol? name) name)]
      ;; Fn: UCore の引数列は第 2 欄、UCore+ は第 3 欄。
      [`(Fn ,parameters ,_ ,_ ,body)
       (or (first-reserved (map parameter-name parameters))
           (walk body))]
      [`(Fn ,_ ,parameters ,_ ,_ ,body)
       (or (first-reserved (map parameter-name parameters))
           (walk body))]
      ;; Let: raw UCore は第 2 欄、UCore+ は span の後の第 3 欄。
      [`(Let ,binder ,bound ,body)
       (or (reserved-name binder) (walk bound) (walk body))]
      [`(Let ,_ ,binder ,bound ,body)
       (or (reserved-name binder) (walk bound) (walk body))]
      ;; Recur: raw UCore は関数名が第 2 要素、UCore+ は span と callable の後に関数名が来る。
      [`(Recur ,function ,parameters ,_ ,_ ,body ,continuation)
       (or (reserved-name function)
           (first-reserved (map parameter-name parameters))
           (walk body)
           (walk continuation))]
      [`(Recur ,_ ,_ ,function ,parameters ,_ ,_ ,body ,continuation)
       (or (reserved-name function)
           (first-reserved (map parameter-name parameters))
           (walk body)
           (walk continuation))]
      ;; Loop は Recur と同じ束縛を持ち、初回呼出しの実引数も走査する。
      [`(Loop ,function ,parameters ,_ ,_ ,body (,arguments ...))
       (or (reserved-name function)
           (first-reserved (map parameter-name (map first parameters)))
           (walk body)
           (for/or ([argument (in-list arguments)]) (walk argument)))]
      [`(Loop ,_ ,function ,parameters ,_ ,_ ,body (,arguments ...))
       (or (reserved-name function)
           (first-reserved (map parameter-name (map first parameters)))
           (walk body)
           (for/or ([argument (in-list arguments)]) (walk argument)))]
      ;; Task 2 では FnDecl を Recur と同じ束縛形として検査する。
      [`(FnDecl ,function ,parameters ,_ ,_ ,body ,continuation)
       (or (reserved-name function)
           (first-reserved (map parameter-name parameters))
           (walk body)
           (walk continuation))]
      [`(FnDecl ,_ ,function ,parameters ,_ ,_ ,body ,continuation)
       (or (reserved-name function)
           (first-reserved (map parameter-name parameters))
           (walk body)
           (walk continuation))]
      ;; raw の branch は branch-reserved が、UCore+ の branch は generic 走査が拾う。
      [`(Eliminate ,scrutinee ,branches)
       #:when (list? branches)
       (or (walk scrutinee)
           (for/or ([branch (in-list branches)])
             (branch-reserved branch))
           (for/or ([branch (in-list branches)])
             (walk branch)))]
      [(? list?)
       (for/or ([child (in-list value)])
         (walk child))]
      [_ #f]))
  (walk term))

;; 条件 1 は構文上の走査であり、型注釈と変数名の Return は数えない。
(define (mentions-return? node)
  (match node
    [`(Return ,_ ,_) #t]
    [`(TryBind ,_ ,_ ,_) #t]
    [`(TryBind ,_ ,_ ,_ ,_) #t]
    [`(#:ef ,labels ,_) (and (list? labels) (memq 'Return labels) #t)]
    [`(,(or '#:ty '#:var '#:bind '#:lit) ,_ ...) #f]
    [(? list?) (ormap mentions-return? node)]
    [_ #f]))

;; P1c2b。modes を渡すと binding mode を持つ entry を作る。
;; place-flags の真の entry は c1c1 の P に属する Let 束縛である。
;; 非 Let binder は place-flags を渡さず、同名の外側 entry を遮蔽する。
;; entry は (name type mode place? flow-key) で、非 mut の flow-key は #f。
(define (extend environment names types [modes #f] [place-flags #f]
                [flow-keys #f])
  (append
   (for/list ([name (in-list names)]
              [type (in-list types)]
              [index (in-naturals)])
     (define mode (and modes (list-ref modes index)))
     (define place? (and place-flags (list-ref place-flags index)))
     (define flow-key (and flow-keys (list-ref flow-keys index)))
     (list name type mode (and place? #t) flow-key))
   environment))

;; P1c2b。mode を持つ entry から binding mode を返す。
(define (binding-mode-of environment name)
  (match (assoc name environment)
    [(list _ _ mode _ ...) mode]
    [_ #f]))

(define (place-binding? environment name)
  (match (assoc name environment)
    [(list _ _ _ #t _ ...) #t]
    [_ #f]))

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

;; Owned の関数を関数の位置へ置くときに place を経由する根。
(define owned-function-roots '(Move CurryVal))

;; 関数の位置の Owned<NFn ...> を一段だけ剥がす。elaborate では拒否せず、
;; 型が関数でない形は後段の既存の non-function 判定へ渡す。
(define (owned-function-type? type)
  (match type
    [`(Owned (NFn ,_ ...)) #t]
    [_ #f]))

(define (peel-owned-function-elab type core)
  (cond
    [(not (owned-function-type? type)) (values type #f)]
    [else
     (define worn (peel-node core))
     (if (and (pair? worn) (memq (car worn) owned-function-roots))
         (values (second type) #t)
         (values type #f))]))

(define (type? value)
  (and (redex-match? G2 τ value)
       (type-shape-ok? value)))

(define (row-union left right)
  (term (row-∪ ,left ,right)))

(define (rows-union rows)
  (for/fold ([combined '()])
            ([row (in-list rows)])
    (row-union combined row)))

(define (row-difference row removed)
  (term (row-\\ ,row ,removed)))

(define (row-subset? left right)
  (term (row-⊆ ,left ,right)))

(define (row-member? label row)
  (term (row-∈ ,label ,row)))

(define (classify-recur-body-for-gate function parameters body environment
                                      callables)
  ;; block scrutinee の Reassign を分類器が型検査できるよう mut mode は保つ。
  (define classifier-environment
    (for/list ([entry (in-list environment)])
      (match entry
        [(list name type 'mut _ ...) (list name type 'mut)]
        [(list name type _ ...) (list name type)]
        [_ entry])))
  (classify-recur-body function parameters body classifier-environment callables))

(define (check-recur-body-gate s function parameters body environment
                               callables declared-row)
  (when (and (eq? (classify-recur-body-for-gate function parameters body
                                                  environment callables)
                  'Unknown)
             (not (row-member? 'Partial declared-row)))
    (reject s 'unknown-recur-requires-partial)))

(define (normalize-row row)
  (for/fold ([normalized '()])
            ([label (in-list row)])
    (row-union normalized (list label))))

;; RFN-003: elaboration では、その位置で見えている命題文脈を候補へ変換して
;; 渡す。typing の Γ_pc⁰ に対応する。
(define (type-compatible? actual expected propositions)
  (compat? actual expected (initial-candidate-context propositions)))

;; OWN-004。ownership.rkt は 2 引数の互換性述語を要求する。elaborate の
;; type-compatible? は命題文脈を第 3 引数に取るため、その位置の文脈を
;; 捕らえた閉包を渡す。互換性の判定と Union の候補選択が同じ述語で行われる。
(define (narrowing-kind actual expected propositions)
  (owned-narrowing-kind/for-elaboration
   actual expected
   (lambda (a e) (type-compatible? a e propositions))))

;; c3b。NFn 内側の損失は tag 互換でも恒等変換ではない。
(define (identity-conversion? actual expected context propositions)
  (and (tag-compat? actual expected context)
       (eq? (owned-narrowing-kind
             actual expected
             (lambda (a e) (type-compatible? a e propositions)))
            'ok)))

(define (identity-fit? actual expected context propositions)
  (and (identity-conversion? actual expected context propositions)
       (type-compatible? actual expected propositions)))

(define (union-compatible-members actual members propositions)
  (define exact
    (filter (lambda (member) (type-equiv? actual member)) members))
  (if (pair? exact)
      exact
      (filter (lambda (member)
                (type-compatible? actual member propositions))
              members)))

(define (mut-union-retaggable? actual expected context propositions)
  (define actual* (normalize-type actual))
  (define expected* (normalize-type expected))
  (cond
    [(type-equiv? actual* expected*) #t]
    [(and (pair? actual*) (eq? (car actual*) 'Record)
          (pair? expected*) (eq? (car expected*) 'Record))
     (define actual-row (second actual*))
     (define expected-row (second expected*))
     (and (= (length actual-row) (length expected-row))
          (for/and ([expected-field (in-list expected-row)])
            (define label (first expected-field))
            (define actual-field (assoc label actual-row))
            (and actual-field
                 (eq? (third actual-field) (third expected-field))
                 (eq? (and (member 'opt (cdddr actual-field)) #t)
                      (and (member 'opt (cdddr expected-field)) #t))
                 (mut-union-retaggable? (second actual-field)
                                        (second expected-field)
                                        context propositions))))]
    [(and (pair? expected*) (eq? (car expected*) 'Union))
     (for/and ([actual-member (in-list (union-members actual*))])
       (define expected-members (union-members expected*))
       (define compatible
         (union-compatible-members actual-member expected-members propositions))
       (define candidates
         (if (pair? compatible)
             compatible
             (filter (lambda (member)
                       (mut-union-retaggable? actual-member member context
                                              propositions))
                     expected-members)))
       (and (= (length candidates) 1)
            (mut-union-retaggable? actual-member (first candidates)
                                   context propositions)))]
    [else #f]))

(define (mut-union-rebuildable? actual expected context propositions)
  (define actual* (normalize-type actual))
  (define expected* (normalize-type expected))
  (if (type-compatible? actual* expected* propositions)
      #f
      (cond
        [(and (pair? actual*) (eq? (car actual*) 'Record)
              (pair? expected*) (eq? (car expected*) 'Record))
         (define actual-row (second actual*))
         (define expected-row (second expected*))
         (define needs-rebuild? #f)
         (define fields-fit?
           (for/and ([expected-field (in-list expected-row)])
             (define label (first expected-field))
             (define expected-type (second expected-field))
             (define expected-mark (third expected-field))
             (define expected-tail (cdddr expected-field))
             (define actual-field (assoc label actual-row))
             (cond
               [(not actual-field)
                (and (member 'opt expected-tail) #t)]
               [else
                (define actual-type (second actual-field))
                (define actual-mark (third actual-field))
                (define actual-tail (cdddr actual-field))
                (and (not (and (eq? actual-mark 'imm)
                               (eq? expected-mark 'mut)))
                     (or (not (member 'opt actual-tail))
                         (member 'opt expected-tail))
                     (if (and (eq? actual-mark 'mut)
                              (eq? expected-mark 'mut))
                         (and (mut-union-retaggable? actual-type expected-type
                                                     context propositions)
                              (unless (type-equiv? actual-type expected-type)
                                (set! needs-rebuild? #t))
                              #t)
                         (if (type-compatible? actual-type expected-type
                                               propositions)
                             #t
                             (and (mut-union-rebuildable?
                                   actual-type expected-type context propositions)
                                  (begin (set! needs-rebuild? #t) #t)))))])))
         (and fields-fit? needs-rebuild?)]
        [(and (pair? expected*) (eq? (car expected*) 'Union))
         (define members (union-members expected*))
         (define components
           (if (and (pair? actual*) (eq? (car actual*) 'Union))
               (union-members actual*)
               (list actual*)))
         (define needs-rebuild? #f)
         (define all-fit?
           (for/and ([component (in-list components)])
             (define compatible
               (union-compatible-members component members propositions))
             (if (pair? compatible)
                 #t
                 (let ([rebuildable
                        (filter (lambda (member)
                                  (mut-union-rebuildable? component member
                                                          context propositions))
                                members)])
                   (and (pair? rebuildable)
                        (begin (set! needs-rebuild? #t) #t))))))
         (and all-fit? needs-rebuild?)]
        [else #f])))

;; OWN-004。残余の drop が要る場合だけ Proof を挿入し、先に Owned 残余を
;; 取り除いた型を後続の通常の convert へ渡す。reject は呼び出し側の既存の
;; 判定順序に委ねる。
(define (discharge-remainder core actual expected s propositions)
  (match (narrowing-kind actual expected propositions)
    [`(drop-obligation ,_ ,_)
     (define target (remainder-target-type actual expected))
     (unless (rsd-eligible? actual expected)
       (error 'discharge-remainder
              "判定が適格でない drop-obligation を返した: ~s => ~s"
              actual expected))
     (define proof
       `(ProofRep (Reserved o-narrow)
                  (RemainderSafelyDropped ,actual ,target)))
     (values `(Discharge ,s ,proof ,core) target)]
    [_ (values core actual)]))

;; RFN-001/002: 表層注釈に書いてよい命題。判定表の (Prop id) と G1 の 2 命題を
;; 許し、(Presence label) は許さない。文法でも外しているが、注釈は Redex の
;; パターンを経ずに渡る経路があるため、解決時にも同じ線引きを課す。
(define (annotation-proposition? proposition)
  (match proposition
    [(or 'ValidNarrativeTrait 'TypeNarrativeCap) #t]
    [`(Prop ,_) (and (validator-row-by-proposition proposition) #t)]
    [`(ValidNarrativeTrait ,_) #t]
    [`(Implements ,_ ,_) #t]
    [`(RequiresBoth ,_ ,_) #t]
    [_ #f]))

(define (resolve-proposition proposition delta invalid-reason span)
  (unless (annotation-proposition? proposition)
    (reject span invalid-reason proposition))
  (define resolved
    (match proposition
      [`(Implements ,type ,trait)
       `(Implements ,(resolve-annotation type delta span) ,trait)]
      [_ proposition]))
  (or (normalize-proposition resolved)
      (reject span invalid-reason proposition)))

(define (resolve-obligations obligations delta span)
  (for/list ([proposition (in-list obligations)])
    (resolve-proposition proposition delta 'invalid-obligation span)))

(define (resolve-annotation raw-annotation delta inherited-span)
  (define span (nearest-span raw-annotation inherited-span))
  (define annotation (peel-ty raw-annotation))
  (define resolved
    (match annotation
      [`(Record ,row)
       (unless (field-row-unique? row)
         (reject span 'duplicate-record-label row))
       `(Record
         ,(for/list ([field (in-list row)])
            (match-define (list* label type rest) field)
            (list* label (resolve-annotation type delta span) rest)))]
      [`(List ,element)
       `(List ,(resolve-annotation element delta span))]
      [`(Option ,element)
       `(Option ,(resolve-annotation element delta span))]
      [`(Result ,ok-type ,error-type)
       `(Result ,(resolve-annotation ok-type delta span)
                ,(resolve-annotation error-type delta span))]
      [`(Data ,name (,arguments ...))
       `(Data ,name ,(map (lambda (argument)
                            (resolve-annotation argument delta span))
                          arguments))]
      [`(Owned ,inner)
       `(Owned ,(resolve-annotation inner delta span))]
      [`(Untrusted ,inner)
       `(Untrusted ,(resolve-annotation inner delta span))]
      [`(Refined ,inner ,proposition)
       `(Refined
         ,(resolve-annotation inner delta span)
         ,(resolve-proposition proposition delta 'invalid-proposition span))]
      [`(Union ,left ,right)
       `(Union ,(resolve-annotation left delta span)
               ,(resolve-annotation right delta span))]
      [`(Intersection ,left ,right)
       `(Intersection ,(resolve-annotation left delta span)
                      ,(resolve-annotation right delta span))]
      [`(NFn (,parameters ...) ,return-type ,row ,obligations)
       `(NFn ,(for/list ([parameter (in-list parameters)])
                (resolve-annotation parameter delta span))
             ,(resolve-annotation return-type delta span)
             ()
             ,(resolve-type-row row delta span)
             ,(resolve-obligations obligations delta span)
             User)]
      [`(TypeInfo ,kind) `(TypeInfo ,kind)]
      [`(Proof ,proposition)
       `(Proof
         ,(resolve-proposition proposition delta 'invalid-proposition span))]
      [(? symbol? name)
       (match (lookup delta name)
         [`(TypeRep ,_ ,type-form Type)
          (if (type? type-form)
              type-form
              (reject span 'invalid-type-representation name))]
         [`(TypeRep ,_ ,_ ,kind)
          (reject span 'unsaturated-type name kind)]
         [_ (reject span 'unknown-type name)])]
      [_ (reject span 'invalid-type-annotation annotation)]))
  (define normalized (normalize-type resolved))
  (if (and normalized (type? normalized))
      normalized
      (reject span 'invalid-resolved-type resolved)))

(define (resolve-type-row raw-row delta inherited-span)
  (define span (nearest-span raw-row inherited-span))
  (define row (peel-ef raw-row))
  (normalize-row
   (for/list ([label (in-list row)])
     (match label
       [`(Return ,boundary ,type)
        `(Return ,boundary ,(resolve-annotation type delta span))]
       [`(Yield ,type)
        `(Yield ,(resolve-annotation type delta span))]
       [(or 'Suspend 'Partial 'Compile 'Own 'Mutation) label]
       [_ (reject span 'invalid-effect-label label)]))))

(define (nearest-function-boundary boundaries)
  (for/first ([boundary (in-list boundaries)]
              #:when (eq? (first boundary) 'FunctionBoundary))
    boundary))

(define (nearest-expression-boundary boundaries)
  (for/first ([boundary (in-list boundaries)]
              #:break (memq (first boundary)
                            '(FunctionBoundary LeaveBoundaryStop))
              #:when (eq? (first boundary) 'ExpressionBoundary))
    boundary))

(define (boundary-span descriptor) (fourth descriptor))

(define (span-hull left right)
  `(#:span ,(second left) ,(min (third left) (third right))
           ,(max (fourth left) (fourth right))))

(define (span-through-end start end)
  ;; 逆順は位置順を持たない synthetic span だけで起こりうるため、source span の逆転は hull で隠さない。
  (if (and (eq? (second start) '#:synthetic)
           (eq? (second end) '#:synthetic)
           (> (third start) (fourth end)))
      (span-hull start end)
      `(#:span ,(second start) ,(third start) ,(fourth end))))

(define (resolve-declaration-row raw-row delta boundaries inherited-span
                                 #:loop-row? [loop-row? #f])
  (define span (nearest-span raw-row inherited-span))
  (define row (peel-ef raw-row))
  (if (eq? row '#:infer)
      '()
      (normalize-row
       (for/list ([label (in-list row)])
         (match label
           ['Return
            (match (nearest-function-boundary boundaries)
              [`(,_ ,_ #:infer ,_)
               ;; SUR-008。合成位置で戻り型が未定の間、宣言 row の Return は解決できない。
               (reject span 'return-type-not-inferable 'return-in-synth)]
              [(list _ boundary (list '#:probe _) _ _adapter ...)
               ;; SUR-015（spec §6.2）。下見では Return row の型を仮置きする。
               `(Return ,boundary Never)]
              [(list _ boundary type _ _adapter ...)
               `(Return ,boundary ,type)]
              [_ (reject span 'return-label-outside-boundary)])]
           ['Leave
            (if loop-row?
                (match (nearest-expression-boundary boundaries)
                  [(list _ boundary (list '#:probe _ ...) _ _adapter ...)
                   `(Return ,boundary Never)]
                  [(list _ _ '#:infer _ _adapter ...)
                   (reject span 'return-type-not-inferable 'return-in-synth)]
                  [(list _ boundary type _ _adapter ...)
                   `(Return ,boundary ,type)]
                  [_ (reject span 'leave-outside-expression-boundary)])
                (reject span 'invalid-effect-label label))]
           [`(Yield ,type)
            `(Yield ,(resolve-annotation type delta span))]
           [(or 'Suspend 'Partial 'Compile 'Own 'Mutation) label]
           [_ (reject span 'invalid-effect-label label)])))))

(define (kind-arity kind span)
  (match kind
    ['Type 0]
    [`(Type -> ,rest) (add1 (kind-arity rest span))]
    [_ (reject span 'invalid-kind kind)]))

(define (apply-type-constructor type-form arguments span)
  (match* (type-form arguments)
    [('List (list element)) `(List ,element)]
    [('Option (list element)) `(Option ,element)]
    [('Result (list ok-type error-type)) `(Result ,ok-type ,error-type)]
    [(_ _) (reject span 'invalid-type-application type-form arguments)]))

(define (interpret-spec raw-spec delta inherited-span)
  (define span (nearest-span raw-spec inherited-span))
  (define spec (peel-ty raw-spec))
  (match spec
    [(? symbol? name)
     (match (lookup delta name)
       [`(TypeRep ,_ ,type-form ,kind) (list type-form kind)]
       [_ (reject span 'unknown-type-spec name)])]
    [`(Spec ,head ,arguments ...)
     (match-define (list head-form head-kind)
       (interpret-spec head delta span))
     (define arity (kind-arity head-kind span))
     (unless (and (positive? arity)
                  (= arity (length arguments)))
       (reject span 'kind-mismatch spec head-kind))
     (define interpreted
       (for/list ([argument (in-list arguments)])
         (interpret-spec argument delta span)))
     (unless (andmap (lambda (result)
                       (and (equal? (second result) 'Type)
                            (type? (first result))))
                     interpreted)
       (reject span 'kind-mismatch spec))
     (list (apply-type-constructor head-form (map first interpreted) span)
           'Type)]
    [_ (reject span 'invalid-type-spec spec)]))

(define (authorized? propositions)
  (for/or ([entry (in-list propositions)])
    (match entry
      [`(,_ (TypeNarrativeCap ,_)) #t]
      [_ #f])))

(define (constructor-result constructor type-arguments span)
  (match (cons constructor type-arguments)
    [(list (or 'true 'false)) 'Bool]
    [(list (or 'nil 'cons) element) `(List ,element)]
    [(list (or 'none 'some) element) `(Option ,element)]
    [(list (or 'ok 'ng) ok-type error-type)
     `(Result ,ok-type ,error-type)]
    [(cons (app data-constructor (list name _)) arguments)
     (define decl (data-decl name))
     (if (= (length arguments) (length (second decl)))
         `(Data ,name ,arguments)
         (reject span 'constructor-type-arity constructor type-arguments))]
    [_ (reject span 'constructor-type-arity constructor type-arguments)]))

(define (sets-union sets)
  (for/fold ([combined (set)])
            ([item (in-list sets)])
    (set-union combined item)))

(define (free-vars raw-expression)
  (define expression (erase-surface raw-expression))
  (free-vars/erased expression))

;; spec §8。注釈あり Let と mode-only Let で同じ検査を走らせるための抽出で
;; ある。束縛型の決定と mut の検査と narrowing の検査を持つ。
;; 環境の拡張は呼ぶ側に残すので name は取らない。
(define (bind-with-mode s binding-mode declared-type actual-type propositions)
  (define binding-type
    (cond
      [(eq? actual-type 'Never) declared-type]
      [else
       (unless (or (type-compatible? actual-type declared-type propositions)
                   (mut-union-rebuildable?
                    actual-type declared-type '() propositions))
         (reject s 'type-mismatch declared-type actual-type))
       (match declared-type
         [`(Record ,declared-row)
          (match-define `(Record ,actual-row) actual-type)
          (define residual
            (field-row-residual actual-row declared-row))
          (when (and (eq? binding-mode 'const)
                     (pair? residual))
            (reject s 'const-record-residual residual))
          ;; P1c2b。mut も残余を戻す。typing の binding-context と揃える。
          (if (memq binding-mode '(let mut))
              `(Record ,(append declared-row residual))
              declared-type)]
         [_ declared-type])]))
  (when (and (eq? binding-mode 'mut)
             (or (not (owned-free? binding-type))
                 (unbound-borrowed-type? binding-type (set))))
    ;; mut binding の古い値を再代入で捨てるため、Owned と借用を
    ;; mutable な環境へ入れない。Record の内側も再帰的に検査する。
    (reject s 'mut-binding-unsupported-type binding-type))
  ;; OWN-004。let は最上位の残余を束縛型へ戻すため、残余反映後の
  ;; binding-type を expected 側に使う。これで入れ子の欄だけを検査する。
  (match (narrowing-kind actual-type binding-type propositions)
    ['ok (void)]
    [`(drop-obligation ,_ ,_)
     (reject s 'owned-narrowing-needs-proof binding-type actual-type)]
    [_ (unless (mut-union-rebuildable?
                actual-type binding-type (initial-candidate-context propositions)
                propositions)
         (reject s 'owned-narrowing-rejected binding-type actual-type))])
  binding-type)

(define (free-vars/erased expression)
  (match expression
    [(or (? integer?) (? string?) 'unit) (set)]
    [(? symbol? name) (set name)]
    [`(Fn ((,names ,_) ...) ,_ ,_ ,body)
     (set-subtract (free-vars/erased body) (list->set names))]
    [`(Apply ,terms ...)
     (sets-union (map free-vars/erased terms))]
    [`(Let (,name ,_ ,_) ,bound ,body)
     (set-union (free-vars/erased bound)
                (set-remove (free-vars/erased body) name))]
    ;; spec §8。2 欄の束縛子である。この節が無いと下の素の名前の節へ落ち、
    ;; (x let) という list を 1 つの名前として set-remove へ渡すので、
    ;; 束縛した名前が自由変数のまま残る。
    [`(Let (,name ,bmode) ,bound ,body)
     #:when (memq bmode '(const let mut))
     (set-union (free-vars/erased bound)
                (set-remove (free-vars/erased body) name))]
    [`(Let ,name ,bound ,body)
     (set-union (free-vars/erased bound)
                (set-remove (free-vars/erased body) name))]
    [`(TryBind ,name ,bound ,body)
     (set-union (free-vars/erased bound)
                (set-remove (free-vars/erased body) name))]
    [`(Rec (,fields ...))
     (sets-union
      (for/list ([field (in-list fields)])
        (match field
          [`(,_ ,_ ,body) (free-vars/erased body)]
          [_ (set)])))]
    [`(Absent ,_) (set)]
    [`(Proj ,record ,_) (free-vars/erased record)]
    [`(ProjOpt ,_ ,record ,_) (free-vars/erased record)]
    [`(Construct ,_ (Types ,_ ...) ,fields ...)
     (sets-union (map free-vars/erased fields))]
    [`(Construct ,_ ,fields ...)
     (sets-union (map free-vars/erased fields))]
    [`(Eliminate ,scrutinee (,branches ...))
     (set-union
      (free-vars/erased scrutinee)
      (sets-union
       (for/list ([branch (in-list branches)])
         (match branch
           [`(,_ ,(? symbol? parameter) -> ,body)
            (set-remove (free-vars/erased body) parameter)]
           [`(,_ (,parameters ...) -> ,body)
            (set-subtract (free-vars/erased body) (list->set parameters))]
           [_ (set)]))))]
    [`(IfSome (,clauses ...))
     (sets-union
      (for/list ([clause (in-list clauses)])
        (match clause
          [`(,condition ,body)
           (set-union (free-vars/erased condition)
                      (free-vars/erased body))])))]
    [`(BlockBody ,body) (free-vars/erased body)]
    [`(BlockBody ,_ ,body) (free-vars/erased body)]
    [`(Return ,body) (free-vars/erased body)]
    [`(Leave ,body) (free-vars/erased body)]
    [`(NarrativeExpr ,body) (free-vars/erased body)]
    [`(Recur ,function ((,parameters ,_) ...) ,_ ,_ ,body ,continuation)
     (set-union
      (set-subtract (free-vars/erased body)
                    (list->set (cons function parameters)))
      (set-remove (free-vars/erased continuation) function))]
    [`(Loop ,function ((,parameters ,_) ...) ,_ ,_ ,body (,arguments ...))
     (set-union
      (set-subtract (free-vars/erased body)
                    (list->set (cons function parameters)))
      (set-remove (sets-union (map free-vars/erased arguments)) function))]
    [`(FnDecl ,function ((,parameters ,_) ...) ,_ ,_ ,body ,continuation)
     (set-union
      (set-subtract (free-vars/erased body)
                    (list->set (cons function parameters)))
      (set-remove (free-vars/erased continuation) function))]
    [`(Yield ,observed ,next)
     (set-union (free-vars/erased observed) (free-vars/erased next))]
    [`(Suspend ,body) (free-vars/erased body)]
    [`(Reassign ,name ,value)
     (set-union (free-vars/erased name) (free-vars/erased value))]
    [`(Move ,name) (set name)]
    [`(Drop ,body) (free-vars/erased body)]
    [`(Curry ,function ,argument)
     (set-union (free-vars/erased function) (free-vars/erased argument))]
    [`(TypeMake ,_) (set)]
    [`(LetType ,_ (TypeMake ,_) ,body) (free-vars/erased body)]
    [_ (set)]))

(define (owned-captures expression locally-bound environment)
  (define visible-environment
    (for/fold ([visible '()])
              ([entry (in-list environment)])
      (if (assoc (first entry) visible)
          visible
          (cons entry visible))))
  (define outer-resources
    (for/set ([entry (in-list visible-environment)]
              #:when (resource-type? (second entry)))
      (first entry)))
  (sort
   (set->list
    (set-intersect
     (set-subtract (free-vars expression) (list->set locally-bound))
     outer-resources))
   symbol<?))

(define (captures-owned? expression locally-bound environment)
  (pair? (owned-captures expression locally-bound environment)))

;; §5: Diagnostic の生成は 1 箇所へ集約する。reject は struct を組み立てず、
;; registry の引き当てと欄の検証を通る経路をここへ揃える。
(define (elab-failure->diagnostic failure expansion-context)
  (define reason (exn:fail:elab-reason failure))
  (define phase (exn:fail:elab-phase failure))
  (define-values (expected found)
    (distribute-details reason (exn:fail:elab-details failure)))
  (diagnostic-of phase reason
                   #:primary-span (exn:fail:elab-primary-span failure)
                   #:expected expected
                   #:found found
                   #:related (exn:fail:elab-related failure)
                   #:expansion-context expansion-context))

(define (elab raw-expression #:expansion-context [expansion-context (hash)])
  (parameterize ([current-failure-returns (mutable-seteq)])
   (with-handlers ([exn:fail:elab?
                    (lambda (failure)
                      `(err ,(elab-failure->diagnostic failure expansion-context)))])
    (define reserved (reserved-binder-in raw-expression))
    (when reserved
      (reject (entry-span raw-expression)
              'reserved-binder-symbol
              (symbol->string reserved)))
    ;; span.md §7.4: UCore+ と UCore は交わらない。spanless な入力は
    ;; annotate-surface で UCore+ へ正規化し、以後は 1 つの形だけを扱う。
    ;; span を一部だけ持つ項はどちらにも属さず、ここで落ちる。
    (define expression
      (cond
        [(redex-match? UCore+ e raw-expression)
         (if (spans-ok? raw-expression)
             raw-expression
             (reject (entry-span raw-expression)
                     'invalid-syntax raw-expression))]
        [(redex-match? UCore e raw-expression) (annotate-surface raw-expression)]
        [else (reject (entry-span raw-expression)
                      'invalid-syntax raw-expression)]))

    (define boundary-counter 0)
    (define callable-counter 0)
    (define owned-counter 0)
    (define reversed-callables '())

    ;; SUR-014c0b1b spec §3。mut binder key から現在の C と pin への写像。
    (struct flow-entry (type pins) #:transparent)
    (struct loop-trial (function targets entry-views log) #:transparent)
    (struct pending-escape
      (boundary snapshot payload-core payload-result return-type span cell)
      #:transparent)
    (define current-boundary-escapes (make-parameter #f))
    (define current-escape-reachable? (make-parameter #t))
    (define current-loop-trials (make-parameter '()))
    (define current-loop-trial-catching? (make-parameter #f))
    (define current-generated-for-loop (make-parameter #f))
    (define flow-state (box (hasheq)))
    (define (flow-snapshot) (unbox flow-state))
    (define (flow-restore! snapshot) (set-box! flow-state snapshot))
    (define (boundary-escape-snapshot)
      (and (current-boundary-escapes)
           (hash-copy (current-boundary-escapes))))
    (define (boundary-escape-restore! snapshot)
      (define escapes (current-boundary-escapes))
      (when (and escapes snapshot)
        (hash-clear! escapes)
        (for ([(boundary pending) (in-hash snapshot)])
          (hash-set! escapes boundary pending))))
    ;; Recur 本体の Return は外側 Narrative が後で合流するため、flow だけ巻き戻す。
    (define (call-with-flow-rollback thunk #:preserve-escapes? [preserve-escapes? #f])
      (define snapshot (flow-snapshot))
      (define escapes (boundary-escape-snapshot))
      (dynamic-wind
       void thunk
       (λ ()
         (flow-restore! snapshot)
         (unless preserve-escapes?
           (boundary-escape-restore! escapes)))))
    (define (fresh-flow-key) (gensym 'mut-flow))
    (define (flow-key-of environment name)
      (match (assoc name environment)
        [(list _ _ 'mut _ key) key]
        [_ #f]))
    (define (flow-type key)
      (flow-entry-type (hash-ref (unbox flow-state) key)))
    (define (flow-pins key)
      (flow-entry-pins (hash-ref (unbox flow-state) key)))
    (define (loop-trial-suppressed-key? key)
      (for/or ([trial (in-list (current-loop-trials))])
        (memq key (loop-trial-targets trial))))
    (define (flow-set-type! key type)
      (define entry (hash-ref (unbox flow-state) key))
      (set-box! flow-state
                (hash-set (unbox flow-state) key
                          (flow-entry type (flow-entry-pins entry)))))
    (define (flow-add-pin! key pin)
      (unless (loop-trial-suppressed-key? key)
        (define normalized
          (or (normalize-type pin)
              (error 'flow-add-pin! "正規化できない pin: ~s" pin)))
        (define entry (hash-ref (unbox flow-state) key))
        (unless (ormap (λ (current) (type-equiv? current normalized))
                       (flow-entry-pins entry))
          (set-box! flow-state
                    (hash-set (unbox flow-state) key
                              (flow-entry
                               (flow-entry-type entry)
                               (append (flow-entry-pins entry) (list normalized))))))
        (void)))
    (define (flow-pin-captures! body bound-names environment)
      (for ([name (in-set (set-subtract (free-vars body)
                                        (list->set bound-names)))])
        (define key (flow-key-of environment name))
        (when key (flow-add-pin! key (flow-type key)))))
    (define (record-loop-back-edge! function arguments)
      (define function-name
        (match (peel-node function)
          [(? symbol? name) name]
          [_ #f]))
      (define trial
        (and function-name
             (for/or ([candidate (in-list (current-loop-trials))])
               (and (eq? function-name (loop-trial-function candidate))
                    candidate))))
      (when (and trial (andmap judgment-completes? arguments))
        (set-box! (loop-trial-log trial)
                  (append (unbox (loop-trial-log trial))
                          (list (flow-snapshot))))
        (for ([key (in-list (loop-trial-targets trial))])
          (flow-set-type! key
                          (hash-ref (loop-trial-entry-views trial) key))))
      (void))
    (define (live-flow-keys environment)
      (remove-duplicates
       (filter values
               (for/list ([name (in-list (remove-duplicates
                                          (map first environment)))])
                 (flow-key-of environment name)))))
    (define (flow-view environment name)
      (define key (flow-key-of environment name))
      (if key (flow-type key) (lookup environment name)))

    (define (fresh-boundary)
      (define boundary
        (string->symbol (format "boundary~a" boundary-counter)))
      (set! boundary-counter (add1 boundary-counter))
      boundary)

    (define (judgment-completes? result)
      (not (eq? (judgment-type result) 'Never)))

    (define (register-pending-escape boundary return-type span result)
      (define escapes (current-boundary-escapes))
      (and escapes
           (judgment-completes? result)
           (let* ([pending
                   (pending-escape boundary (flow-snapshot)
                                   (judgment-core result) result
                                   return-type span (box #f))]
                  [previous (hash-ref escapes boundary '())])
             (hash-set! escapes boundary (append previous (list pending)))
             pending)))

    (define (option-payload-adapter? adapter)
      (or (eq? adapter 'option-payload)
          (match adapter [`(Option ,_) #t] [_ #f])))

    (define (option-adapter-payload-type adapter)
      (match adapter [`(Option ,type) type] [_ #f]))

    (define (leave-probe-candidate-type candidate adapter)
      (match candidate
        [`(leave-payload ,type) type]
        [`(Option ,type) #:when (eq? adapter 'option-payload) type]
        [_ candidate]))

    (define (wrap-leave-payload span result adapter)
      (match adapter
        [`(Option ,payload-type)
         (define payload-core (judgment-core result))
         (define field-core
           (if (and (owned-type? payload-type)
                    (not (match (peel-node payload-core)
                           [`(OwnLeaf ,_) #t]
                           [_ #f])))
               `(OwnLeaf ,span ,payload-core)
               payload-core))
         (judgment
          `(Construct ,span (#:ty ,adapter ,span) some
                      ,field-core)
          adapter (judgment-row result) adapter adapter)]
        [_ result]))

    (define (elaborate-boundary-escape expression s returned boundary
                                       environment delta
                                       propositions boundaries
                                       #:reachable? [reachable? #t]
                                       #:leave-adapter [leave-adapter #f])
      (match boundary
        [`(,_ ,_ #:infer ,_)
         ;; Return と Leave は境界解決後の推論経路を共有する。
         (reject s 'return-type-not-inferable 'return-in-synth)]
        [(list boundary-kind boundary-id
               (list '#:probe candidates unresolved-leave-boxes ...)
               _ _adapter ...)
         (if (not reachable?)
             (let* ([checked-result
                     (for/or ([candidate (in-list (unbox candidates))]
                              #:unless (eq? candidate 'Never))
                       (with-handlers ([exn:fail:elab? (λ (_) #f)])
                         (call-with-restored-state
                          (λ ()
                            (check returned
                                   (leave-probe-candidate-type
                                    candidate leave-adapter)
                                   environment delta
                                   propositions boundaries)))))]
                    [returned-result
                     (or checked-result
                         (call-with-restored-state
                          (λ ()
                            (synth returned environment delta propositions
                                   boundaries))))])
               ;; 到達不能な Leave は payload の Core を残すが、候補や flow は更新しない。
               (judgment (judgment-core returned-result) 'Never
                         (judgment-row returned-result)
                         (judgment-core-type returned-result)
                         (judgment-normal-type returned-result)))
             (begin
               ;; SUR-015。payload を合成できなければ本番へ回す。
               (unless (and (current-failure-returns)
                            (set-member? (current-failure-returns)
                                         expression))
                 (let ([returned-result
                        (with-handlers ([exn:fail:elab? (λ (_) #f)])
                          (call-with-flow-rollback
                           (λ ()
                             (synth returned environment delta propositions
                                    boundaries))))])
                   (if returned-result
                       (set-box! candidates
                                 (append (unbox candidates)
                                         (list
                                          (if (option-payload-adapter?
                                               leave-adapter)
                                              `(leave-payload
                                                ,(judgment-type returned-result))
                                              (judgment-type returned-result)))))
                       ;; 下見不能な Leave の状態を型候補へ混ぜない。
                       (when (and (eq? boundary-kind 'ExpressionBoundary)
                                  (pair? unresolved-leave-boxes)
                                  (box? (first unresolved-leave-boxes)))
                         (set-box! (first unresolved-leave-boxes) #t)))))
               (judgment `(#:lit unit ,s) 'Never
                         `((Return ,boundary-id Never))))) ]
        [(list boundary-kind boundary-id return-type _ _adapter ...)
         #:when (memq boundary-kind '(ExpressionBoundary FunctionBoundary))
         (define payload-type
           (or (option-adapter-payload-type leave-adapter) return-type))
         (if (not reachable?)
             (let ([returned-result
                    ;; Dead payload の Core は親の局所型検査にも必要なので保持する。
                    (with-handlers ([exn:fail:elab?
                                     (λ (_)
                                       (call-with-restored-state
                                        (λ ()
                                          (synth returned environment delta
                                                 propositions boundaries))))])
                      (call-with-restored-state
                       (λ ()
                         (check returned payload-type environment delta
                                propositions boundaries))))])
               ;; 到達不能な Leave は payload の row だけを保ち、脱出と flow は作らない。
               (judgment (judgment-core returned-result) 'Never
                         (judgment-row returned-result)
                         (judgment-core-type returned-result)
                         (judgment-normal-type returned-result)))
             (let* ([returned-result
                     (check returned payload-type
                            environment delta propositions boundaries)]
                    [adapted-result
                     (wrap-leave-payload s returned-result leave-adapter)]
                    [pending
                     (match boundary
                       [`(ExpressionBoundary ,candidate ,_ ,_ ,_)
                        (register-pending-escape candidate return-type s
                                                 adapted-result)]
                       [_ #f])])
               (judgment
                (or pending
                    `(Perform ,s (Return ,boundary-id
                                          (#:ty ,return-type ,s))
                              ,(judgment-core adapted-result)))
                'Never
                (row-union `((Return ,boundary-id ,return-type))
                           (judgment-row adapted-result)))))]
        [_ (reject s 'return-outside-boundary)]))

    (define (resolve-pending-escapes core)
      (cond
        [(pending-escape? core)
         (define resolved (unbox (pending-escape-cell core)))
         (unless resolved
           (error 'resolve-pending-escapes
                  "境界で確定されていない脱出: ~s" core))
         (resolve-pending-escapes resolved)]
        [(pair? core)
         (cons (resolve-pending-escapes (car core))
               (resolve-pending-escapes (cdr core)))]
        [else core]))

    (define (classification-view core)
      ;; 脱出直前の再構成は payload 評価後で再帰呼出しを含まず、分類事実を変えない。
      (cond
        [(pending-escape? core)
         (define span (pending-escape-span core))
         `(Perform ,span
                   (Return ,(pending-escape-boundary core)
                           (#:ty ,(pending-escape-return-type core) ,span))
                   ,(classification-view
                     (pending-escape-payload-core core)))]
        [(pair? core)
         (cons (classification-view (car core))
               (classification-view (cdr core)))]
        [else core]))

    (define (fresh-callable signature)
      (define callable
        (string->symbol (format "callable~a" callable-counter)))
      (set! callable-counter (add1 callable-counter))
      (set! reversed-callables
            (cons (list callable signature) reversed-callables))
      callable)

    ;; G5c5b1 spec §4.3。Owned の仮引数を Core の仮引数列へ置くための生名を
    ;; 取る。生名は変数の名前空間に入るため、fresh-boundary のように連番
    ;; だけで作ることはできない。
    ;;
    ;; 予約する記号は次の 4 つの和である。
    ;;   surface の本体に現れる記号
    ;;   宣言した仮引数の名前すべて。本体で使われない仮引数も含める
    ;;   Recur の場合は、宣言した関数の名前
    ;;   その時点の環境の定義域
    ;;
    ;; 本体に現れない仮引数の名前を入れるのは、生名と同じつづりになると
    ;; Lam の仮引数列で名前が重複するためである。Recur の関数の名前を
    ;; 入れるのは、生名と同じつづりになると本体の再帰呼出しが Let の
    ;; binder ではなく生名へ束縛されるためである。
    ;;
    ;; span や型注釈の中の記号まで拾うため予約は過剰になるが、衝突しない
    ;; という性質は保たれる。
    (define (form-symbols form)
      (let loop ([node form] [acc (set)])
        (cond
          [(symbol? node) (set-add acc node)]
          [(pair? node) (loop (cdr node) (loop (car node) acc))]
          [else acc])))

    (define (function-reserved-names function arguments environment)
      (for/fold ([taken
                  (set-union (form-symbols function)
                             (list->set (map first environment)))])
                ([argument (in-list arguments)])
        (set-union taken (form-symbols argument))))

    ;; 採った候補を予約集合へ加えてから次の位置へ進む。elab 全体で共有する
    ;; 連番を使うため、入れ子の Fn の間でも生名は重ならない。同じ入力に
    ;; 対して同じ名前が出るため、凍結 fixture と試験の期待値が安定する。
    (define (fresh-owned-name reserved)
      (let next ()
        (define candidate
          (string->symbol (format "owned~a" owned-counter)))
        (set! owned-counter (add1 owned-counter))
        (if (set-member? reserved candidate)
            (next)
            candidate)))

    ;; P2m2b spec §3.1。変換が置く枝と Let の binder に使う生名。
    ;; 入力の式に現れる symbol と衝突させず、elab 内で一意にする。
    (define union-counter 0)
    (define union-reserved (form-symbols raw-expression))
    ;; mut 欄の再構築中は、その内側でも関数 adapter を作らない。
    (define mut-field-adapter-forbidden? (make-parameter #f))
    (define mut-field-retagging? (make-parameter #f))
    (define (conversion-noop? actual expected context propositions)
      (if (mut-field-retagging?)
          (type-equiv? actual expected)
          (identity-fit? actual expected context propositions)))
    (define (contains-nfn? type)
      (or (match type [`(NFn ,_ ...) #t] [_ #f])
          (and (pair? type) (ormap contains-nfn? type))))
    ;; VAR-003 は mut 欄の Union 選択にも及ぶ。実行時の各 Union 枝と
    ;; Record の共通欄を対応させ、対応する NFn は型同値の場合だけ残す。
    (define (mut-field-functions-invariant? actual expected propositions)
      (let walk ([actual (normalize-type actual)]
                 [expected (normalize-type expected)])
        (match actual
          ['Never #t]
          [`(Union ,_ ,_)
           (for/and ([member (in-list (union-members actual))])
             (walk member expected))]
          [_
           (match expected
             [`(Union ,_ ,_)
              (for/or ([member (in-list (union-members expected))])
                (and (type-compatible? actual member propositions)
                     (walk actual member)))]
             [`(NFn ,_ ...)
              (and (match actual [`(NFn ,_ ...) #t] [_ #f])
                   (type-equiv? actual expected))]
             [`(Record ,expected-row)
              (match actual
                [`(Record ,actual-row)
                 (for/and ([field (in-list actual-row)])
                   (define corresponding
                     (assq (first field) expected-row))
                   (or (not corresponding)
                       (not (contains-nfn? (second field)))
                       (walk (second field) (second corresponding))))]
                [_ (not (contains-nfn? actual))])]
             [_
              (cond
                [(not (contains-nfn? actual)) #t]
                [(and (list? actual) (list? expected)
                      (= (length actual) (length expected))
                      (equal? (car actual) (car expected)))
                 (andmap walk (cdr actual) (cdr expected))]
                [else #f])])])))
    (define (mut-field-candidate? actual member propositions)
      (or (not (mut-field-adapter-forbidden?))
          (mut-field-functions-invariant? actual member propositions)))
    (define (fresh-union-name)
      (let next ()
        (define candidate
          (string->symbol (format "union~a" union-counter)))
        (set! union-counter (add1 union-counter))
        (if (set-member? union-reserved candidate) (next) candidate)))

    (define (failure-return s payload)
      (define result `(Return ,s ,payload))
      (define returns (current-failure-returns))
      (unless returns
        (error 'failure-return "elab の入口が failure return の印を設定していない"))
      (set-add! returns result)
      result)

    (define (resource-branch-body s member name alias body [alias-span s])
      (if alias
          `(Scope ,s ()
                  (Let ,s ((#:bind ,alias ,alias-span) let (#:ty ,member ,s))
                       (#:var ,name ,s)
                       ,body))
          body))

    ;; 試行 Core に残余の discharge が含まれるかを調べる。
    (define (core-has-remainder-drop? core)
      (or (match core
            [`(Discharge ,_ (ProofRep (Reserved o-narrow)
                                      (RemainderSafelyDropped ,_ ,_)) ,_)
             #t]
            [`(Discharge (ProofRep (Reserved o-narrow)
                                  (RemainderSafelyDropped ,_ ,_)) ,_)
             #t]
            [_ #f])
          (and (pair? core)
               (ormap core-has-remainder-drop? core))))

    ;; 候補への再構築を試す間に生名を消費しても、本番の変換名へ影響
    ;; させない。試行で使う項は破棄するため、変換が参照を埋め込める
    ;; span 付き Core 変数を渡す。
    (define (rebuild-probe-core actual member kind s propositions
                                #:transfer [transfer 'move])
      (call-with-restored-state
       (lambda ()
         (define actual-kind (narrowing-kind actual member propositions))
         (and (case kind
                [(ok) (eq? actual-kind 'ok)]
                [(drop-obligation)
                 (match actual-kind [`(drop-obligation ,_ ,_) #t] [_ #f])]
                [else #f])
              (with-handlers ([exn:fail:elab? (lambda (_) #f)])
                (define-values (probe-core probe-type)
                  (if (eq? kind 'drop-obligation)
                      (discharge-remainder `(#:var rebuild-probe ,s)
                                           actual member s propositions)
                  (values `(#:var rebuild-probe ,s) actual)))
                (define-values (converted _type)
                  (convert probe-core probe-type member s propositions
                           #:transfer transfer))
                converted)))))

    (define (rebuild-reachable? actual member kind s propositions
                                #:transfer [transfer 'move])
      (and (rebuild-probe-core actual member kind s propositions
                               #:transfer transfer)
           #t))

    ;; 成分の位置でなく損失の種類で優先順位を決める。試行による生名の消費は
    ;; rebuild-probe-core が復元する。
    (define (union-member-tiers actual members s propositions
                                #:transfer [transfer 'move])
      (define context (initial-candidate-context propositions))
      (define eligible-members
        (filter (lambda (member)
                  (mut-field-candidate? actual member propositions))
                members))
      (define analyses
        (for/list ([member (in-list eligible-members)])
          (define kind (narrowing-kind actual member propositions))
          (define target
            (match kind
              [`(drop-obligation ,_ ,_)
               (remainder-target-type actual member)]
              [_ #f]))
          (list member kind
                (conversion-noop? actual member context propositions)
                target)))
      (define tier1
        (for/list ([analysis (in-list analyses)]
                   #:when (and (third analysis)
                               (eq? (second analysis) 'ok)))
          (first analysis)))
      (define tier2-probes
        (for/list ([analysis (in-list analyses)]
                   #:when (and (not (third analysis))
                               (eq? (second analysis) 'ok)))
          (cons (first analysis)
                (rebuild-probe-core actual (first analysis) 'ok s propositions
                                    #:transfer transfer))))
      (define tier2
        (for/list ([probe (in-list tier2-probes)]
                   #:when (and (cdr probe)
                               (not (core-has-remainder-drop? (cdr probe)))))
          (car probe)))
      (define tier2-lossy
        (for/list ([probe (in-list tier2-probes)]
                   #:when (and (cdr probe)
                               (core-has-remainder-drop? (cdr probe))))
          (car probe)))
      (define tier3
        (for/list ([analysis (in-list analyses)]
                   #:when (and (match (second analysis)
                                  [`(drop-obligation ,_ ,_) #t]
                                  [_ #f])
                               (fourth analysis)
                               (conversion-noop? (fourth analysis)
                                                 (first analysis)
                                                 context propositions)))
          (first analysis)))
      (define tier4-rebuild
        (for/list ([analysis (in-list analyses)]
                   #:when (and (match (second analysis)
                                  [`(drop-obligation ,_ ,_) #t]
                                  [_ #f])
                               (fourth analysis)
                               (not (conversion-noop? (fourth analysis)
                                                      (first analysis)
                                                      context propositions))
                               (rebuild-reachable? actual (first analysis)
                                                   'drop-obligation s
                                                   propositions
                                                   #:transfer transfer)))
          (first analysis)))
      (define tier4
        (remove-duplicates (append tier4-rebuild tier2-lossy) type-equiv?))
      (define fallback
        (if (pair? tier4)
            '()
            (filter
             (lambda (member)
               ((if (mut-field-retagging?)
                    mut-union-retaggable?
                    mut-union-rebuildable?)
                actual member context propositions))
             eligible-members)))
      (values tier1 tier2 tier3 (if (pair? tier4) tier4 fallback)))

    ;; 完全一致の後、損失のない成分を優先する。
    (define (choose-union-member actual expected s propositions
                                 #:no-member-key [no-member-key 'type-mismatch]
                                 #:transfer [transfer 'move])
      (define members
        (filter (lambda (member)
                  (mut-field-candidate? actual member propositions))
                (union-members expected)))
      (define exact
        (for/first ([member (in-list members)]
                    #:when (type-equiv? member actual))
          member))
      (cond
        [exact exact]
        [else
         (define-values (tier1 tier2 tier3 tier4)
           (union-member-tiers actual members s propositions
                               #:transfer transfer))
         (define selected-tier
           (or (and (pair? tier1) tier1)
               (and (pair? tier2) tier2)
               (and (pair? tier3) tier3)
               (and (pair? tier4) tier4)))
         (cond
           [selected-tier
            (match selected-tier
              [(list member) member]
              [_ (reject s 'ambiguous-union-member expected actual
                         selected-tier)])]
           [else
            (define owned-rejection?
              (for/or ([member (in-list members)])
                (define kind (narrowing-kind actual member propositions))
                (and (type-compatible? actual member propositions)
                     (or (eq? kind 'reject)
                        (match kind
                           [`(drop-obligation ,_ ,_) #t]
                           [_ #f])))))
            (reject s (if owned-rejection?
                          'owned-narrowing-rejected
                          no-member-key)
                    expected actual)])]))

    (define (union-inject core actual expected s propositions
                          #:no-member-key [no-member-key 'type-mismatch]
                          #:transfer [transfer 'move])
      (define member
        (choose-union-member actual expected s propositions
                             #:no-member-key no-member-key
                             #:transfer transfer))
      (define context (initial-candidate-context propositions))
      (define-values (discharged actual*)
        (discharge-remainder core actual member s propositions))
      (define payload
        (if (conversion-noop? actual* member context propositions)
            discharged
            (let-values ([(converted _type)
                          (convert discharged actual* member s propositions
                                   #:transfer transfer)])
              converted)))
      `(UnionInject ,s (#:ty ,expected ,s) (#:ty ,member ,s) ,payload))

    ;; 関数値の引数と結果は、同じ OWN-004 の順で変換してから通常の convert
    ;; へ渡す。内側の損失は adapter 本体の RSD で回収する。
    (define (convert-adapter-value core actual expected s propositions
                                   #:transfer [transfer 'move])
      (unless (type-compatible? actual expected propositions)
        (reject s 'type-mismatch expected actual))
      (define-values (discharged actual*)
        (discharge-remainder core actual expected s propositions))
      (match (narrowing-kind actual* expected propositions)
        ['ok (void)]
        [_ (reject s 'owned-narrowing-rejected expected actual*)])
      (define-values (converted converted-type)
        (convert discharged actual* expected s propositions
                 #:transfer transfer))
      (values converted converted-type))

    (define (function-adapter core actual expected s propositions)
      (when (mut-field-adapter-forbidden?)
        (reject s 'type-mismatch expected actual))
      (match* (actual expected)
        [(`(NFn (,actual-parameters ...) ,actual-return ,_actual-in
                ,_actual-out ,actual-obligations ,_actual-origin)
          `(NFn (,expected-parameters ...) ,expected-return ,expected-in
                ,expected-out ,expected-obligations ,_expected-origin))
         (unless (= (length actual-parameters) (length expected-parameters))
           (reject s 'type-mismatch expected actual))
         (unless (type-compatible? actual expected propositions)
           (reject s 'type-mismatch expected actual))
         (define proofs
           (obligation-proofs
            actual-obligations (initial-candidate-context propositions)))
         (when (memq #f proofs)
           ;; adapter の定義位置で元の callable の Q を搬送できない。
           (reject s 'type-mismatch expected actual))

         (define source-name (fresh-union-name))
         (define function-name (fresh-union-name))
         (define parameter-names
           (for/list ([_ (in-list expected-parameters)])
             (fresh-union-name)))
         (define converted-arguments
           (for/list ([name (in-list parameter-names)]
                      [source-type (in-list expected-parameters)]
                      [target-type (in-list actual-parameters)])
             (define resource-argument? (resource-type? source-type))
             (define-values (converted _type)
               (convert-adapter-value
                (if resource-argument?
                    `(Forward ,s (#:var ,name ,s))
                    `(#:var ,name ,s))
                source-type target-type s propositions
                #:transfer (if resource-argument? 'forward 'move)))
             (define local-name
               (and (not resource-argument?) (fresh-union-name)))
             (list local-name target-type converted resource-argument?)))
         (define applied
           `(Apply ,s (#:var ,function-name ,s)
                   ,@(for/list ([argument (in-list converted-arguments)])
                       (if (fourth argument)
                           (third argument)
                           `(#:var ,(first argument) ,s)))))
         (define applied-with-proofs
           (for/fold ([body applied]) ([proof (in-list (reverse proofs))])
             `(Discharge ,s ,proof ,body)))
         ;; 呼び出しを E_tail の束縛式に置き、返り値の転送はその後で行う。
         (define return-name (fresh-union-name))
         (define-values (converted-return _converted-return-type)
           (convert-adapter-value
                                  (if (resource-type? actual-return)
                                      `(Forward ,s (#:var ,return-name ,s))
                                      `(#:var ,return-name ,s))
                                  actual-return expected-return s propositions
                                  #:transfer 'forward))
         (define converted-return-let
           `(Let ,s ((#:bind ,return-name ,s)
                     ,(if (resource-type? actual-return) 'let 'const)
                     (#:ty ,actual-return ,s))
                 ,applied-with-proofs
                 ,converted-return))
         (define body-core
           (for/fold ([body converted-return-let])
                     ([argument (in-list (reverse converted-arguments))]
                      #:unless (fourth argument))
             `(Let ,s ((#:bind ,(first argument) ,s) let
                       (#:ty ,(second argument) ,s))
                   ,(third argument)
                   ,body)))
         (define parameter-binders
           (cons `(#:bind ,function-name ,s)
                 (for/list ([name (in-list parameter-names)])
                   `(#:bind ,name ,s))))
         (define boundary (fresh-boundary))
         (define signature
           `(NFn ,(cons actual expected-parameters) ,expected-return
                ,expected-in ,expected-out ,expected-obligations User))
         (define callable (fresh-callable signature))
         (define-values (capture-raw-names raw-names capture-binders
                                           core-binders reserved-with-formals)
           (prepare-fn-binders s parameter-binders
                               (cons function-name parameter-names)
                               (cons actual expected-parameters)
                               '() '() body-core '()))
         ;; 結果位置の Forward gate は所有する Lam の本体を検査するため、
         ;; 資源引数の有無にかかわらず完成形を型付けする。
         (define body-result (judgment body-core expected-return '()))
         (define adapter-lambda
           (finish-fn s parameter-binders
                      (cons actual expected-parameters)
                      '() '() capture-raw-names raw-names capture-binders
                      core-binders expected-return boundary body-result
                      signature callable reserved-with-formals))
         (match (core-type-of/diagnostic
                 (judgment-core adapter-lambda) '()
                 (reverse reversed-callables))
           [(list adapter-type _row)
            (unless (type-equiv? adapter-type signature)
              (reject s 'type-mismatch signature adapter-type))]
           [diagnostic
            (case (diagnostic-id diagnostic)
              [("E-EFF-002" "E-EFF-005")
               (reject s 'undeclared-function-effect
                       (diagnostic-expected diagnostic)
                       (diagnostic-found diagnostic))]
              [("E-OWN-036")
               ;; 生成形からは届かず、elaborate には Forward 専用の診断 key が無い。
               (reject s 'type-mismatch expected actual)]
              [else (reject s 'type-mismatch expected actual)])])
         (values
          `(Let ,s ((#:bind ,source-name ,s) let (#:ty ,actual ,s))
                ,core
                (Curry ,s ,(judgment-core adapter-lambda)
                       (#:var ,source-name ,s)))
          expected)]
        [(_ _) (reject s 'type-mismatch expected actual)]))

    (define (record-row-of type)
      (match type [`(Record ,row) row] [_ #f]))

    ;; P2m2b spec §3.1。(values Core 変換後の型) を返すか、その位置で拒否する。
    (define (convert core actual expected s propositions #:entry? [entry? #f]
                     #:transfer [transfer 'move])
      (define actual* (normalize-type actual))
      (define expected* (normalize-type expected))
      (define context (initial-candidate-context propositions))
      ;; tag-compatible な短絡と decompose の枝対応より先に不変性を確認する。
      (when (and (mut-field-adapter-forbidden?)
                 (not (mut-field-functions-invariant?
                       actual* expected* propositions)))
        (reject s 'type-mismatch expected* actual*))
      (define actual-union?
        (match actual* [`(Union ,_ ,_) #t] [_ #f]))
      (define expected-union?
        (match expected* [`(Union ,_ ,_) #t] [_ #f]))
      (cond
        [(eq? actual* 'Never) (values core 'Never)]
        [(conversion-noop? actual* expected* context propositions)
         (values core actual*)]
        [(and expected-union? (not actual-union?))
         (values (union-inject core actual* expected* s propositions
                               #:transfer transfer)
                 expected*)]
        [actual-union?
         (decompose core actual* expected* s propositions
                    #:entry? entry? #:transfer transfer)]
        [(and (record-row-of actual*) (record-row-of expected*))
         (rebuild-record core (record-row-of actual*) (record-row-of expected*)
                         s propositions #:transfer transfer)]
        [(and (match actual* [`(NFn ,_ ...) #t] [_ #f])
              (match expected* [`(NFn ,_ ...) #t] [_ #f])
              (not (type-compatible? actual* expected* propositions)))
         (reject s 'type-mismatch expected* actual*)]
        [(and (match actual* [`(NFn ,_ ...) #t] [_ #f])
              (match expected* [`(NFn ,_ ...) #t] [_ #f]))
         (function-adapter core actual* expected* s propositions)]
        [else (reject s 'type-mismatch expected actual)]))

    ;; 型だけを合流し、record の欄を作り直す必要があるかも返す。
    ;; return 候補には Core が無いため、枝の型付けと共通の判定を使う。
    (define (merge-branch-types types s)
      (define live (filter (lambda (type) (not (eq? type 'Never))) types))
      (define all-equivalent?
        (and (pair? live)
             (andmap (lambda (type) (type-equiv? type (first live))) live)))
      (define record-join?
        (and (pair? live)
             (andmap (match-lambda [`(Record ,_) #t] [_ #f]) live)
             (not all-equivalent?)))
      (define target
        (cond
          [(null? live) 'Never]
          [all-equivalent? (first live)]
          [record-join?
           (or (row005-join live)
               (apply reject s 'type-mismatch (take live 2)))]
          [else
           (define union
             (normalize-type
              (foldr (lambda (type rest) `(Union ,type ,rest))
                     (last live)
                     (drop-right live 1))))
           (when (owned-union-member? union)
             (define first-type (first live))
             (apply reject
                    s 'type-mismatch
                    (list first-type
                          (or (findf (lambda (type)
                                       (not (type-equiv? type first-type)))
                                     live)
                              first-type))))
           union]))
      (values target record-join?))

    ;; c2b1 spec §5.1。枝を ROW-005 の上界へそろえ、実際に作り直した Core の型から
    ;; Core の合流型を求める。Never の枝は Core と同じく上界から除く。
    (define (merge-branches cores types s propositions)
      (define live (filter (lambda (type) (not (eq? type 'Never))) types))
      (define-values (target record-join?) (merge-branch-types types s))
      (define rebuilt-pairs
        (for/list ([core (in-list cores)] [type (in-list types)])
          (cond
            [(or (eq? type 'Never) (eq? target 'Never)) (cons core type)]
            [else
             (define-values (core-after-discharge type-after-discharge)
               (if record-join?
                   (discharge-remainder core type target s propositions)
                   (values core type)))
             (when record-join?
               (match (narrowing-kind type-after-discharge target propositions)
                 ['ok (void)]
                 [`(drop-obligation ,_ ,_)
                  (reject s 'owned-narrowing-needs-proof target
                          type-after-discharge)]
                 [_ (reject s 'owned-narrowing-rejected target
                            type-after-discharge)]))
             (let-values ([(core* type*)
                           (convert core-after-discharge
                                    type-after-discharge target s propositions)])
               (cons core* type*))])))
      (define rebuilt-live-types
        (filter (lambda (type) (not (eq? type 'Never)))
                (map cdr rebuilt-pairs)))
      (define upper
        (if (null? rebuilt-live-types)
            'Never
            (branch-types-upper-bound rebuilt-live-types)))
      (when (tag-bound-failure? upper)
        (define first-type (first live))
        (apply reject
               s 'type-mismatch
               (list first-type
                     (or (findf (lambda (type)
                                  (not (type-equiv? type first-type)))
                                live)
                         first-type))))
      (values (map car rebuilt-pairs) upper))

    (define (decompose core actual expected s propositions #:entry? [entry? #f]
                       #:transfer [transfer 'move])
      (define context (initial-candidate-context propositions))
      (define branches
        (for/list ([member (in-list (union-members actual))])
          (define name (fresh-union-name))
          (define alias
            (and (not entry?)
                 (resource-type? member)
                 (fresh-owned-name (set-add union-reserved name))))
          (list member name alias)))
      (define (reference name) `(#:var ,name ,s))
      (define (consume-reference ref)
        (if (eq? transfer 'forward)
            `(Forward ,s ,ref)
            `(Move ,s ,ref)))
      (define (eliminate bodies)
        `(UnionEliminate ,s ,core
           ,(for/list ([branch (in-list branches)]
                       [body (in-list bodies)])
              (match-define (list member name _alias) branch)
              `(,s (#:ty ,member ,s) (#:bind ,name ,s) -> ,body))))
      (define (wrap-reference mode type bound [move? #f])
        (define name (fresh-union-name))
        (define ref (reference name))
        `(Let ,s ((#:bind ,name ,s)
                  ,(if (and move? (eq? transfer 'forward) (eq? mode 'const))
                       'let
                       mode)
                  (#:ty ,type ,s))
              ,bound
              ,(if move? (consume-reference ref) ref)))
      (match expected
        [`(Record ,expected-row)
         ;; 各枝を expected の欄型を持つ W_k に揃えてから上界を取る。
         ;; 成分の元の型ではなく W_k の型を合流するため、ここで同じ OWN-004 と convert の順序を行う。
         (define (record-wrapped-type member)
           (define member-row
             (match member
               [`(Record ,row) row]
               [_ (reject s 'type-mismatch expected actual)]))
           (define residual (field-row-residual member-row expected-row))
           ;; Proof の型対に入れる W_k を Core の正規形へそろえる。
           (or (normalize-type `(Record ,(append expected-row residual)))
               (reject s 'type-mismatch expected actual)))
         (define branch-types
           (for/list ([branch (in-list branches)])
             (match-define (list member _name _alias) branch)
             (if (eq? member 'Never)
                 'Never
                 (record-wrapped-type member))))
         (define wrapped-types
           (filter (lambda (type) (not (eq? type 'Never))) branch-types))
         (define upper
           (if (null? wrapped-types)
               'Never
               (or (row005-join wrapped-types)
                   (reject s 'type-mismatch expected actual))))
         (values
          (eliminate
           (for/list ([branch (in-list branches)]
                      [wrapped-type (in-list branch-types)])
             (match-define (list member name alias) branch)
             (define ref (reference (or alias name)))
             (define consumed-ref
               (if (and alias (not entry?))
                   (consume-reference ref)
                   (reference name)))
             (define converted
               (if (eq? member 'Never)
                   consumed-ref
                     (let-values ([(member-core member-type)
                                   (discharge-remainder consumed-ref member
                                                       wrapped-type s
                                                       propositions)])
                     (define preserve-branch-residual?
                       (and (tag-compat? member-type expected context)
                            (match (owned-narrowing-kind
                                    member-type expected
                                    (lambda (a e)
                                      (type-compatible? a e propositions)))
                              [`(drop-obligation ,_ ,_) #t]
                              [_ #f])))
                     ;; OWN-004 は残余を除いた実型で再確認する。
                     (match (narrowing-kind member-type wrapped-type propositions)
                       ['ok (void)]
                       [`(drop-obligation ,_ ,_)
                        (reject s 'owned-narrowing-needs-proof wrapped-type
                                member-type)]
                       [_ (unless (mut-union-rebuildable?
                                   member-type wrapped-type context propositions)
                            (reject s 'owned-narrowing-rejected wrapped-type
                                    member-type))])
                     (let* ([source
                             (if (or (conversion-noop?
                                      member-type expected context propositions)
                                     preserve-branch-residual?)
                                 member-core
                                 (let-values ([(rebuilt _type)
                                               (convert member-core member-type
                                                        expected s propositions
                                                        #:entry? entry?
                                                        #:transfer transfer)])
                                   rebuilt))]
                            [wrapped
                             (wrap-reference
                              'let expected source
                              (and (not entry?)
                                   (resource-type? wrapped-type)))])
                       (let-values ([(wrapped-core wrapped-type-after)
                                     (discharge-remainder wrapped wrapped-type
                                                          upper s propositions)])
                         (match (narrowing-kind wrapped-type-after upper
                                                propositions)
                           ['ok (void)]
                           [`(drop-obligation ,_ ,_)
                            (reject s 'owned-narrowing-needs-proof upper
                                    wrapped-type-after)]
                           [_ (unless (mut-union-rebuildable?
                                       wrapped-type-after upper context propositions)
                                (reject s 'owned-narrowing-rejected upper
                                        wrapped-type-after))])
                         (if (type-equiv? wrapped-type-after upper)
                             wrapped-core
                             (let-values ([(rebuilt _type)
                                           (convert wrapped-core
                                            wrapped-type-after upper s
                                                    propositions #:entry? entry?
                                                    #:transfer transfer)])
                               rebuilt)))))))
             (resource-branch-body s member name alias converted)))
          upper)]
        [_
         (define bodies
           (for/list ([branch (in-list branches)])
             (match-define (list member name alias) branch)
             (define-values (body _type)
               (convert (if alias
                            (consume-reference (reference alias))
                            (reference name))
                        member expected s propositions #:entry? entry?
                        #:transfer transfer))
             (resource-branch-body s member name alias body)))
         ;; c2 spec §3。Union の成分は root が Owned でないので、root Owned の
         ;; expected への成分の convert は手前で落ち、ここへは届かない。
         (when (owned-type? expected)
           (reject s 'invalid-resolved-type expected))
         (define eliminated (eliminate bodies))
         ;; 非資源の adapter 結果は UnionEliminate 自体を T に保つ。
         (values
          (if (and (eq? transfer 'forward) (not (resource-type? expected)))
              eliminated
              (wrap-reference 'const expected eliminated
                              (and (not entry?) (resource-type? expected))))
          expected)]))

    ;; P2m2c spec §5.1。expected の欄ごとに作り直し、変換か印の変更が要る欄だけを
    ;; RecRewrite の entry にする。欄を物理的に落とさないので、出力の型は残余を保つ。
    (define (rebuild-record core actual-row expected-row s propositions
                            #:transfer [transfer 'move])
      (define context (initial-candidate-context propositions))
      (define (mismatch)
        (reject s 'type-mismatch `(Record ,expected-row) `(Record ,actual-row)))
      (define entries+types
        (for/list ([expected-field (in-list expected-row)])
          (match-define (list label expected-type expected-mark _ ...)
            expected-field)
          (define actual-field (assq label actual-row))
          (cond
            [(not actual-field)
             ;; expected だけの欄は optional のときに限り最後の tag-compat? が通す。
             #f]
            [else
             (match-define (list _ actual-type actual-mark actual-tail ...)
               actual-field)
             (when (and (eq? actual-mark 'imm) (eq? expected-mark 'mut))
               (mismatch))
             ;; VAR-003 の mut 欄の NFn 不変性を RecRewrite の entry でも保つ。
             (when (and (eq? actual-mark 'mut)
                        (eq? expected-mark 'mut)
                        (match actual-type [`(NFn ,_ ...) #t] [_ #f])
                        (match expected-type [`(NFn ,_ ...) #t] [_ #f])
                        (not (type-equiv? actual-type expected-type)))
               (mismatch))
             (define mark-changed? (not (eq? actual-mark expected-mark)))
             ;; entry を作る欄でだけ生名を取り、恒等の欄で counter を進めない。
             (define (identity-entry)
               (define binder (fresh-union-name))
               (list (list label binder actual-type expected-mark
                           actual-type `(#:var ,binder ,s))
                     (list* label actual-type expected-mark actual-tail)))
             (cond
               [(and (eq? actual-mark 'mut) (eq? expected-mark 'mut))
                (cond
                  [(type-equiv? actual-type expected-type) #f]
                  [(mut-union-retaggable? actual-type expected-type context
                                          propositions)
                   (define binder (fresh-union-name))
                   (define-values (body converted-type)
                     (parameterize
                         ([mut-field-adapter-forbidden? #t]
                          [mut-field-retagging? #t])
                       (convert `(#:var ,binder ,s) actual-type expected-type s
                                propositions #:entry? #t #:transfer transfer)))
                   (unless (type-equiv? converted-type expected-type)
                     (mismatch))
                   (list (list label binder actual-type expected-mark
                               converted-type body)
                         (list* label converted-type expected-mark
                                actual-tail))]
                  [else (mismatch)])]
               [(owned-type? actual-type)
                ;; T-RecRewrite は root Owned の欄を identity entry に限る。
                (unless (tag-compat? actual-type expected-type context)
                  (mismatch))
                (and mark-changed? (identity-entry))]
              [(conversion-noop? actual-type expected-type context
                                 propositions)
               (and mark-changed? (identity-entry))]
              [else
                (define binder (fresh-union-name))
                (define-values (body converted-type)
                  (parameterize
                      ([mut-field-adapter-forbidden?
                        (or (mut-field-adapter-forbidden?)
                            (and (eq? actual-mark 'mut)
                                 (eq? expected-mark 'mut)))])
                    (convert `(#:var ,binder ,s) actual-type expected-type s
                             propositions #:entry? #t #:transfer transfer)))
                (list (list label binder actual-type expected-mark
                            converted-type body)
                      (list* label converted-type expected-mark
                             actual-tail))])])))
      (define rewritten (filter values entries+types))
      (when (null? rewritten) (mismatch))
      (define output-row
        (for/list ([field (in-list actual-row)])
          (define hit (assq (first field) (map second rewritten)))
          (or hit field)))
      (define output-type (normalize-type `(Record ,output-row)))
      (unless (tag-compat? output-type `(Record ,expected-row) context)
        (mismatch))
      (values
       `(RecRewrite ,s ,core
          ,(for/list ([item (in-list rewritten)])
             (match-define (list label binder input-type mark output-type body)
               (first item))
             `((#:lbl ,label ,s) (#:bind ,binder ,s) (#:ty ,input-type ,s)
               ,mark (#:ty ,output-type ,s) ,body)))
       output-type))

    (define (fresh-names/all parameter-types reserved predicate)
      (let loop ([types parameter-types] [taken reserved] [acc '()])
        (cond
          [(null? types) (values (reverse acc) taken)]
          [(predicate (car types))
           (define name (fresh-owned-name taken))
           (loop (cdr types) (set-add taken name) (cons name acc))]
          [else (loop (cdr types) taken (cons #f acc))])))

    (define (fresh-resource-names/all parameter-types reserved)
      (fresh-names/all parameter-types reserved resource-type?))

    ;; 返り値は仮引数の位置と同じ長さの列であり、資源型でない位置には #f を
    ;; 置く。位置の対応を崩さないためである。
    (define (fresh-resource-names parameter-types reserved)
      (define-values (names _)
        (fresh-resource-names/all parameter-types reserved))
      names)

    ;; 関数位置の Owned<NFn ...> を一時的な place へ載せる。Core を再度
    ;; synth へ通すと同じ正規化が再発火するため、judgment だけを差し替える。
    (define (normalize-owned-function result function-span reserved)
      (define type (judgment-type result))
      (define core (judgment-core result))
      (define root (peel-node core))
      (cond
        [(not (owned-function-type? type)) (values result #f)]
        [(and (pair? root) (memq (car root) owned-function-roots))
         (values result #f)]
        [else
         (define name (fresh-owned-name reserved))
         (values
          (judgment `(Move ,function-span (#:var ,name ,function-span))
                    type
                    '(Own))
          (list name type function-span core (judgment-row result)))]))

    ;; 正規化した関数を Let へ閉じる。wrap が無い場合は元の judgment を返す。
    (define (close-owned-function wrap body-result)
      (cond
        [(not wrap) body-result]
        [else
         (match-define (list name type name-span bound-core bound-row) wrap)
         (judgment
          `(Let ,name-span
                ((#:bind ,name ,name-span) let (#:ty ,type ,name-span))
                ,bound-core
                ,(judgment-core body-result))
          (judgment-type body-result)
          (row-union bound-row (judgment-row body-result))
          (judgment-core-type body-result)
          (judgment-normal-type body-result))]))

    ;; 生名の binder は対応する仮引数の binder の span をそのまま持つ。
    ;; 名前だけを差し替えて位置は動かさない。G2+ は各仮引数へ
    ;; (#:bind x s_b) を要求するためである。
    (define (resource-parameter-binders parameter-binders raw-names)
      (for/list ([binder (in-list parameter-binders)]
                 [raw (in-list raw-names)])
        (if raw
            `(#:bind ,raw ,(wrapper-span binder))
            binder)))

    ;; 生成した Let の span は、対応する仮引数の binder の span で揃える。
    ;; この Let が仮引数の宣言そのものを Core へ写したものだからである。
    ;; binder は surface が書いた binder をそのまま使う。名前も span も
    ;; 仮引数の宣言と一致する。
    (define (wrap-resource-lets parameter-binders parameter-types raw-names core)
      (for/fold ([acc core])
                ([binder (in-list (reverse parameter-binders))]
                 [type (in-list (reverse parameter-types))]
                 [raw (in-list (reverse raw-names))])
        (if raw
            (let ([s_b (wrapper-span binder)])
              `(Let ,s_b (,binder let (#:ty ,type ,s_b))
                    (#:var ,raw ,s_b)
                    ,acc))
            acc)))

    ;; 捕捉した名前を Lam の生名へ載せ替える。捕捉元には surface の binder
    ;; が無いため、Let とその内部の包みには Fn 自身の span を使う。
    (define (wrap-capture-lets capture-names capture-types capture-raw-names
                               core span)
      (for/fold ([acc core])
                ([name (in-list (reverse capture-names))]
                 [type (in-list (reverse capture-types))]
                 [raw (in-list (reverse capture-raw-names))])
        `(Let ,span ((#:bind ,name ,span) let (#:ty ,type ,span))
              (#:var ,raw ,span)
              ,acc)))

    ;; 捕捉を Curry の固定引数へ変換し、各段の Owned な残余関数を place へ
    ;; 載せる。返り値の row には最終 Move の Own も含める。
    (define (wrap-captured-function captures capture-types
                                    lam-core lam-type span reserved)
      (define-values (place-names _unused-taken)
        (for/fold ([names '()] [taken reserved])
                  ([_capture (in-list captures)])
          (define name (fresh-owned-name taken))
          (values (cons name names) (set-add taken name))))
      (define places (reverse place-names))
      (define stages '())
      (define current-core lam-core)
      (define current-type lam-type)
      (define current-row '())
      (for ([capture (in-list captures)]
            [place (in-list places)]
            [capture-type (in-list capture-types)])
        (define signature
          (if (owned-type? current-type)
              (second current-type)
              current-type))
        (match signature
          [`(NFn (,first-type ,remaining-types ...)
                 ,return-type ,latent-in ,latent-out ,obligations ,origin)
           (unless (equal? first-type capture-type)
             (error 'wrap-captured-function
                    "捕捉型と Curry の先頭引数型が一致しない: ~s ~s"
                    capture-type first-type))
           (define argument-core
             `(#:var ,capture ,span))
           (define fixed-core
             (if (owned-type? capture-type)
                 `(OwnLeaf ,span (Move ,span ,argument-core))
                 `(Move ,span ,argument-core)))
           (define residual-origin
             `(Derived ,origin (Curry ,(erase-origin-core fixed-core))))
           (define residual
             `(NFn ,remaining-types ,return-type ,latent-in ,latent-out
                   ,obligations ,residual-origin))
           (define curry-core
             `(Curry ,span ,current-core
                     ,fixed-core))
           (set! stages
                 (cons (list place `(Owned ,residual) curry-core)
                       stages))
           (set! current-core `(Move ,span (#:var ,place ,span)))
           (set! current-type `(Owned ,residual))
           (set! current-row (row-union current-row '(Own)))]
          [_ (error 'wrap-captured-function
                   "捕捉の Curry 連鎖に非関数型を受けた: ~s"
                   current-type)]))
      (define nested
        (for/fold ([acc current-core])
                  ([stage (in-list stages)])
          (match-define (list place type bound) stage)
          `(Let ,span ((#:bind ,place ,span) let (#:ty ,type ,span))
                ,bound
                ,acc)))
      (judgment nested current-type current-row))

    (define (check-many expressions types environment delta propositions boundaries span)
      (unless (= (length expressions) (length types))
        (reject span 'arity-mismatch (length types) (length expressions)))
      (let loop ([items expressions]
                 [expected-types types]
                 [reachable? (current-escape-reachable?)]
                 [results '()])
        (if (null? items)
            (reverse results)
            (let ([result
                   (parameterize ([current-escape-reachable? reachable?])
                     (check (first items) (first expected-types)
                            environment delta propositions boundaries))])
              (loop (rest items) (rest expected-types)
                    (and reachable? (judgment-completes? result))
                    (cons result results))))))

    (define (elaborate-constructor constructor fields expected type-span
                                   environment delta propositions boundaries)
      (define schema (constructor-schema expected))
      (define field-types (and schema (lookup schema constructor)))
      (unless field-types
        (reject type-span 'constructor-type-mismatch expected constructor))
      (define results
        (check-many fields field-types
                    environment delta propositions boundaries type-span))
      ;; Owned な欄だけ producer の根として OwnLeaf で包む。包まない欄は
      ;; 型検査の gate が既定で拒否する。
      (define field-cores
        (for/list ([result (in-list results)]
                   [field-type (in-list field-types)])
          (if (owned-type? field-type)
              `(OwnLeaf ,type-span ,(judgment-core result))
              (judgment-core result))))
      (define result
        (judgment `(Construct ,type-span (#:ty ,expected ,type-span) ,constructor
                              ,@field-cores)
                  expected
                  (rows-union (map judgment-row results))
                  expected
                  expected))
      (propagate-context-never result results))

    (define (eliminate-front scrutinee branches eliminate-span
                             environment delta propositions boundaries
                             #:on-clause [on-clause void]
                             #:scrutinee-result [provided-scrutinee-result #f])
      (define scrutinee-result
        (or provided-scrutinee-result
            (synth scrutinee environment delta propositions boundaries)))
      ;; 包みは data 型を包むだけで構成子を変えない。typing.rkt と同じ表を引く。
      (define-values (data-type rewrap)
        (peel-eliminate-wrapper (type-for-context scrutinee-result)))
      (define schema-core (constructor-schema data-type))
      (unless schema-core
        (reject eliminate-span 'non-data-eliminate (judgment-type scrutinee-result)))
      (define schema
        (for/list ([row (in-list schema-core)])
          (list (first row) (map rewrap (second row)))))
      (define expected-constructors (map first schema))
      (define actual-constructors
        (for/list ([raw-branch (in-list branches)])
          (match (peel-branch raw-branch)
            [`(,constructor (,_ ...) -> ,_) constructor]
            [_ (reject eliminate-span 'invalid-branch raw-branch)])))
      (unless (and (= (length branches) (length schema))
                   (not (check-duplicates actual-constructors))
                   (andmap (lambda (constructor)
                             (member constructor actual-constructors))
                           expected-constructors))
        (reject eliminate-span 'non-exhaustive-eliminate actual-constructors))
      (define clauses
        (for/list ([raw-branch (in-list branches)])
          (match-define `(,constructor (,raw-parameters ...) -> ,body)
            (peel-branch raw-branch))
          (define parameters (map peel-bind raw-parameters))
          (define field-types (lookup schema constructor))
          (unless (and field-types
                       (= (length parameters) (length field-types))
                       (not (check-duplicates parameters)))
            (reject eliminate-span 'invalid-branch-binders raw-branch))
          (define-values (resource-names _reserved)
            (fresh-resource-names/all
             field-types
             (set-union (form-symbols raw-branch)
                        (list->set (map first environment)))))
          (define core-parameters
            (resource-parameter-binders raw-parameters resource-names))
          (define clause
            (list raw-branch constructor raw-parameters body
                  (extend environment parameters field-types #f
                          (map resource-type? field-types))
                  field-types resource-names core-parameters))
          ;; check-eliminate の互換な診断順を保つため、利用側の枝検査は
          ;; binder の検査直後、次の枝の binder 検査より前に呼ぶ。
          (parameterize
              ([current-escape-reachable?
                (and (current-escape-reachable?)
                     (judgment-completes? scrutinee-result))])
            (on-clause clause))
          clause))
      (values scrutinee-result clauses))

    (define (record-when-arm-fallthrough! span)
      (define fallthroughs (current-when-arm-fallthroughs))
      (unless (box? fallthroughs)
        (reject span 'invalid-syntax))
      (set-box! fallthroughs (append (unbox fallthroughs) (list span))))

    (define (deferred-when-fallthroughs expression)
      (match (current-deferred-when-fallthroughs)
        [(cons target fallthroughs)
         (and (eq? target expression) fallthroughs)]
        [_ #f]))

    (define (first-when-fallthrough spans)
      (first (sort spans < #:key third)))

    (define (finish-when-fallthroughs result spans result-type span deferred)
      (cond
        [(null? spans) result]
        [deferred
         (set-box! deferred (append (unbox deferred) spans))
         result]
        [(not (equal? (normalize-type result-type) 'Unit))
         (reject (first-when-fallthrough spans) 'when-arm-missing-return)]
        [else result]))

    ;; Surface から % 始まりは書けない。lowering の接頭辞を変えるときはここも更新する。
    (define (for-generated-name? name prefix)
      (and (symbol? name)
           (string-prefix? (symbol->string name) prefix)))

    (define (variable-reference-name expression)
      (match expression
        [`(#:var ,name ,_) name]
        [`(Move ,_ (#:var ,name ,_)) name]
        [_ #f]))

    ;; 生成 for の資源 head だけ、本体の scope を再帰 Apply の外へ切り出す。
    (define (scope-generated-for-branch clause branch-core)
      (define loop-name (current-generated-for-loop))
      (match clause
        [(list raw-branch 'cons (list raw-head raw-tail) _body _environment
               (list head-type _tail-type) _resource-names _core-parameters)
         (define shape
           (match (peel-branch raw-branch)
             [(list 'cons (list _ _) '->
                    (list 'Let _
                          (list (list '#:bind statement _) 'const
                                (list '#:ty 'Unit _))
                          _bound
                          (list 'Apply _ (list '#:var callee _) argument)))
              (and loop-name
                   (for-generated-name? loop-name "%for-loop")
                   (resource-type? head-type)
                   (for-generated-name? statement "%stmt")
                   (eq? callee loop-name)
                   (for-generated-name? (variable-reference-name argument)
                                        "%for-tail")
                   (eq? (variable-reference-name argument)
                        (peel-bind raw-tail))
                   statement)]
             [_ #f]))
         (if (not shape)
             branch-core
             (match branch-core
               [`(Let ,statement-span
                      ((#:bind ,core-statement ,binder-span)
                       const (#:ty Unit ,unit-span))
                      ,body
                      ,continuation)
                #:when (and (eq? core-statement shape)
                            (match continuation
                              [`(Apply ,_ (#:var ,callee ,_) ,argument)
                               (and (eq? callee loop-name)
                                    (eq? (variable-reference-name argument)
                                         (peel-bind raw-tail)))]
                              [_ #f]))
                (define head-name (peel-bind raw-head))
                (define element-name
                  (fresh-owned-name
                   (set-union (form-symbols branch-core)
                              (set head-name (peel-bind raw-tail) loop-name))))
                (define element-span (wrapper-span raw-head))
                `(Let ,statement-span
                      ((#:bind ,core-statement ,binder-span)
                       const (#:ty Unit ,unit-span))
                      (Scope ,element-span ()
                        (Let ,element-span
                             ((#:bind ,element-name ,element-span)
                              let (#:ty ,head-type ,element-span))
                             (Move ,element-span
                                   (#:var ,head-name ,element-span))
                             ,(span-rename body head-name element-name)))
                      ,continuation)]
               [_ branch-core]))]
        [_ branch-core]))

    (define (union-eliminate scrutinee-result branches expected eliminate-span
                             environment delta propositions boundaries
                             #:defer-fallthroughs [deferred #f])
      (define entry-flow (flow-snapshot))
      (define union-type
        (match (normalize-type (type-for-context scrutinee-result))
          [`(Owned ,inner) inner]
          [type type]))
      (define members (union-members union-type))
      (define (pattern raw-branch)
        (match (peel-branch raw-branch)
          [(list (and raw-type (list '#:ty τ _))
                 (and raw-binder (list '#:bind _ _)) '-> body)
           (list 'member (normalize-type τ) raw-type raw-binder body raw-branch)]
          [(list constructor (list raw-parameters ...) '-> body)
           (list 'constructor constructor raw-parameters body raw-branch)]
          [_ (reject eliminate-span 'invalid-branch raw-branch)]))
      (define patterns (map pattern branches))
      (define assigned (make-hash))
      (for ([member-type (in-list members)])
        (hash-set! assigned member-type '()))
      (for ([item (in-list patterns)])
        (match item
          [(list 'member τ _ _ _ raw-branch)
           (define matches
             (filter (lambda (member-type)
                       (and τ (type-equiv? τ member-type)))
                     members))
           (unless (= (length matches) 1)
             (reject eliminate-span 'non-exhaustive-eliminate raw-branch))
           (define member-type (first matches))
           (hash-set! assigned member-type
                      (append (hash-ref assigned member-type) (list item)))]
          [(list 'constructor constructor _ _ raw-branch)
           (define matches
             (for/list ([member-type (in-list members)]
                        #:when (and (constructor-schema member-type)
                                    (assoc constructor
                                           (constructor-schema member-type))))
               member-type))
           (unless (= (length matches) 1)
             (reject eliminate-span 'non-exhaustive-eliminate raw-branch))
           (define member-type (first matches))
           (hash-set! assigned member-type
                      (append (hash-ref assigned member-type) (list item)))]))
      (define groups
        (for/list ([member-type (in-list members)])
          (define group (hash-ref assigned member-type))
          (define member-patterns
            (filter (lambda (item) (eq? (first item) 'member)) group))
          (define constructor-patterns
            (filter (lambda (item) (eq? (first item) 'constructor)) group))
          (define schema (constructor-schema member-type))
          (define expected-constructors (and schema (map first schema)))
          (define actual-constructors (map second constructor-patterns))
          (unless
              (or (and (= (length member-patterns) 1)
                       (null? constructor-patterns))
                  (and schema
                       (null? member-patterns)
                       (= (length actual-constructors)
                          (length expected-constructors))
                       (not (check-duplicates actual-constructors))
                       (andmap (lambda (constructor)
                                 (and (memq constructor actual-constructors) #t))
                               expected-constructors)))
            (reject eliminate-span 'non-exhaustive-eliminate group))
          (list member-type (if (pair? member-patterns)
                                (first member-patterns)
                                constructor-patterns))))
      (define fallthroughs (box '()))
      (define branch-work
        (parameterize ([current-when-arm-fallthroughs fallthroughs])
          (for/list ([group (in-list groups)])
          (match-define (list member-type branch-group) group)
          (define member-pattern? (eq? (first branch-group) 'member))
          (define source-binder-node
            (and member-pattern? (fourth branch-group)))
          (define source-binder
            (and source-binder-node (peel-bind source-binder-node)))
          (define resource-member? (resource-type? member-type))
          (define binder
            (if (and member-pattern? (not resource-member?))
                source-binder
                (fresh-union-name)))
          (define alias-span
            (if source-binder-node
                (wrapper-span source-binder-node)
                eliminate-span))
          (define alias
            (and resource-member?
                 (or source-binder
                     (fresh-owned-name (set-add union-reserved binder)))))
          (define body-binder (or alias binder))
          (define branch-environment
            (extend environment (list body-binder) (list member-type) #f
                    (list resource-member?)))
          (define body-expression
            (if member-pattern?
                (fifth branch-group)
                `(Eliminate ,eliminate-span
                            ,(if resource-member?
                                 `(Move ,eliminate-span
                                        (#:var ,body-binder ,eliminate-span))
                                 `(#:var ,body-binder ,eliminate-span))
                            ,(map fifth branch-group))))
          (define body-deferred
            (and (not member-pattern?)
                 (match (peel-node body-expression)
                   [`(Eliminate ,_ ,_) #t]
                   [_ #f])
                 (box '())))
          (define body-result
            (begin
              (flow-restore! entry-flow)
              (parameterize
                  ([current-escape-reachable?
                    (and (current-escape-reachable?)
                         (judgment-completes? scrutinee-result))]
                   [current-deferred-when-fallthroughs
                    (and body-deferred
                         (cons body-expression body-deferred))])
                (if expected
                    (check body-expression expected branch-environment
                           delta propositions boundaries)
                    (synth body-expression branch-environment
                           delta propositions boundaries)))))
          (when body-deferred
            (set-box! fallthroughs
                      (append (unbox fallthroughs) (unbox body-deferred))))
          (define encoded-body
            (resource-branch-body eliminate-span member-type binder alias
                                  (judgment-core body-result) alias-span))
          (define branch
            (if member-pattern?
                (let ([raw-branch (sixth branch-group)])
                  (match (peel-branch raw-branch)
                    [(list raw-type raw-binder '-> _)
                     (list (branch-span raw-branch)
                           raw-type
                           (if resource-member?
                               `(#:bind ,binder ,eliminate-span)
                               raw-binder)
                           '-> encoded-body)]))
                `(,eliminate-span
                  (#:ty ,member-type ,eliminate-span)
                  (#:bind ,binder ,eliminate-span)
                  -> ,encoded-body)))
          (list branch
                (flow-branch
                 branch-environment
                 (judgment encoded-body
                           (judgment-type body-result)
                           (judgment-row body-result)
                           (judgment-core-type body-result)
                           (judgment-normal-type body-result))
                 (flow-snapshot) #f)))))
      (define-values (branch-results _joined-flow)
        (join-branch-flows
         eliminate-span environment entry-flow (map second branch-work)
         propositions
         #:reachable? (judgment-completes? scrutinee-result)))
      (define results
        (for/list ([item (in-list branch-work)]
                   [branch-result (in-list branch-results)])
          (list (first item) branch-result)))
      (define-values (branch-cores core-type)
        (merge-branches (map judgment-core branch-results)
                        (map judgment-core-type branch-results)
                        eliminate-span propositions))
      (define result
        (judgment
       `(UnionEliminate ,eliminate-span
                        ,(judgment-core scrutinee-result)
                        ,(for/list ([result (in-list results)]
                                    [branch-core (in-list branch-cores)])
                           (define branch (first result))
                           (append (take branch 4) (list branch-core))))
       (if (or (eq? (judgment-type scrutinee-result) 'Never)
               (eq? core-type 'Never))
           'Never
           (or expected core-type))
       (rows-union
        (cons (judgment-row scrutinee-result)
              (map judgment-row branch-results)))
       (if (eq? (judgment-type scrutinee-result) 'Never)
           'Never
           core-type)
       (default-normal-type core-type)))
      (finish-when-fallthroughs result (unbox fallthroughs)
                                (or expected (judgment-type result))
                                eliminate-span deferred))

    (define (member-pattern? raw-branch)
      (match (peel-branch raw-branch)
        [(list (list '#:ty _ _) (list '#:bind _ _) '-> _) #t]
        [_ #f]))

    (define (root-owned-union? type)
      (match (normalize-type type)
        [`(Owned (Union ,_ ,_)) #t]
        [_ #f]))

    (define (union-type? type)
      (match (normalize-type type)
        [`(Union ,_ ,_) #t]
        [_ #f]))

    (define (check-eliminate scrutinee branches expected eliminate-span
                             environment delta propositions boundaries
                             #:scrutinee-result [provided-scrutinee-result #f]
                             #:defer-fallthroughs [deferred #f])
      (define entry-flow #f)
      (define reversed-branch-results '())
      (define fallthroughs (box '()))
      (define-values (scrutinee-result clauses)
        (parameterize ([current-when-arm-fallthroughs fallthroughs])
          (eliminate-front
           scrutinee branches eliminate-span environment delta propositions boundaries
           #:scrutinee-result provided-scrutinee-result
           #:on-clause
           (lambda (clause)
             (match-define (list _ _ _ body branch-environment _ _ _) clause)
             (unless entry-flow (set! entry-flow (flow-snapshot)))
             (flow-restore! entry-flow)
             (define result
               (check body expected branch-environment
                      delta propositions boundaries))
             (set! reversed-branch-results
                   (cons (flow-branch branch-environment result
                                      (flow-snapshot) #f)
                         reversed-branch-results))))))
      (unless entry-flow (set! entry-flow (flow-snapshot)))
      (define-values (joined-results _joined-flow)
        (join-branch-flows
         eliminate-span environment entry-flow
         (reverse reversed-branch-results)
         propositions
         #:reachable?
         (judgment-completes? (or provided-scrutinee-result
                                  scrutinee-result))))
      (define branch-results
        (for/list ([result (in-list joined-results)])
          (list (judgment-core result)
                (judgment-row result)
                (judgment-core-type result))))
      (define-values (rebuilt-branch-cores core-type)
        (merge-branches (map first branch-results)
                        (map third branch-results)
                        eliminate-span propositions))
      (define result
        (judgment
       `(Eliminate ,eliminate-span
                   ,(judgment-core scrutinee-result)
                   ,(for/list ([clause (in-list clauses)]
                               [result (in-list branch-results)]
                               [branch-core (in-list rebuilt-branch-cores)])
                      (match-define
                        (list raw-branch constructor raw-parameters _ _ field-types
                              resource-names core-parameters)
                        clause)
                      (define scoped-for-core
                        (scope-generated-for-branch clause branch-core))
                      (define core
                        (if (ormap values resource-names)
                            `(Scope ,eliminate-span ()
                                    ,(wrap-resource-lets
                                      raw-parameters field-types resource-names
                                      scoped-for-core))
                            scoped-for-core))
                      `(,(branch-span raw-branch) ,constructor ,core-parameters
                        -> ,core)))
       (if (or (eq? (judgment-type scrutinee-result) 'Never)
               (eq? core-type 'Never))
           'Never
           expected)
       (rows-union
        (cons (judgment-row scrutinee-result)
              (map second branch-results)))
       (if (eq? (judgment-type scrutinee-result) 'Never)
           'Never
           core-type)
       (default-normal-type core-type)))
      (finish-when-fallthroughs result (unbox fallthroughs) expected
                                eliminate-span deferred))

    (define (synth-eliminate scrutinee-result branches eliminate-span
                             environment delta propositions boundaries
                             #:defer-fallthroughs [deferred #f])
      (define entry-flow (flow-snapshot))
      (define scrutinee-type (type-for-context scrutinee-result))
      (cond
        [(or (root-owned-union? scrutinee-type)
             (union-type? scrutinee-type))
         (union-eliminate scrutinee-result branches #f eliminate-span
                          environment delta propositions boundaries
                          #:defer-fallthroughs deferred)]
        [(ormap member-pattern? branches)
         (reject eliminate-span 'non-union-eliminate
                 #:phase 'typing scrutinee-type)]
        [else
         (define-values (data-type _rewrap)
           (peel-eliminate-wrapper scrutinee-type))
         (unless (constructor-schema data-type)
           (reject eliminate-span 'non-data-eliminate scrutinee-type))
         (define fallthroughs (box '()))
         (define result
           (parameterize ([current-when-arm-fallthroughs fallthroughs])
             (define-values (checked-scrutinee clauses)
               (eliminate-front
                (judgment-core scrutinee-result) branches eliminate-span
                environment delta propositions boundaries
                #:scrutinee-result scrutinee-result))
             (for ([raw-branch (in-list branches)])
               (match (peel-branch raw-branch)
                 [`(,_ (,_ ...) -> ,body)
                  #:when (branch-needs-expected-type? body)
                  (reject eliminate-span 'eliminate-needs-expected-type)]
                 [_ (void)]))
             (define flow-branches
               (for/list ([clause (in-list clauses)])
                 (flow-restore! entry-flow)
                 (match-define
                   (list _ _ _ body branch-environment _ _ _) clause)
                 (define branch-result
                   (parameterize
                       ([current-escape-reachable?
                         (and (current-escape-reachable?)
                              (judgment-completes? scrutinee-result))])
                     (synth body branch-environment delta propositions boundaries)))
                 (flow-branch branch-environment branch-result (flow-snapshot)
                              #f)))
             (define-values (results _joined-flow)
               (join-branch-flows
                eliminate-span environment entry-flow flow-branches
                propositions
                #:reachable? (judgment-completes? scrutinee-result)))
             (define-values (branch-cores core-type)
               (merge-branches (map judgment-core results)
                               (map judgment-core-type results)
                               eliminate-span propositions))
             (judgment
             `(Eliminate ,eliminate-span ,(judgment-core checked-scrutinee)
                      ,(for/list ([clause (in-list clauses)]
                                  [core (in-list branch-cores)])
                         (match-define
                           (list raw-branch constructor raw-parameters _ _
                                 field-types resource-names core-parameters)
                           clause)
                         (define scoped-for-core
                           (scope-generated-for-branch clause core))
                         (define wrapped-core
                           (if (ormap values resource-names)
                               `(Scope ,eliminate-span ()
                                       ,(wrap-resource-lets
                                         raw-parameters field-types
                                         resource-names scoped-for-core))
                               scoped-for-core))
                         `(,(branch-span raw-branch) ,constructor
                           ,core-parameters -> ,wrapped-core)))
          (if (eq? (judgment-type scrutinee-result) 'Never)
              'Never
              core-type)
          (rows-union
           (cons (judgment-row checked-scrutinee)
                 (map judgment-row results)))
          core-type
          (default-normal-type core-type))))
         (finish-when-fallthroughs result (unbox fallthroughs)
                                   (judgment-type result) eliminate-span
                                   deferred)]))

    (define (try-bind-kind type)
      (match (normalize-type type)
        [`(Option ,_) 'option]
        [`(Result ,_ ,_) 'result]
        [_ #f]))

    (define (try-bind-boundary s-bind kind data-type right-type boundaries)
      (match (nearest-function-boundary boundaries)
        [#f (reject s-bind 'return-outside-boundary)]
        [`(,_ ,_ #:infer ,_)
         (reject s-bind 'return-type-not-inferable)]
        [(list _ _ (list '#:probe _) _ _adapter ...) (void)]
        [(list _ _ boundary-type boundary-s _adapter ...)
         (define compatible?
           (match* (kind boundary-type data-type)
             [('option `(Option ,_) `(Option ,_)) #t]
             [('result `(Result ,_ ,boundary-error)
                       `(Result ,_ ,right-error))
              (type-equiv? boundary-error right-error)]
             [(_ _ _) #f]))
         (unless compatible?
           (reject s-bind 'try-bind-boundary-mismatch
                   #:related (list (list 'return-boundary boundary-s
                                         "失敗を受ける境界"))
                   boundary-type right-type))]))

    (define (try-bind-branches s x s_x body data-type kind)
      (match kind
        ['option
         (list
          `(,s some ((#:bind ,x ,s_x)) -> ,body)
          `(,s none () ->
            ,(failure-return s `(Construct ,s none))))]
        ['result
         (define error-type (third data-type))
         (define error-binder (fresh-union-name))
         (define error-value
           (if (resource-type? error-type)
               `(Move ,s (#:var ,error-binder ,s))
               `(#:var ,error-binder ,s)))
         (list
          `(,s ok ((#:bind ,x ,s_x)) -> ,body)
          `(,s ng ((#:bind ,error-binder ,s)) ->
            ,(failure-return s `(Construct ,s ng ,error-value))))]))

    (define (elaborate-try-bind s name name-span right right-result body
                                expected environment delta propositions
                                boundaries)
      (define right-never?
        (eq? (judgment-type right-result) 'Never))
      (define right-normal-type (type-for-context right-result))
      (cond
        [(and right-never? (eq? right-normal-type 'Never))
         (define body-environment
           (extend environment (list name) '(Never) #f '(#f)))
         (define body-result
           (parameterize ([current-escape-reachable? #f])
             (if expected
                 (check-never-bound-body body expected body-environment delta
                                         propositions boundaries)
                 (synth body body-environment delta propositions boundaries))))
         (define result
           (judgment
            `(Let ,s ((#:bind ,name ,name-span) const (#:ty Never ,name-span))
                  ,(judgment-core right-result) ,(judgment-core body-result))
            'Never
            (row-union (judgment-row right-result) (judgment-row body-result))
            'Never
            (if (eq? (judgment-type body-result) 'Never)
                '⊥
                (judgment-normal-type body-result))))
         (if expected
             (check-against-expected result expected s propositions)
             result)]
        [else
         (define-values (data-type _rewrap)
           (peel-eliminate-wrapper right-normal-type))
         (define kind (try-bind-kind data-type))
         (unless kind
           (reject (span-of right) 'try-bind-non-adt right-normal-type))
         (define bind-span (span-hull name-span (span-of right)))
         (try-bind-boundary bind-span kind data-type right-normal-type boundaries)
         (define branches
           (try-bind-branches s name name-span body data-type kind))
         (define result
           (if expected
               (check-eliminate right branches expected s environment delta
                                propositions boundaries
                                #:scrutinee-result right-result)
               (synth-eliminate right-result branches s environment delta
                                propositions boundaries)))
         (if right-never?
             ;; Never の RHS では枝を検査するが、Core に残すと実行不能な枝の
             ;; dead Return が payload 値へ消えた後も、末尾 Unit が型付けされる。
             (judgment (judgment-core right-result) 'Never
                       (judgment-row result) 'Never
                       (judgment-normal-type result))
             result)]))

    ;; SUR-012。UCore+ の型欄が省略の標識かを返す。
    (define (inferred? type)
      (match type [`(#:infer ,_) #t] [_ #f]))

    ;; SUR-003。UCore+ の row 欄が省略の標識かを返す。
    (define (inferred-row? raw-row)
      (eq? (peel-ef raw-row) '#:infer))

    ;; SUR-012 / SUR-003 / P2l2b2。注釈付き Let の宣言型を期待型に使う形である。
    (define (needs-expected-type? expression #:if-some? [if-some? #f])
      (match (peel-node expression)
        [`(Fn ((,_ ,parameter-types) ...) ,_ ,raw-row ,_)
         (or (ormap inferred? parameter-types)
             (inferred-row? raw-row))]
        [`(Construct ,_ (Types ,_ ...) ,_ ...) #f]
        [`(Construct ,_ ,_ ...) #t]
        ;; P2m spec §7.2。Eliminate は結果型の期待型を必要とする。
        [`(Eliminate ,_ ,_) #t]
        [`(IfSome ,_ ,_) if-some?]
        ;; Surface block は Let の列なので、末尾まで期待型の必要性を伝える。
        [`(Let ,_ ,_ ,body) (needs-expected-type? body #:if-some? if-some?)]
        [`(NarrativeExpr ,body) (needs-expected-type? body #:if-some? if-some?)]
        [_ #f]))

    ;; 注釈付き let と Reassign は同じ期待型依存の RHS を check する。
    (define (expected-type-checkable? expression expected)
      (or (needs-expected-type? expression #:if-some? #t)
          (match* ((peel-node expression) expected)
            [(`(Rec (,fields ...)) `(Record ,row))
             ;; 空リストも有効な Rec なので、欄ごとの check を内側へ伝える。
             (list? (omitted-optional-labels
                     (map (lambda (field) (peel-lbl (first field))) fields)
                     row))]
            [(_ _) #f])))

    ;; SUR-014。data の合成位置の事前検査だけが使う。入れ子の Eliminate は枝の結果位置を見る。
    (define (branch-needs-expected-type? expression)
      (match (peel-node expression)
        [`(Eliminate ,_ (,branches ...))
         (for/or ([branch (in-list branches)])
           (branch-needs-expected-type? (last (peel-branch branch))))]
        [`(Let ,_ ,_ ,body) (branch-needs-expected-type? body)]
        [`(NarrativeExpr ,body) (branch-needs-expected-type? body)]
        [_ (needs-expected-type? expression)]))

    (define (prepare-fn s parameter-binders raw-parameter-types body
                        environment delta
                        #:expected-parameter-types
                        [expected-parameter-types #f])
      (define parameters (map peel-bind parameter-binders))
      (when (check-duplicates parameters)
        (reject s 'duplicate-parameter parameters))
      (define parameter-types
        (for/list ([raw (in-list raw-parameter-types)]
                   [i (in-naturals)])
          (if (inferred? raw)
              (list-ref expected-parameter-types i)
              (resolve-annotation raw delta s))))
      (define captures (owned-captures body parameters environment))
      (define capture-types
        (for/list ([name (in-list captures)])
          (lookup environment name)))
      (for ([name (in-list captures)] [type (in-list capture-types)])
        (when (and (resource-type? type)
                   (not (owned-type? type))
                   (not (place-binding? environment name)))
          ;; 集約資源型を Move できるのは P の place だけである。
          ;; 仮引数など place でない資源型の捕捉は Curry 化する前に拒否し、
          ;; Core の Move と同じ診断 key を保つ。
          (reject s 'move-non-owned name)))
      (values parameters parameter-types captures capture-types))

    (define (prepare-fn-binders s parameter-binders parameters parameter-types
                                captures capture-types body environment)
      (define reserved
        (set-union (form-symbols body)
                   (list->set parameters)
                   (list->set (map first environment))))
      (define-values (capture-raw-names reserved-with-captures)
        (fresh-resource-names/all capture-types reserved))
      (define-values (raw-names reserved-with-formals)
        (fresh-resource-names/all parameter-types reserved-with-captures))
      (define capture-binders
        (for/list ([raw (in-list capture-raw-names)])
          `(#:bind ,raw ,s)))
      (define core-binders
        (resource-parameter-binders parameter-binders raw-names))
      (values capture-raw-names raw-names capture-binders core-binders
              reserved-with-formals))

    (define (check-function-body-row s body-result return-type boundary
                                     declared-row)
      (define own-return `((Return ,boundary ,return-type)))
      (define residual-row
        (row-difference (judgment-row body-result) own-return))
      (unless (row-subset? residual-row declared-row)
        (reject s 'undeclared-function-effect declared-row residual-row)))

    (define (block-body? body)
      (match body [`(BlockBody ,_ ,_) #t] [_ #f]))

    (define (block-body-span body)
      (match body
        [`(BlockBody ,span ,_) span]
        [_ (error 'block-body-span "BlockBody が必要である: ~s" body)]))

    (define (without-block-fallthrough result)
      (if (eq? (judgment-type result) 'Never)
          (judgment (judgment-core result) 'Never (judgment-row result)
                    (judgment-core-type result) '⊥)
          result))

    (define (require-when-arm-body close-span)
      (unless (box? (current-when-arm-fallthroughs))
        (reject close-span 'invalid-syntax)))

    (define (synth-when-arm-block-body close-span inner environment delta
                                      propositions boundaries)
      (require-when-arm-body close-span)
      (define result
        (synth inner environment delta propositions boundaries))
      (cond
        [(eq? (judgment-type result) 'Never)
         (without-block-fallthrough result)]
        [else
         (unless (eq? (judgment-type result) 'Unit)
           (reject close-span 'invalid-syntax))
         (record-when-arm-fallthrough! close-span)
         result]))

    (define (check-when-arm-block-body close-span inner expected environment
                                       delta propositions boundaries)
      (require-when-arm-body close-span)
      (define result
        (check inner 'Unit environment delta propositions boundaries))
      (cond
        [(eq? (judgment-type result) 'Never)
         (without-block-fallthrough result)]
        [else
         (unless (eq? (judgment-type result) 'Unit)
           (reject close-span 'invalid-syntax))
         (record-when-arm-fallthrough! close-span)
         (if (equal? (normalize-type expected) 'Unit)
             result
             (judgment (judgment-core result) expected
                       (judgment-row result) expected expected))]))

    (define (check-function-body body return-type return-span
                                 environment delta propositions boundaries)
      (match body
        [`(BlockBody ,block-span ,inner)
         (if (equal? (normalize-type return-type) 'Unit)
             (check inner return-type environment delta propositions boundaries)
             (let ([result (synth inner environment delta propositions boundaries)])
               (unless (eq? (judgment-type result) 'Never)
                 (reject block-span 'function-body-missing-return
                         #:related
                         (if return-span
                             (list (list 'return-type-annotation return-span
                                         "戻り型の注釈"))
                             '())))
               result))]
        [_ (check body return-type environment delta propositions boundaries)]))

    (define (probe-block-return span body environment delta propositions
                                boundaries)
      (match body
        [`(BlockBody ,_ ,inner)
         (call-with-restored-state
          (λ ()
            (define candidates (box '()))
            (define boundary (fresh-boundary))
            (define failure #f)
            (define result
              (with-handlers ([exn:fail:elab?
                               (λ (error) (set! failure error) #f)])
                (synth inner environment delta propositions
                       (cons `(FunctionBoundary ,boundary
                                                (#:probe ,candidates) ,span)
                             boundaries))))
            (values result (unbox candidates) failure)))]
        [_ (error 'probe-block-return "BlockBody が必要である: ~s" body)]))

    (define (infer-block-return-type span body environment delta propositions
                                     boundaries)
      (define block-span (block-body-span body))
      (define-values (result candidates failure)
        (probe-block-return span body environment delta propositions boundaries))
      (cond
        [(and result (eq? (judgment-type result) 'Never))
         (if (pair? candidates)
             (let-values ([(type _record-join?)
                           (merge-branch-types candidates span)])
               type)
             (reject span 'return-type-not-inferable))]
        [(and result (eq? (judgment-type result) 'Unit))
         (when (ormap (λ (candidate) (not (equal? candidate 'Unit))) candidates)
           (reject block-span 'function-body-missing-return))
         'Unit]
        [result (reject block-span 'function-body-missing-return)]
        [(pair? candidates) (first candidates)]
        [failure (raise failure)]
        [else (reject span 'return-type-not-inferable)]))

    (define (row-member-return? row boundary)
      (for/or ([label (in-list row)])
        (match label
          [`(Return ,candidate ,_) (equal? candidate boundary)]
          [_ #f])))

    (define (finish-fn s parameter-binders parameter-types
                       captures capture-types capture-raw-names raw-names
                       capture-binders core-binders
                       return-type boundary body-result
                       signature callable reserved-with-formals)
      (define lam-core
        `(Lam ,s User ,callable
              ,(append capture-binders core-binders)
              (Handle ,s (Return ,boundary (#:ty ,return-type ,s))
                      (,s (#:bind return-value ,s) ->
                          (#:var return-value ,s))
                      (Scope ,s ()
                             ,(wrap-capture-lets
                               captures capture-types capture-raw-names
                               (wrap-resource-lets
                                parameter-binders parameter-types raw-names
                                (judgment-core body-result))
                               s)))))
      (if (null? captures)
          (judgment lam-core signature '())
          (wrap-captured-function
           captures capture-types
           lam-core signature s reserved-with-formals)))

    ;; 注釈付き Fn の共通経路。resolve-return は現在の resolve-annotation の
    ;; 位置で呼び、診断の優先順位を変えない。
    (define (elaborate-annotated-fn s parameter-binders raw-parameter-types
                                   resolve-return raw-row body
                                   environment delta propositions boundaries
                                   #:expected-parameter-types
                                   [expected-parameter-types #f]
                                   #:inherited-row
                                   [inherited-row #f]
                                   #:return-span [return-span #f])
      (define-values (parameters parameter-types captures capture-types)
        (prepare-fn s parameter-binders raw-parameter-types body
                    environment delta
                    #:expected-parameter-types expected-parameter-types))
      (define _capture-flow-pin
        (flow-pin-captures! body parameters environment))
      (define return-type (resolve-return))
      (define declared-row
        (or inherited-row
            (resolve-declaration-row raw-row delta boundaries s)))
      (define boundary (fresh-boundary))
      (define-values (capture-raw-names raw-names capture-binders core-binders
                                        reserved-with-formals)
        (prepare-fn-binders s parameter-binders parameters parameter-types
                            captures capture-types body environment))
      (define signature
        `(NFn ,(append capture-types parameter-types)
             ,return-type () ,declared-row () User))
      (define callable (fresh-callable signature))
      (define body-result
        (parameterize ([current-escape-reachable? #t])
          (call-with-flow-rollback
           (λ ()
             (check-function-body
              body return-type return-span
              (extend environment parameters parameter-types #f
                      (map resource-type? parameter-types))
              delta propositions
              (cons `(FunctionBoundary ,boundary ,return-type ,s) boundaries))))))
      (check-function-body-row s body-result return-type boundary declared-row)
      (finish-fn s parameter-binders parameter-types
                 captures capture-types capture-raw-names raw-names
                 capture-binders core-binders
                 return-type boundary body-result
                 signature callable reserved-with-formals))

    (define (elaboration-state)
      (list boundary-counter callable-counter owned-counter union-counter
            reversed-callables))
    (define (restore-elaboration-state! saved)
      (set! boundary-counter (first saved))
      (set! callable-counter (second saved))
      (set! owned-counter (third saved))
      (set! union-counter (fourth saved))
      (set! reversed-callables (fifth saved)))

    ;; 下見で消費した fresh 名と callable 表を本検査へ漏らさない。
    (define (call-with-restored-state thunk)
      (define saved (elaboration-state))
      (dynamic-wind
       void
       (λ ()
         (parameterize ([current-loop-trial-catching? #f])
           (call-with-flow-rollback thunk)))
       (λ () (restore-elaboration-state! saved))))

    (define (probe-candidate-boxes boundaries)
      (for/fold ([boxes '()]) ([boundary (in-list boundaries)])
        (match boundary
          [(list _ _ (list '#:probe candidate-box probe-state-boxes ...)
                 _ _adapter ...)
           (for/fold ([boxes boxes])
                     ([candidate-box (in-list (cons candidate-box
                                                    probe-state-boxes))])
             (if (and (box? candidate-box)
                      (not (memq candidate-box boxes)))
                 (cons candidate-box boxes)
                 boxes))]
          [_ boxes])))

    (define (call-with-loop-trial-catch boundaries thunk on-catch)
      (if (not (current-loop-trial-catching?))
          (thunk)
          (let* ([saved-flow (flow-snapshot)]
                 [saved-escapes (boundary-escape-snapshot)]
                 [deferred (current-deferred-when-fallthroughs)]
                 [boxes
                  (remove-duplicates
                   (append
                    (probe-candidate-boxes boundaries)
                    (if (box? (current-when-arm-fallthroughs))
                        (list (current-when-arm-fallthroughs))
                        '())
                    (if (and (pair? deferred) (box? (cdr deferred)))
                        (list (cdr deferred))
                        '()))
                   eq?)]
                 [saved-boxes
                  (for/list ([candidate-box (in-list boxes)])
                    (list candidate-box (unbox candidate-box)))]
                 [failure-returns (current-failure-returns)]
                 [saved-failure-returns (set->list failure-returns)])
            (with-handlers
                ([exn:fail:elab?
                  (λ (_)
                    (flow-restore! saved-flow)
                    (boundary-escape-restore! saved-escapes)
                    (for ([saved-box (in-list saved-boxes)])
                      (set-box! (first saved-box) (second saved-box)))
                    (for ([returned (in-list (set->list failure-returns))])
                      (set-remove! failure-returns returned))
                    (for ([returned (in-list saved-failure-returns)])
                      (set-add! failure-returns returned))
                    (on-catch))])
              (thunk)))))

    (define (call-with-loop-trial-rollback boundaries thunk)
      (define saved-state (elaboration-state))
      (define saved-flow (flow-snapshot))
      (define saved-escapes (boundary-escape-snapshot))
      (define deferred (current-deferred-when-fallthroughs))
      (define boxes
        (remove-duplicates
         (append (probe-candidate-boxes boundaries)
                 (if (box? (current-when-arm-fallthroughs))
                     (list (current-when-arm-fallthroughs))
                     '())
                 (if (and (pair? deferred) (box? (cdr deferred)))
                     (list (cdr deferred))
                     '()))
         eq?))
      (define saved-boxes
        (for/list ([candidate-box (in-list boxes)])
          (list candidate-box (unbox candidate-box))))
      (define failure-returns (current-failure-returns))
      (define saved-failure-returns (set->list failure-returns))
      (dynamic-wind
       void thunk
       (λ ()
         (restore-elaboration-state! saved-state)
         (flow-restore! saved-flow)
         (boundary-escape-restore! saved-escapes)
         (for ([saved-box (in-list saved-boxes)])
           (set-box! (first saved-box) (second saved-box)))
         (for ([returned (in-list (set->list failure-returns))])
           (set-remove! failure-returns returned))
         (for ([returned (in-list saved-failure-returns)])
           (set-add! failure-returns returned)))))

    ;; 失敗した検査の fresh 名、implicit Return 印、外側 probe の候補を戻す。
    (define (call-with-elaboration-rollback-on-error boundaries thunk)
      (define saved-state (elaboration-state))
      (define saved-flow (flow-snapshot))
      (define saved-escapes (boundary-escape-snapshot))
      (define saved-probes
        (for/list ([candidate-box (in-list (probe-candidate-boxes boundaries))])
          (list candidate-box (unbox candidate-box))))
      (define outer-failure-returns (current-failure-returns))
      (define attempted-failure-returns (mutable-seteq))
      (for ([returned (in-set outer-failure-returns)])
        (set-add! attempted-failure-returns returned))
      (with-handlers
          ([exn?
            (λ (error)
              (restore-elaboration-state! saved-state)
              (flow-restore! saved-flow)
              (boundary-escape-restore! saved-escapes)
              (for ([saved-probe (in-list saved-probes)])
                (set-box! (first saved-probe) (second saved-probe)))
              (raise error))])
        (define result
          (parameterize ([current-loop-trial-catching? #f]
                         [current-failure-returns attempted-failure-returns])
            (thunk)))
        (for ([returned (in-set attempted-failure-returns)])
          (set-add! outer-failure-returns returned))
        result))

    (define (check-never-bound-body body expected environment delta
                                    propositions boundaries)
      (with-handlers ([exn:fail:elab?
                       (λ (_) (synth body environment delta propositions
                                     boundaries))])
        (call-with-elaboration-rollback-on-error
         boundaries
         (λ () (check body expected environment delta propositions boundaries)))))

    ;; SUR-015（spec §6.1、§6.2）。通常の本体結果型を優先し、Never なら
    ;; 最初に合成できた Return payload の型を候補にする。
    ;; ponytail: 入れ子ごとに下見を行うため深さに対して指数の費用。必要になれば節点ごとに記憶する。
    (define (probe-return-type span body environment delta propositions boundaries)
      (call-with-restored-state
       (λ ()
         (define candidates (box '()))
         (define boundary (fresh-boundary))
         (define body-type
           (with-handlers ([exn:fail:elab? (λ (_) #f)])
             (judgment-type
              (synth body environment delta propositions
                     (cons `(FunctionBoundary ,boundary
                                              (#:probe ,candidates) ,span)
                           boundaries)))))
         (cond [(and body-type (not (eq? body-type 'Never))) body-type]
               [(pair? (unbox candidates)) (first (unbox candidates))]
               [else #f]))))

    ;; shortcut: 入れ子の when を scrutinee に置くと下見と本検査が部分式を再走査して深さに対する費用が指数増加し、改善時は下見の Core を本検査で再利用する。
    (define (probe-narrative-type body environment delta propositions
                                  boundaries span)
      (call-with-restored-state
       (λ ()
         (define candidate-box (box '()))
         (define unresolved-leave-box (box #f))
         (define body-expression (peel-node body))
         (define for-option? (for-option-boundary? body))
         (define for-option-none-span
           (and for-option?
                (match body
                  [`(Let ,_ ,_ ,_ (Construct ,none-span none)) none-span]
                  [_ #f])))
         (define leave-adapter (and for-option? 'option-payload))
         (define deferred
           (and (match (peel-node body) [`(Eliminate ,_ ,_) #t] [_ #f])
                (box '())))
         (define boundary (fresh-boundary))
         (define failure #f)
         (define body-result
           (parameterize
               ([current-deferred-when-fallthroughs
                 (and deferred (cons body deferred))])
             (with-handlers ([exn:fail:elab?
                              (λ (error) (set! failure error) #f)])
               (synth body environment delta propositions
                      (cons `(ExpressionBoundary ,boundary
                                                 (#:probe ,candidate-box
                                                  ,unresolved-leave-box)
                                                 ,span ,leave-adapter)
                            boundaries)))))
         (define normal-type
           (and body-result (judgment-normal-type body-result)))
         (define unresolved-leave? (unbox unresolved-leave-box))
         (define candidates
           (append
            (if (and normal-type (not (eq? normal-type '⊥)))
                (list normal-type)
                '())
            (filter (λ (type) (not (eq? type 'Never)))
                    (map (λ (candidate)
                           (leave-probe-candidate-type candidate leave-adapter))
                         (unbox candidate-box)))))
         (cond
           [(pair? candidates)
            (let-values ([(type _record-join?)
                          (merge-branch-types candidates span)])
              (if for-option? `(Option ,type) type))]
           [(and for-option? failure
                 (eq? (exn:fail:elab-reason failure)
                      'constructor-needs-expected-type)
                 for-option-none-span
                 (equal? (exn:fail:elab-primary-span failure)
                         for-option-none-span))
            (reject span 'narrative-expression-needs-expected-type)]
           [failure (raise failure)]
           [(and body-result
                 (match body-expression [`(Eliminate ,_ ,_) #t] [_ #f])
                 (eq? (judgment-core-type body-result) 'Never)
                 (null? candidates)
                 (not unresolved-leave?))
            (reject span 'narrative-expression-needs-expected-type)]
           [(and body-result
                 (eq? (judgment-type body-result) 'Never)
                 (not unresolved-leave?))
            'Never]
           [else (reject span 'narrative-expression-needs-expected-type)]))))

    (define (if-some-explicit clauses s s_0 T)
      (define (expand remaining)
        (match remaining
          [(cons `(,s_i ,then-span ,condition ,body) rest)
           (define chain-span (span-through-end s_i s))
           (define condition-span (span-of condition))
           (define body-span then-span)
           (define false-span
             (if (null? rest) s_0 (span-through-end (first (first rest)) s)))
           (define false-body
             (if (null? rest)
                 `(Construct ,s_0 none (Types ,(resolved-type-argument T)))
                 (expand rest)))
           `(Let ,chain-span
              ((#:bind %ifcond-option ,condition-span) const (#:ty Bool ,s_i))
              ,condition
              (NarrativeExpr ,chain-span
                (Eliminate ,chain-span (#:var %ifcond-option ,condition-span)
                  ((,body-span true () ->
                    (Construct ,body-span some
                               (Types ,(resolved-type-argument T)) ,body))
                   (,false-span false () -> ,false-body)))))]))
      (expand clauses))

    (define (for-option-boundary? body)
      (match (peel-node body)
        [`(Let ((#:bind ,name ,_) const (#:ty Unit ,_)) ,_ ,_)
         ;; Surface では % 始まりの名前を書けない。%for-option を変える場合は、この判定も更新する。
         (regexp-match? #rx"^%for-option" (symbol->string name))]
        [_ #f]))

    (define (if-some-boundary-adapter body expected environment)
      (match (peel-node body)
        [`(Let ((#:bind ,name ,_) const (#:ty Unit ,_)) ,_ ,_)
         #:when (regexp-match? #rx"^%for-option" (symbol->string name))
         (match (normalize-type expected)
           [`(Option ,payload-type) `(Option ,payload-type)]
           [_ #f])]
        [`(Eliminate (#:var ,condition-name ,_) ,_)
         (and (assoc condition-name environment)
              ;; Surface では % 始まりの名前を書けないため、%ifcond-option 接頭辞で if-some-explicit の合成 binder（else のない if）を識別する。
              ;; binder 名を変える場合は、この判定も更新しないと識別できない。
              (regexp-match? #rx"^%ifcond-option" (symbol->string condition-name))
              (match (normalize-type expected)
                [`(Option ,payload-type) `(Option ,payload-type)]
                [_ #f]))]
        [_ #f]))

    (define (probe-if-some-part expression environment delta propositions
                                boundaries boundary-span)
      ;; shortcut: IfSome の下見後に明示形を再検査するため入れ子で指数増加し、改善時は観測 Core を再利用する。
      (call-with-restored-state
       (λ ()
         (define candidates (box '()))
         (define fallthroughs (box '()))
         (define boundary (fresh-boundary))
         (define failure #f)
         (define result
           (with-handlers ([exn:fail:elab?
                            (λ (error) (set! failure error) #f)])
             (parameterize ([current-when-arm-fallthroughs fallthroughs])
               (synth expression environment delta propositions
                      (cons `(ExpressionBoundary ,boundary
                                                 (#:probe ,candidates)
                                                 ,boundary-span option-payload)
                            boundaries)))))
         (list result (unbox candidates) failure (unbox fallthroughs)))))

    (define (check-if-some-explicit clauses s s_0 T expected
                                    environment delta propositions boundaries)
      (define fallthroughs (box '()))
      (define result
        (parameterize ([current-when-arm-fallthroughs fallthroughs])
          (check (if-some-explicit clauses s s_0 T) expected
                 environment delta propositions boundaries)))
      (finish-when-fallthroughs result (unbox fallthroughs) T s #f))

    (define (if-some-result-type clauses s environment delta
                                 propositions boundaries)
      ;; 候補の並びは入れ子の false 枝の評価順に合わせる。
      (define observations
        (append*
         (for/list ([clause (in-list clauses)] [index (in-naturals)])
           (match-define (list s_i _then-span condition body) clause)
           (append
            (if (zero? index)
                '()
                (let ([previous-span
                       (span-through-end
                        (first (list-ref clauses (sub1 index))) s)])
                  (list (probe-if-some-part
                         condition environment delta propositions boundaries
                         previous-span))))
            (list (probe-if-some-part
                   body environment delta propositions boundaries
                   (span-through-end s_i s)))))))
      ;; 原文の順の列は c_i（i > 1）を then_i の前に挟む。
      (define then-results
        (for/list ([clause (in-list clauses)] [index (in-naturals)])
          (list-ref observations (* index 2))))
      (define successful-live
        (for/list ([probe (in-list then-results)]
                   #:when (and (first probe)
                               (not (eq? (judgment-type (first probe)) 'Never))
                               (null? (fourth probe))))
          (first probe)))
      (define fallthroughs
        (append* (map fourth then-results)))
      (define raw-candidates
        (append* (map second observations)))
      (define leave-payload-types
        (for/list ([candidate (in-list raw-candidates)]
                   #:when (match candidate [`(leave-payload ,_) #t] [_ #f]))
          (second candidate)))
      (define return-candidates
        (filter (λ (candidate)
                  (not (match candidate [`(leave-payload ,_) #t] [_ #f])))
                raw-candidates))
      (define merged-type
        (cond
          [(pair? leave-payload-types)
           (define return-payload-types
             (for/list ([candidate (in-list return-candidates)])
               (match candidate
                 [`(Option ,inner) inner]
                 [_ (reject s 'type-mismatch 'Option candidate)])))
           (let-values ([(type _record-join?)
                         (merge-branch-types
                          (append (map judgment-type successful-live)
                                  leave-payload-types return-payload-types)
                          s)])
             type)]
          [(pair? successful-live)
           (let-values ([(cores type)
                         (merge-branches
                          (map judgment-core successful-live)
                          (map judgment-type successful-live)
                          s propositions)])
             type)]
          [(pair? fallthroughs) 'Unit]
          [else #f]))
      (define candidates return-candidates)
      (define failure
        (for/first ([probe (in-list observations)]
                    #:when (third probe))
          (third probe)))
      (define T
        (cond
          [merged-type merged-type]
          [(pair? candidates)
           (match (first candidates)
             [`(Option ,inner) inner]
             [_ (reject s 'type-mismatch 'Option (first candidates))])]
          [failure (raise failure)]
          [else (reject s 'narrative-expression-needs-expected-type)]))
      `(Option ,T))

    (define (elaborate-inferred-fn s parameter-binders raw-parameter-types
                                  raw-row body
                                  environment delta propositions boundaries)
      (define-values (parameters parameter-types captures capture-types)
        (prepare-fn s parameter-binders raw-parameter-types body
                    environment delta))
      (define _capture-flow-pin
        (flow-pin-captures! body parameters environment))
      (define declared-row
        (resolve-declaration-row raw-row delta boundaries s))
      (define parameter-environment
        (extend environment parameters parameter-types #f
                (map resource-type? parameter-types)))
      (define inferred-return-type
        (parameterize ([current-escape-reachable? #t])
          (if (block-body? body)
              (infer-block-return-type s body parameter-environment
                                       delta propositions boundaries)
              (and (mentions-return? (list raw-row body))
                   (probe-return-type s body parameter-environment
                                      delta propositions boundaries)))))
      (if inferred-return-type
          (elaborate-annotated-fn
           s parameter-binders raw-parameter-types
           (λ () inferred-return-type)
           raw-row body environment delta propositions boundaries)
          (let ()
            (define boundary (fresh-boundary))
            (define body-result
              (parameterize ([current-escape-reachable? #t])
                (call-with-flow-rollback
                 (λ ()
                   (synth body parameter-environment
                          delta propositions
                          (cons `(FunctionBoundary ,boundary #:infer ,s)
                                boundaries))))))
            (define return-type (judgment-type body-result))
            (check-function-body-row s body-result return-type boundary declared-row)
            (define-values (capture-raw-names raw-names capture-binders core-binders
                                              reserved-with-formals)
              (prepare-fn-binders s parameter-binders parameters parameter-types
                                  captures capture-types body environment))
            (define signature
              `(NFn ,(append capture-types parameter-types)
                   ,return-type () ,declared-row () User))
            ;; 省略時は、本体が作る入れ子の CallableId の後に割り当てる。
            (define callable (fresh-callable signature))
          (finish-fn s parameter-binders parameter-types
                     captures capture-types capture-raw-names raw-names
                     capture-binders core-binders
                     return-type boundary body-result
                     signature callable reserved-with-formals))))

    ;; 注釈付きの Recur と FnDecl は、関数宣言境界の有無だけを共有する。
    (define (elaborate-recur-annotated
             s raw-function parameter-binders raw-parameter-types
             resolve-return raw-row body continuation
             environment delta propositions boundaries
             #:boundary? boundary?
             #:allow-block-body? [allow-block-body? #f]
             #:prepared-header [prepared-header #f]
             #:inherited-row [inherited-row #f]
             #:return-span [return-span #f]
             #:on-body-result [on-body-result #f]
             #:exclude-loop-trial [exclude-loop-trial #f]
             #:row-trial [row-trial #f]
             #:loop-row? [loop-row? #f])
      (when (and (block-body? body) (not allow-block-body?))
        (reject (block-body-span body) 'invalid-syntax))
      (define-values (function parameters parameter-types)
        (if prepared-header
            (apply values prepared-header)
            (let ([function (peel-bind raw-function)]
                  [parameters (map peel-bind parameter-binders)])
              (when (check-duplicates (cons function parameters))
                (reject s 'duplicate-recur-binder function parameters))
              (define parameter-types
                (for/list ([type (in-list raw-parameter-types)])
                  (resolve-annotation type delta s)))
              (when (captures-owned? body (cons function parameters) environment)
                (reject s 'owned-recur-capture))
              (values function parameters parameter-types))))
      (define return-type (resolve-return))
      (define declared-row
        (or inherited-row
            (resolve-declaration-row raw-row delta boundaries s
                                     #:loop-row? loop-row?)))
      (define signature
        `(NFn ,parameter-types ,return-type () ,declared-row () User))
      (define boundary (and boundary? (fresh-boundary)))
      (define callable (fresh-callable signature))
      (define raw-names
        (fresh-resource-names
         parameter-types
         (set-union (form-symbols body)
                    (list->set parameters)
                    (set function)
                    (list->set (map first environment)))))
      (define core-binders
        (resource-parameter-binders parameter-binders raw-names))
      (define function-environment
        (extend environment (list function) (list signature)))
      (define body-environment
        (extend function-environment parameters parameter-types #f
                (map resource-type? parameter-types)))
      (define body-boundaries
        (cond
          [boundary
           (cons `(FunctionBoundary ,boundary ,return-type ,s) boundaries)]
          [loop-row? boundaries]
          [else
           ;; 関数境界を作らない FnDecl / Recur 本体から Leave を外へ漏らさない。
           (cons '(LeaveBoundaryStop) boundaries)]))
      (define _capture-flow-pin
        (flow-pin-captures! body (cons function parameters) environment))
      (define body-result
        (parameterize ([current-escape-reachable?
                        (or boundary? (current-escape-reachable?))])
          (call-with-flow-rollback
           (λ ()
             (define result
               (check-function-body body return-type return-span body-environment
                                    delta propositions body-boundaries))
             (when on-body-result (on-body-result result))
             (when row-trial
               (set-box! row-trial
                         (list (judgment-row result)
                               (classify-recur-body-for-gate
                                function parameters
                                (classification-view (judgment-core result))
                                body-environment
                                (reverse reversed-callables)))))
             result)
           #:preserve-escapes? #t)))
      (unless row-trial
        (if boundary
            (check-function-body-row s body-result return-type boundary declared-row)
            (unless (row-subset? (judgment-row body-result) declared-row)
              (reject s 'undeclared-recur-effect
                      declared-row (judgment-row body-result)))))
      (define continuation-result
        (parameterize
            ([current-loop-trials
              (if exclude-loop-trial
                  (remq exclude-loop-trial (current-loop-trials))
                  (current-loop-trials))])
          (synth continuation function-environment
                 delta propositions boundaries)))
      (define handled-body
        (if (and boundary
                 (row-member-return? (judgment-row body-result) boundary))
            `(Handle ,s (Return ,boundary (#:ty ,return-type ,s))
                     (,s (#:bind return-value ,s) ->
                         (#:var return-value ,s))
                     (Scope ,s () ,(judgment-core body-result)))
            (judgment-core body-result)))
      ;; Owned の仮引数を 1 つ以上持つときだけ Scope で包む。recur は
      ;; 関数境界を押さないため、包まないと呼出し側の Scope へ place が
      ;; 積み上がる。Owned を持たない Recur の形は変えない。既存の
      ;; lowering に PScopeExit を増やさないためである。
      (define wrapped-body
        (if (ormap values raw-names)
            `(Scope ,s ()
                    ,(wrap-resource-lets parameter-binders parameter-types
                                      raw-names handled-body))
            handled-body))
      (define recur-core
        `(Recur ,s ,callable ,raw-function ,core-binders
                ,wrapped-body
                ,(judgment-core continuation-result)))
      (unless row-trial
        (check-recur-body-gate s function parameters
                               (classification-view
                                (judgment-core body-result))
                               body-environment
                               (reverse reversed-callables)
                               declared-row))
      (judgment recur-core
                (judgment-type continuation-result)
                (judgment-row continuation-result)))

    ;; SUR-008 / SUR-015。Recur の推論前検査を FnDecl の下見前にも共有する。
    (define (prepare-inferred-recur-header
             s raw-function parameter-binders raw-parameter-types
             body environment delta)
      (define function (peel-bind raw-function))
      (define parameters (map peel-bind parameter-binders))
      (when (check-duplicates (cons function parameters))
        (reject s 'duplicate-recur-binder function parameters))
      (define parameter-types
        (for/list ([type (in-list raw-parameter-types)])
          (resolve-annotation type delta s)))
      (when (captures-owned? body (cons function parameters) environment)
        (reject s 'owned-recur-capture))
      (flow-pin-captures! body (cons function parameters) environment)
      (when (set-member? (free-vars body) function)
        (reject s 'return-type-not-inferable 'self-reference))
      (values function parameters parameter-types
              (extend environment parameters parameter-types #f
                      (map resource-type? parameter-types))))

    ;; SUR-008 / SUR-015。戻り型が推論される Recur と、候補が無い FnDecl。
    ;; FnDecl のときだけ body-boundary? により Return の旧 E-TYP-024 を保つ。
    (define (elaborate-recur-inferred
             s raw-function parameter-binders raw-parameter-types
             raw-row body continuation
             environment delta propositions boundaries
             #:body-boundary? [body-boundary? #f])
      (define-values (function parameters parameter-types parameter-environment)
        (prepare-inferred-recur-header
         s raw-function parameter-binders raw-parameter-types body environment delta))
      (define declared-row
        (resolve-declaration-row raw-row delta boundaries s))
      (define body-boundary (and body-boundary? (fresh-boundary)))
      (define body-boundaries
        (if body-boundary
            (cons `(FunctionBoundary ,body-boundary #:infer ,s) boundaries)
            (cons '(LeaveBoundaryStop) boundaries)))
      (define body-result
        (parameterize ([current-escape-reachable?
                        (or body-boundary? (current-escape-reachable?))])
          (call-with-flow-rollback
           (λ ()
             (synth body parameter-environment delta propositions body-boundaries))
           #:preserve-escapes? #t)))
      (define return-type (judgment-type body-result))
      (unless (row-subset? (judgment-row body-result) declared-row)
        (reject s 'undeclared-recur-effect
                declared-row (judgment-row body-result)))
      (define signature
        `(NFn ,parameter-types ,return-type () ,declared-row () User))
      (define callable (fresh-callable signature))
      (define raw-names
        (fresh-resource-names
         parameter-types
         (set-union (form-symbols body)
                    (list->set parameters)
                    (set function)
                    (list->set (map first environment)))))
      (define core-binders
        (resource-parameter-binders parameter-binders raw-names))
      (define function-environment
        (extend environment (list function) (list signature)))
      (define continuation-result
        (synth continuation function-environment
               delta propositions boundaries))
      (define wrapped-body
        (if (ormap values raw-names)
            `(Scope ,s ()
                    ,(wrap-resource-lets parameter-binders parameter-types
                                      raw-names (judgment-core body-result)))
            (judgment-core body-result)))
      (define recur-core
        `(Recur ,s ,callable ,raw-function ,core-binders
                ,wrapped-body ,(judgment-core continuation-result)))
      (check-recur-body-gate s function parameters
                             (classification-view
                              (judgment-core body-result))
                             parameter-environment
                             (reverse reversed-callables)
                             declared-row)
      (judgment recur-core
                (judgment-type continuation-result)
                (judgment-row continuation-result)))

    ;; SUR-015（spec §6.1〜§6.4）。FnDecl の候補なし経路は既存の推論規則へ戻す。
    (define (elaborate-inferred-fndecl
             s raw-function parameter-binders raw-parameter-types
             raw-row body continuation
             environment delta propositions boundaries)
      (if (block-body? body)
          (let-values ([(function parameters parameter-types parameter-environment)
                        (prepare-inferred-recur-header
                         s raw-function parameter-binders raw-parameter-types
                         body environment delta)])
            (define declared-row
              (resolve-declaration-row raw-row delta boundaries s))
            (define return-type
              (infer-block-return-type s body parameter-environment
                                       delta propositions boundaries))
            (elaborate-recur-annotated
             s raw-function parameter-binders raw-parameter-types
             (λ () return-type)
             raw-row body continuation
             environment delta propositions boundaries
             #:boundary? (mentions-return? (list raw-row body))
             #:allow-block-body? #t
             #:prepared-header (list function parameters parameter-types)
             #:inherited-row declared-row))
          (if (not (mentions-return? (list raw-row body)))
              (elaborate-recur-inferred
               s raw-function parameter-binders raw-parameter-types
               raw-row body continuation environment delta propositions boundaries)
              (let-values ([(function parameters parameter-types parameter-environment)
                            (prepare-inferred-recur-header
                             s raw-function parameter-binders raw-parameter-types
                             body environment delta)])
                ;; FnDecl の宣言 row は、自身の境界を積む前に外側で解決する。
                (define _declared-row
                  (resolve-declaration-row raw-row delta boundaries s))
                (define inferred-return-type
                  (probe-return-type s body parameter-environment
                                     delta propositions boundaries))
                (if inferred-return-type
                    (elaborate-recur-annotated
                     s raw-function parameter-binders raw-parameter-types
                     (λ () inferred-return-type)
                     raw-row body continuation
                     environment delta propositions boundaries
                     #:boundary? #t)
                    (elaborate-recur-inferred
                     s raw-function parameter-binders raw-parameter-types
                     raw-row body continuation
                     environment delta propositions boundaries
                     #:body-boundary? #t))))))

    (define (synth expression environment delta propositions boundaries)
      (define s (span-of expression))
      (define result
        (synth/raw expression environment delta propositions boundaries))
      (define normalized (normalize-type (judgment-type result)))
      (unless normalized
        (reject s 'non-normalizable-type (judgment-type result)))
      (define normal-type
        (if (eq? (judgment-normal-type result) '⊥)
            '⊥
            (or (normalize-type (judgment-normal-type result))
                (reject s 'non-normalizable-type
                        (judgment-normal-type result)))))
      (define normalized-core-type
        (or (normalize-type (judgment-core-type result))
            (reject s 'non-normalizable-type
                    (judgment-core-type result))))
      (judgment (judgment-core result)
                normalized
                (judgment-row result)
                normalized-core-type
                normal-type))

    (define (validate-loop-shape! s raw-function parameter-binders
                                  raw-result-type body arguments)
      (define function (peel-bind raw-function))
      (define (violation reason)
        (error 'elaborate "loop 印の形の違反: ~a (~s)" reason s))
      (define (check-binder! binder)
        (when (eq? (binder-name binder) function)
          (violation 'function-rebound)))
      (define (check-parameter-binders! parameters)
        (for ([parameter (in-list parameters)])
          (check-binder! parameter)))
      (check-parameter-binders! parameter-binders)
      (when (inferred? raw-result-type)
        (violation 'inferred-result-type))
      (for ([argument (in-list arguments)])
        (unless
            (or (match argument
                  [`(#:var ,_ ,_) #t]
                  [`(#:lit ,_ ,_) #t]
                  [_ #f])
                (match (peel-node argument)
                  [`(Move ,place)
                   (symbol? (peel-node place))]
                  [_ #f]))
          (violation 'non-atomic-initial-argument)))
      (when (for/or ([argument (in-list arguments)])
              (set-member? (free-vars argument) function))
        (violation 'self-reference-in-initial-argument))

      (define (walk-branch branch delayed?)
        (match branch
          [`(,_ ,_ (,binders ...) -> ,branch-body)
           (for-each check-binder! binders)
           (walk branch-body delayed?)]
          [`(,_ (#:ty ,_ ,_) ,binder -> ,branch-body)
           (check-binder! binder)
           (walk branch-body delayed?)]
          [_ (violation 'unknown-branch-shape)]))

      (define (walk expression delayed?)
        (match (peel-node expression)
          [(? exact-integer?) (void)]
          [(? string?) (void)]
          ['unit (void)]
          [(? symbol? name)
           (when (eq? name function)
             (violation 'function-used-outside-apply-head))]
          [`(Apply ,callee ,arguments ...)
           (match callee
             [`(#:var ,name ,_) #:when (eq? name function)
              (when delayed? (violation 'delayed-self-call))]
             [_ (walk callee delayed?)])
           (for-each (λ (argument) (walk argument delayed?)) arguments)]
          [`(Fn ((,binders ,_) ...) ,_ ,_ ,body)
           (check-parameter-binders! binders)
           (walk body #t)]
          [`(Let ,binder ,bound ,body)
           (check-binder! binder)
           (walk bound delayed?)
           (walk body delayed?)]
          [`(Rec ((,_ ,_ ,fields) ...))
           (for-each (λ (field) (walk field delayed?)) fields)]
          [`(Proj ,record ,_) (walk record delayed?)]
          [`(Construct ,_ (Types ,_ ...) ,fields ...)
           (for-each (λ (field) (walk field delayed?)) fields)]
          [`(Construct ,_ ,fields ...)
           (for-each (λ (field) (walk field delayed?)) fields)]
          [`(Eliminate ,scrutinee (,branches ...))
           (walk scrutinee delayed?)
           (for-each (λ (branch) (walk-branch branch delayed?)) branches)]
          [`(IfSome (,clauses ...) ,_)
           (for ([clause (in-list clauses)])
             (match clause
               [`(,_ ,_ ,condition ,branch-body)
                (walk condition delayed?)
                (walk branch-body delayed?)]
               [_ (violation 'unknown-if-some-shape)]))]
          [`(BlockBody ,body) (walk body delayed?)]
          [`(Return ,body) (walk body delayed?)]
          [`(Leave ,body) (walk body delayed?)]
          [`(NarrativeExpr ,body) (walk body delayed?)]
          [`(TryBind ,binder ,bound ,body)
           (check-binder! binder)
           (walk bound delayed?)
           (walk body delayed?)]
          [`(Recur ,nested-function ((,binders ,_) ...) ,_ ,_ ,body
                   ,continuation)
           (check-binder! nested-function)
           (check-parameter-binders! binders)
           (walk body #t)
           (walk continuation delayed?)]
          [`(Loop ,nested-function ((,binders ,_) ...) ,_ ,_ ,body
                  (,initial-arguments ...))
           (check-binder! nested-function)
           (check-parameter-binders! binders)
           (walk body #t)
           (for-each (λ (argument) (walk argument delayed?))
                     initial-arguments)]
          [`(FnDecl ,nested-function ((,binders ,_) ...) ,_ ,_ ,body
                    ,continuation)
           (check-binder! nested-function)
           (check-parameter-binders! binders)
           (walk body #t)
           (walk continuation delayed?)]
          [`(Yield ,observed ,next)
           (walk observed delayed?)
           (walk next delayed?)]
          [`(Suspend ,body) (walk body delayed?)]
          [`(Move ,place) (walk place delayed?)]
          [`(Reassign ,place ,value)
           (walk place delayed?)
           (walk value delayed?)]
          [`(Drop ,body) (walk body delayed?)]
          [`(Curry ,function-expression ,argument)
           (walk function-expression delayed?)
           (walk argument #t)]
          [`(TypeMake ,_) (void)]
          [`(LetType ,_ ,_ ,body) (walk body delayed?)]
          [_ (violation (format "unknown-production ~s"
                                (peel-node expression)))]))
      (walk body #f))

    ;; 正格な被演算子が Never でも通常の型検査と row の合併は済ませる。
    (define (propagate-context-never result children)
      (if (ormap (λ (child) (eq? (judgment-type child) 'Never)) children)
          (judgment (judgment-core result) 'Never (judgment-row result)
                    'Never (judgment-normal-type result))
          result))

    (define (type-for-context result)
      (if (and (eq? (judgment-type result) 'Never)
               (not (eq? (judgment-normal-type result) '⊥)))
          (judgment-normal-type result)
          (judgment-type result)))

    (define (elaborate-let-tail s binder binding-type binding-mode
                                bound-result bound-never? body environment delta
                                propositions boundaries core-binder bound-core
                                #:declared-type [declared-type binding-type]
                                #:expected [expected #f])
      (define name (peel-bind binder))
      (define flow-key
        (and (eq? binding-mode 'mut) (fresh-flow-key)))
      (define environment-type
        (if flow-key declared-type binding-type))
      (define body-environment
        (extend environment (list name) (list environment-type)
                (and (eq? binding-mode 'mut) '(mut))
                (list (resource-type? binding-type))
                (and flow-key (list flow-key))))
      (define _flow-entry
        (when flow-key
          (set-box! flow-state
                    (hash-set (unbox flow-state) flow-key
                              (flow-entry binding-type '())))))
      (define identity-resource?
        (and (resource-type? binding-type)
             (eq? (peel-node body) name)))
      (define body-result
        (dynamic-wind
         void
         (λ ()
           (parameterize
               ([current-escape-reachable?
                 (and (current-escape-reachable?) (not bound-never?))])
             (cond
               [identity-resource?
                (judgment `(#:var ,name ,(span-of body)) binding-type '())]
               [(and expected bound-never?)
                (check-never-bound-body body expected body-environment delta
                                        propositions boundaries)]
               [(and expected (not bound-never?))
                (check body expected body-environment delta propositions
                       boundaries)]
               [else
                (synth body body-environment delta propositions boundaries)])))
         (λ ()
           (when flow-key
             (set-box! flow-state
                       (hash-remove (unbox flow-state) flow-key))))))
      (define let-type
        (if (or bound-never? (eq? (judgment-type body-result) 'Never))
            'Never
            (judgment-type body-result)))
      (define let-normal-type
        (if (and bound-never?
                 (eq? (judgment-type body-result) 'Never))
            '⊥
            (judgment-normal-type body-result)))
      (define let-result
        (judgment `(Let ,s ,core-binder
                        ,bound-core
                  ,(judgment-core body-result))
                  let-type
                  (row-union (judgment-row bound-result)
                             (judgment-row body-result))
                  let-type
                  let-normal-type))
      (if (and expected identity-resource?)
          ;; 資源 identity Let は資源の place を保つため、Let 全体を検査する。
          (check-against-expected let-result expected s propositions)
          (if (and expected bound-never?)
              (check-against-expected let-result expected s propositions)
              let-result)))

    (define (elaborate-mut-compatible-value s binding-mode declared-type value
                                            environment delta propositions
                                            boundaries
                                            #:mismatch-key [mismatch-key #f])
      (define result
        (if (expected-type-checkable? value declared-type)
            (check value declared-type environment delta propositions boundaries)
            (synth value environment delta propositions boundaries)))
      (define (with-mismatch-key thunk actual-type)
        (if mismatch-key
            (with-handlers
                ([exn:fail:elab?
                  (lambda (failure)
                    (if (memq (exn:fail:elab-reason failure)
                              '(type-mismatch owned-narrowing-needs-proof
                                owned-narrowing-rejected))
                        (reject s mismatch-key declared-type actual-type)
                        (raise failure)))])
              (thunk))
            (thunk)))
      (if (eq? (judgment-type result) 'Never)
          (values result (judgment-core result) declared-type
                  (bind-with-mode s binding-mode declared-type declared-type
                                  propositions)
                  #t)
          (let ()
            (define source-core-type (judgment-core-type result))
            ;; let/mut は最上位の Record 残余を束縛型へ戻すため、その残余は
            ;; RSD の対象から除く。const と Record 以外は宣言型まで回収する。
            (define remainder-target
              (match* (binding-mode source-core-type declared-type)
                [((or 'let 'mut) `(Record ,actual-row) `(Record ,declared-row))
                 `(Record ,(append declared-row
                                   (field-row-residual actual-row declared-row)))]
                [(_ _ _) declared-type]))
            (define-values (discharged-core discharged-type)
              (discharge-remainder (judgment-core result)
                                   source-core-type remainder-target s propositions))
            (define-values (bound-core actual-type)
              (with-mismatch-key
               (lambda ()
                 (if (and (memq binding-mode '(let mut))
                          (tag-compat? discharged-type declared-type
                                       (initial-candidate-context propositions))
                          (match (narrowing-kind discharged-type declared-type
                                                propositions)
                            [`(drop-obligation ,_ ,_) #t]
                            [_ #f]))
                     ;; let/mut は最上位の Owned 残余を束縛型へ戻す。
                     (values discharged-core discharged-type)
                     (convert discharged-core discharged-type declared-type s
                              propositions)))
               source-core-type))
            ;; OWN-004 は変換前の Core の型と変換後の型の間でも検査する。
            (with-mismatch-key
             (lambda ()
               (match (narrowing-kind discharged-type actual-type propositions)
                 ['ok (void)]
                 [`(drop-obligation ,_ ,_)
                  (reject s 'owned-narrowing-needs-proof actual-type
                          discharged-type)]
                 [_ (unless (mut-union-rebuildable?
                             discharged-type actual-type
                             (initial-candidate-context propositions) propositions)
                      (reject s 'owned-narrowing-rejected actual-type
                              discharged-type))]))
             source-core-type)
            (define binding-type
              (with-mismatch-key
               (lambda ()
                 (bind-with-mode s binding-mode declared-type actual-type
                                 propositions))
               actual-type))
            (values result bound-core declared-type binding-type #f))))

    (define (rebuild-flow-value s core actual target propositions)
      (if (reassign-narrowing? actual target)
          core
          (let-values ([(converted converted-type)
                        (with-handlers
                            ([exn:fail:elab?
                              (lambda (_failure)
                                (reject s 'reassign-type-mismatch
                                        target actual))])
                          (convert core actual target s propositions))])
            (define-values (discharged discharged-type)
              (discharge-remainder converted converted-type target s propositions))
            (if (type-equiv? discharged-type target)
                discharged
                `(Discharge ,s
                            (ProofRep (Reserved o-narrow)
                                      (RemainderSafelyDropped
                                       ,discharged-type ,target))
                            ,discharged)))))

    (struct flow-branch (environment result snapshot escape) #:transparent)

    (define (flow-name-for-key environment key)
      (for/or ([entry (in-list environment)])
        (match entry
          [(list name _ 'mut _ entry-key)
           (and (eq? entry-key key) name)]
          [_ #f])))

    (define (flow-entry-at snapshot key fallback)
      (hash-ref snapshot key (λ () fallback)))

    (define (join-flow-pins entries)
      (for/fold ([pins '()])
                ([pin (in-list (append-map flow-entry-pins entries))])
        (if (ormap (λ (existing) (type-equiv? existing pin)) pins)
            pins
            (append pins (list pin)))))

    ;; 枝の検査は同じ入口から始め、正常出口の C だけを合流する。
    (define (join-branch-flows s environment entry branches propositions
                               #:reachable? [reachable? #t]
                               #:live-keys [provided-live-keys #f])
      (define live-branches
        (if reachable?
            (filter (λ (branch)
                      (judgment-completes? (flow-branch-result branch)))
                    branches)
            '()))
      (cond
        [(null? live-branches)
         (flow-restore! entry)
         (values (map (λ (branch) (flow-branch-result branch)) branches)
                 entry)]
        [else
         (define keys (or provided-live-keys (live-flow-keys environment)))
         (define joined-entries
           (for/list ([key (in-list keys)])
             (define name (flow-name-for-key environment key))
             (define base-entry (hash-ref entry key))
             (define branch-entries
               (for/list ([branch (in-list live-branches)])
                 (flow-entry-at (flow-branch-snapshot branch) key base-entry)))
             (define branch-types (map flow-entry-type branch-entries))
             (define pins (map flow-entry-pins branch-entries))
             (define declared-type (lookup environment name))
             (define branch-index 0)
             (define (rebuildable? actual target)
               (define branch (list-ref live-branches branch-index))
               (set! branch-index (add1 branch-index))
               (or (reassign-narrowing? actual target)
                   (with-handlers ([exn:fail:elab? (λ (_) #f)])
                     (call-with-restored-state
                      (λ ()
                        (flow-restore! (flow-branch-snapshot branch))
                        (rebuild-flow-value s `(#:var ,name ,s)
                                            actual target propositions)
                        #t)))))
             (define target
               (flow-join-decision branch-types pins declared-type
                                   propositions rebuildable?))
             (when (eq? target 'reassign-type-mismatch)
               (reject s 'reassign-type-mismatch declared-type
                       (first branch-types)))
             (list key target (join-flow-pins branch-entries))))
         (define joined-snapshot
           (for/fold ([snapshot entry])
                     ([joined (in-list joined-entries)])
             (match-define (list key type pins) joined)
             (hash-set snapshot key (flow-entry type pins))))
         (define rewritten-results
           (for/list ([branch (in-list branches)])
             (define result (flow-branch-result branch))
             (if (not (memq branch live-branches))
                 result
                 (let* ([escape (flow-branch-escape branch)]
                        [reassignments
                        (for/list ([joined (in-list joined-entries)]
                                   #:do [(match-define (list key target _pins)
                                           joined)]
                                   #:unless
                                   (reassign-narrowing?
                                    (flow-entry-type
                                     (flow-entry-at
                                      (flow-branch-snapshot branch) key
                                      (hash-ref entry key)))
                                    target))
                          (list key
                                (flow-name-for-key environment key)
                                (flow-entry-type
                                 (flow-entry-at
                                  (flow-branch-snapshot branch) key
                                  (hash-ref entry key)))
                                target))])
                   (cond
                     [(and (null? reassignments) (not escape)) result]
                     [(and escape (null? reassignments))
                      (define span (pending-escape-span escape))
                      (judgment
                       `(Perform ,span
                                 (Return ,(pending-escape-boundary escape)
                                         (#:ty ,(pending-escape-return-type escape)
                                               ,span))
                                 ,(judgment-core result))
                       'Never
                       (row-union
                        (judgment-row result)
                        `((Return ,(pending-escape-boundary escape)
                                  ,(pending-escape-return-type escape))))
                       'Never '⊥)]
                     [else
                      (define core
                        (call-with-flow-rollback
                         (λ ()
                           (flow-restore! (flow-branch-snapshot branch))
                           (define result-core (judgment-core result))
                           (define result-type (judgment-core-type result))
                           (define temporary (fresh-union-name))
                           (define resource? (resource-type? result-type))
                           (define tail
                             (if resource?
                                 `(Move ,s (#:var ,temporary ,s))
                                 `(#:var ,temporary ,s)))
                           (define rebuilt-tail
                             (for/fold ([body tail])
                                       ([reassignment
                                         (in-list (reverse reassignments))])
                               (match-define (list key name actual target)
                                 reassignment)
                               (define rebuilt
                                 (rebuild-flow-value
                                  s `(#:var ,name ,s) actual target propositions))
                               (define unit-name (fresh-union-name))
                               `(Let ,s
                                     ((#:bind ,unit-name ,s) const
                                      (#:ty Unit ,s))
                                     (Reassign ,s (#:var ,name ,s)
                                               (#:ty ,target ,s) ,rebuilt)
                                     ,body)))
                           (define operand
                             `(Let ,s
                                   ((#:bind ,temporary ,s)
                                    ,(if resource? 'let 'const)
                                    (#:ty ,result-type ,s))
                                   ,result-core ,rebuilt-tail))
                           (if escape
                               `(Perform ,(pending-escape-span escape)
                                         (Return
                                          ,(pending-escape-boundary escape)
                                         (#:ty ,(pending-escape-return-type escape)
                                                ,(pending-escape-span escape)))
                                         ,operand)
                               operand))))
                      (if escape
                          (judgment
                           core 'Never
                           (row-union
                            (row-union
                             (judgment-row result)
                             `((Return ,(pending-escape-boundary escape)
                                       ,(pending-escape-return-type escape))))
                            '(Mutation))
                           'Never '⊥)
                          (judgment core
                                    (judgment-type result)
                                    (row-union (judgment-row result) '(Mutation))
                                    (judgment-core-type result)
                                    (judgment-normal-type result)))])))))
         (flow-restore! joined-snapshot)
         (values rewritten-results joined-snapshot)]))

    (define (elaborate-loop s raw-function parameter-binders
                            raw-parameter-types raw-return-type raw-row
                            body arguments environment delta propositions
                            boundaries)
      (define function (peel-bind raw-function))
      (define parameters (map peel-bind parameter-binders))
      (when (and (ormap inferred? raw-parameter-types)
                 (not (= (length raw-parameter-types) (length arguments))))
        (reject s 'arity-mismatch (length raw-parameter-types) (length arguments)))
      (define initial-arguments
        (for/list ([argument (in-list arguments)])
          (define name (variable-reference-name argument))
          (if (and name
                   (for-generated-name? name "%for-list")
                   (resource-type? (flow-view environment name))
                   (not (match (peel-node argument)
                          [`(Move ,_) #t]
                          [_ #f])))
              `(Move ,(span-of argument) ,argument)
              argument)))
      (define loop-parameter-types
        (for/list ([raw-type (in-list raw-parameter-types)]
                   [argument (in-list initial-arguments)])
          (if (inferred? raw-type)
              (let* ([argument-type
                      (call-with-loop-trial-rollback
                       boundaries
                       (λ ()
                         (judgment-type
                          (synth argument environment delta propositions
                                 boundaries))))]
                     [actual
                      (or (normalize-type argument-type)
                          (reject s 'non-normalizable-type argument-type))])
                (match actual
                  [`(List ,_) (list '#:ty actual (span-of argument))]
                  [_ (reject s 'type-mismatch '(List _) actual)]))
              raw-type)))
      (define loop-body
        (match body
          [`(Eliminate ,eliminate-span (#:var ,rest ,rest-span) ,branches)
           #:when (and (for-generated-name? function "%for-loop")
                       (for-generated-name? rest "%for-rest")
                       (= (length parameters) 1)
                       (eq? rest (first parameters))
                       (= (length loop-parameter-types) 1)
                       (resource-type?
                        (resolve-annotation (first loop-parameter-types)
                                            delta s)))
           `(Eliminate ,eliminate-span
                       (Move ,rest-span (#:var ,rest ,rest-span))
                       ,branches)]
          [_ body]))
      (define inferred-loop-row? (inferred-row? raw-row))
      (define free-names
        (set-subtract (free-vars loop-body)
                      (list->set (cons function parameters))))
      (define targets
        (for/list ([name (in-list (remove-duplicates (map first environment)))]
                   #:when (and (set-member? free-names name)
                               (flow-key-of environment name)))
          (list name (flow-key-of environment name))))
      (define keys (map second targets))
      (define declared-types
        (for/hash ([target (in-list targets)])
          (values (second target) (lookup environment (first target)))))
      (define initial-views
        (for/hash ([key (in-list keys)]) (values key (flow-type key))))
      (define initial-state (flow-snapshot))
      (define (with-views state views)
        (for/fold ([updated state]) ([(key type) (in-hash views)])
          (define entry (hash-ref updated key))
          (hash-set updated key (flow-entry type (flow-entry-pins entry)))))
      (define (trial-on views [inherited-row #f] [collect-row? #f])
        (define trial-state (with-views initial-state views))
        (define entry-views
          (for/hash ([key (in-list keys)])
            (values key (hash-ref views key))))
        (define trial (loop-trial function keys entry-views (box '())))
        (define row-result (and collect-row? (box #f)))
        (define trial-failure #f)
        (with-handlers ([exn:fail:elab? (λ (failure) (set! trial-failure failure))])
          (call-with-loop-trial-rollback
           boundaries
           (λ ()
             (flow-restore! trial-state)
             (parameterize ([current-loop-trial-catching? #t]
                            [current-loop-trials
                             (cons trial (current-loop-trials))])
               (parameterize
                   ([current-generated-for-loop
                     (and (for-generated-name? function "%for-loop")
                          function)])
                 (elaborate-recur-annotated
                  s raw-function parameter-binders loop-parameter-types
                  (λ () (resolve-annotation raw-return-type delta s))
                  raw-row loop-body
                  `(Apply ,s (#:var ,function ,s) ,@initial-arguments)
                  environment delta propositions boundaries
                  #:boundary? #f
                  #:inherited-row inherited-row
                  #:on-body-result
                  (λ (result)
                    (when (judgment-completes? result)
                      (set-box! (loop-trial-log trial)
                                (append (unbox (loop-trial-log trial))
                                        (list (flow-snapshot))))))
                  #:row-trial row-result
                  #:exclude-loop-trial trial
                  #:loop-row? #t))))))
        (values (unbox (loop-trial-log trial))
                (and row-result (unbox row-result))
                trial-failure))
      (define (fixed-point [inherited-row #f] [collect-row? #f])
        (let iterate ([views initial-views]
                      [history (for/hash ([key (in-list keys)])
                                 (values key (list (hash-ref initial-views key))))]
                      [removed (for/hash ([key (in-list keys)])
                                 (values key (set)))]
                      [fixed-at-declared (set)])
          (define trial-entry (with-views initial-state views))
          (define-values (records row-facts trial-failure)
            (trial-on views inherited-row collect-row?))
          (when (and collect-row? trial-failure (not row-facts))
            (raise trial-failure))
          (define-values (next-views next-removed next-fixed)
            (for/fold ([next-views (hasheq)]
                       [next-removed removed]
                       [next-fixed fixed-at-declared])
                      ([target (in-list targets)])
              (define name (first target))
              (define key (second target))
              (define declared (hash-ref declared-types key))
              (define current (hash-ref views key))
              (cond
                [(set-member? fixed-at-declared key)
                 (values (hash-set next-views key declared)
                         next-removed next-fixed)]
                [else
                 (define snapshots (cons trial-entry records))
                 (define inputs
                   (for/list ([snapshot (in-list snapshots)])
                     (flow-entry-type (hash-ref snapshot key))))
                 (define fit-failed? #f)
                 (define fit-index -1)
                 (define (fits? actual candidate)
                   (set! fit-index (add1 fit-index))
                   (define snapshot (list-ref snapshots fit-index))
                   (define fits
                     (with-handlers ([exn:fail:elab? (λ (_) #f)])
                       (call-with-loop-trial-rollback
                        boundaries
                        (λ ()
                          (flow-restore! snapshot)
                          (or (reassign-narrowing? actual candidate)
                              (begin
                                (rebuild-flow-value
                                 s `(#:var ,name ,s) actual candidate propositions)
                                #t))))))
                   (unless fits (set! fit-failed? #t))
                   fits)
                 (define-values (candidate _path)
                   (flow-join-type inputs declared propositions))
                 (define joined
                   (loop-join inputs declared propositions fits?))
                 (define fallback? (or (not candidate) fit-failed?))
                 (define-values (widened removed*)
                   (if fallback?
                       (values declared (hash-ref removed key))
                       (loop-widen current joined declared
                                   (hash-ref removed key))))
                 (define cycle?
                   (and (not (type-equiv? widened current))
                        (loop-cycle? widened (hash-ref history key))))
                 (define next (if cycle? declared widened))
                 (values (hash-set next-views key next)
                         (hash-set next-removed key removed*)
                         (if (or fallback? cycle?)
                             (set-add next-fixed key)
                             next-fixed))])))
          (if (for/and ([key (in-list keys)])
                (type-equiv? (hash-ref views key) (hash-ref next-views key)))
              (if collect-row?
                  (values next-views row-facts)
                  next-views)
              (iterate next-views
                       (for/fold ([next-history history])
                                 ([key (in-list keys)])
                         (hash-set next-history key
                                   (append (hash-ref history key)
                                           (list (hash-ref next-views key)))))
                       next-removed next-fixed))))
      (define-values (final-loop-row final-views)
        (if inferred-loop-row?
            (let iterate-row ([row '()])
              ;; row trial は targets が空でも 1 回実行し、本体の row を採取する。
              (define-values (views row-facts) (fixed-point row #t))
              (unless row-facts
                (error 'elaborate-loop "#:infer loop の本体 row を採取できなかった" s))
              (match-define (list body-row classification) row-facts)
              (define next-row (normalize-row body-row))
              (if (row-subset? next-row row)
                  (values (if (eq? classification 'Unknown)
                              (normalize-row (cons 'Partial row))
                              row)
                          views)
                  (iterate-row next-row)))
            (values #f (if (null? targets) initial-views (fixed-point)))))
      (define prefix-assignments
        (for/list ([target (in-list targets)]
                   #:do [(define name (first target))
                         (define key (second target))
                         (define current (hash-ref initial-views key))
                         (define final (hash-ref final-views key))]
                   #:unless (type-equiv? (normalize-type current)
                                         (normalize-type final)))
          (define rebuilt
            (rebuild-flow-value s `(#:var ,name ,s) current final propositions))
          (list name final rebuilt)))
      (for ([target (in-list targets)])
        (flow-set-type! (second target)
                        (hash-ref final-views (second target))))
      ;; 外側 trial 中なら、入れ子 loop の本検査もその trial の一部として catch を継承する。
      (define recur-result
        (parameterize
            ([current-generated-for-loop
              (and (for-generated-name? function "%for-loop") function)])
          (elaborate-recur-annotated
           s raw-function parameter-binders loop-parameter-types
           (λ () (resolve-annotation raw-return-type delta s))
           raw-row loop-body
           `(Apply ,s (#:var ,function ,s) ,@initial-arguments)
           environment delta propositions boundaries
           #:boundary? #f
           #:inherited-row final-loop-row
           #:loop-row? #t)))
      (if (null? prefix-assignments)
          recur-result
          (let ([core
                 (for/fold ([tail (judgment-core recur-result)])
                           ([assignment (in-list (reverse prefix-assignments))])
                   (match-define (list name type rebuilt) assignment)
                   (define temporary (fresh-union-name))
                   `(Let ,s
                         ((#:bind ,temporary ,s) const (#:ty Unit ,s))
                         (Reassign ,s (#:var ,name ,s) (#:ty ,type ,s) ,rebuilt)
                         ,tail))])
            (judgment core
                      (judgment-type recur-result)
                      (row-union '(Mutation) (judgment-row recur-result))
                      (judgment-core-type recur-result)
                      (judgment-normal-type recur-result)))))

    (define (elaborate-annotated-let-bound s binding-mode raw-type bound
                                           environment delta propositions
                                           boundaries)
      (define declared-type (resolve-annotation raw-type delta s))
      (when (and (eq? binding-mode 'mut)
                 (or (not (owned-free? declared-type))
                     (unbound-borrowed-type? declared-type (set))))
        ;; 宣言型だけで明らかな affine/borrowed binding は bound を合成する
        ;; 前に拒むため、elaborate と typing が同じ key を返す。
        (reject s 'mut-binding-unsupported-type declared-type))
      (call-with-loop-trial-catch
       boundaries
       (λ ()
         (elaborate-mut-compatible-value
          s binding-mode declared-type bound environment delta propositions
          boundaries))
       (λ ()
         (define placeholder-core `(#:lit unit ,s))
         (define placeholder
           (judgment placeholder-core declared-type '()))
         (values placeholder placeholder-core declared-type
                 (bind-with-mode s binding-mode declared-type declared-type
                                 propositions)
                 #f))))

    (define (projection-chain expression environment)
      (define (walk node)
        (match (peel-node node)
          [(? symbol? name) (list name node '())]
          [`(Proj ,record ,raw-label)
           (match (walk record)
             [(list name root steps)
              (list name root
                    (append steps (list (list raw-label node))))]
             [_ #f])]
          [_ #f]))
      (match (walk expression)
        [(list name root steps)
         (and (place-binding? environment name)
              (list name root steps))]
        [_ #f]))

    (define (elaborate-place-projection expression environment)
      (match (projection-chain expression environment)
        [(list root root-node steps)
         (define initial-type (normalize-type (flow-view environment root)))
         (define initial-core `(#:var ,root ,(span-of root-node)))
         (define-values (projected-type projected-core _index)
           (for/fold ([current-type initial-type]
                      [current-core initial-core]
                      [index 0])
                     ([step (in-list steps)])
             (define terminal? (= index (sub1 (length steps))))
             (match-define (list raw-label node) step)
             (define span (span-of node))
             (define label (peel-lbl raw-label))
             (match current-type
               [`(Record ,row)
                (define field (assoc label row))
                (unless field (reject span 'unknown-record-label label))
                (define field-type (second field))
                (define optional? (field-optional? field))
                (when (and optional? (not terminal?))
                  (reject span 'project-non-record `(Option ,field-type)))
                (when (and terminal? (resource-type? field-type))
                  (reject span 'owned-variable-requires-move label))
                (if optional?
                    (values `(Option ,field-type)
                            `(ProjOpt ,span (#:ty ,field-type ,span)
                                      ,current-core ,raw-label)
                            (add1 index))
                    (values field-type
                            `(Proj ,span ,current-core ,raw-label)
                            (add1 index)))]
               [_ (reject span 'project-non-record current-type)])))
         (judgment projected-core projected-type '())]
        [_ #f]))

    (define (synth/raw expression environment delta propositions boundaries)
      (define s (span-of expression))
      (match (peel-node expression)
        [(? integer? literal) (judgment `(#:lit ,literal ,s) 'Int '())]
        [(? string? literal) (judgment `(#:lit ,literal ,s) 'String '())]
        ['unit (judgment `(#:lit unit ,s) 'Unit '())]

        [(? symbol? name)
         (define local-type (flow-view environment name))
         (cond
           [local-type
            ;; UCore に Handle と RecRewrite は無い。encoding と handler の
            ;; Core は直接組み立て、identity Let は synth-let-body が
            ;; E-Var を通さずに値を渡す。
            (if (resource-type? local-type)
                (reject s 'owned-variable-requires-move name)
                (judgment `(#:var ,name ,s) local-type '()))]
           [else
            (match (lookup (current-Γ0) name)
              [(list type value)
               (when (resource-type? type)
                 (reject s 'owned-variable-requires-move name))
               (judgment (attach-span value s) type '())]
               [_ (reject s 'unbound-variable name)])])]

        [`(Loop ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                ,raw-result-type ,raw-row ,body (,arguments ...))
         (validate-loop-shape! s raw-function
                               (map list parameter-binders raw-parameter-types)
                               raw-result-type body arguments)
         (elaborate-loop s raw-function parameter-binders
                         raw-parameter-types raw-result-type raw-row
                         body arguments environment delta propositions
                         boundaries)]

        [`(FnDecl ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                  ,raw-return-type ,raw-row ,body ,continuation)
         #:when (not (inferred? raw-return-type))
         (elaborate-recur-annotated
          s raw-function parameter-binders raw-parameter-types
          (λ () (resolve-annotation raw-return-type delta s))
          raw-row body continuation
          environment delta propositions boundaries
          #:boundary? (mentions-return? (list raw-row body))
          #:allow-block-body? #t
          #:return-span (nearest-span raw-return-type s))]

        [`(FnDecl ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                  (#:infer ,_) ,raw-row ,body ,continuation)
         (elaborate-inferred-fndecl
          s raw-function parameter-binders raw-parameter-types
          raw-row body continuation
          environment delta propositions boundaries)]

        [`(FnDecl ,fields ...)
         (synth/raw `(Recur ,s ,@fields)
                    environment delta propositions boundaries)]

        [`(Fn ((,parameter-binders ,raw-parameter-types) ...)
              ,_ ,_ ,_)
         #:when (ormap inferred? raw-parameter-types)
         ;; 合成位置では仮引数型を推論する手がかりが無い。
         ;; 重複の診断は期待型の有無によらず先に行う。
         (define parameters (map peel-bind parameter-binders))
         (when (check-duplicates parameters)
           (reject s 'duplicate-parameter parameters))
         (define infer-span
           (for/first ([type (in-list raw-parameter-types)]
                       #:when (inferred? type))
             (second type)))
         (reject infer-span 'parameter-type-not-inferable
                 'no-expected-function)]

        [`(Fn ((,parameter-binders ,raw-parameter-types) ...)
              (#:infer ,_) ,raw-row ,body)
         (elaborate-inferred-fn s parameter-binders raw-parameter-types raw-row
                                body environment delta propositions boundaries)]

        [`(Fn ((,parameter-binders ,raw-parameter-types) ...)
              ,raw-return-type ,raw-row ,body)
         (elaborate-annotated-fn
          s parameter-binders raw-parameter-types
          (λ () (resolve-annotation raw-return-type delta s))
          raw-row body environment delta propositions boundaries
          #:return-span
          (and (not (inferred? raw-return-type))
               (nearest-span raw-return-type s)))]

        [`(BlockBody ,inner)
         (synth-when-arm-block-body (block-body-span expression) inner environment delta
                                   propositions boundaries)]

        [`(BlockBody ,_)
         (reject s 'invalid-syntax)]

        [`(Apply ,function ,arguments ...)
         (define raw-function-result
           (synth function environment delta propositions boundaries))
         (define function-never?
           (eq? (judgment-type raw-function-result) 'Never))
         (define-values (function-result wrap)
           (if function-never?
               (values raw-function-result #f)
               (normalize-owned-function
                raw-function-result (span-of function)
                (function-reserved-names function arguments environment))))
         (define function-type
           (if function-never?
               (match (type-for-context function-result)
                 [`(Owned ,inner) inner]
                 [type type])
               (let-values ([(type _owned?)
                             (peel-owned-function-elab
                              (judgment-type function-result)
                              (judgment-core function-result))])
                 type)))
         (match function-type
           [`(NFn ,parameter-types ,return-type ,_latent-in ,latent-row ,obligations ,_origin)
            ;; PRF-004: 判定と搬送で探索を二重に走らせない。obligation-proofs は
            ;; 各義務を一度だけ解き、充足できない義務と搬送できない P をどちらも
            ;; #f で返す。obligations-dischargeable? の呼び出しはここから外す。
            (define proofs
              (obligation-proofs
               obligations
               (initial-candidate-context propositions)))
            (when (memq #f proofs)
              (reject s 'unsatisfied-proof-obligation obligations))
            (define loop-callee (variable-reference-name function))
            (define checked-arguments
              (for/list ([argument (in-list arguments)]
                         [index (in-naturals)])
                (define name (variable-reference-name argument))
                (define expected
                  (and (< index (length parameter-types))
                       (list-ref parameter-types index)))
                (if (and (eq? loop-callee (current-generated-for-loop))
                         name
                         (for-generated-name? name "%for-tail")
                         expected
                         (resource-type? expected)
                         (not (match (peel-node argument)
                                [`(Move ,_) #t]
                                [_ #f])))
                    `(Move ,(span-of argument) ,argument)
                    argument)))
            (define argument-results
              (parameterize
                  ([current-escape-reachable?
                    (and (current-escape-reachable?)
                         (judgment-completes? function-result))])
                (check-many checked-arguments parameter-types
                            environment delta propositions boundaries s)))
            (define applied
              `(Apply ,s ,(judgment-core function-result)
                      ,@(map judgment-core argument-results)))
            (define result
              (close-owned-function
               wrap
               (propagate-context-never
                (judgment
                ;; 義務列の先頭を最も外側にする。逆順に畳むと (φ_1 (φ_2 Apply)) になる。
                (for/fold ([core applied]) ([proof (in-list (reverse proofs))])
                  `(Discharge ,s ,proof ,core))
                return-type
                (rows-union
                 (append (list (judgment-row function-result))
                         (map judgment-row argument-results)
                         (list latent-row))))
               (cons function-result argument-results))))
            (record-loop-back-edge! function argument-results)
            result]
           [_ (reject s 'apply-non-function (judgment-type function-result))])]

        [`(Rec (,raw-fields ...))
         (define raw-labels (map first raw-fields))
         (define fields
           (for/list ([field (in-list raw-fields)])
             (match-define `(,raw-label ,mutability ,field-expression) field)
             (list (peel-lbl raw-label) mutability field-expression)))
         (unless (field-row-unique? fields)
           (reject s 'duplicate-record-label fields))
         (define field-reachable? (current-escape-reachable?))
         (define field-results
           (for/list ([field (in-list fields)])
             (match-define `(,label ,mutability ,field-expression) field)
             (define result
               (parameterize ([current-escape-reachable? field-reachable?])
                 (synth field-expression environment delta propositions boundaries)))
             (set! field-reachable?
                   (and field-reachable? (judgment-completes? result)))
             (define field-type (type-for-context result))
             (when (and (not (eq? (judgment-normal-type result) '⊥))
                        (owned-type? field-type))
               (reject s 'owned-record-field label))
             (list label mutability result)))
         (define normal-row
           (for/list ([field (in-list field-results)])
             (match-define (list label mutability result) field)
             (list label (type-for-context result) mutability)))
         (define normal-type
           (if (ormap (λ (field)
                        (eq? (judgment-normal-type (third field)) '⊥))
                      field-results)
               '⊥
               `(Record ,normal-row)))
         (propagate-context-never
          (judgment
           `(Rec ,s
             ,(for/list ([field (in-list field-results)]
                         [raw-label (in-list raw-labels)])
                (match-define (list _label mutability result) field)
                `(,raw-label ,mutability ,(judgment-core result))))
           `(Record
             ,(for/list ([field (in-list field-results)])
                (match-define (list label mutability result) field)
                `(,label ,(judgment-type result) ,mutability)))
           (rows-union
            (for/list ([field (in-list field-results)])
              (judgment-row (third field))))
           `(Record
             ,(for/list ([field (in-list field-results)])
                (match-define (list label mutability result) field)
                `(,label ,(judgment-core-type result) ,mutability)))
           normal-type)
          (map third field-results))]

        [`(Proj ,record ,raw-label)
         (or (elaborate-place-projection expression environment)
             (let ([label (peel-lbl raw-label)])
               (define record-result
                 (synth record environment delta propositions boundaries))
               (match (type-for-context record-result)
                 ['Never
                  (judgment `(Proj ,s ,(judgment-core record-result) ,raw-label)
                            'Never (judgment-row record-result) 'Never '⊥)]
                 [`(Record ,row)
                  (define field (assoc label row))
                  (cond
                    [(not field) (reject s 'unknown-record-label label)]
                    [(field-optional? field)
                     (define field-type (second field))
                     (propagate-context-never
                      (judgment `(ProjOpt ,s (#:ty ,field-type ,s)
                                          ,(judgment-core record-result) ,raw-label)
                                `(Option ,field-type)
                                (judgment-row record-result))
                      (list record-result))]
                    [else
                     (match (field-row-lookup row label)
                       [(list field-type _)
                        (propagate-context-never
                         (judgment `(Proj ,s ,(judgment-core record-result) ,raw-label)
                                   field-type
                                   (judgment-row record-result))
                         (list record-result))]
                       [_ (reject s 'unknown-record-label label)])])]
                 [_ (reject s 'project-non-record
                            (type-for-context record-result))])))]

        ;; spec §8。注釈なしの const と let と let mut である。宣言型が
        ;; 無いので束縛式の型をそのまま宣言型とみなす。宣言型だけで分かる
        ;; mut の検査は走らせようがなく、bind-with-mode の中の推論後の
        ;; 検査が同じ key を返す。
        [`(Let (,raw-name ,binding-mode) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define actual-type (type-for-context bound-result))
         (define binding-type
           (bind-with-mode s binding-mode actual-type actual-type
                           propositions))
         (elaborate-let-tail
          s raw-name binding-type binding-mode bound-result
          (eq? (judgment-type bound-result) 'Never) body environment
          delta propositions boundaries
          `(,raw-name ,binding-mode (#:ty ,binding-type ,(span-of bound)))
          (judgment-core bound-result))]

        ;; 注釈なし Let の (#:bind x s) を注釈あり Let の 3 つ組として
        ;; 誤って分解しないよう、binder の包みの形で分岐する。
        [`(Let (,raw-name ,binding-mode ,raw-type) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
         (define-values (bound-result bound-core declared-type binding-type
                         bound-never?)
           (elaborate-annotated-let-bound
            s binding-mode raw-type bound environment delta propositions
            boundaries))
         (elaborate-let-tail
          s raw-name binding-type binding-mode
          bound-result
          bound-never?
          body environment delta propositions boundaries
          `(,raw-name ,binding-mode (#:ty ,declared-type
                                      ,(wrapper-span raw-type)))
          bound-core
          #:declared-type declared-type)]

        [`(Let ,raw-name ,bound ,body)
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define binding-type (type-for-context bound-result))
         (elaborate-let-tail
          s raw-name binding-type #f bound-result
          (eq? (judgment-type bound-result) 'Never) body environment delta
          propositions boundaries
          `(,raw-name (#:ty ,(judgment-type bound-result) ,s))
          (judgment-core bound-result))]

        [`(Construct ,constructor (Types ,raw-types ...) ,fields ...)
         (define type-arguments
           (for/list ([type (in-list raw-types)])
             (match type
               [(resolved-type-argument resolved) resolved]
               [_ (resolve-annotation type delta s)])))
         (define result-type
           (constructor-result constructor type-arguments s))
         (elaborate-constructor constructor fields result-type
                                s
                                environment delta propositions boundaries)]

        [`(Construct ,_ ,_ ...)
         (reject s 'constructor-needs-expected-type)]

        [`(Eliminate ,scrutinee (,branches ...))
         (define scrutinee-result
           (synth scrutinee environment delta propositions boundaries))
         (define result
           (synth-eliminate scrutinee-result branches s
                            environment delta propositions boundaries
                            #:defer-fallthroughs
                            (deferred-when-fallthroughs expression)))
         (when (and (eq? (judgment-core-type result) 'Never)
                    (andmap
                     (λ (branch)
                       (define body (last (peel-branch branch)))
                       (and (pair? body) (eq? (first body) 'NarrativeExpr)))
                     branches))
           (reject s 'narrative-expression-needs-expected-type))
         result]

        [`(IfSome (,clauses ...) ,s_0)
         (define expected
           (if-some-result-type clauses s environment delta
                               propositions boundaries))
         (match-define `(Option ,T) expected)
         (check-if-some-explicit clauses s s_0 T expected
                                 environment delta propositions boundaries)]

        [`(TryBind (#:bind ,name ,name-span) ,right ,body)
         (define scrutinee-result
           (synth right environment delta propositions boundaries))
         (elaborate-try-bind s name name-span right scrutinee-result body #f
                             environment delta propositions boundaries)]

        [`(Eliminate ,_ ,_)
         (reject s 'eliminate-needs-expected-type)]

        [`(Return ,returned)
         (elaborate-boundary-escape
          expression s returned (nearest-function-boundary boundaries)
          environment delta propositions boundaries
          #:reachable? (current-escape-reachable?))]

        [`(Leave ,returned)
         (define boundary (nearest-expression-boundary boundaries))
         (unless boundary
           (reject s 'leave-outside-expression-boundary))
         (elaborate-boundary-escape
          expression s returned boundary environment delta propositions
          boundaries #:reachable? (current-escape-reachable?)
          #:leave-adapter
          (match boundary
            [`(ExpressionBoundary ,_ ,_ ,_ ,adapter) adapter]
            [_ #f]))]

        [`(NarrativeExpr ,body)
         (define expected
           (probe-narrative-type body environment delta propositions
                                 boundaries s))
         ;; probe と本番は別状態で走り、最終 Core は check 規則が作る。
         (check expression expected environment delta propositions boundaries)]

        [`(Recur ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                 (#:infer ,_) ,raw-row ,body ,continuation)
         (elaborate-recur-inferred
          s raw-function parameter-binders raw-parameter-types
          raw-row body continuation
          environment delta propositions boundaries)]

        [`(Recur ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                 ,raw-return-type ,raw-row ,body ,continuation)
         (elaborate-recur-annotated
          s raw-function parameter-binders raw-parameter-types
          (λ () (resolve-annotation raw-return-type delta s))
          raw-row body continuation
          environment delta propositions boundaries
          #:boundary? #f)]

        [`(Yield ,observed ,next)
         (define observed-result
           (synth observed environment delta propositions boundaries))
         (define next-result
           (parameterize
               ([current-escape-reachable?
                 (and (current-escape-reachable?)
                      (judgment-completes? observed-result))])
             (synth next environment delta propositions boundaries)))
         (define observed-type (type-for-context observed-result))
         (when (eq? observed-type 'Never)
           (reject s 'ill-typed #:phase 'typing))
         (define observed-core
           (if (owned-type? observed-type)
               `(OwnLeaf ,s ,(judgment-core observed-result))
               (judgment-core observed-result)))
         (propagate-context-never
          (judgment
           `(Yield ,s ,observed-core
                   ,(judgment-core next-result))
           (judgment-type next-result)
           (rows-union
            (list (judgment-row observed-result)
                  (judgment-row next-result)
                  `((Yield ,observed-type))))
           (judgment-core-type next-result)
           (judgment-normal-type next-result))
          (list observed-result next-result))]

        [`(Suspend ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (judgment `(Suspend ,s ,(judgment-core result))
                   (judgment-type result)
                   (row-union (judgment-row result) '(Suspend))
                   (judgment-core-type result)
                   (judgment-normal-type result))]

        [`(Move ,raw-name)
         (define name (peel-node raw-name))
         (define binding-type (lookup environment name))
         (cond
           [(owned-type? binding-type)
            (judgment `(Move ,s ,raw-name) binding-type '(Own))]
           [(and binding-type
                 (place-binding? environment name)
                 (resource-type? binding-type))
            (judgment `(Move ,s ,raw-name) binding-type '(Own))]
           [else (reject s 'move-non-owned name)])]

        ;; spec §7.7。Reassign は elaborate を越える最初の記憶域書き換えの形で
        ;; ある。target は binder なので judgment を作らず、生の綴りのまま運ぶ。
        [`(Reassign ,raw-name ,value)
         (define name (peel-node raw-name))
         (define declared-type (lookup environment name))
         (define key (flow-key-of environment name))
         (unless declared-type (reject s 'unbound-variable name))
         (unless (eq? (binding-mode-of environment name) 'mut)
           (reject s 'immutable-binding name))
         (unless key (reject s 'immutable-binding name))
         (define-values (result value-core _target-type value-type rhs-never?)
           (elaborate-mut-compatible-value
            s 'mut declared-type value environment delta propositions boundaries
            #:mismatch-key 'reassign-type-mismatch))
         (if (or rhs-never? (eq? (judgment-normal-type result) '⊥))
             (let ([current-type (flow-view environment name)])
               (judgment `(Reassign ,s ,raw-name (#:ty ,current-type ,s)
                                    ,(judgment-core result))
                         'Never (judgment-row result) 'Never '⊥))
             (let ()
               (define flow-type
                 (or (normalize-type value-type)
                     (reject s 'non-normalizable-type value-type)))
               (define pins (flow-pins key))
               (define pin (and (pair? pins) (first pins)))
               (when (and pin
                          (not (andmap (lambda (candidate)
                                         (type-equiv? candidate pin))
                                       pins)))
                 (reject s 'reassign-type-mismatch declared-type flow-type))
               (define final-type
                 (if (and pin (not (type-equiv? flow-type pin)))
                     pin flow-type))
               (define final-core
                 (if (type-equiv? flow-type final-type)
                     value-core
                     (rebuild-flow-value s value-core flow-type final-type
                                         propositions)))
               (unless (storage-ok? final-type)
                 (reject s 'mutable-callable-storage-requires-partial final-type))
               (flow-set-type! key final-type)
               (judgment `(Reassign ,s ,raw-name (#:ty ,final-type ,s) ,final-core)
                         'Unit
                         (row-union (judgment-row result) '(Mutation)))))]

        [`(Drop ,raw-name)
         #:when (let ([name (peel-node raw-name)])
                  (and (symbol? name)
                       (or (owned-type? (lookup environment name))
                           (and (place-binding? environment name)
                                (resource-type? (lookup environment name))))))
         (judgment `(Drop ,s (Move ,s ,raw-name)) 'Unit '(Own))]

        [`(Drop ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (define operand-type (type-for-context result))
         (unless (resource-type? operand-type)
           (reject s 'drop-non-owned operand-type))
         (propagate-context-never
          (judgment `(Drop ,s ,(judgment-core result))
                    'Unit
                    (row-union (judgment-row result) '(Own)))
          (list result))]

        [`(Curry ,function ,argument)
         (define raw-function-result
           (synth function environment delta propositions boundaries))
         (define function-never?
           (eq? (judgment-type raw-function-result) 'Never))
         (define-values (function-result wrap)
           (if function-never?
               (values raw-function-result #f)
               (normalize-owned-function
                raw-function-result (span-of function)
                (function-reserved-names function (list argument) environment))))
         (define-values (function-type function-owned?)
           (if function-never?
               (match (type-for-context function-result)
                 [`(Owned ,inner) (values inner #t)]
                 [type (values type #f)])
               (peel-owned-function-elab (judgment-type function-result)
                                         (judgment-core function-result))))
         (match function-type
           [`(NFn (,first-type ,remaining-types ...)
                  ,return-type ,latent-in ,latent-out ,obligations ,origin)
            (define argument-result
              (parameterize
                  ([current-escape-reachable?
                    (and (current-escape-reachable?)
                         (judgment-completes? function-result))])
                (check argument first-type
                       environment delta propositions boundaries)))
            (define argument-core
              (if (owned-type? first-type)
                  `(OwnLeaf ,s ,(judgment-core argument-result))
                  (judgment-core argument-result)))
            (define new-origin
              `(Derived ,origin (Curry ,(erase-origin-core argument-core))))
            (define bare-result
              `(NFn ,remaining-types ,return-type ,latent-in ,latent-out
                    ,obligations ,new-origin))
            (close-owned-function
             wrap
             (propagate-context-never
              (judgment
              `(Curry ,s ,(judgment-core function-result)
                      ,argument-core)
              (if (or function-owned? (resource-type? first-type))
                  `(Owned ,bare-result)
                  bare-result)
              (row-union (judgment-row function-result)
                         (judgment-row argument-result)))
              (list function-result argument-result)))]
           [_ (reject s 'curry-non-function function-type)])]

        [`(TypeMake ,spec)
         (unless (authorized? propositions)
           (reject s 'missing-type-narrative-capability))
         (match-define (list type-form kind)
           (interpret-spec spec delta s))
         (judgment
          `(TypeRep ,s (Derived (Reserved o-type-narrative)
                             (Make ,type-form))
                    ,type-form
                    ,kind)
          `(TypeInfo ,kind)
          '(Compile))]

        [`(LetType ,name (TypeMake ,_ ,spec) ,body)
         (unless (authorized? propositions)
           (reject s 'missing-type-narrative-capability))
         (match-define (list type-form kind)
           (interpret-spec spec delta s))
         (define representation
           `(TypeRep (Derived (Reserved o-type-narrative)
                              (Make ,type-form))
                     ,type-form
                     ,kind))
         (define body-result
           (synth body
                  environment
                  (cons (list name representation) delta)
                  propositions
                  boundaries))
         (judgment (judgment-core body-result)
                   (judgment-type body-result)
                   (row-union (judgment-row body-result) '(Compile)))]

        [_ (reject s 'cannot-synthesize expression)]))

    ;; 合成の結果を期待型と比べる。汎用の _ 節と E-Lambda-Infer-Check が共有する。
    (define (check-against-expected result expected s propositions)
      (unless (or (type-compatible? (judgment-type result) expected propositions)
                  (mut-union-rebuildable?
                   (judgment-type result) expected
                   (initial-candidate-context propositions) propositions))
        (reject s 'type-mismatch expected (judgment-type result)))
      (if (eq? (judgment-type result) 'Never)
          (judgment (judgment-core result) 'Never (judgment-row result)
                    'Never (judgment-normal-type result))
          (let ()
            (define-values (core actual-type)
              (discharge-remainder (judgment-core result)
                                   (judgment-core-type result)
                                   expected s propositions))
            (match (narrowing-kind actual-type expected propositions)
              ['ok (void)]
              [`(drop-obligation ,_ ,_)
               (reject s 'owned-narrowing-needs-proof expected
                       actual-type)]
              [_ (unless (mut-union-rebuildable?
                          actual-type expected
                          (initial-candidate-context propositions) propositions)
                   (reject s 'owned-narrowing-rejected expected actual-type))])
            (define-values (converted core-type)
              (convert core actual-type expected s propositions))
            (judgment converted expected (judgment-row result) core-type))))

    ;; Rec の欄を Record 型へ直接 check できる形かを返す。
    (define (record-literal-member? raw-fields expected)
      (match expected
        [`(Record ,expected-fields)
         (define written
           (map (λ (field) (peel-lbl (first field))) raw-fields))
         (define omitted (omitted-optional-labels written expected-fields))
         (or (and (= (length written) (length expected-fields))
                  (equal? (sort written symbol<?)
                          (sort (map first expected-fields) symbol<?)))
             (and omitted (pair? omitted)))]
        [_ #f]))

    (define (check-rec-against-union expression raw-fields expected s
                                     environment delta propositions boundaries)
      (define members (union-members expected))
      (define context (initial-candidate-context propositions))
      (define (trial thunk)
        (call-with-restored-state
         (λ ()
           (with-handlers ([exn:fail:elab? (λ (_) #f)])
             (thunk)))))
      (define synthesized-result
        (trial (λ () (synth expression environment delta propositions
                            boundaries))))
      (define synthesized
        (and synthesized-result (judgment-type synthesized-result)))
      (define candidate-members
        (if synthesized
            (filter (lambda (candidate)
                      (mut-field-candidate? synthesized candidate propositions))
                    members)
            members))
      (define exact
        (and synthesized
             (for/first ([candidate (in-list candidate-members)]
                         #:when (type-equiv? candidate synthesized))
               candidate)))
      (define first-stage
        (if exact
            (list exact)
            (if synthesized
                (filter (λ (candidate)
                          (identity-fit? synthesized candidate context
                                         propositions))
                        candidate-members)
                '())))
      (define (normal-path)
        (check-against-expected
         (synth expression environment delta propositions boundaries)
         expected s propositions))
      ;; 一意な候補を通常経路へ戻すと、後段の Union 注入が別候補を選びうる。
      (match first-stage
        [(list candidate)
         (define result
           (check expression candidate environment delta
                  propositions boundaries))
         (judgment
          `(UnionInject ,s (#:ty ,expected ,s)
                        (#:ty ,candidate ,s)
                        ,(judgment-core result))
          expected (judgment-row result) expected)]
        [(list _first _second ...)
         (reject s 'ambiguous-union-member expected synthesized first-stage)]
        [_
         (define-values (tier1 tier2 tier3 tier4b)
           (if synthesized
               (union-member-tiers synthesized candidate-members s propositions)
               (values '() '() '() '())))
         (define literal-results
           (filter
            values
            (for/list ([candidate (in-list candidate-members)]
                       #:when (record-literal-member? raw-fields candidate))
              (define result
                (trial
                 (λ ()
                   (check expression candidate environment delta
                          propositions boundaries))))
              (and result (list candidate result)))))
         (define literal-safe
           (for/list ([entry (in-list literal-results)]
                      #:unless (core-has-remainder-drop?
                                (judgment-core (second entry))))
             (first entry)))
         (define literal-lossy
           (for/list ([entry (in-list literal-results)]
                      #:when (core-has-remainder-drop?
                              (judgment-core (second entry))))
             (first entry)))
         (define (without-earlier candidates earlier)
           (remove-duplicates
            (filter (λ (candidate)
                      (not (ormap (λ (prior)
                                    (type-equiv? candidate prior))
                                  earlier)))
                    candidates)
            type-equiv?))
         (define-values (tier1* tier2* tier3* tier4a* tier4b*)
           (let* ([tier1* (remove-duplicates tier1 type-equiv?)]
                  [tier2* (without-earlier
                           (append tier2 literal-safe) tier1*)]
                  [prior2 (append tier1* tier2*)]
                  [tier3* (without-earlier tier3 prior2)]
                  [prior3 (append prior2 tier3*)]
                  [tier4a* (without-earlier literal-lossy prior3)]
                  [prior4a (append prior3 tier4a*)]
                  [tier4b* (without-earlier tier4b prior4a)])
             (values tier1* tier2* tier3* tier4a* tier4b*)))
         (define selected-tier
           (for/first ([tier (in-list
                              (list tier1* tier2* tier3* tier4a* tier4b*))]
                       #:when (pair? tier))
             tier))
         (match selected-tier
           [#f (normal-path)]
           [(list candidate)
            (define direct-literal?
              (ormap (λ (entry)
                       (type-equiv? candidate (first entry)))
                     literal-results))
            (if direct-literal?
                (let* ([result
                        (check expression candidate environment delta
                               propositions boundaries)]
                       [injected
                        `(UnionInject ,s (#:ty ,expected ,s)
                                      (#:ty ,candidate ,s)
                                      ,(judgment-core result))])
                  (judgment
                   injected
                   expected (judgment-row result) expected))
                (normal-path))]
           [candidates
            (reject s 'ambiguous-union-member expected
                    (or synthesized expected) candidates)])]))

    (define (check expression expected environment delta propositions boundaries)
      (define s (span-of expression))
      (match (peel-node expression)
        [`(BlockBody ,inner)
         (check-when-arm-block-body (block-body-span expression) inner expected environment delta
                                    propositions boundaries)]

        [`(Let (,raw-name ,binding-mode) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
        (define bound-result
          (synth bound environment delta propositions boundaries))
         (define actual-type (type-for-context bound-result))
         (define binding-type
           (bind-with-mode s binding-mode actual-type actual-type
                           propositions))
         (elaborate-let-tail
          s raw-name binding-type binding-mode bound-result
          (eq? (judgment-type bound-result) 'Never) body environment
          delta propositions boundaries
          `(,raw-name ,binding-mode (#:ty ,binding-type ,(span-of bound)))
          (judgment-core bound-result)
          #:expected expected)]

        [`(Let (,raw-name ,binding-mode ,raw-type) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
         (define-values (bound-result bound-core declared-type binding-type
                         bound-never?)
           (elaborate-annotated-let-bound
            s binding-mode raw-type bound environment delta propositions
            boundaries))
         (elaborate-let-tail
          s raw-name binding-type binding-mode bound-result bound-never?
          body environment
          delta propositions boundaries
          `(,raw-name ,binding-mode (#:ty ,declared-type
                                         ,(wrapper-span raw-type)))
          bound-core
          #:declared-type declared-type
          #:expected expected)]

        [`(Let ,raw-name ,bound ,body)
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define binding-type (type-for-context bound-result))
         (elaborate-let-tail
          s raw-name binding-type #f bound-result
          (eq? (judgment-type bound-result) 'Never) body environment delta
          propositions boundaries
          `(,raw-name (#:ty ,binding-type ,s))
          (judgment-core bound-result)
          #:expected expected)]

        [`(Construct ,constructor (Types ,_ ...) ,_ ...)
         (define result
           (synth expression environment delta propositions boundaries))
         (if (eq? (judgment-type result) 'Never)
             (check-against-expected result expected s propositions)
             (let ([result-type (judgment-type result)])
               (unless (or (type-compatible? (judgment-type result) expected
                                             propositions)
                           (mut-union-rebuildable?
                            result-type expected
                            (initial-candidate-context propositions) propositions))
                 (reject s 'type-mismatch expected result-type))
               (let-values ([(core actual-type)
                             (discharge-remainder
                              (judgment-core result)
                              (judgment-core-type result) expected s propositions)])
                 (match (narrowing-kind actual-type expected propositions)
                   ['ok (void)]
                   [`(drop-obligation ,_ ,_)
                    (reject s 'owned-narrowing-needs-proof expected
                            actual-type)]
                   [_ (unless (mut-union-rebuildable?
                               actual-type expected
                               (initial-candidate-context propositions) propositions)
                        (reject s 'owned-narrowing-rejected expected actual-type))])
                 (let-values ([(converted core-type)
                               (convert core actual-type expected s propositions)])
                   (judgment converted expected (judgment-row result) core-type)))))]

        [`(Construct ,constructor ,fields ...)
         (elaborate-constructor constructor fields expected
                                s
                                environment delta propositions boundaries)]

        [`(Eliminate ,scrutinee (,branches ...))
         (define scrutinee-result
           (synth scrutinee environment delta propositions boundaries))
         (define scrutinee-type (type-for-context scrutinee-result))
         (define deferred
           (deferred-when-fallthroughs expression))
         (cond
           [(or (root-owned-union? scrutinee-type)
                (union-type? scrutinee-type))
            (union-eliminate scrutinee-result branches expected s
                             environment delta propositions boundaries
                             #:defer-fallthroughs deferred)]
           [(ormap member-pattern? branches)
            (reject s 'non-union-eliminate #:phase 'typing scrutinee-type)]
           [else
            (check-eliminate scrutinee branches expected s
                             environment delta propositions boundaries
                             #:scrutinee-result scrutinee-result
                             #:defer-fallthroughs deferred)])]

        [`(IfSome (,clauses ...) ,s_0)
         (match (normalize-type expected)
           [`(Option ,T)
            (check-if-some-explicit clauses s s_0 T expected
                                    environment delta propositions boundaries)]
           [_
            (check-against-expected
             (synth expression environment delta propositions boundaries)
             expected s propositions)])]

        [`(TryBind (#:bind ,name ,name-span) ,right ,body)
         (define scrutinee-result
           (synth right environment delta propositions boundaries))
         (elaborate-try-bind s name name-span right scrutinee-result body
                             expected environment delta propositions boundaries)]

        [`(NarrativeExpr ,body)
         (define boundary (fresh-boundary))
         (define leave-adapter
           (if-some-boundary-adapter body expected environment))
         (define entry-flow (flow-snapshot))
         (define boundary-keys (live-flow-keys environment))
         (define escapes (make-hasheq))
         (define deferred
           (and (match (peel-node body) [`(Eliminate ,_ ,_) #t] [_ #f])
                (box '())))
         (define body-result
           (parameterize
               ([current-boundary-escapes escapes]
                [current-deferred-when-fallthroughs
                 (and deferred (cons body deferred))])
             (check body expected environment delta propositions
                    (cons `(ExpressionBoundary ,boundary ,expected ,s
                                               ,leave-adapter)
                          boundaries))))
         (define normal-exit (flow-snapshot))
         (define fallthrough-result-type
           (or (option-adapter-payload-type leave-adapter) expected))
         (when (and deferred
                    (pair? (unbox deferred))
                    (not (equal? (normalize-type fallthrough-result-type) 'Unit)))
           (reject (first-when-fallthrough (unbox deferred))
                   'when-arm-missing-return))
         (define pending (hash-ref escapes boundary '()))
         (define branches
           (cons (flow-branch environment body-result normal-exit #f)
                 (for/list ([escape (in-list pending)])
                   (flow-branch environment
                                (pending-escape-payload-result escape)
                                (pending-escape-snapshot escape)
                                escape))))
         (define-values (joined-results _joined-flow)
           (join-branch-flows s environment entry-flow branches propositions
                              #:live-keys boundary-keys))
         (for ([escape (in-list pending)]
               [result (in-list (cdr joined-results))])
           (set-box! (pending-escape-cell escape) (judgment-core result)))
         (define resolved-body-core
           (resolve-pending-escapes
            (judgment-core (first joined-results))))
         (define boundary-row
           (rows-union
            (cons (judgment-row body-result)
                  (map judgment-row joined-results))))
         (define own-return `((Return ,boundary ,expected)))
         (define propagate?
           (and (eq? (judgment-type body-result) 'Never)
                (null? pending)))
         (judgment
          `(Handle ,s (Return ,boundary (#:ty ,expected ,s))
                   (,s (#:bind return-value ,s) ->
                       (#:var return-value ,s))
                   (Scope ,s () ,resolved-body-core))
          (if propagate? 'Never expected)
          (row-difference boundary-row own-return)
          (if propagate? 'Never expected)
          (if propagate?
              (judgment-normal-type body-result)
              expected))]

        [`(Rec (,raw-fields ...))
         #:when (record-literal-member? raw-fields expected)
         (define raw-labels (map first raw-fields))
         (define written-labels (map peel-lbl raw-labels))
         (match-define `(Record ,expected-fields) expected)
         (define omitted
           (omitted-optional-labels written-labels expected-fields))
         (define fields
           (for/list ([field (in-list raw-fields)])
             (match-define `(,raw-label ,mutability ,field-expression) field)
             (list (peel-lbl raw-label) mutability field-expression)))
         (unless (field-row-unique? fields)
           (reject s 'duplicate-record-label fields))
         (define field-reachable? (current-escape-reachable?))
         (define field-results
           (for/list ([field (in-list fields)])
             (match-define `(,label ,mutability ,field-expression) field)
             (define field-type (second (assq label expected-fields)))
             (define result
               (parameterize ([current-escape-reachable? field-reachable?])
                 (check field-expression field-type environment delta propositions
                        boundaries)))
             (set! field-reachable?
                   (and field-reachable? (judgment-completes? result)))
             (when (and (not (eq? (judgment-normal-type result) '⊥))
                        (owned-type? (type-for-context result)))
               (reject s 'owned-record-field label))
             (list label mutability result)))
         (define absent-fields
           (for/list ([field (in-list expected-fields)]
                      #:when (memq (first field) (or omitted '())))
             (match-define (list label field-type mutability 'opt) field)
             (list (list '#:lbl label s)
                   mutability
                   (list 'Absent s (list '#:ty field-type s)))))
         (define rec-result
           (judgment
            `(Rec ,s
              ,(append
                (for/list ([field (in-list field-results)]
                           [raw-label (in-list raw-labels)])
                  (match-define (list _ mutability result) field)
                  `(,raw-label ,mutability ,(judgment-core result)))
                absent-fields))
            `(Record
              ,(append
                (for/list ([field (in-list field-results)])
                  (match-define (list label mutability result) field)
                  `(,label ,(type-for-context result) ,mutability))
                (for/list ([field (in-list expected-fields)]
                           #:when (memq (first field) (or omitted '())))
                  `(,(first field) ,(second field) ,(third field) opt))))
            (rows-union
             (for/list ([field (in-list field-results)])
               (judgment-row (third field))))
            `(Record
              ,(append
                (for/list ([field (in-list field-results)])
                  (match-define (list label mutability result) field)
                  `(,label ,(judgment-core-type result) ,mutability))
                (for/list ([field (in-list expected-fields)]
                           #:when (memq (first field) (or omitted '())))
                  `(,(first field) ,(second field) ,(third field) opt))))
            expected))
         (check-against-expected
          (propagate-context-never
           rec-result
           (map third field-results))
          expected s propositions)]

        [`(Rec (,raw-fields ...))
         #:when (match expected [`(Union ,_ ,_) #t] [_ #f])
         (check-rec-against-union expression raw-fields expected s
                                  environment delta propositions boundaries)]

        [`(Fn ((,parameter-binders ,raw-parameter-types) ...)
              ,raw-return-type ,raw-row ,body)
         #:when (or (inferred? raw-return-type)
                    (ormap inferred? raw-parameter-types)
                    (inferred-row? raw-row))
         ;; σ と σi は Typed Core の型なので、resolve-annotation には通さない。
         (define omitted-parameters?
           (ormap inferred? raw-parameter-types))
         (define parameters (map peel-bind parameter-binders))
         (when (and omitted-parameters? (check-duplicates parameters))
           (reject s 'duplicate-parameter parameters))
         (define infer-span
           (for/first ([type (in-list raw-parameter-types)]
                       #:when (inferred? type))
             (second type)))
         (define function-type
           (match expected
             [`(Owned ,inner) inner]
             [_ expected]))
         (match function-type
           [`(NFn ,parameter-types ,return-type ,_ ,expected-row . ,_)
            (when (and omitted-parameters?
                       (not (= (length parameter-types)
                               (length raw-parameter-types))))
              (reject infer-span 'parameter-type-not-inferable 'arity-mismatch))
            (check-against-expected
             (elaborate-annotated-fn
              s parameter-binders raw-parameter-types
              (if (inferred? raw-return-type)
                  (λ () return-type)
                  (λ () (resolve-annotation raw-return-type delta s)))
              raw-row body environment delta propositions boundaries
              #:expected-parameter-types
              (and omitted-parameters? parameter-types)
              #:inherited-row
              (and (inferred-row? raw-row) expected-row)
              #:return-span
              (and (not (inferred? raw-return-type))
                   (nearest-span raw-return-type s)))
             expected s propositions)]
           [_
            (check-against-expected
             (synth expression environment delta propositions boundaries)
             expected s propositions)])]

        [_
         (check-against-expected
          (synth expression environment delta propositions boundaries)
          expected s propositions)]))

    (define result (synth expression '() Δ0 Π0 '()))
    (list (uniquify-binders (judgment-core result))
          (judgment-type result)
          (judgment-row result)
          (reverse reversed-callables)))))

;; reject は primary-span を必須の第 1 引数に取る。渡し忘れと引数の逆順、
;; registry に無い reason を、どれも実行時に落として fail-loud にする。
;; reject は provide しないため、内部から検査する。
(module+ test
  (require rackunit)

  (define ok-span '(#:span src 3 7))

  (define synthetic-span
    (span-through-end '(#:span #:synthetic 20 20)
                      '(#:span #:synthetic 14 14)))
  (check-true (span-ok? synthetic-span))
  (check-equal? synthetic-span '(#:span #:synthetic 14 20))
  (define reversed-source-span
    (span-through-end '(#:span src 20 20) '(#:span src 14 14)))
  (check-false (span-ok? reversed-source-span))
  (check-equal? reversed-source-span '(#:span src 20 14))

  ;; primary-span を渡し忘れると reason が span の位置へ入る。
  (check-exn #px"arity mismatch"
             (lambda () (reject 'unknown-type)))

  ;; primary-span と reason を逆順に渡した場合も同じ検査で落ちる。
  (check-exn #px"span として妥当でない"
             (lambda () (reject 'unknown-type ok-span)))

  ;; 座標が逆順の span は span-ok? を満たさない。
  (check-exn #px"span として妥当でない"
             (lambda () (reject '(#:span src 9 2) 'unknown-type)))

  ;; registry に無い reason は汎用 code へ落とさず error にする。
  (check-exn #px"registry に無い reason"
             (lambda ()
               (reject ok-span 'no-such-reason)))

  ;; 正しい呼び出しは exn:fail:elab を投げ、details と既定 related を保つ。
  (define failure
    (with-handlers ([exn:fail:elab? values])
      (reject ok-span 'unknown-type 'Foo)))
  (check-pred exn:fail:elab? failure)
  (check-equal? (exn:fail:elab-primary-span failure) ok-span)
  (check-equal? (exn:fail:elab-reason failure) 'unknown-type)
  (check-equal? (exn:fail:elab-details failure) '(Foo))
  (check-equal? (exn:fail:elab-related failure) '())

  ;; 3 つの details を Diagnostic の 2 欄へ落とさず保持する。
  (define ambiguous-failure
    (with-handlers ([exn:fail:elab? values])
      (reject ok-span 'ambiguous-union-member 'Expected 'Actual '(A B))))
  (define ambiguous-diagnostic
    (elab-failure->diagnostic ambiguous-failure (hash)))
  (check-equal? (diagnostic-expected ambiguous-diagnostic) 'Expected)
  (check-equal? (diagnostic-found ambiguous-diagnostic) '(Actual (A B)))

  (define diagnostic-before-related
    (match (elab '(Fn () Bool () (Return 1)))
      [`(err ,diagnostic) diagnostic]
      [other (error 'elaborate-test "診断を期待したが成功した: ~s" other)]))
  (check-equal?
   diagnostic-before-related
   (diagnostic "E-TYP-012" 'error 'TYP
               "型が期待と一致しない" "型が期待と一致しない"
               '(#:span #:synthetic 4 4)
               '() '() '() 'Bool 'Int
               '((surface synthetic-span (#:span #:synthetic 4 4)))
               '() #f #f '() '() #f))

  (define related-failure
    (with-handlers ([exn:fail:elab? values])
      (reject ok-span 'unknown-type
              #:related (list (list 'return-boundary '(#:span src 2 3) "境界")))))
  (check-equal? (exn:fail:elab-details related-failure) '())
  (check-equal? (diagnostic-related
                 (elab-failure->diagnostic related-failure (hash)))
                (list (list 'return-boundary '(#:span src 2 3) "境界"))))

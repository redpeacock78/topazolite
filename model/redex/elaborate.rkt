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
         "type-equiv.rkt"
         "type-shape.rkt"
         "uniquify.rkt"
         "ucore.rkt"
         (only-in "typing.rkt"
                  tag-upper-bound
                  tag-types-upper-bound
                  tag-bound-failure?
                  branch-types-upper-bound
                  merge-record-types/impl)
         "validators.rkt")

(provide UCore
         elab
         mentions-return?
         ;; c2b1 spec §4.1 の欄の型の合流とその単体試験に使う。
         row005-join)

(struct judgment (core type row core-type)
  #:transparent
  #:constructor-name make-judgment/raw
  #:omit-define-syntaxes)

;; 既存の三引数の構築は judgment の型を Core の型として使う。
;; check の一部だけ、実際に生成した Core の型を明示する。
(define judgment
  (case-lambda
    [(core type row) (make-judgment/raw core type row type)]
    [(core type row core-type)
     (make-judgment/raw core type row core-type)]))
(struct exn:fail:elab exn:fail (primary-span reason details) #:transparent)

;; primary-span は第 1 引数であり既定値を持たない。既定値を持たせると渡し忘れ
;; が黙って通り、DIA-002 の契約が静かに崩れる。span-ok? と registry の検査で
;; 渡し忘れ、引数の逆順、registry に無い reason を実行時に落とす。
(define (reject primary-span reason . details)
  (unless (span-ok? primary-span)
    (error 'reject "span として妥当でない値を primary-span に受けた: ~s"
           primary-span))
  (unless (diagnostic-code-of 'elaborate reason)
    (error 'reject "registry に無い reason である: ~s" reason))
  (raise
   (exn:fail:elab
    (format "elaboration failed: ~a" reason)
    (current-continuation-marks)
    primary-span
    reason
    details)))

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
          'reassign-type-mismatch)
      (list expected actual))
     (values expected actual)]
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
    [`(#:ef ,labels ,_) (and (list? labels) (memq 'Return labels) #t)]
    [`(,(or '#:ty '#:var '#:bind '#:lit) ,_ ...) #f]
    [(? list?) (ormap mentions-return? node)]
    [_ #f]))

;; P1c2b。modes を渡すと 3 要素 entry を作る。
;; place-flags の真の entry は c1c1 の P に属する Let 束縛である。
;; 非 Let binder は place-flags を渡さず、同名の外側 entry を遮蔽する。
(define (extend environment names types [modes #f] [place-flags #f])
  (append
   (for/list ([name (in-list names)]
              [type (in-list types)]
              [index (in-naturals)])
     (define mode (and modes (list-ref modes index)))
     (define place? (and place-flags (list-ref place-flags index)))
     (cond
       [place? (list name type mode #t)]
       [modes (list name type mode)]
       [else (list name type)]))
   environment))

;; P1c2b。mode を持つ entry から binding mode を返す。
(define (binding-mode-of environment name)
  (match (assoc name environment)
    [(list _ _ mode _ ...) mode]
    [_ #f]))

(define (place-binding? environment name)
  (match (assoc name environment)
    [(list _ _ _ #t) #t]
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

(define (check-recur-body-gate s function parameters body environment
                               callables declared-row)
  ;; 分類器は型環境だけを使うため、elaborate の束縛 metadata を渡さない。
  (define classifier-environment
    (for/list ([entry (in-list environment)])
      (match entry
        [(list name type _ ...) (list name type)]
        [_ entry])))
  (when (and (eq? (classify-recur-body function parameters body
                                       classifier-environment callables)
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

;; OWN-004。残余の drop が要る場合だけ Proof を挿入し、先に Owned 残余を
;; 取り除いた型を後続の通常の convert へ渡す。reject は呼び出し側の既存の
;; 判定順序に委ねる。
(define (discharge-remainder core actual expected s propositions)
  (match (narrowing-kind actual expected propositions)
    [`(drop-obligation ,_ ,_)
     (define target (remainder-target-type actual expected))
     (unless target
       (error 'discharge-remainder
              "drop-obligation に runtime removal shape がない: ~s => ~s"
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

(define (nearest-boundary boundaries)
  (and (pair? boundaries) (car boundaries)))

(define (resolve-declaration-row raw-row delta boundaries inherited-span)
  (define span (nearest-span raw-row inherited-span))
  (define row (peel-ef raw-row))
  (if (eq? row '#:infer)
      '()
      (normalize-row
       (for/list ([label (in-list row)])
         (match label
           ['Return
            (match (nearest-boundary boundaries)
              [`(,_ ,_ #:infer)
               ;; SUR-008。合成位置で戻り型が未定の間、宣言 row の Return は解決できない。
               (reject span 'return-type-not-inferable 'return-in-synth)]
              [`(,_ ,boundary (#:probe ,_))
               ;; SUR-015（spec §6.2）。下見では Return row の型を仮置きする。
               `(Return ,boundary Never)]
              [`(,_ ,boundary ,type) `(Return ,boundary ,type)]
              [_ (reject span 'return-label-outside-boundary)])]
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
       (unless (type-compatible? actual-type declared-type propositions)
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
    [_ (reject s 'owned-narrowing-rejected binding-type actual-type)])
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
           [`(,_ (,parameters ...) -> ,body)
            (set-subtract (free-vars/erased body) (list->set parameters))]
           [_ (set)]))))]
    [`(Return ,body) (free-vars/erased body)]
    [`(NarrativeExpr ,body) (free-vars/erased body)]
    [`(Recur ,function ((,parameters ,_) ...) ,_ ,_ ,body ,continuation)
     (set-union
      (set-subtract (free-vars/erased body)
                    (list->set (cons function parameters)))
      (set-remove (free-vars/erased continuation) function))]
    [`(FnDecl ,function ((,parameters ,_) ...) ,_ ,_ ,body ,continuation)
     (set-union
      (set-subtract (free-vars/erased body)
                    (list->set (cons function parameters)))
      (set-remove (free-vars/erased continuation) function))]
    [`(Yield ,observed ,next)
     (set-union (free-vars/erased observed) (free-vars/erased next))]
    [`(Suspend ,body) (free-vars/erased body)]
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
  (define-values (expected found)
    (distribute-details reason (exn:fail:elab-details failure)))
  (diagnostic-of 'elaborate reason
                   #:primary-span (exn:fail:elab-primary-span failure)
                   #:expected expected
                   #:found found
                   #:expansion-context expansion-context))

(define (elab raw-expression #:expansion-context [expansion-context (hash)])
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

    (define (fresh-boundary)
      (define boundary
        (string->symbol (format "boundary~a" boundary-counter)))
      (set! boundary-counter (add1 boundary-counter))
      boundary)

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
    (define (fresh-union-name)
      (let next ()
        (define candidate
          (string->symbol (format "union~a" union-counter)))
        (set! union-counter (add1 union-counter))
        (if (set-member? union-reserved candidate) (next) candidate)))

    ;; 候補への再構築を試す間に生名を消費しても、本番の変換名へ影響
    ;; させない。試行で使う項は破棄するため、変換が参照を埋め込める
    ;; span 付き Core 変数を渡す。
    (define (rebuild-reachable? actual member kind s propositions)
      (define saved-union union-counter)
      (define saved-owned owned-counter)
      (dynamic-wind
       void
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
                (define-values (_probe-core _probe-type)
                  (convert probe-core probe-type member s propositions))
                #t)))
       (lambda ()
         (set! union-counter saved-union)
         (set! owned-counter saved-owned))))

    ;; 成分の位置でなく損失の種類で優先順位を決める。試行による生名の消費は
    ;; rebuild-reachable? が復元する。
    (define (union-member-tiers actual members s propositions)
      (define context (initial-candidate-context propositions))
      (define analyses
        (for/list ([member (in-list members)])
          (define kind (narrowing-kind actual member propositions))
          (define target
            (match kind
              [`(drop-obligation ,_ ,_)
               (remainder-target-type actual member)]
              [_ #f]))
          (list member kind (tag-compat? actual member context) target)))
      (define tier1
        (for/list ([analysis (in-list analyses)]
                   #:when (and (third analysis)
                               (eq? (second analysis) 'ok)))
          (first analysis)))
      (define tier2
        (for/list ([analysis (in-list analyses)]
                   #:when (and (not (third analysis))
                               (eq? (second analysis) 'ok)
                               (rebuild-reachable? actual (first analysis) 'ok
                                                   s propositions)))
          (first analysis)))
      (define tier3
        (for/list ([analysis (in-list analyses)]
                   #:when (and (match (second analysis)
                                  [`(drop-obligation ,_ ,_) #t]
                                  [_ #f])
                               (fourth analysis)
                               (tag-compat? (fourth analysis) (first analysis)
                                            context)))
          (first analysis)))
      (define tier4
        (for/list ([analysis (in-list analyses)]
                   #:when (and (match (second analysis)
                                  [`(drop-obligation ,_ ,_) #t]
                                  [_ #f])
                               (fourth analysis)
                               (not (tag-compat? (fourth analysis)
                                                 (first analysis) context))
                               (rebuild-reachable? actual (first analysis)
                                                   'drop-obligation s
                                                   propositions)))
          (first analysis)))
      (values tier1 tier2 tier3 tier4))

    ;; 完全一致の後、損失のない成分を優先する。
    (define (choose-union-member actual expected s propositions
                                 #:no-member-key [no-member-key 'type-mismatch])
      (define members (union-members expected))
      (define exact
        (for/first ([member (in-list members)]
                    #:when (type-equiv? member actual))
          member))
      (cond
        [exact exact]
        [else
         (define-values (tier1 tier2 tier3 tier4)
           (union-member-tiers actual members s propositions))
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
                          #:no-member-key [no-member-key 'type-mismatch])
      (define member
        (choose-union-member actual expected s propositions
                             #:no-member-key no-member-key))
      (define context (initial-candidate-context propositions))
      (define-values (discharged actual*)
        (discharge-remainder core actual member s propositions))
      (define payload
        (if (tag-compat? actual* member context)
            discharged
            (let-values ([(converted _type)
                          (convert discharged actual* member s propositions)])
              converted)))
      `(UnionInject ,s (#:ty ,expected ,s) (#:ty ,member ,s) ,payload))

    (define (record-row-of type)
      (match type [`(Record ,row) row] [_ #f]))

    ;; P2m2b spec §3.1。(values Core 変換後の型) を返すか、その位置で拒否する。
    (define (convert core actual expected s propositions #:entry? [entry? #f])
      (define actual* (normalize-type actual))
      (define expected* (normalize-type expected))
      (define context (initial-candidate-context propositions))
      (define actual-union?
        (match actual* [`(Union ,_ ,_) #t] [_ #f]))
      (define expected-union?
        (match expected* [`(Union ,_ ,_) #t] [_ #f]))
      (cond
        [(tag-compat? actual* expected* context)
         (values core actual*)]
        [(and expected-union? (not actual-union?))
         (values (union-inject core actual* expected* s propositions)
                 expected*)]
        [actual-union?
         (decompose core actual* expected* s propositions #:entry? entry?)]
        [(and (record-row-of actual*) (record-row-of expected*))
         (rebuild-record core (record-row-of actual*) (record-row-of expected*)
                         s propositions)]
        [else (reject s 'type-mismatch expected actual)]))

    ;; c2b1 spec §5.1。枝を ROW-005 の上界へそろえ、実際に作り直した Core の型から
    ;; Core の合流型を求める。Never の枝は Core と同じく上界から除く。
    (define (merge-branches cores types s propositions)
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

    (define (decompose core actual expected s propositions #:entry? [entry? #f])
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
      (define (eliminate bodies)
        `(UnionEliminate ,s ,core
           ,(for/list ([branch (in-list branches)]
                       [body (in-list bodies)])
              (match-define (list member name _alias) branch)
              `(,s (#:ty ,member ,s) (#:bind ,name ,s) -> ,body))))
      (define (resource-branch-body member name alias body)
        (if entry?
            body
            (if alias
                `(Scope ,s ()
                        (Let ,s ((#:bind ,alias ,s) let (#:ty ,member ,s))
                             ,(reference name)
                             ,body))
                body)))
      (define (wrap-reference mode type bound [move? #f])
        (define name (fresh-union-name))
        (define ref (reference name))
        `(Let ,s ((#:bind ,name ,s) ,mode (#:ty ,type ,s))
              ,bound
              ,(if move? `(Move ,s ,ref) ref)))
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
           `(Record ,(append expected-row residual)))
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
               (if (and alias (not entry?)) `(Move ,s ,ref) (reference name)))
             (define converted
               (if (eq? member 'Never)
                   consumed-ref
                   (let* ([_member-narrowing
                           ;; expected 欄の内側にある Owned の残余も失わないよう、
                           ;; member から W_k への OWN-004 を変換より先に検査する。
                           (match (narrowing-kind member wrapped-type propositions)
                             ['ok (void)]
                             [`(drop-obligation ,_ ,_)
                              (reject s 'owned-narrowing-needs-proof wrapped-type
                                      member)]
                             [_ (reject s 'owned-narrowing-rejected wrapped-type
                                        member)])]
                          [_narrowing-check
                           (match (narrowing-kind wrapped-type upper propositions)
                             ['ok (void)]
                             [`(drop-obligation ,_ ,_)
                              (reject s 'owned-narrowing-needs-proof upper
                                      wrapped-type)]
                             [_ (reject s 'owned-narrowing-rejected upper
                                        wrapped-type)])]
                          [source
                           (if (tag-compat? member expected context)
                               consumed-ref
                               (let-values ([(rebuilt _type)
                                             (convert consumed-ref member expected s
                                                      propositions
                                                      #:entry? entry?)])
                                 rebuilt))]
                          [wrapped
                           (wrap-reference
                            'let expected source
                            (and (not entry?)
                                 (resource-type? wrapped-type)))])
                     (if (type-equiv? wrapped-type upper)
                         wrapped
                         (let-values ([(rebuilt _type)
                                       (convert wrapped wrapped-type upper s
                                                propositions #:entry? entry?)])
                           rebuilt)))))
             (resource-branch-body member name alias converted)))
          upper)]
        [_
         (define bodies
           (for/list ([branch (in-list branches)])
             (match-define (list member name alias) branch)
             (define-values (body _type)
               (convert (if alias
                            `(Move ,s ,(reference alias))
                            (reference name))
                        member expected s propositions #:entry? entry?))
             (resource-branch-body member name alias body)))
         ;; c2 spec §3。Union の成分は root が Owned でないので、root Owned の
         ;; expected への成分の convert は手前で落ち、ここへは届かない。
         (when (owned-type? expected)
           (reject s 'invalid-resolved-type expected))
         (values
          (wrap-reference 'const expected (eliminate bodies)
                          (and (not entry?) (resource-type? expected)))
          expected)]))

    ;; P2m2c spec §5.1。expected の欄ごとに作り直し、変換か印の変更が要る欄だけを
    ;; RecRewrite の entry にする。欄を物理的に落とさないので、出力の型は残余を保つ。
    (define (rebuild-record core actual-row expected-row s propositions)
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
             (define mark-changed? (not (eq? actual-mark expected-mark)))
             ;; entry を作る欄でだけ生名を取り、恒等の欄で counter を進めない。
             (define (identity-entry)
               (define binder (fresh-union-name))
               (list (list label binder actual-type expected-mark
                           actual-type `(#:var ,binder ,s))
                     (list* label actual-type expected-mark actual-tail)))
             (cond
               [(owned-type? actual-type)
                ;; T-RecRewrite は root Owned の欄を identity entry に限る。
                (unless (tag-compat? actual-type expected-type context)
                  (mismatch))
                (and mark-changed? (identity-entry))]
               [(tag-compat? actual-type expected-type context)
                (and mark-changed? (identity-entry))]
               [else
                (define binder (fresh-union-name))
                (define-values (body converted-type)
                  (convert `(#:var ,binder ,s) actual-type expected-type s
                           propositions #:entry? #t))
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
          (row-union bound-row (judgment-row body-result)))]))

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
      (for/list ([item (in-list expressions)]
                 [type (in-list types)])
        (check item type environment delta propositions boundaries)))

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
      (judgment `(Construct ,type-span (#:ty ,expected ,type-span) ,constructor
                            ,@field-cores)
                expected
                (rows-union (map judgment-row results))))

    (define (eliminate-front scrutinee branches eliminate-span
                             environment delta propositions boundaries
                             #:on-clause [on-clause void])
      (define scrutinee-result
        (synth scrutinee environment delta propositions boundaries))
      ;; 包みは data 型を包むだけで構成子を変えない。typing.rkt と同じ表を引く。
      (define-values (data-type rewrap)
        (peel-eliminate-wrapper (judgment-type scrutinee-result)))
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
          (on-clause clause)
          clause))
      (values scrutinee-result clauses))

    (define (check-eliminate scrutinee branches expected eliminate-span
                             environment delta propositions boundaries)
      (define reversed-branch-results '())
      (define-values (scrutinee-result clauses)
        (eliminate-front
         scrutinee branches eliminate-span environment delta propositions boundaries
         #:on-clause
         (lambda (clause)
           (match-define (list _ _ _ body branch-environment _ _ _) clause)
           (define result
             (check body expected branch-environment
                    delta propositions boundaries))
           (set! reversed-branch-results
                 (cons (list (judgment-core result)
                             (judgment-row result)
                             (judgment-core-type result))
                       reversed-branch-results)))))
      (define branch-results (reverse reversed-branch-results))
      (define-values (rebuilt-branch-cores core-type)
        (merge-branches (map first branch-results)
                        (map third branch-results)
                        eliminate-span propositions))
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
                      (define core
                        (if (ormap values resource-names)
                            `(Scope ,eliminate-span ()
                                    ,(wrap-resource-lets
                                      raw-parameters field-types resource-names
                                      branch-core))
                            branch-core))
                      `(,(branch-span raw-branch) ,constructor ,core-parameters
                        -> ,core)))
       expected
       (rows-union
        (cons (judgment-row scrutinee-result)
              (map second branch-results)))
       core-type))

    ;; SUR-012。UCore+ の型欄が省略の標識かを返す。
    (define (inferred? type)
      (match type [`(#:infer ,_) #t] [_ #f]))

    ;; SUR-003。UCore+ の row 欄が省略の標識かを返す。
    (define (inferred-row? raw-row)
      (eq? (peel-ef raw-row) '#:infer))

    ;; SUR-012 / SUR-003 / P2l2b2。注釈付き Let の宣言型を期待型に使う形である。
    (define (needs-expected-type? expression)
      (match (peel-node expression)
        [`(Fn ((,_ ,parameter-types) ...) ,_ ,raw-row ,_)
         (or (ormap inferred? parameter-types)
             (inferred-row? raw-row))]
        [`(Construct ,_ (Types ,_ ...) ,_ ...) #f]
        [`(Construct ,_ ,_ ...) #t]
        ;; P2m spec §7.2。Eliminate は結果型の期待型を必要とする。
        [`(Eliminate ,_ ,_) #t]
        [_ #f]))

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
                                   [inherited-row #f])
      (define-values (parameters parameter-types captures capture-types)
        (prepare-fn s parameter-binders raw-parameter-types body
                    environment delta
                    #:expected-parameter-types expected-parameter-types))
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
        (check body return-type
               (extend environment parameters parameter-types #f
                       (map resource-type? parameter-types))
               delta propositions
               (cons `(FunctionBoundary ,boundary ,return-type) boundaries)))
      (check-function-body-row s body-result return-type boundary declared-row)
      (finish-fn s parameter-binders parameter-types
                 captures capture-types capture-raw-names raw-names
                 capture-binders core-binders
                 return-type boundary body-result
                 signature callable reserved-with-formals))

    ;; SUR-015（spec §6.2）。下見中に消費した各連番と callable 表を必ず戻す。
    (define (call-with-restored-state thunk)
      (define saved (list boundary-counter callable-counter owned-counter
                          union-counter reversed-callables))
      (dynamic-wind
       void
       thunk
       (λ ()
         (set! boundary-counter (first saved))
         (set! callable-counter (second saved))
         (set! owned-counter (third saved))
         (set! union-counter (fourth saved))
         (set! reversed-callables (fifth saved)))))

    ;; SUR-015（spec §6.1、§6.2）。通常の本体結果型を優先し、Never なら
    ;; 最初に合成できた Return payload の型を候補にする。
    ;; ponytail: 入れ子ごとに下見を行うため深さに対して指数の費用。必要になれば節点ごとに記憶する。
    (define (probe-return-type body environment delta propositions boundaries)
      (call-with-restored-state
       (λ ()
         (define candidates (box '()))
         (define boundary (fresh-boundary))
         (define body-type
           (with-handlers ([exn:fail:elab? (λ (_) #f)])
             (judgment-type
              (synth body environment delta propositions
                     (cons `(FunctionBoundary ,boundary
                                              (#:probe ,candidates))
                           boundaries)))))
         (cond [(and body-type (not (eq? body-type 'Never))) body-type]
               [(pair? (unbox candidates)) (first (unbox candidates))]
               [else #f]))))

    (define (elaborate-inferred-fn s parameter-binders raw-parameter-types
                                  raw-row body
                                  environment delta propositions boundaries)
      (define-values (parameters parameter-types captures capture-types)
        (prepare-fn s parameter-binders raw-parameter-types body
                    environment delta))
      (define declared-row
        (resolve-declaration-row raw-row delta boundaries s))
      (define parameter-environment
        (extend environment parameters parameter-types #f
                (map resource-type? parameter-types)))
      (define inferred-return-type
        (and (mentions-return? (list raw-row body))
             (probe-return-type body parameter-environment
                                delta propositions boundaries)))
      (if inferred-return-type
          (elaborate-annotated-fn
           s parameter-binders raw-parameter-types
           (λ () inferred-return-type)
           raw-row body environment delta propositions boundaries)
          (let ()
            (define boundary (fresh-boundary))
            (define body-result
              (synth body parameter-environment
                     delta propositions
                     (cons `(FunctionBoundary ,boundary #:infer) boundaries)))
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
             #:boundary? boundary?)
      (define function (peel-bind raw-function))
      (define parameters (map peel-bind parameter-binders))
      (when (check-duplicates (cons function parameters))
        (reject s 'duplicate-recur-binder function parameters))
      (define parameter-types
        (for/list ([type (in-list raw-parameter-types)])
          (resolve-annotation type delta s)))
      (when (captures-owned? body (cons function parameters) environment)
        (reject s 'owned-recur-capture))
      (define return-type (resolve-return))
      (define declared-row
        (resolve-declaration-row raw-row delta boundaries s))
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
        (if boundary
            (cons `(FunctionBoundary ,boundary ,return-type) boundaries)
            boundaries))
      (define body-result
        (check body return-type body-environment
               delta propositions body-boundaries))
      (if boundary
          (check-function-body-row s body-result return-type boundary declared-row)
          (unless (row-subset? (judgment-row body-result) declared-row)
            (reject s 'undeclared-recur-effect
                    declared-row (judgment-row body-result))))
      (define continuation-result
        (synth continuation function-environment
               delta propositions boundaries))
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
      (check-recur-body-gate s function parameters
                             (judgment-core body-result)
                             body-environment
                             (reverse reversed-callables)
                             declared-row)
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
            (cons `(FunctionBoundary ,body-boundary #:infer) boundaries)
            boundaries))
      (define body-result
        (synth body parameter-environment delta propositions body-boundaries))
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
                             (judgment-core body-result)
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
              (probe-return-type body parameter-environment
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
                 #:body-boundary? #t)))))

    (define (synth expression environment delta propositions boundaries)
      (define s (span-of expression))
      (define result
        (synth/raw expression environment delta propositions boundaries))
      (define normalized (normalize-type (judgment-type result)))
      (unless normalized
        (reject s 'non-normalizable-type (judgment-type result)))
      (judgment (judgment-core result)
                normalized
                (judgment-row result)))

    (define (synth-let-body body name binding-type environment
                            delta propositions boundaries)
      (if (and (resource-type? binding-type)
               (eq? (peel-node body) name))
          ;; identity Let は place を介さず値をそのまま渡す。
          (judgment `(#:var ,name ,(span-of body)) binding-type '())
          (synth body environment delta propositions boundaries)))

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
         (define initial-type (normalize-type (lookup environment root)))
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
         (define local-type (lookup environment name))
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

        [`(FnDecl ,raw-function ((,parameter-binders ,raw-parameter-types) ...)
                  ,raw-return-type ,raw-row ,body ,continuation)
         #:when (not (inferred? raw-return-type))
         (elaborate-recur-annotated
          s raw-function parameter-binders raw-parameter-types
          (λ () (resolve-annotation raw-return-type delta s))
          raw-row body continuation
          environment delta propositions boundaries
          #:boundary? (mentions-return? (list raw-row body)))]

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
          raw-row body environment delta propositions boundaries)]

        [`(Apply ,function ,arguments ...)
         (define raw-function-result
           (synth function environment delta propositions boundaries))
         (define reserved
           (function-reserved-names function arguments environment))
         (define-values (function-result wrap)
           (normalize-owned-function raw-function-result (span-of function)
                                     reserved))
         (define-values (function-type _function-owned?)
           (peel-owned-function-elab (judgment-type function-result)
                                     (judgment-core function-result)))
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
            (define argument-results
              (check-many arguments parameter-types
                          environment delta propositions boundaries s))
            (define applied
              `(Apply ,s ,(judgment-core function-result)
                      ,@(map judgment-core argument-results)))
            (close-owned-function
             wrap
             (judgment
              ;; 義務列の先頭を最も外側にする。逆順に畳むと (φ_1 φ_2) が
              ;; (Discharge P_1 (Discharge P_2 (Apply ...))) になる。
              (for/fold ([core applied]) ([proof (in-list (reverse proofs))])
                `(Discharge ,s ,proof ,core))
              return-type
              (rows-union
               (append (list (judgment-row function-result))
                       (map judgment-row argument-results)
                       (list latent-row)))))]
           [_ (reject s 'apply-non-function (judgment-type function-result))])]

        [`(Rec (,raw-fields ...))
         (define raw-labels (map first raw-fields))
         (define fields
           (for/list ([field (in-list raw-fields)])
             (match-define `(,raw-label ,mutability ,field-expression) field)
             (list (peel-lbl raw-label) mutability field-expression)))
         (unless (field-row-unique? fields)
           (reject s 'duplicate-record-label fields))
         (define field-results
           (for/list ([field (in-list fields)])
             (match-define `(,label ,mutability ,field-expression) field)
             (define result
               (synth field-expression environment delta propositions boundaries))
             (when (owned-type? (judgment-type result))
               (reject s 'owned-record-field label))
             (list label mutability result)))
         (judgment
          `(Rec ,s
            ,(for/list ([field (in-list field-results)]
                        [raw-label (in-list raw-labels)])
               (match-define (list label mutability result) field)
               `(,raw-label ,mutability ,(judgment-core result))))
          `(Record
            ,(for/list ([field (in-list field-results)])
               (match-define (list label mutability result) field)
               `(,label ,(judgment-type result) ,mutability)))
          (rows-union
           (for/list ([field (in-list field-results)])
             (judgment-row (third field)))))]

        [`(Proj ,record ,raw-label)
         (or (elaborate-place-projection expression environment)
             (let ([label (peel-lbl raw-label)])
               (define record-result
                 (synth record environment delta propositions boundaries))
               (match (judgment-type record-result)
                 [`(Record ,row)
                  (define field (assoc label row))
                  (cond
                    [(not field) (reject s 'unknown-record-label label)]
                    [(field-optional? field)
                     (define field-type (second field))
                     (judgment `(ProjOpt ,s (#:ty ,field-type ,s)
                                         ,(judgment-core record-result) ,raw-label)
                               `(Option ,field-type)
                               (judgment-row record-result))]
                    [else
                     (match (field-row-lookup row label)
                       [(list field-type _)
                        (judgment `(Proj ,s ,(judgment-core record-result) ,raw-label)
                                  field-type
                                  (judgment-row record-result))]
                       [_ (reject s 'unknown-record-label label)])])]
                 [_ (reject s 'project-non-record (judgment-type record-result))])))]

        ;; spec §8。注釈なしの const と let と let mut である。宣言型が
        ;; 無いので束縛式の型をそのまま宣言型とみなす。宣言型だけで分かる
        ;; mut の検査は走らせようがなく、bind-with-mode の中の推論後の
        ;; 検査が同じ key を返す。
        [`(Let (,raw-name ,binding-mode) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
         (define name (peel-bind raw-name))
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define actual-type (judgment-type bound-result))
         (define binding-type
           (bind-with-mode s binding-mode actual-type actual-type
                           propositions))
         (define body-result
           (synth-let-body
            body name binding-type
            (extend environment (list name) (list binding-type)
                    (and (eq? binding-mode 'mut) '(mut))
                    (list (resource-type? binding-type)))
            delta propositions boundaries))
         (judgment
          `(Let ,s (,raw-name ,binding-mode
                              (#:ty ,binding-type ,(span-of bound)))
                ,(judgment-core bound-result)
                ,(judgment-core body-result))
          (judgment-type body-result)
          (row-union (judgment-row bound-result)
                     (judgment-row body-result)))]

        ;; 注釈なし Let の (#:bind x s) を注釈あり Let の 3 つ組として
        ;; 誤って分解しないよう、binder の包みの形で分岐する。
        [`(Let (,raw-name ,binding-mode ,raw-type) ,bound ,body)
         #:when (and (pair? raw-name) (eq? (car raw-name) '#:bind))
         (define name (peel-bind raw-name))
         (define declared-type (resolve-annotation raw-type delta s))
         (when (and (eq? binding-mode 'mut)
                    (or (not (owned-free? declared-type))
                        (unbound-borrowed-type? declared-type (set))))
           ;; 宣言型だけで明らかな affine/borrowed binding は bound を合成する
           ;; 前に拒むため、elaborate と typing が同じ key を返す。
           (reject s 'mut-binding-unsupported-type declared-type))
         (define record-literal-checkable?
           (match* ((peel-node bound) declared-type)
             [(`(Rec (,fields ...)) `(Record ,row))
              ;; 空リストも有効な Rec なので、欄ごとの check を内側へ伝える。
              (list? (omitted-optional-labels
                      (map (lambda (field) (peel-lbl (first field))) fields)
                      row))]
             [(_ _) #f]))
         (define bound-result
           (if (or (needs-expected-type? bound) record-literal-checkable?)
               (check bound declared-type environment delta propositions boundaries)
               (synth bound environment delta propositions boundaries)))
         (define source-core-type (judgment-core-type bound-result))
         ;; let/mut は最上位の Record 残余を束縛型へ戻すため、その残余は
         ;; RSD の対象から除く。const と Record 以外は宣言型まで回収する。
         (define remainder-target
           (match* (binding-mode source-core-type declared-type)
             [((or 'let 'mut) `(Record ,actual-row) `(Record ,declared-row))
              `(Record ,(append declared-row
                                (field-row-residual actual-row declared-row)))]
             [(_ _ _) declared-type]))
         (define-values (discharged-core discharged-type)
           (discharge-remainder (judgment-core bound-result)
                                source-core-type remainder-target s
                                propositions))
         (define-values (bound-core actual-type)
           (convert discharged-core discharged-type declared-type s
                    propositions))
         ;; OWN-004 は変換前の Core の型と変換後の型の間でも検査する。
         (match (narrowing-kind discharged-type actual-type propositions)
           ['ok (void)]
           [`(drop-obligation ,_ ,_)
            (reject s 'owned-narrowing-needs-proof actual-type
                    discharged-type)]
           [_ (reject s 'owned-narrowing-rejected actual-type
                      discharged-type)])
         (define binding-type
           (bind-with-mode s binding-mode declared-type actual-type
                           propositions))
         (define body-result
           (synth-let-body
            body name binding-type
            (extend environment (list name) (list binding-type)
                    (and (eq? binding-mode 'mut) '(mut))
                    (list (resource-type? binding-type)))
            delta propositions boundaries))
         (judgment
          `(Let ,s (,raw-name ,binding-mode
                              (#:ty ,declared-type ,(wrapper-span raw-type)))
                ,bound-core
                ,(judgment-core body-result))
          (judgment-type body-result)
          (row-union (judgment-row bound-result)
                     (judgment-row body-result)))]

        [`(Let ,raw-name ,bound ,body)
         (define name (peel-bind raw-name))
         (define bound-result
           (synth bound environment delta propositions boundaries))
         (define binding-type (judgment-type bound-result))
         (define body-result
           (synth-let-body
            body name binding-type
            (extend environment (list name) (list binding-type) #f
                    (list (resource-type? binding-type)))
            delta propositions boundaries))
         (judgment
          `(Let ,s (,raw-name (#:ty ,(judgment-type bound-result) ,s))
                ,(judgment-core bound-result)
                ,(judgment-core body-result))
          (judgment-type body-result)
          (row-union (judgment-row bound-result)
                     (judgment-row body-result)))]

        [`(Construct ,constructor (Types ,raw-types ...) ,fields ...)
         (define type-arguments
           (for/list ([type (in-list raw-types)])
             (resolve-annotation type delta s)))
         (define result-type
           (constructor-result constructor type-arguments s))
         (elaborate-constructor constructor fields result-type
                                s
                                environment delta propositions boundaries)]

        [`(Construct ,_ ,_ ...)
         (reject s 'constructor-needs-expected-type)]

        [`(Eliminate ,scrutinee (,branches ...))
         ;; 構文だけで決まる拒否を枝の elaboration より先に行い、callable
         ;; 登録などの副作用を起こさない。
         (for ([raw-branch (in-list branches)])
           (match (peel-branch raw-branch)
             [`(,_ (,_ ...) -> ,body)
              #:when (needs-expected-type? body)
              (reject s 'eliminate-needs-expected-type)]
             [_ (void)]))
         (define-values (scrutinee-result clauses)
           (eliminate-front scrutinee branches s
                            environment delta propositions boundaries))
         (define results
           (for/list ([clause (in-list clauses)])
             (match-define (list _ _ _ body branch-environment _ _ _) clause)
             (synth body branch-environment delta propositions boundaries)))
         (define-values (branch-cores core-type)
           (merge-branches (map judgment-core results)
                           (map judgment-core-type results)
                           s propositions))
         (judgment
          `(Eliminate ,s ,(judgment-core scrutinee-result)
                      ,(for/list ([clause (in-list clauses)]
                                  [core (in-list branch-cores)])
                         (match-define
                           (list raw-branch constructor raw-parameters _ _
                                 field-types resource-names core-parameters)
                           clause)
                         (define wrapped-core
                           (if (ormap values resource-names)
                               `(Scope ,s ()
                                       ,(wrap-resource-lets
                                         raw-parameters field-types resource-names
                                         core))
                               core))
                         `(,(branch-span raw-branch) ,constructor ,core-parameters
                           -> ,wrapped-core)))
          core-type
          (rows-union
           (cons (judgment-row scrutinee-result)
                 (map judgment-row results))))]

        [`(Eliminate ,_ ,_)
         (reject s 'eliminate-needs-expected-type)]

        [`(Return ,returned)
         (match (nearest-boundary boundaries)
           [`(,_ ,_ #:infer)
            ;; SUR-008。推論中の戻り型で Return の payload を検査できない。
            (reject s 'return-type-not-inferable 'return-in-synth)]
           [`(,_ ,boundary (#:probe ,candidates))
            ;; SUR-015（spec §6.2）。payload を合成できなければ本番へ回す。
            (with-handlers ([exn:fail:elab? (λ (_) (void))])
              (define returned-result
                (synth returned environment delta propositions boundaries))
              (set-box! candidates
                        (append (unbox candidates)
                                (list (judgment-type returned-result)))))
            (judgment `(#:lit unit ,s) 'Never `((Return ,boundary Never)))]
           [`(,_ ,boundary ,return-type)
            (define returned-result
              (check returned return-type
                     environment delta propositions boundaries))
            (judgment
             `(Perform ,s (Return ,boundary (#:ty ,return-type ,s))
                       ,(judgment-core returned-result))
             'Never
             (row-union `((Return ,boundary ,return-type))
                        (judgment-row returned-result)))]
           [_ (reject s 'return-outside-boundary)])]

        [`(NarrativeExpr ,_)
         (reject s 'narrative-expression-needs-expected-type)]

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
           (synth next environment delta propositions boundaries))
         (define observed-core
           (if (owned-type? (judgment-type observed-result))
               `(OwnLeaf ,s ,(judgment-core observed-result))
               (judgment-core observed-result)))
         (judgment
          `(Yield ,s ,observed-core
                  ,(judgment-core next-result))
          (judgment-type next-result)
          (rows-union
           (list (judgment-row observed-result)
                 (judgment-row next-result)
                 `((Yield ,(judgment-type observed-result))))))]

        [`(Suspend ,body)
         (define result
           (synth body environment delta propositions boundaries))
         (judgment `(Suspend ,s ,(judgment-core result))
                   (judgment-type result)
                   (row-union (judgment-row result) '(Suspend)))]

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
         (define slot-type (lookup environment name))
         (unless slot-type (reject s 'unbound-variable name))
         (unless (eq? (binding-mode-of environment name) 'mut)
           (reject s 'immutable-binding name))
         (define result
           (synth value environment delta propositions boundaries))
         (define value-type (judgment-core-type result))
         (define slot-union?
           (match (normalize-type slot-type)
             [`(Union ,_ ,_) #t]
             [_ #f]))
         (define value-union?
           (match (normalize-type value-type)
             [`(Union ,_ ,_) #t]
             [_ #f]))
         (define value-core
           (cond
             ;; P2m2b spec §3.4。Never は変換を置かずそのまま通す。
             [(eq? (normalize-type value-type) 'Never)
              (judgment-core result)]
             ;; Union への代入は成分を一意に選んで tag を付ける。
             [(and slot-union? (not value-union?))
              (union-inject (judgment-core result) value-type slot-type
                            s propositions
                            #:no-member-key 'reassign-type-mismatch)]
             [(reassign-narrowing? value-type slot-type) (judgment-core result)]
             [else (reject s 'reassign-type-mismatch slot-type value-type)]))
         (unless (storage-ok? slot-type)
           (reject s 'mutable-callable-storage-requires-partial slot-type))
         (judgment `(Reassign ,s ,raw-name ,value-core)
                   'Unit
                   (row-union (judgment-row result) '(Mutation)))]

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
         (unless (resource-type? (judgment-type result))
           (reject s 'drop-non-owned (judgment-type result)))
         (judgment `(Drop ,s ,(judgment-core result))
                   'Unit
                   (row-union (judgment-row result) '(Own)))]

        [`(Curry ,function ,argument)
         (define raw-function-result
           (synth function environment delta propositions boundaries))
         (define-values (function-result wrap)
           (normalize-owned-function
            raw-function-result
            (span-of function)
            (function-reserved-names function (list argument) environment)))
         (define-values (function-type function-owned?)
           (peel-owned-function-elab (judgment-type function-result)
                                     (judgment-core function-result)))
         (match function-type
           [`(NFn (,first-type ,remaining-types ...)
                  ,return-type ,latent-in ,latent-out ,obligations ,origin)
            (define argument-result
              (check argument first-type
                     environment delta propositions boundaries))
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
             (judgment
              `(Curry ,s ,(judgment-core function-result)
                      ,argument-core)
              (if (or function-owned? (resource-type? first-type))
                  `(Owned ,bare-result)
                  bare-result)
              (row-union (judgment-row function-result)
                         (judgment-row argument-result))))]
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
      (unless (type-compatible? (judgment-type result) expected propositions)
        (reject s 'type-mismatch expected (judgment-type result)))
      (define-values (core actual-type)
        (discharge-remainder (judgment-core result)
                             (judgment-core-type result)
                             expected s propositions))
      (match (narrowing-kind actual-type expected propositions)
        ['ok (void)]
        [`(drop-obligation ,_ ,_)
         (reject s 'owned-narrowing-needs-proof expected
                 actual-type)]
        [_ (reject s 'owned-narrowing-rejected expected
                   actual-type)])
      (define-values (converted core-type)
        (convert core actual-type expected s propositions))
      (judgment converted expected (judgment-row result) core-type))

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
      (define exact
        (and synthesized
             (for/first ([candidate (in-list members)]
                         #:when (type-equiv? candidate synthesized))
               candidate)))
      (define first-stage
        (if exact
            (list exact)
            (if synthesized
                (filter (λ (candidate)
                          (tag-compat? synthesized candidate context))
                        members)
                '())))
      (define (normal-path)
        (check-against-expected
         (synth expression environment delta propositions boundaries)
         expected s propositions))
      (match first-stage
        [(list _candidate) (normal-path)]
        [(list _first _second ...)
         (reject s 'ambiguous-union-member expected synthesized first-stage)]
        [_
         (define-values (tier1 tier2 tier3 tier4b)
           (if synthesized
               (union-member-tiers synthesized members s propositions)
               (values '() '() '() '())))
         (define literal-results
           (filter
            values
            (for/list ([candidate (in-list members)]
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
            (if (ormap (λ (entry)
                         (type-equiv? candidate (first entry)))
                       literal-results)
                (let ([result
                       (check expression candidate environment delta
                              propositions boundaries)])
                  (judgment
                   `(UnionInject ,s (#:ty ,expected ,s)
                                 (#:ty ,candidate ,s)
                                 ,(judgment-core result))
                   expected (judgment-row result) expected))
                (normal-path))]
           [candidates
            (reject s 'ambiguous-union-member expected
                    (or synthesized expected) candidates)])]))

    (define (check expression expected environment delta propositions boundaries)
      (define s (span-of expression))
      (match (peel-node expression)
        [`(Construct ,constructor (Types ,_ ...) ,_ ...)
         (define result
           (synth expression environment delta propositions boundaries))
         (unless (type-compatible? (judgment-type result) expected
                                   propositions)
           (reject s 'type-mismatch expected (judgment-type result)))
         (define actual-core-type (judgment-core-type result))
         (define-values (core actual-type)
           (discharge-remainder (judgment-core result)
                                actual-core-type expected s propositions))
         (match (narrowing-kind actual-type expected propositions)
           ['ok (void)]
           [`(drop-obligation ,_ ,_)
            (reject s 'owned-narrowing-needs-proof expected
                    actual-type)]
           [_ (reject s 'owned-narrowing-rejected expected
                      actual-type)])
         (define-values (converted core-type)
           (convert core actual-type expected s propositions))
         (judgment converted expected (judgment-row result) core-type)]

        [`(Construct ,constructor ,fields ...)
         (elaborate-constructor constructor fields expected
                                s
                                environment delta propositions boundaries)]

        [`(Eliminate ,scrutinee (,branches ...))
         (check-eliminate scrutinee branches expected
                          s
                          environment delta propositions boundaries)]

        [`(NarrativeExpr ,body)
         (define boundary (fresh-boundary))
         (define body-result
           (check body expected environment delta propositions
                  (cons `(ExpressionBoundary ,boundary ,expected)
                        boundaries)))
         (define own-return `((Return ,boundary ,expected)))
         (judgment
          `(Handle ,s (Return ,boundary (#:ty ,expected ,s))
                   (,s (#:bind return-value ,s) ->
                       (#:var return-value ,s))
                   (Scope ,s () ,(judgment-core body-result)))
          expected
          (row-difference (judgment-row body-result) own-return))]

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
         (define field-results
           (for/list ([field (in-list fields)])
             (match-define `(,label ,mutability ,field-expression) field)
             (define field-type (second (assq label expected-fields)))
             (define result
               (check field-expression field-type environment delta propositions
                     boundaries))
             (when (owned-type? (judgment-type result))
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
                  `(,label ,(judgment-type result) ,mutability))
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
                  `(,(first field) ,(second field) ,(third field) opt))))))
         (check-against-expected rec-result expected s propositions)]

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
              (and (inferred-row? raw-row) expected-row))
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
          (reverse reversed-callables))))

;; reject は primary-span を必須の第 1 引数に取る。渡し忘れと引数の逆順、
;; registry に無い reason を、どれも実行時に落として fail-loud にする。
;; reject は provide しないため、内部から検査する。
(module+ test
  (require rackunit)

  (define ok-span '(#:span src 3 7))

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

  ;; 正しい呼び出しは exn:fail:elab を投げ、3 欄を保つ。
  (define failure
    (with-handlers ([exn:fail:elab? values])
      (reject ok-span 'unknown-type 'Foo)))
  (check-pred exn:fail:elab? failure)
  (check-equal? (exn:fail:elab-primary-span failure) ok-span)
  (check-equal? (exn:fail:elab-reason failure) 'unknown-type)
  (check-equal? (exn:fail:elab-details failure) '(Foo))

  ;; 3 つの details を Diagnostic の 2 欄へ落とさず保持する。
  (define ambiguous-failure
    (with-handlers ([exn:fail:elab? values])
      (reject ok-span 'ambiguous-union-member 'Expected 'Actual '(A B))))
  (define ambiguous-diagnostic
    (elab-failure->diagnostic ambiguous-failure (hash)))
  (check-equal? (diagnostic-expected ambiguous-diagnostic) 'Expected)
  (check-equal? (diagnostic-found ambiguous-diagnostic) '(Actual (A B))))

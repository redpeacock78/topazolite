#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "backend-matrix.rkt"
         "erase.rkt"
         "lang.rkt"
         "origins.rkt"
         "pr-lang.rkt")

(provide lower
         lower/with-matrix
         lower-value
         var-code
         tag-code
         label-code
         boundary-code
         shim
         tycode
         primitive-arity
         arithmetic-primitives
         resource-primitives
         shim-primitives
         repr-ok?
         row-kinds
         effect-kinds-of
         latent-kinds
         latent-visible?)

;;; backend-matrix.md §5 の符号化

;; 源の記号空間を種類ごとの接頭辞つきの記号へ写す。単射性は接頭辞の一意性から
;; 従う。像は最初の : で一意に分かれ、PR の literal に : を含むものは無い。
(define (encode-name prefix name)
  (string->symbol (format "~a:~a" prefix name)))

(define (var-code x)       (encode-name 'v x))
(define (tag-code K)       (encode-name 'k K))
(define (label-code label) (encode-name 'f label))
(define (boundary-code b)  (encode-name 'b b))
(define (shim nm)          (encode-name 'tz nm))

;; τ は記号とリストだけからなるので、write の単射性がそのまま tycode の単射性に
;; なる。型同値で正規化しないのは、machine.rkt の R-HandleSkip が源の op 全体を
;; equal? で比べるためである。正規化すると源が別物として扱う 2 つの op を目標側が
;; 同一視する。
(define (tycode type)
  (encode-name 'ty (format "~s" type)))

;; (Return b τ) の符号の組み立て。make-lowering の op-code は τ の検査を足して
;; ここへ委ねる。backend-matrix.md §6 の row-kinds は検査を通った源の行だけを
;; 受け取るので、組み立てだけを呼ぶ。
(define (return-code b type)
  `(return ,(boundary-code b) ,(tycode type)))

;;; primitive

;; backend-matrix.md §7。shim へ写すのはこの 7 件だけである。名前と feature の対応は
;; backend-matrix.rkt の primitive-features が持つので、名前の束はそこから引き、
;; ここに書き写さない。算術と比較の 6 件と資源取得を分けておくのは、
;; backend-matrix.md §10 の表の検査が算術と比較の側だけを対象にするためで
;; ある（G3c で使う）。
(define arithmetic-primitives
  (append-map feature-primitives arithmetic-shim-features))
(define resource-primitives (feature-primitives 'primitive-acquire))
(define shim-primitives (append arithmetic-primitives resource-primitives))

;; arity を写して二重定義にしない。Γ0 の NFn の引数個数をそのまま使う。
(define (primitive-arity nm)
  (match (lookup Γ0 nm)
    [(list (list 'NFn (list argument-types ...) _ _ _) _) (length argument-types)]
    [_ #f]))

;; 固定名。prim-body に自由変数が無いので捕獲は起きず、gensym なしで写しが決定的
;; になる（backend-matrix.md §7）。
(define (primitive-formals arity)
  (for/list ([index (in-range 1 (add1 arity))])
    (string->symbol (format "pa_~a" index))))

;;; 診断

;; 診断は例外ではなく値で返す（backend-matrix.md §8）。
;; let/ec で脱出させると、部分的な出力と診断を同時に返す経路が
;; 構文の上で作れない。
(define (with-diagnostics backend proc)
  (let/ec escape
    (define (fail feature-id reason)
      (escape 'capability (capability-diagnostic feature-id backend reason)))
    (values 'ok (proc fail))))

;; 形の頭シンボル。変数と literal は頭を持たないので擬似的な頭を返す。unit は
;; G1 の literal なので変数になれず、記号だが %literal 側である。
(define (core-head core)
  (cond
    [(or (exact-integer? core) (string? core) (eq? core 'unit)) '%literal]
    [(symbol? core) '%variable]
    [(and (pair? core) (symbol? (car core))) (car core)]
    [else #f]))

(define (core-literal? value)
  (or (exact-integer? value) (string? value) (eq? value 'unit)))

;; classify.rkt:17 と elaborate.rkt:98 の同名の判定と同じものである。どちらも
;; module 内に閉じているので、ここでも 3 行を持つ。
(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

;;; lowering 本体

;; backend / matrix / fail を閉じ込めて、写しの各行を 1 引数の関数として書く。
(define (make-lowering backend matrix fail)
  ;; 形の feature を引き、backend が非対応なら診断へ脱出する。対応表に無い頭
  ;; シンボルは unknown-core-form で閉じる（backend-matrix.md §8）。
  (define (require-feature-id! feature-id)
    (when (eq? (feature-support/matrix matrix feature-id backend) 'unsupported)
      (fail feature-id
            (format "feature ~a は backend ~a で非対応である"
                    feature-id backend))))

  (define (require-feature! head)
    (define feature-id (core-form-feature head))
    (unless feature-id
      (fail 'unknown-core-form
            (format "対応表に無い Typed Core の形: ~a" head)))
    (require-feature-id! feature-id))

  ;; op-code。τ でない入力に符号を作らない（backend-matrix.md §5）。
  (define (op-code op)
    (match op
      [`(Return ,b ,type)
       (unless (redex-match? G2m τ type)
         (fail 'unknown-core-type
               (format "op-code の入力が Typed Core の τ でない: ~s" type)))
       (return-code b type)]
      [_ (fail 'unknown-core-form (format "op の形が (Return b τ) でない: ~s" op))]))

  ;; prim-body。名前で 3 つに分ける（backend-matrix.md §7）。PrimVal の頭が指す
  ;; primitive-value は η 展開の closure を作るだけの feature なので、shim へ写す
  ;; 名前の可否はここでもう一度、名前ごとの feature で引く
  ;; （backend-matrix.md §7）。頭に算術
  ;; の feature を割り当てると、算術を unsupported と宣言したときに kernel と
  ;; trait と acquire の診断まで巻き込んで閉じてしまう。
  (define (prim-body nm)
    (cond
      [(primitive-feature nm)
       => (lambda (feature-id)
            (require-feature-id! feature-id)
            `(PPrim ,(shim nm) ,@(primitive-formals (primitive-arity nm))))]
      [(assq nm kernel-gamma0-entries)
       (fail 'kernel-primitive
             (format "Typed Core の kernel primitive は写し先を持たない: ~a" nm))]
      [(assq nm trait-gamma0-entries)
       (fail 'trait-primitive
             (format "trait primitive は Phase 2 以降の emitter を待つ: ~a" nm))]
      [else
       (fail 'unknown-core-form (format "Γ0 に無い primitive の名前: ~a" nm))]))

  ;; CurryVal。適用済み引数を penv へ入れ、対応する parameter を列から除く。
  ;; PClosure でない関数側や parameter の尽きた形は well-typed な源項に現れない
  ;; が、lower の全域性のために診断で閉じる。
  (define (curry-closure function argument)
    (match function
      [`(PClosure ,env (,formal ,rest ...) ,body)
       `(PClosure ,(append env (list (list formal argument))) ,rest ,body)]
      [_ (fail 'unknown-core-form
               (format "CurryVal の関数側が parameter を持つ PClosure でない: ~s"
                       function))]))

  ;; 型に依存する規則の選択を写す側で解く（backend-matrix.md §5）。
  ;; 目標項には結果だけが残る。
  (define (let-form type px bound body)
    (if (owned-type? type)
        `(PLetOwned ,px ,bound ,body)
        `(PLet ,px ,bound ,body)))

  (define (branch br)
    (match br
      [`(,tag (,formals ...) -> ,body)
       `(,(tag-code tag) ,(map var-code formals) -> ,(lower-core body))]
      [_ (fail 'unknown-core-form (format "分岐の形が br でない: ~s" br))]))

  ;; backend-matrix.md §7 の値の表
  (define (lower-val value)
    (require-feature! (core-head value))
    (match value
      [(? core-literal?) value]
      [`(Construct ,_ ,tag ,arguments ...)
       `(PTagged ,(tag-code tag) ,@(map lower-val arguments))]
      [`(resource ,n) `(PResource ,n)]
      [`(Lam ,_ ,_ (,formals ...) ,body)
       `(PClosure () ,(map var-code formals) ,(lower-core body))]
      [`(PrimVal ,_ ,nm)
       ;; primitive の名前を先に検査してから arity を読む。diagnostic で閉じる経路を
       ;; primitive-arity の #f に渡して例外化しないためである。
       (define body (prim-body nm))
       `(PClosure () ,(primitive-formals (primitive-arity nm)) ,body)]
      [`(CurryVal ,_ ,function ,argument)
       (curry-closure (lower-val function) (lower-val argument))]
      [`(RecurVal ,_ ,f (,formals ...) ,body)
       (define px-f (var-code f))
       (define pxs (map var-code formals))
       `(PClosure () ,pxs
                  (PLetrec ,px-f
                           (PLam ,pxs ,(lower-core body))
                           (PApp ,px-f ,@pxs)))]
      [`(TypeRep ,_ ,_ ,_) '(PTagged typerep)]
      [`(ProofRep ,_ ,_) '(PTagged proof)]
      [`(Rec ((,labels ,_ ,fields) ...))
       `(PRec ,(map (lambda (label field)
                      (list (label-code label) (lower-val field)))
                    labels fields))]
      [`(UVal ,inner) `(PTagged uval ,(lower-val inner))]
      [`(RVal ,_ ,inner) `(PTagged rval ,(lower-val inner))]
      [_ (fail 'unknown-core-form (format "lower-value: ~s" value))]))

  ;; backend-matrix.md §7 の計算の表。v は値の表へ委譲する。
  (define (lower-core core)
    (cond
      [(redex-match? G2m v core) (lower-val core)]
      [else
       (require-feature! (core-head core))
       (match core
         [(? symbol?) (var-code core)]
         [`(Apply ,function ,arguments ...)
          `(PApp ,(lower-core function) ,@(map lower-core arguments))]
         [`(Let (,x ,type) ,bound ,body)
          (let-form type (var-code x) (lower-core bound) (lower-core body))]
         [`(Let (,x ,_ ,type) ,bound ,body)
          (let-form type (var-code x) (lower-core bound) (lower-core body))]
         [`(Construct ,_ ,tag ,arguments ...)
          `(PTagged ,(tag-code tag) ,@(map lower-core arguments))]
         [`(Eliminate ,scrutinee (,branches ...))
          `(PMatch ,(lower-core scrutinee) ,(map branch branches))]
         [`(Perform ,op ,argument)
          `(PEffect ,(op-code op) ,(lower-core argument))]
         [`(Handle ,op (,x -> ,handler) ,body)
          `(PInstall ,(op-code op)
                     (PLam (,(var-code x)) ,(lower-core handler))
                     ,(lower-core body))]
         [`(Scope (,places ...) ,body)
          ;; 場所は natural であり literal と衝突しないので符号化しない
          ;; （backend-matrix.md §5）。
          `(PScopeExit ,places ,(lower-core body))]
         [`(Recur ,_ ,f (,formals ...) ,body ,rest)
          `(PLetrec ,(var-code f)
                    (PLam ,(map var-code formals) ,(lower-core body))
                    ,(lower-core rest))]
         [`(Yield ,observed ,next)
          `(PRuntime yield ,(lower-core observed) ,(lower-core next))]
         [`(Suspend ,body) `(PRuntime suspend ,(lower-core body))]
         [`(Move ,w)
          `(PRuntime move ,(if (exact-nonnegative-integer? w)
                               `(PPlace ,w)
                               (var-code w)))]
         [`(Drop ,body) `(PRuntime drop ,(lower-core body))]
         [`(Curry ,function ,argument)
          `(PRuntime curry ,(lower-core function) ,(lower-core argument))]
         [`(Rec ((,labels ,_ ,fields) ...))
          `(PRec ,(map (lambda (label field)
                         (list (label-code label) (lower-core field)))
                       labels fields))]
         [`(Proj ,record ,label)
          `(PProj ,(lower-core record) ,(label-code label))]
         ;; Proof は実行時に意味を持たない。内側の写しをそのまま返す。
         [`(Discharge ,_ ,body) (lower-core body)]
         [`(Error ,p) `(PError ,p)]
         [_ (fail 'unknown-core-form (format "lower: ~s" core))])]))

  (values lower-val lower-core))

;; production の入口。正典表を既定で使い、表を引数に取らない
;; （backend-matrix.md §5）。
(define (lower core backend)
  (lower/with-matrix core backend backend-features))

;; test seam。unsupported を含む profile を作って診断機構そのものを試す。
(define (lower/with-matrix core-in backend matrix)
  ;; span.md §7: lowering は出力に span を残さない。入口で一度だけ投影する。
  ;; 投影は with-diagnostics の外へ置く。内側へ入れて診断へ潰すと、span 機構が
  ;; head を得たときの誤りが unknown-core-form として現れ、Core の形の誤りと区別できなくなる。
  ;; lower の全域性は Core の形に対するものであり、span 機構の誤りはその外にある
  ;; （span.md §7.3）。
  (define core (erase-core core-in))
  (with-diagnostics backend
    (lambda (fail)
      (define-values (lower-val lower-core) (make-lowering backend matrix fail))
      (lower-core core))))

;; 値の表を直接呼ぶ入口。UVal と RVal のように well-typed な源項から到達しない形を
;; fixture で試すために使う。
(define (lower-value value-in backend)
  (define value (erase-core value-in))
  (with-diagnostics backend
    (lambda (fail)
      (define-values (lower-val lower-core)
        (make-lowering backend backend-features fail))
      (lower-val value))))

;;; backend-matrix.md §5 表現規約

;; ADT の写しはすべて (PTagged K pv ...) である。List と Option と Result を
;; 同じ行にまとめるのは backend-matrix.md §5 の表と同じ粒度である。
(define (ptagged? value)
  (match value [`(PTagged ,_ ,_ ...) #t] [_ #f]))

(define (ptagged-with? value tag)
  (match value [`(PTagged ,K ,_ ...) (equal? K tag)] [_ #f]))

;; repr(τ) への適合。表を τ の形ごとに書き、判定を全域にする。
(define (repr-ok? type value)
  (match type
    ['Int (exact-integer? value)]
    ['Bool (or (ptagged-with? value (tag-code 'true))
               (ptagged-with? value (tag-code 'false)))]
    ['Unit (equal? value 'unit)]
    ['String (string? value)]
    ;; Never は住人を持たない。値が来た時点で偽である。
    ['Never #f]
    ['Res (match value [`(PResource ,_) #t] [_ #f])]
    [`(List ,_) (ptagged? value)]
    [`(Option ,_) (ptagged? value)]
    [`(Result ,_ ,_) (ptagged? value)]
    ;; 所有は静的な区別であり実行時表現に現れない。
    [`(Owned ,inner) (repr-ok? inner value)]
    [`(NFn ,_ ,_ ,_ ,_) (match value [`(PClosure ,_ ,_ ,_) #t] [_ #f])]
    ;; TypeInfo と Proof は実行時に意味を持たないので tag だけが残る。
    [`(TypeInfo ,_) (equal? value '(PTagged typerep))]
    [`(Proof ,_) (equal? value '(PTagged proof))]
    [`(Record ,_) (match value [`(PRec ,_) #t] [_ #f])]
    ;; machine.rkt の δ が実行時に区別しているので tag を残す。
    [`(Untrusted ,inner)
     (match value
       [`(PTagged uval ,payload) (repr-ok? inner payload)]
       [_ #f])]
    [`(Refined ,inner ,_)
     (match value
       [`(PTagged rval ,payload) (repr-ok? inner payload)]
       [_ #f])]
    ;; backend-matrix.md §5 の表に行が無い 2 形。lang.rkt:76 の G2 の τ には
    ;; あるので、
    ;; 表を分配して補う。行を落とすと repr-ok? が生成項の一部で偽を返し、
    ;; backend-matrix.md §5 の言明がその項について述べられなくなる。
    ;; 狭めではなく表の補完である。
    [`(Union ,left ,right) (or (repr-ok? left value) (repr-ok? right value))]
    [`(Intersection ,left ,right)
     (and (repr-ok? left value) (repr-ok? right value))]
    [_ #f]))

;;; backend-matrix.md §6 Effect のラベル種別

;; ℓ から kind へ。(Return b τ) だけは op-code の像である pop 全体を種別に使う。
;; 境界名だけにすると、同じ b で τ が違う handler が源側では残す Effect を目標側
;; が消してしまう。
(define (effect-label-kind label)
  (match label
    [`(Return ,b ,type) (return-code b type)]
    ;; PRuntime yield は型符号を担がないので、型成分はここで落ちる
    ;; （backend-matrix.md §12）。
    [`(Yield ,_) 'yield]
    ['Suspend 'suspend]
    ['Partial 'partial]
    ['Compile 'compile]
    ['Own 'own]
    [_ (error 'effect-label-kind "未知の Effect ラベル: ~s" label)]))

(define (row-kinds row)
  (for/fold ([kinds (set)]) ([label (in-list row)])
    (set-add kinds (effect-label-kind label))))

(define (kinds-of-all cores)
  (for/fold ([kinds (set)]) ([core (in-list cores)])
    (set-union kinds (effect-kinds-of core))))

;; 目標項に残る Effect の種別を取り出す residual extractor。
;; backend-matrix.md §6 のラベル種別の表と、続く散文に対応する。
;; 形ごとの節を並べ、最後に「その他は部分項の和」を置く。PClosure と PLam と
;; PInstall と PError の 4 形は和と違う寄与を持つので、和へ落とすと寄与がずれる。
(define (effect-kinds-of core)
  (match core
    ;; --- 値の形。現在行はすべて () である ---
    [(? exact-integer?) (set)]
    ['unit (set)]
    [(? string?) (set)]
    [`(PResource ,_) (set)]
    [`(PPlace ,_) (set)]
    ;; Lam の現在行は空で、本体の Effect は NFn の latent row に入る。本体を和に
    ;; 含めると、関数を作っただけで Effect が立つ。
    [`(PClosure ,_ ,_ ,_) (set)]
    ;; backend-matrix.md §6 の「値の形と PLam の寄与は空」という散文に従い、
    ;; 空にする。Recur の写しは (PLetrec f (PLam ...) rest) であり、
    ;; 源の Recur の typing は継続の行だけを返すので、PLam を和に含めると
    ;; (1) の包含が破れる。
    [`(PLam ,_ ,_) (set)]
    ;; --- 変数。unit の節より後に置く ---
    [(? symbol?) (set)]
    ;; --- 計算の形 ---
    ;; Apply は callee の latent row を現在行へ足す。
    [`(PApp ,function ,arguments ...)
     (set-union (latent-kinds function)
                (effect-kinds-of function)
                (kinds-of-all arguments))]
    [`(PLet ,_ ,bound ,body) (kinds-of-all (list bound body))]
    [`(PLetOwned ,_ ,bound ,body) (kinds-of-all (list bound body))]
    [`(PLetrec ,_ ,bound ,body) (kinds-of-all (list bound body))]
    [`(PTagged ,_ ,arguments ...) (kinds-of-all arguments)]
    [`(PRec ((,_ ,fields) ...)) (kinds-of-all fields)]
    ;; Proj は row を足さない。
    [`(PProj ,record ,_) (effect-kinds-of record)]
    [`(PMatch ,scrutinee (,branches ...))
     (set-union (effect-kinds-of scrutinee)
                (kinds-of-all
                 (for/list ([branch (in-list branches)])
                   (match branch [`(,_ (,_ ...) -> ,body) body] [_ '()]))))]
    ;; Γ0 の 7 件の primitive の latent row はすべて () である。
    [`(PPrim ,_ ,arguments ...) (kinds-of-all arguments)]
    [`(PEffect ,pop ,argument) (set-add (effect-kinds-of argument) pop)]
    ;; handler の寄与に latent-kinds を使う。handler の写しは (PLam (px) ...) で
    ;; あり、PLam の寄与が空なので effect-kinds-of では handler の Effect が消える。
    ;; 源の Handle は handler-row を row-union するので、開いた側と揃える。
    ;; 除去は本体だけに効かせる。集合を作ってから大域的に差を取ると、同じ pop を
    ;; 持つ PEffect が handler の外側にも現れたとき、外側の出現まで消える。
    [`(PInstall ,pop ,handler ,body)
     (set-union (latent-kinds handler)
                (set-remove (effect-kinds-of body) pop))]
    [`(PRuntime move ,argument) (set-add (effect-kinds-of argument) 'own)]
    [`(PRuntime drop ,argument) (set-add (effect-kinds-of argument) 'own)]
    [`(PRuntime yield ,observed ,next)
     (set-add (kinds-of-all (list observed next)) 'yield)]
    [`(PRuntime suspend ,body) (set-add (effect-kinds-of body) 'suspend)]
    ;; Curry の row は function row と argument row の和で、何も足さない。
    [`(PRuntime curry ,function ,argument)
     (kinds-of-all (list function argument))]
    ;; Scope の row は body の row そのもので、own を足さない。
    [`(PScopeExit ,_ ,body) (effect-kinds-of body)]
    ;; (Error _) は型付かない。
    [`(PError ,_) (set)]
    ;; backend-matrix.md §6 の散文が定める部分項の Effect 合成へ
    ;; 黙って落ちる形が無いようにする。
    ;; 上の節が PR の形をすべて挙げているので、ここへ落ちるのは
    ;; PR に形が増えたときだけである。
    ;; 落ちた形は寄与が和になり静かに通ってしまうため、
    ;; 形ごとの fixture を検査側に置く。
    [(? pair?) (kinds-of-all (list (car core) (cdr core)))]
    [_ (set)]))

;; 適用先の潜在 Effect を取り出す。適用先が構文上の関数値でないときは空集合を
;; 返す。過小近似だが、(1) は包含なのでこの側で成り立つ。
(define (latent-kinds core)
  (match core
    [`(PClosure ,_ ,_ ,body) (effect-kinds-of body)]
    [`(PLam ,_ ,body) (effect-kinds-of body)]
    [_ (set)]))

;; 目標側から latent Effect が取れる範囲。PApp の適用先がすべて構文上の PClosure
;; か PLam であることを、項全体について見る。
(define (latent-visible? core)
  (let walk ([node core])
    (match node
      [`(PApp ,function ,arguments ...)
       (and (match function
              [`(PClosure ,_ ,_ ,_) #t]
              [`(PLam ,_ ,_) #t]
              [_ #f])
            (walk function)
            (andmap walk arguments))]
      [(? pair?) (and (walk (car node)) (walk (cdr node)))]
      [_ #t])))

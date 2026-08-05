#lang racket

(require racket/match
         redex/reduction-semantics
         "backend-matrix.rkt"
         "lang.rkt"
         "origins.rkt")

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
         shim-primitives)

;;; §6.4 の符号化

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

;;; primitive

;; spec §4.4。shim へ写すのはこの 7 件だけである。名前と feature の対応は
;; backend-matrix.rkt の primitive-features が持つので、名前の束はそこから引き、
;; ここに書き写さない。算術と比較の 6 件と資源取得を分けておくのは、spec §9 の表
;; の検査が算術と比較の側だけを対象にするためである（G3c で使う）。
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
;; になる（spec §4.4）。
(define (primitive-formals arity)
  (for/list ([index (in-range 1 (add1 arity))])
    (string->symbol (format "pa_~a" index))))

;;; 診断

;; 診断は例外ではなく値で返す（spec §8.4）。let/ec で脱出させると、部分的な出力と
;; 診断を同時に返す経路が構文の上で作れない。
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
  ;; シンボルは unknown-core-form で閉じる（spec §8.3）。
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

  ;; op-code。τ でない入力に符号を作らない（spec §6.4）。
  (define (op-code op)
    (match op
      [`(Return ,b ,type)
       (unless (redex-match? G2m τ type)
         (fail 'unknown-core-type
               (format "op-code の入力が Typed Core の τ でない: ~s" type)))
       `(return ,(boundary-code b) ,(tycode type))]
      [_ (fail 'unknown-core-form (format "op の形が (Return b τ) でない: ~s" op))]))

  ;; prim-body。名前で 3 つに分ける（spec §4.4）。PrimVal の頭が指す
  ;; primitive-value は η 展開の closure を作るだけの feature なので、shim へ写す
  ;; 名前の可否はここでもう一度、名前ごとの feature で引く（spec §8.3）。頭に算術
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

  ;; 型に依存する規則の選択を写す側で解く（spec §6.3）。目標項には結果だけが残る。
  (define (let-form type px bound body)
    (if (owned-type? type)
        `(PLetOwned ,px ,bound ,body)
        `(PLet ,px ,bound ,body)))

  (define (branch br)
    (match br
      [`(,tag (,formals ...) -> ,body)
       `(,(tag-code tag) ,(map var-code formals) -> ,(lower-core body))]
      [_ (fail 'unknown-core-form (format "分岐の形が br でない: ~s" br))]))

  ;; §4.4 の値の表
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

  ;; §4.4 の計算の表。v は値の表へ委譲する。
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
          ;; 場所は natural であり literal と衝突しないので符号化しない（§6.4）。
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

;; production の入口。正典表を既定で使い、表を引数に取らない（spec §6.2）。
(define (lower core backend)
  (lower/with-matrix core backend backend-features))

;; test seam。unsupported を含む profile を作って診断機構そのものを試す。
(define (lower/with-matrix core backend matrix)
  (with-diagnostics backend
    (lambda (fail)
      (define-values (lower-val lower-core) (make-lowering backend matrix fail))
      (lower-core core))))

;; 値の表を直接呼ぶ入口。§8.3 の形ごとの fixture が UVal と RVal のように
;; well-typed な源項から到達しない形を試すために使う。
(define (lower-value value backend)
  (with-diagnostics backend
    (lambda (fail)
      (define-values (lower-val lower-core)
        (make-lowering backend backend-features fail))
      (lower-val value))))

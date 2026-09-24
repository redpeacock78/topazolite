#lang racket

(require racket/match
         "diagnostic.rkt"
         "traits.rkt"
         "type-equiv.rkt")

(provide lower-surface lift-template-type (struct-out lowered))

(struct lowered (term trait-rows impl-rows spans) #:transparent)

;; spec §7.2.1。別名の表を引かずにそのまま uτ になる名前である。
;; ucore.rkt:13 の A の先頭 4 つと綴りが一致する。
(define primitive-type-names '(Int Bool Unit String))

;; spec §5.2。Surface の節点はすべて (Ctor span ...) の形なので、span は
;; 第 2 要素である。spec §7 が (span-of ty) と書いているものだが、
;; span-core.rkt の span-of は #:lit と #:var の形も見るので名前を分ける。
(define (node-span n) (second n))

;; spec §6。宣言の並びを 1 度目に読む。名前の衝突と重複だけを見て、
;; 展開前の sty のまま表へ入れる。前方参照を許すには、展開を始める前に
;; 全宣言を読み終えている必要がある。
(define (build-alias-env items fail)
  (for/fold ([env (hash)]) ([item (in-list items)])
    (match item
      [`(STypeDecl ,_ (SName ,s_n ,name) ,ty)
       ;; spec §6.3。Self は trait 宣言の中だけの名前であり、別名にできない。
       (when (eq? name 'Self)
         (fail 'surface-unknown-type-name s_n))
       ;; spec §6.1。原始型との衝突を重複より先に見る。これで
       ;; type Int を 2 回書いても E-SUR-011 が 1 つ目で出る。
       (when (memq name primitive-type-names)
         (fail 'surface-reserved-type-name s_n))
       (when (hash-has-key? env name)
         (fail 'surface-duplicate-type-alias s_n))
       (hash-set env name ty)]
      [_ env])))

;; spec §6.1。2 度目は宣言の並び順に読む。使われない宣言の中の誤りも
;; ここで見つかる。展開の結果は捨て、診断のためだけに歩く。
;; 宣言している名前を stack の初期値にするので、循環の診断は
;; 「その宣言の定義の中にある参照」を指す。
(define (check-alias-definitions items env fail)
  (for ([item (in-list items)])
    (match item
      [`(STypeDecl ,_ (SName ,_ ,name) ,ty)
       (lower-sty ty env fail (list name))]
      [_ (void)])))

;; spec §7.2.1。sty から uτ を作る。span は uτ に残らず、包む側の
;; (#:ty uτ s) が持つ。別名を展開しても包みは展開前の使用箇所の span を
;; 持つので、ここは span を返さない。
;; spec §6。stack は展開中の別名である。同じ別名を 2 箇所から参照するのは
;; 共有であって循環ではないため、「一度でも展開した名前の集合」では
;; 判定しない。定義を展開し終えれば呼び出しの戻りとともに降りる。
(define (lower-sty ty env fail [stack '()] #:self? [self? #f])
  (match ty
    [`(TName ,s Self)
     (if self? 'Self (fail 'surface-unknown-type-name s))]
    [`(TName ,s ,name)
     (cond
       [(memq name primitive-type-names) name]
       [(memq name stack) (fail 'surface-recursive-type-alias s)]
       [(hash-ref env name #f)
        => (λ (definition) (lower-sty definition env fail (cons name stack)))]
       [else (fail 'surface-unknown-type-name s)])]
    [`(TRec ,_ ,fields)
     `(Record ,(lower-ty-fields fields env fail stack #:self? self?))]
    [`(TFn ,_ ,arguments ,result)
     ;; spec §7.2.1。効果行と義務は Surface に表記が無いので空である。
     `(NFn ,(for/list ([a (in-list arguments)])
              (lower-sty a env fail stack #:self? self?))
           ,(lower-sty result env fail stack #:self? self?)
           ()
           ())]))

;; spec §7.2.1。TRec の欄の可変性は imm に固定する。Surface に mut の
;; 表記が無いためである。
;; spec §6.1。左から右へ見て、最初の 2 度目で止める。
(define (lower-ty-fields fields env fail stack #:self? [self? #f])
  (for/fold ([seen '()] [row '()] #:result (reverse row))
            ([field (in-list fields)])
    (match field
      [`(TField ,_ (SLabel ,s_l ,label) ,ty)
       (when (memq label seen)
         (fail 'surface-duplicate-field s_l))
       (values (cons label seen)
               (cons (list label (lower-sty ty env fail stack #:self? self?) 'imm)
                     row))])))

;; spec §6.4。lower-sty が作る NFn は UCore の 4 欄であり、template-type? と
;; type-shape-ok? は Typed Core の 6 欄を要求する。この差を埋める。
;; 効果行と義務は Surface に表記が無いので空にし、origin は宣言が利用者の
;; 原文に由来するので User にする。
(define (lift-template-type t)
  (match t
    [`(NFn ,args ,ret ,_ ,_)
     `(NFn ,(map lift-template-type args) ,(lift-template-type ret)
           () () () User)]
    [(? list?) (map lift-template-type t)]
    [_ t]))

;; spec §6.6 手順 3。基底へ行を重ねて trait-env を作り直す。
;; 衝突した鍵は必ず新しい行の鍵である。基底どうしの衝突は基底を
;; 作った時点で落ちており、新しい trait 名どうしの衝突は E-SUR-013 が
;; 先に拾い、新しい impl の oid は next-impl-index が一意にする。
(define (extend-env base trait-rows impl-rows spans fail)
  (make-trait-env
   #:trait (append (trait-env-trait-rows base) trait-rows)
   #:impl (append (trait-env-impl-rows base) impl-rows)
   #:intersect (trait-env-intersect-rows base)
   #:scope (trait-env-scope-rows base)
   #:fail (λ (reason kind key) (fail reason (hash-ref spans (cons kind key))))))

;; spec §6.6 手順 1。template は欄の並びであり、Record の包みを持たない。
(define (lower-trait-decls items base env fail)
  (for/fold ([rows '()] [spans (hash)] #:result (values (reverse rows) spans))
            ([item (in-list items)])
    (match item
      [`(STraitDecl ,s (SName ,s_n ,name) ,fields)
       (when (or (trait-row-by-name name base)
                 (findf (λ (r) (eq? (trait-name r) name)) rows))
         (fail 'surface-duplicate-trait-decl s_n))
       (define oid (string->symbol (format "o-trait-user-~a" name)))
       (define template
         (second (normalize-type
                  (lift-template-type
                   `(Record ,(lower-ty-fields fields env fail '() #:self? #t))))))
       (define row (list oid name 'root template))
       (values (cons row rows)
               (hash-set* spans (cons 'trait-name name) s_n
                          (cons 'origin-id oid) s
                          (cons 'primitive-name (trait-constant-name row)) s))]
      [_ (values rows spans)])))

;; spec §6.6。基底を含めた通し番号にする。基底が既定の環境であれば
;; 利用者の impl 行が無いので 1 から始まる。
(define (next-impl-index env trait)
  (define prefix (format "o-impl-user-~a-" trait))
  (add1
   (for/fold ([m 0]) ([row (in-list (trait-env-impl-rows env))])
     (define s (symbol->string (impl-oid row)))
     (define n (string-length prefix))
     (define suffix
       (and (> (string-length s) n)
            (string=? prefix (substring s 0 n))
            (substring s n)))
     ;; <n> は ASCII の数字列だけを番号と読む。string->number は
     ;; "1/2" や "1.5" も数として返すので、そのまま使うと正整数から外れる。
     (if (and suffix (regexp-match? #px"^[0-9]+$" suffix))
         (max m (string->number suffix))
         m))))

;; spec §6.6 手順 2。core-info は宣言の節点から (binder prim) を引く表で
;; あり、lower-item が行と同じ番号の項を作るために使う。
(define (lower-impl-decls items staged spans env fail)
  (for/fold ([tenv staged] [rows '()] [spans spans] [info (hasheq)]
             #:result (values (reverse rows) spans info))
            ([item (in-list items)])
    (match item
      [`(SImplDecl ,s (SName ,s_n ,trait) ,ty (SRec ,s_b ,fields))
       (define trait-row (or (trait-row-by-name trait tenv)
                             (fail 'surface-unknown-trait-name s_n)))
       (when (memq trait (map intersect-output (trait-env-intersect-rows tenv)))
         (fail 'surface-impl-composite-trait s_n))
       (define labels (for/list ([f (in-list fields)])
                        (match f [`(SField ,_ (SLabel ,_ ,label) ,_) label])))
       (unless (equal? (sort labels symbol<?)
                       (sort (map first (trait-template trait-row)) symbol<?))
         (fail 'surface-impl-requirement-mismatch s_b))
       (define target (normalize-type (lift-template-type (lower-sty ty env fail))))
       (when (for/or ([r (in-list (impl-rows-by-trait trait tenv))])
               (type-equiv? (impl-target-type r) target))
         (fail 'surface-duplicate-impl-decl (node-span ty)))
       (define n (next-impl-index tenv trait))
       (define oid (string->symbol (format "o-impl-user-~a-~a" trait n)))
       (define prim (string->symbol (format "impl-user-~a-~a" trait n)))
       (define binder (string->symbol (format "%impl-~a-~a" trait n)))
       (define row (list oid prim 'impl trait target 'root))
       (define spans* (hash-set* spans (cons 'origin-id oid) s
                                 (cons 'primitive-name prim) s))
       (values (extend-env tenv '() (list row) spans* fail)
               (cons row rows) spans* (hash-set info item (list binder prim)))]
      [_ (values tenv rows spans info)])))

;; spec §7.2。Fn と Recur が同じ形の引数欄を取るので、ここへ切り出す。
;; 型注釈の span は sty の使用箇所のものであり、別名を展開しても動かない。
(define (lower-params params env fail)
  (for/list ([p (in-list params)])
    (match p
      [`(SParam ,_ (SName ,s_x ,x) ,ty)
       (list (list '#:bind x s_x)
             (list '#:ty (lower-sty ty env fail) (node-span ty)))])))

;; spec §7.2。record 式の欄も可変性を imm に固定する。Surface に mut の
;; 表記が無いためである。
;; spec §6.1。左から右へ見て、最初の 2 度目で止める。
(define (lower-rec-fields fields env fail)
  (for/fold ([seen '()] [row '()] #:result (reverse row))
            ([field (in-list fields)])
    (match field
      [`(SField ,_ (SLabel ,s_l ,label) ,e)
       (when (memq label seen)
         (fail 'surface-duplicate-field s_l))
       (values (cons label seen)
               (cons (list (list '#:lbl label s_l) 'imm (lower-sexpr e env fail))
                     row))])))

;; spec §7.2 の対応表である。
(define (lower-sexpr e env fail)
  (match e
    [`(SInt ,s ,n) `(#:lit ,n ,s)]
    [`(SStr ,s ,str) `(#:lit ,str ,s)]
    [`(SUnit ,s) `(#:lit unit ,s)]
    ;; true と false は構成子であり literal ではない。
    [`(SBool ,s ,b) `(Construct ,s ,b)]
    [`(SVar ,s ,x) `(#:var ,x ,s)]
    [`(SFn ,s ,params ,result-ty ,body)
     ;; Surface に効果の表記が無いので効果行は空である。span は Fn 自身の
     ;; ものを使う。
     `(Fn ,s ,(lower-params params env fail)
          (#:ty ,(lower-sty result-ty env fail) ,(node-span result-ty))
          (#:ef () ,s)
          ,(lower-sexpr body env fail))]
    [`(SApply ,s ,f ,arguments)
     `(Apply ,s ,(lower-sexpr f env fail)
             ,@(for/list ([a (in-list arguments)]) (lower-sexpr a env fail)))]
    [`(SProj ,s ,target (SLabel ,s_l ,label))
     `(Proj ,s ,(lower-sexpr target env fail) (#:lbl ,label ,s_l))]
    ;; spec §6.1。受け側を 1 度だけ束縛し、選んだ label ごとに Proj を積んだ
    ;; Rec を作る。受け側の綴り %projrec は lexer の ident-start? が % を
    ;; 受理しないため、入力の識別子と衝突しない。入れ子の射影では内側の
    ;; %projrec が外側の束縛式の中だけで使われるので、影が問題にならない。
    [`(SProjRec ,s ,target ,labels)
     (define s_r (node-span target))
     (define receiver `(#:var %projrec ,s_r))
     `(Let ,s ((#:bind %projrec ,s_r) const)
           ,(lower-sexpr target env fail)
           (Rec ,s
                ,(for/list ([l (in-list labels)])
                   (define s_l (second l))
                   (define name (third l))
                   `((#:lbl ,name ,s_l) imm
                     (Proj ,s_l ,receiver (#:lbl ,name ,s_l))))))]
    [`(SRec ,s ,fields)
     `(Rec ,s ,(lower-rec-fields fields env fail))]
    [`(SBlock ,_ ,binds ,tail)
     ;; spec §7.2。block 自身は節点を作らず、束縛の入れ子と末尾式になる。
     (fold-items binds tail env (hasheq) fail)]))

;; spec §7.3。尾部の span は「その宣言の始まり」から「末尾式の終わり」までで
;; ある。span は (#:span sid lo hi) の 4 要素である。
(define (tail-span item end-span)
  (list '#:span (second end-span) (third (node-span item)) (fourth end-span)))

;; spec §7.2。spitem 1 つを、残りの項を取って包む手続きへ落とす。
;; 型と trait の宣言は節点を作らないので、残りをそのまま返す。
(define (lower-item item s_tail env core-info fail)
  (match item
    [`(STypeDecl ,_ ,_ ,_) (λ (rest) rest)]
    [`(STraitDecl ,_ ,_ ,_) (λ (rest) rest)]
    [`(SImplDecl ,s ,_ ,_ ,body)
     ;; spec §6.6。生成した primitive を Let の束縛名にしない。elab は局所の
     ;; environment を Γ0 より先に引くので、同名の Let は Proof の経路を隠す。
     (match-define (list binder prim) (hash-ref core-info item))
     (define body-core (lower-sexpr body env fail))
     (λ (rest) `(Let ,s_tail ((#:bind ,binder ,s) const)
                     (Apply ,s (#:var ,prim ,s) ,body-core) ,rest))]
    [`(SBind ,_ ,bmode (SName ,s_x ,x) ,ty-or-none ,bound)
     (define binder
       (if (eq? ty-or-none '#:none)
           ;; spec §8。注釈が無ければ 2 欄の束縛子である。
           (list (list '#:bind x s_x) bmode)
           (list (list '#:bind x s_x) bmode
                 (list '#:ty (lower-sty ty-or-none env fail)
                       (node-span ty-or-none)))))
     (define bound-core (lower-sexpr bound env fail))
     (λ (rest) `(Let ,s_tail ,binder ,bound-core ,rest))]
    [`(SFnDecl ,s (SName ,s_f ,f) ,params ,result-ty ,body)
     (define params-core (lower-params params env fail))
     (define result-core (lower-sty result-ty env fail))
     (define body-core (lower-sexpr body env fail))
     ;; 効果行の span は宣言自身のものである。Surface に効果の表記が無い。
     (λ (rest) `(Recur ,s_tail (#:bind ,f ,s_f) ,params-core
                       (#:ty ,result-core ,(node-span result-ty))
                       (#:ef () ,s)
                       ,body-core ,rest))]))

;; spec §7.2。畳み込みは右である。lower [b1 b2] e = L(b1, L(b2, lower e))。
;; spec §6.1。診断は 1 件だけ返すので、どれが返るかは走る順序で決まる。
;; 落とす順序は原文の並び順であり、包む順序だけが逆である。末尾式は
;; 原文では最後なので、宣言をすべて落とし終えてから落とす。
(define (fold-items items tail env core-info fail)
  (define end-span (node-span tail))
  (define wraps
    (for/list ([item (in-list items)])
      (lower-item item (tail-span item end-span) env core-info fail)))
  (define tail-core (lower-sexpr tail env fail))
  (for/fold ([acc tail-core]) ([wrap (in-list (reverse wraps))])
    (wrap acc)))

;; spec §7。入口である。parse の診断はそのまま返す。呼ぶ側に
;; 「parse の結果を場合分けしてから lower-surface を呼ぶ」手続きを課すと、
;; その場合分けを忘れた経路が静かに落ちる（parser.rkt:10-13 と同じ理由）。
;; spec §6.1。診断は 1 件だけ返すので、最初の fail で脱出する。
(define (lower-surface program base)
  (cond
    [(diagnostic? program) program]
    [else
     (match program
       [`(SProgram ,_ ,items ,e)
        (let/ec return
          (define (fail key s)
            (return (diagnostic-of 'surface key #:primary-span s)))
          (define env (build-alias-env items fail))
          (check-alias-definitions items env fail)
          (define-values (trait-rows trait-spans)
            (lower-trait-decls items base env fail))
          (define staged (extend-env base trait-rows '() trait-spans fail))
          (define-values (impl-rows spans core-info)
            (lower-impl-decls items staged trait-spans env fail))
          (lowered (fold-items items e env core-info fail)
                   trait-rows impl-rows spans))])]))

#lang racket

(require racket/match
         racket/set
         (only-in redex/reduction-semantics caching-enabled?)
         "diagnostic.rkt"
         "rows.rkt"
         "traits.rkt"
         "type-equiv.rkt"
         (only-in "data-env.rkt"
                  data-index-decls
                  data-index-constructors
                  empty-data-index
                  build-data-index
                  data-reserved-type-names
                  builtin-data-constructors)
         (only-in "origins.rkt" Γ0 validate-data-decls!)
         (only-in (submod "data-env.rkt" data-env-internal) data-index-parameter))

(provide lower-surface lift-template-type (struct-out lowered))

(struct lowered (term trait-rows impl-rows intersect-rows data-decls spans) #:transparent)

;; spec §7.2.1。別名の表を引かずにそのまま uτ になる名前である。
;; ucore.rkt:13 の A の先頭 4 つと綴りが一致する。
(define primitive-type-names '(Int Bool Unit String))
(define type-params (make-parameter '()))

;; spec §9.2。Surface の型構成子の名前と引数の個数である。
;; 写し先はどれも uτ に既にある形で、P2l2b が data 型を足す。
(define type-constructor-arities
  '((List . 1) (Option . 1) (Result . 2) (Owned . 1)))
(define (type-constructor-arity name)
  (cond [(assq name type-constructor-arities) => cdr] [else #f]))

;; spec §5.2。Surface の節点はすべて (Ctor span ...) の形なので、span は
;; 第 2 要素である。spec §7 が (span-of ty) と書いているものだが、
;; span-core.rkt の span-of は #:lit と #:var の形も見るので名前を分ける。
(define (node-span n) (second n))

;; spec §6。宣言の並びを 1 度目に読む。名前の衝突と重複だけを見て、
;; 展開前の sty のまま表へ入れる。前方参照を許すには、展開を始める前に
;; 全宣言を読み終えている必要がある。
(define (data-declaration-related s_T T)
  (if s_T
      (list (list 'data-declaration s_T (format "data 型 ~a の宣言" T)))
      '()))

;; P2l2b1 spec §9.3.4。正則性と正値性の失敗を Surface の span へ戻す。
(define ((data-validation-bail spans fail) reason kind key)
  (define (span-of k)
    (hash-ref spans k (λ () (error 'lower-surface "span の無い data の失敗: ~s ~s" reason key))))
  (match* (kind reason)
    [('data (or 'irregular-recursion 'non-positive-recursion))
     (define T (first key))
     (fail (if (eq? reason 'irregular-recursion)
               'surface-irregular-data-recursion
               'surface-non-positive-data-recursion)
           (span-of (cons 'data key))
           #:related (data-declaration-related (span-of (cons 'data-name T)) T))]
    [(_ _) (error 'lower-surface "Surface から届かない data の失敗: ~s ~s ~s" kind reason key)]))

(define (build-alias-env items base base-data fail)
  (define source-traits
    (for/fold ([h (hasheq)]) ([item (in-list items)])
      (match item
        [`(STraitDecl ,_ (SName ,s_n ,name) ,_)
         (if (hash-has-key? h name) h (hash-set h name s_n))]
        [_ h])))
  (define-values (types seen)
    (for/fold ([env (hash)] [seen (hasheq)]) ([item (in-list items)])
      (match item
        [`(STypeDecl ,_ (SName ,s_n ,name) ,ty)
         ;; spec §6.3。Self は trait 宣言の中だけの名前であり、別名にできない。
         (when (eq? name 'Self)
           (fail 'surface-unknown-type-name s_n))
         ;; spec §6.1。基本型との衝突を重複より先に見る。
         (when (memq name primitive-type-names)
           (fail 'surface-reserved-type-name s_n))
         ;; spec §9.2。型構成子の名前の別名は、TName と TApp で
         ;; 同じ名前が別の型を指すので拒否する。
         (when (type-constructor-arity name)
           (fail 'surface-reserved-type-constructor-name s_n))
         (when (hash-has-key? env name)
           (fail 'surface-duplicate-type-alias s_n))
         (match (hash-ref seen name #f)
           [(list 'data s_d)
            (fail 'surface-type-data-name-collision s_n
                  #:related (data-declaration-related s_d name))]
           [_ (void)])
         (when (hash-has-key? base-data name)
           (fail 'surface-type-data-name-collision s_n))
         (cond
           [(hash-ref source-traits name #f)
            => (λ (s_t)
                 (fail 'surface-type-trait-name-collision s_n
                       #:related (list (list 'trait-declaration s_t
                                             (format "trait ~a の宣言" name)))))]
           [(trait-row-by-name name base)
            (fail 'surface-type-trait-name-collision s_n)])
         (values (hash-set env name ty)
                 (hash-set seen name (list 'alias s_n)))]
        [`(STraitDecl ,_ (SName ,s_n ,name) ,_)
         (when (memq name primitive-type-names)
           (fail 'surface-type-trait-name-collision s_n))
         ;; spec §9.2。型構成子の名前の trait は、TApp の解決で
         ;; 組み込みの型構成子を隠すので型と trait の衝突として拒否する。
         (when (type-constructor-arity name)
           (fail 'surface-type-trait-name-collision s_n))
         (match (hash-ref seen name #f)
           [(list 'data s_d)
            (fail 'surface-type-trait-name-collision s_n
                  #:related (data-declaration-related s_d name))]
           [_ (void)])
         (when (hash-has-key? base-data name)
           (fail 'surface-type-trait-name-collision s_n))
         (values env (if (hash-has-key? seen name)
                         seen
                         (hash-set seen name (list 'trait s_n))))]
        [`(SDataDecl ,_ (SName ,s_n ,name) ,_ ,_ ...)
         ;; P2l2b1 spec §4.3 と §11 の段 1。Self、組み込みの型、data 型どうし、
         ;; 型別名、trait の順に見る。
         (when (eq? name 'Self)
           (fail 'surface-unknown-type-name s_n))
         (when (memq name data-reserved-type-names)
           (fail 'surface-reserved-data-type-name s_n))
         (match (hash-ref seen name #f)
           [(list 'data s_d)
            (fail 'surface-duplicate-data-type s_n
                  #:related (data-declaration-related s_d name))]
           [_ (void)])
         (when (hash-has-key? base-data name)
           (fail 'surface-duplicate-data-type s_n))
         (match (hash-ref seen name #f)
           [(list 'alias s_a)
            (fail 'surface-type-data-name-collision s_n
                  #:related (list (list 'type-alias-declaration s_a
                                        (format "型別名 ~a の宣言" name))))]
           [(list 'trait s_t)
            (fail 'surface-type-trait-name-collision s_n
                  #:related (list (list 'trait-declaration s_t
                                        (format "trait ~a の宣言" name))))]
           [_ (void)])
         (when (trait-row-by-name name base)
           (fail 'surface-type-trait-name-collision s_n))
         (values env (hash-set seen name (list 'data s_n)))]
        [_ (values env seen)])))
  ;; data 型と基底 data 型の marker を全て先に置き、前方参照を許す。
  (define with-data
    (for/fold ([env types]) ([item (in-list items)])
      (match item
        [`(SDataDecl ,_ (SName ,s_n ,name) ,params ,_ ...)
         (hash-set env name (list 'data s_n (length params)))]
        [_ env])))
  (define with-base-data
    (for/fold ([env with-data]) ([(name decl) (in-hash base-data)])
      (hash-set env name (list 'data #f (length (second decl))))))
  ;; trait 名を型別名より優先してマークする。衝突は上で既に拒否した。
  (define trait-marks
    (for/fold ([h (hash)])
              ([name (in-list (append (map trait-name (trait-env-trait-rows base))
                                      (hash-keys source-traits)))])
      (hash-set h name 'trait)))
  (for/fold ([env with-base-data]) ([(name marker) (in-hash trait-marks)])
    (hash-set env name marker)))

;; spec §6.1。2 度目は宣言の並び順に読む。使われない宣言の中の誤りも
;; ここで見つかる。展開の結果は捨て、診断のためだけに歩く。
;; 宣言している名前を stack の初期値にするので、循環の診断は
;; 「その宣言の定義の中にある参照」を指す。
(define (check-alias-definitions items env composite-names fail)
  (for ([item (in-list items)])
    (match item
      [`(STypeDecl ,_ (SName ,_ ,name) ,ty)
       (unless (memq name composite-names)
         (lower-sty ty env fail (list name)))]
      [_ (void)])))

;; spec §4.3 と §11 の段 2。constructor 名の重なりを原文の順に見る。
;; 重複の検査を値の名前との検査より先に全宣言について終える。
;; 組み込みと基底の constructor は原文の span を持たないので related を持たない。
(define (check-data-constructors items base-constructors gamma0-names fail)
  (define (constructors-of item)
    (match item
      [`(SDataDecl ,_ ,_ ,_ ,variants ...)
       (for/list ([v (in-list variants)])
         (match v [`((SName ,s ,k) ,_) (list k s)]))]
      [_ '()]))
  (define (related-of relation what name s)
    (list (list relation s (format "~a ~a の宣言" what name))))
  (for/fold ([seen (hasheq)]) ([c (in-list (append-map constructors-of items))])
    (match-define (list k s) c)
    (cond
      [(or (memq k builtin-data-constructors) (hash-has-key? base-constructors k))
       (fail 'surface-duplicate-constructor s)]
      [(hash-ref seen k #f)
       => (λ (s0) (fail 'surface-duplicate-constructor s
                        #:related (related-of 'constructor-declaration "constructor" k s0)))]
      [else (hash-set seen k s)]))
  ;; 値の名前との重なり。原文の関数とはどちらが先でも後の名前を primary にする。
  (for/fold ([ctors (hasheq)] [fns (hasheq)] #:result (void))
            ([item (in-list items)])
    (match item
      [`(SDataDecl ,_ ,_ ,_ ,_ ...)
       (for/fold ([ctors ctors] [fns fns]) ([c (in-list (constructors-of item))])
         (match-define (list k s) c)
         (cond
           [(hash-ref fns k #f)
            => (λ (s0) (fail 'surface-constructor-value-name-collision s
                             #:related (related-of 'function-declaration "関数" k s0)))]
           [(memq k gamma0-names)
            (fail 'surface-constructor-value-name-collision s)]
           [else (values (hash-set ctors k s) fns)]))]
      [`(SFnDecl ,_ (SName ,s ,f) ,_ ,_ ,_ ,_)
       (cond
         [(hash-ref ctors f #f)
          => (λ (s0) (fail 'surface-constructor-value-name-collision s
                           #:related (related-of 'constructor-declaration "constructor" f s0)))]
         [(hash-has-key? base-constructors f)
          (fail 'surface-constructor-value-name-collision s)]
         [else (values ctors (hash-set fns f s))])]
      [_ (values ctors fns)])))

;; spec §11 の段 3。型仮引数の重複と Self を見る。
(define (check-data-type-parameters items fail)
  (for ([item (in-list items)])
    (match item
      [`(SDataDecl ,_ ,_ ,params ,_ ...)
       (for/fold ([seen (hasheq)]) ([p (in-list params)])
         (match-define `(SName ,s ,x) p)
         (when (eq? x 'Self)
           (fail 'surface-unknown-type-name s))
         (cond
           [(hash-ref seen x #f)
            => (λ (s0) (fail 'surface-duplicate-type-parameter s
                             #:related (list (list 'type-parameter-declaration s0
                                                   (format "型仮引数 ~a の宣言" x)))))]
           [else (hash-set seen x s)]))]
      [_ (void)])))

;; spec §9.3.3 と §11 の段 4。欄の型を型仮引数の下で解決し、台帳の宣言の形へ写す。
;; 欄ごとの span と宣言の名前の span を返し、driver が台帳の失敗を原文へ戻す。
(define (lower-data-decls items env fail)
  (for/fold ([decls '()] [spans (hash)] #:result (values (reverse decls) spans))
            ([item (in-list items)])
    (match item
      [`(SDataDecl ,_ (SName ,s_T ,T) ,params ,variants ...)
       (define xs (map third params))
       (parameterize ([type-params xs])
         (for/fold ([ctors '()] [spans (hash-set spans (cons 'data-name T) s_T)]
                    #:result (values (cons (list T xs (reverse ctors)) decls) spans))
                   ([v (in-list variants)])
           (match-define `((SName ,_ ,K) ,fields) v)
           (define σs
             (for/list ([f (in-list fields)])
               (or (normalize-type (lift-template-type (lower-sty f env fail)))
                   (fail 'surface-type-not-normalizable (node-span f)))))
           (values (cons (list K σs) ctors)
                   (for/fold ([h spans]) ([f (in-list fields)] [i (in-naturals)])
                     (hash-set h (cons 'data (list T K i #f)) (node-span f))))))]
      [_ (values decls spans)])))

;; spec §5.1。合成候補の根と TInter だけを辿り、その葉を返す。
(define (inter-leaves ty)
  (match ty
    [`(TInter ,_ ,l ,r) (append (inter-leaves l) (inter-leaves r))]
    [_ (list ty)]))

(define (composition-candidate? ty)
  (and (match ty [`(TInter ,_ ,_ ,_) #t] [_ #f])
       (andmap (λ (leaf) (match leaf [`(TName ,_ ,_) #t] [_ #f]))
               (inter-leaves ty))))

;; spec §5.1。最大不動点を取り、trait 名または候補名以外の葉が残る候補を除く。
(define (classify-compositions items trait-names)
  (define candidates
    (for/list ([item (in-list items)]
               #:when (match item
                        [`(STypeDecl ,_ ,_ ,ty) (composition-candidate? ty)]
                        [_ #f]))
      (match-define `(STypeDecl ,s (SName ,s_n ,name) ,ty) item)
      (list name s s_n ty)))
  (let loop ([cs candidates])
    (define names (map first cs))
    (define kept
      (filter (λ (c)
                (for/and ([leaf (in-list (inter-leaves (fourth c)))])
                  (define n (third leaf))
                  (or (memq n trait-names) (memq n names))))
              cs))
    (if (= (length kept) (length cs)) cs (loop kept))))

;; spec §5.3。葉は組より前、葉どうしは symbol<?、組どうしは辞書順である。
(define (key<? a b)
  (cond
    [(and (symbol? a) (symbol? b)) (symbol<? a b)]
    [(symbol? a) #t]
    [(symbol? b) #f]
    [(equal? (first a) (first b)) (key<? (second a) (second b))]
    [else (key<? (first a) (first b))]))

(define (key-pair a b) (if (key<? b a) (list b a) (list a b)))

;; spec §5.3。基底の出力名から構造鍵を再帰的に求める。
(define (base-composite-keys base)
  (define by-output
    (for/hasheq ([r (in-list (trait-env-intersect-rows base))])
      (values (intersect-output r) r)))
  (define (key-of n)
    (match (hash-ref by-output n #f)
      [#f n]
      [r (key-pair (key-of (intersect-left r)) (key-of (intersect-right r)))]))
  (for/hasheq ([n (in-hash-keys by-output)]) (values n (key-of n))))

(define (sty->string ty)
  (match ty
    [`(TName ,_ ,n) (symbol->string n)]
    [`(TInter ,_ ,l ,r) (format "(~a & ~a)" (sty->string l) (sty->string r))]))

;; spec §6.2 一段目。宣言名の参照を再帰的に解決し、全宣言の根の鍵と template を記録する。
(define (resolve-composition-keys comps template-of composite-keys fail)
  (define by-name (for/hasheq ([c (in-list comps)]) (values (first c) c)))
  (define memo (make-hasheq))
  (define (node ty visiting)
    (match ty
      [`(TName ,s ,n)
       (cond
         [(hash-ref by-name n #f)
          (when (memq n visiting)
            (fail 'surface-recursive-type-alias s))
          (decl n visiting)]
         [else (cons (hash-ref composite-keys n n) (template-of n))])]
      [`(TInter ,s ,l ,r)
       (match-define (cons kl tl) (node l visiting))
       (match-define (cons kr tr) (node r visiting))
       (define (invalid)
         (fail 'surface-invalid-trait-composition s
               #:related (list (list 'composition-left (node-span l)
                                     (format "`&` の左辺 ~a" (sty->string l)))
                               (list 'composition-right (node-span r)
                                     (format "`&` の右辺 ~a" (sty->string r))))))
       (define t (field-row-⊕ tl tr))
       (when (equal? kl kr) (invalid))
       (unless t (invalid))
       (cons (key-pair kl kr) t)]))
  (define (decl n visiting)
    (or (hash-ref memo n #f)
        (let ([v (node (fourth (hash-ref by-name n)) (cons n visiting))])
          (hash-set! memo n v)
          v)))
  (for ([c (in-list comps)]) (decl (first c) '()))
  memo)

;; spec §6.2 二段目。出力名を決め、新しい鍵ごとに trait 行と intersect 行を作る。
(define (emit-compositions comps memo base composite-keys source-rows)
  (define by-name (for/hasheq ([c (in-list comps)]) (values (first c) c)))
  (define out (make-hash))
  (for ([(n k) (in-hash composite-keys)]) (hash-set! out k n))
  (define named (make-hash))
  (for ([c (in-list comps)])
    (define k (car (hash-ref memo (first c))))
    (unless (hash-has-key? named k) (hash-set! named k c)))
  (define templates (make-hasheq))
  (for ([r (in-list (append (trait-env-trait-rows base) source-rows))])
    (hash-set! templates (trait-name r) (trait-template r)))
  (define hidden 0)
  (define index (next-intersect-index base))
  (define trait-rows '())
  (define intersect-rows '())
  (define spans (hash))
  (define visited (mutable-seteq))
  (define (emit! k o-l o-r s)
    (define c (hash-ref named k #f))
    (define name
      (if c
          (first c)
          (begin
            (set! hidden (add1 hidden))
            (string->symbol (format "%compose-~a" hidden)))))
    (match-define (list l r) (sort (list o-l o-r) symbol<?))
    (define template (field-row-⊕ (hash-ref templates l) (hash-ref templates r)))
    (define trow (list (string->symbol (format "o-trait-user-~a" name)) name 'root template))
    (define irow (list (string->symbol (format "o-intersect-user-~a" index))
                       (string->symbol (format "intersect-user-~a" index))
                       l r name))
    (define-values (s-name s-decl)
      (if c (values (third c) (second c)) (values s s)))
    (set! index (add1 index))
    (hash-set! templates name template)
    (hash-set! out k name)
    (set! trait-rows (cons trow trait-rows))
    (set! intersect-rows (cons irow intersect-rows))
    (set! spans (hash-set* spans
                           (cons 'trait-name name) s-name
                           (cons 'origin-id (first trow)) s-decl
                           (cons 'primitive-name (trait-constant-name trow)) s-decl
                           (cons 'origin-id (intersect-oid irow)) s-decl
                           (cons 'primitive-name (intersect-name irow)) s-decl))
    name)
  (define (node ty)
    (match ty
      [`(TName ,_ ,n)
       (cond
         [(hash-ref by-name n #f)
          => (λ (c)
               (unless (set-member? visited n)
                 (set-add! visited n)
                 (node (fourth c)))
               (let ([k (car (hash-ref memo n))])
                 (cons k (hash-ref out k))))]
         [else (cons (hash-ref composite-keys n n) n)])]
      [`(TInter ,s ,l ,r)
       (match-define (cons kl o-l) (node l))
       (match-define (cons kr o-r) (node r))
       (define k (key-pair kl kr))
       (cons k (or (hash-ref out k #f) (emit! k o-l o-r s)))]))
  (for ([c (in-list comps)])
    (unless (set-member? visited (first c))
      (set-add! visited (first c))
      (node (fourth c))))
  (define outputs
    (for/hasheq ([c (in-list comps)])
      (values (first c) (hash-ref out (car (hash-ref memo (first c)))))))
  (values (reverse trait-rows) (reverse intersect-rows) spans outputs))

;; spec §7.2.1。sty から uτ を作る。span は uτ に残らず、包む側の
;; (#:ty uτ s) が持つ。別名を展開しても包みは展開前の使用箇所の span を
;; 持つので、ここは span を返さない。
;; spec §6。stack は展開中の別名である。同じ別名を 2 箇所から参照するのは
;; 共有であって循環ではないため、「一度でも展開した名前の集合」では
;; 判定しない。定義を展開し終えれば呼び出しの戻りとともに降りる。
;; spec §6.2。型欄だけを辿る。Record の label の Self は型ではない。
(define (type-has-self? t)
  (match t
    ['Self #t]
    [`(Record ,row) (for/or ([field (in-list row)]) (type-has-self? (second field)))]
    [(? pair?) (ormap type-has-self? t)]
    [_ #f]))

;; SUR-003。spec §5.2。Return は宣言 row にだけ書ける。
(define argless-effect-labels '(Partial Suspend Compile Own Mutation))

(define (lower-row row env fail stack self? #:type-row? type-row?)
  (match row
    ['#:none '()]
    [`(SEffRow ,_ ,labels)
     (for/list ([label (in-list labels)])
       (lower-effect-label label env fail stack self? type-row?))]))

;; ラベル名、引数の有無、型引数の lowering の順に検査する。
(define (lower-effect-label label env fail stack self? type-row?)
  (match label
    [`(SEffLabel ,s ,name ,argument)
     (cond
       [(eq? name 'Yield)
        (if (eq? argument '#:none)
            (fail 'surface-invalid-effect-label s)
            `(Yield ,(lower-sty argument env fail stack #:self? self?)))]
       [(or (memq name argless-effect-labels)
            (and (eq? name 'Return) (not type-row?)))
        (if (eq? argument '#:none) name (fail 'surface-invalid-effect-label s))]
       [else (fail 'surface-invalid-effect-label s)])]))

(define (lower-sty ty env fail [stack '()] #:self? [self? #f])
  (match ty
    [`(TName ,s Self)
     (if self? 'Self (fail 'surface-unknown-type-name s))]
    [`(TName ,s ,name)
     (cond
       [(memq name (type-params)) `(Param ,name)]
       [(memq name primitive-type-names) name]
       [(type-constructor-arity name)
        (fail 'surface-type-application-mismatch s)]
       [(memq name stack) (fail 'surface-recursive-type-alias s)]
       [(hash-ref env name #f)
        => (λ (definition)
             (match definition
               ['trait (fail 'surface-trait-in-type-position s)]
               [(list 'data _ 0) `(Data ,name ())]
               [(list 'data s_T _)
                (fail 'surface-type-application-mismatch s
                      #:related (data-declaration-related s_T name))]
               [_ (parameterize ([type-params '()])
                    (lower-sty definition env fail (cons name stack)))]))]
       [else (fail 'surface-unknown-type-name s)])]
    [`(TApp ,s (SName ,s_h ,name) ,arguments)
     (define (mismatch) (fail 'surface-type-application-mismatch s))
     (cond
       [(memq name (type-params)) (mismatch)]
       [(eq? name 'Self)
        (if self? (mismatch) (fail 'surface-unknown-type-name s_h))]
       [(memq name stack) (fail 'surface-recursive-type-alias s_h)]
       [(eq? (hash-ref env name #f) 'trait)
        (fail 'surface-trait-in-type-position s_h)]
       [(match (hash-ref env name #f) [(list 'data s_T n) (list s_T n)] [_ #f])
        => (λ (d)
             (match-define (list s_T n) d)
             (unless (= n (length arguments))
               (fail 'surface-type-application-mismatch s
                     #:related (data-declaration-related s_T name)))
             `(Data ,name ,(for/list ([a (in-list arguments)])
                             (lower-sty a env fail stack #:self? self?))))]
       [(or (memq name primitive-type-names) (hash-ref env name #f))
        (mismatch)]
       [(type-constructor-arity name)
        => (λ (arity)
             (unless (= arity (length arguments)) (mismatch))
             (cons name
                   (for/list ([a (in-list arguments)])
                     (lower-sty a env fail stack #:self? self?))))]
       [else (fail 'surface-unknown-type-name s_h)])]
    [`(TRec ,_ ,fields)
     `(Record ,(lower-ty-fields fields env fail stack #:self? self?))]
    [`(TFn ,_ ,arguments ,result ,row)
     `(NFn ,(for/list ([a (in-list arguments)])
              (lower-sty a env fail stack #:self? self?))
           ,(lower-sty result env fail stack #:self? self?)
           ,(lower-row row env fail stack self? #:type-row? #t)
           ())]
    [`(TUnion ,_ ,l ,r)
     `(Union ,(lower-sty l env fail stack #:self? self?)
             ,(lower-sty r env fail stack #:self? self?))]
    [`(TInter ,s ,l ,r)
     (define l* (lower-sty l env fail stack #:self? self?))
     (define r* (lower-sty r env fail stack #:self? self?))
     (define t `(Intersection ,l* ,r*))
     (if (or (type-has-self? l*) (type-has-self? r*)
             (normalize-type (lift-template-type t)))
         t
         (fail 'surface-type-not-normalizable s))]))

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
(define (extend-env base trait-rows impl-rows intersect-rows spans fail)
  (make-trait-env
   #:trait (append (trait-env-trait-rows base) trait-rows)
   #:impl (append (trait-env-impl-rows base) impl-rows)
   #:intersect (append (trait-env-intersect-rows base) intersect-rows)
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
       (define lifted
         (lift-template-type
          `(Record ,(lower-ty-fields fields env fail '() #:self? #t))))
       ;; spec §6.2.1。Self を含む & は対象型を見るまで正規化できない。
       ;; 全体が正規化できなければ、label で並べ、欄ごとに正規化できたものだけを置き換える。
       ;; 失敗した欄の形はそのまま残し、Intersection の項の順も変えない。
       (define template
         (match (normalize-type lifted)
           [`(Record ,row) row]
           [#f
            (for/list ([field (in-list (sort (second lifted) symbol<? #:key first))])
              (match-define (list label t mode) field)
              (list label (or (normalize-type t) t) mode))]))
       (define row (list oid name 'root template))
       (values (cons row rows)
               (hash-set* spans (cons 'trait-name name) s_n
                          (cons 'origin-id oid) s
                          (cons 'primitive-name (trait-constant-name row)) s))]
      [_ (values rows spans)])))

;; spec §6.2。基底を含めた接頭辞ごとの通し番号にする。
(define (next-index oids prefix)
  (add1
   (for/fold ([m 0]) ([oid (in-list oids)])
     (define s (symbol->string oid))
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

(define (next-impl-index env prefix)
  (next-index (map impl-oid (trait-env-impl-rows env)) prefix))

(define (next-intersect-index env)
  (next-index (map intersect-oid (trait-env-intersect-rows env)) "o-intersect-user-"))

;; spec §6.4。Surface が作る正規型の形についてだけ葉を数える。
;; Intersection は正規化で Record になるので、Record の節で数える。
;; spec §9.2。型構成子の適用は葉の個数が型から決まらないので #f を返す。
(define (sizable-leaves t)
  (define (sum ts)
    (for/fold ([n 0]) ([u (in-list ts)])
      (define k (and n (sizable-leaves u)))
      (and k (+ n k))))
  (match t
    [(or 'Int 'Bool 'Unit 'String) 1]
    [`(NFn ,_ ,_ ,_ ,_ ,_ ,_) 1]
    [`(Record ,row) (sum (map second row))]
    ;; 正規化した Union は平坦で重複が無いので、成分を一度ずつ数える。
    [`(Union ,_ ,_) (sum (union-members t))]
    [_ #f]))

;; 生成規則は名義で結び付ける。形が同じ利用者 trait には適用しない。
(define derive-recipes (hasheq 'o-trait-sizable sizable-leaves))

;; spec §6.2.1。Self を対象型で置き換えた要求型が正規化できなければ E-SUR-020 にする。
;; primary span は対象型、related は impl または derive が書いた trait 名である。
(define (check-requirements trait trait-row target ty s_n fail)
  (define bad
    (for/first ([field (in-list (instantiate-requirements (trait-template trait-row) target))]
                #:unless (normalize-type (second field)))
      field))
  (when bad
    (fail 'surface-type-not-normalizable (node-span ty)
          #:related (list (list 'trait-requirement s_n
                                (format "trait ~a の要求 ~a を正規化できない"
                                        trait (first bad)))))))

;; spec §6.6 手順 2。core-info は宣言の節点から (binder prim) を引く表で
;; あり、lower-item が行と同じ番号の項を作るために使う。derive の値は
;; (binder prim uτ generated-value) である。
(define (lower-impl-decls items staged spans env outputs fail)
  (for/fold ([tenv staged] [rows '()] [spans spans] [info (hasheq)]
             #:result (values (reverse rows) spans info))
            ([item (in-list items)])
    (match item
      [`(SImplDecl ,s (SName ,s_n ,trait) ,ty (SRec ,s_b ,fields))
       (define trait* (hash-ref outputs trait trait))
       (define trait-row (or (trait-row-by-name trait* tenv)
                             (fail 'surface-unknown-trait-name s_n)))
       (when (memq trait* (map intersect-output (trait-env-intersect-rows tenv)))
         (fail 'surface-impl-composite-trait s_n))
       (define labels (for/list ([f (in-list fields)])
                        (match f [`(SField ,_ (SLabel ,_ ,label) ,_) label])))
       (unless (equal? (sort labels symbol<?)
                       (sort (map first (trait-template trait-row)) symbol<?))
         (fail 'surface-impl-requirement-mismatch s_b))
       (define target (normalize-type (lift-template-type (lower-sty ty env fail))))
       (check-requirements trait* trait-row target ty s_n fail)
       (when (for/or ([r (in-list (impl-rows-by-trait trait* tenv))])
               (type-equiv? (impl-target-type r) target))
         (fail 'surface-duplicate-impl-decl (node-span ty)))
       (define n (next-impl-index tenv
                                  (format "o-impl-user-~a-" trait*)))
       (define oid (string->symbol (format "o-impl-user-~a-~a" trait* n)))
       (define prim (string->symbol (format "impl-user-~a-~a" trait* n)))
       (define binder (string->symbol (format "%impl-~a-~a" trait* n)))
       (define row (list oid prim 'impl trait* target 'root))
       (define spans* (hash-set* spans (cons 'origin-id oid) s
                                 (cons 'primitive-name prim) s))
       (values (extend-env tenv '() (list row) '() spans* fail)
               (cons row rows) spans* (hash-set info item (list binder prim)))]
      [`(SDeriveDecl ,s (SName ,s_n ,trait) ,ty)
       (define trait* (hash-ref outputs trait trait))
       (define trait-row (or (trait-row-by-name trait* tenv)
                             (fail 'surface-unknown-trait-name s_n)))
       (when (memq trait* (map intersect-output (trait-env-intersect-rows tenv)))
         (fail 'surface-impl-composite-trait s_n))
       (define uτ (lower-sty ty env fail))
       (define target (normalize-type (lift-template-type uτ)))
       (define recipe (or (hash-ref derive-recipes (trait-origin trait-row) #f)
                          (fail 'surface-derive-no-recipe s)))
       (define leaves (or (recipe target)
                          (fail 'surface-derive-no-recipe s)))
       (check-requirements trait* trait-row target ty s_n fail)
       (when (for/or ([r (in-list (impl-rows-by-trait trait* tenv))])
               (type-equiv? (impl-target-type r) target))
         (fail 'surface-duplicate-impl-decl (node-span ty)))
       (define n (next-impl-index tenv
                                  (format "o-derive-user-~a-" trait*)))
       (define oid (string->symbol (format "o-derive-user-~a-~a" trait* n)))
       (define prim (string->symbol (format "derive-user-~a-~a" trait* n)))
       (define binder (string->symbol (format "%derive-~a-~a" trait* n)))
       (define row (list oid prim 'derive trait* target 'root))
       (define spans* (hash-set* spans (cons 'origin-id oid) s
                                 (cons 'primitive-name prim) s))
       (values (extend-env tenv '() (list row) '() spans* fail)
               (cons row rows) spans*
               (hash-set info item (list binder prim uτ leaves)))]
      [_ (values tenv rows spans info)])))

;; spec §7.2。Fn と Recur が同じ形の引数欄を取るので、ここへ切り出す。
;; 型注釈の span は sty の使用箇所のものであり、別名を展開しても動かない。
(define (lower-params params env fail)
  (for/list ([p (in-list params)])
    (match p
      [`(SParam ,_ (SName ,s_x ,x) #:none)
       (list (list '#:bind x s_x) (list '#:infer s_x))]
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
    ;; Bool は型引数を持たない。空の Types が E-Construct-Synth の型引数注釈になる。
    [`(SBool ,s ,b) `(Construct ,s ,b (Types))]
    [`(SVar ,s ,x) `(#:var ,x ,s)]
    ;; SUR-015。
    [`(SReturn ,s ,value) `(Return ,s ,(lower-sexpr value env fail))]
    [`(SFn ,s ,params ,result-ty ,row ,body)
     (define result-core
       (if (eq? result-ty '#:none)
           `(#:infer ,s)
           `(#:ty ,(lower-sty result-ty env fail) ,(node-span result-ty))))
     (define effect-row
       (if (eq? row '#:none)
           `(#:ef #:infer ,s)
           `(#:ef ,(lower-row row env fail '() #f #:type-row? #f)
                  ,(node-span row))))
     `(Fn ,s ,(lower-params params env fail)
          ,result-core
          ,effect-row
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
    ;; P2l2b1。data 型宣言は項を作らない。名前と欄の検査は lower-surface が行う。
    [`(SDataDecl ,_ ...) (λ (rest) rest)]
    [`(STraitDecl ,_ ,_ ,_) (λ (rest) rest)]
    [`(SImplDecl ,s ,_ ,_ ,body)
     ;; spec §6.6。生成した primitive を Let の束縛名にしない。elab は局所の
     ;; environment を Γ0 より先に引くので、同名の Let は Proof の経路を隠す。
     (match-define (list binder prim) (hash-ref core-info item))
     (define body-core (lower-sexpr body env fail))
     (λ (rest) `(Let ,s_tail ((#:bind ,binder ,s) const)
                     (Apply ,s (#:var ,prim ,s) ,body-core) ,rest))]
    [`(SDeriveDecl ,s ,_ ,_)
     ;; spec §6.7。生成した節点の span はすべて宣言のものである。
     (match-define (list binder prim uτ n) (hash-ref core-info item))
     (define rec-core
       `(Rec ,s (((#:lbl size ,s) imm
                  (Fn ,s (((#:bind %self ,s) (#:ty ,uτ ,s)))
                      (#:ty Int ,s) (#:ef () ,s) (#:lit ,n ,s))))))
     (λ (rest) `(Let ,s_tail ((#:bind ,binder ,s) const)
                     (Apply ,s (#:var ,prim ,s) ,rec-core) ,rest))]
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
    [`(SFnDecl ,s (SName ,s_f ,f) ,params ,result-ty ,row ,body)
     (define params-core (lower-params params env fail))
     (define result-core
       (if (eq? result-ty '#:none)
           `(#:infer ,s)
           `(#:ty ,(lower-sty result-ty env fail) ,(node-span result-ty))))
     ;; 明示 row は row 節の span、省略時は関数宣言全体の span を使う。
     (define effect-row
       `(#:ef ,(lower-row row env fail '() #f #:type-row? #f)
              ,(if (eq? row '#:none) s (node-span row))))
     (define body-core (lower-sexpr body env fail))
     (λ (rest) `(FnDecl ,s_tail (#:bind ,f ,s_f) ,params-core
                       ,result-core
                       ,effect-row
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
(define (lower-surface program base
                       #:data-index [data-index empty-data-index]
                       #:gamma0-names [gamma0-names (map first Γ0)])
  (cond
    [(diagnostic? program) program]
    [else
     (match program
       [`(SProgram ,_ ,items ,e)
        (let/ec return
          (define (fail key s #:related [related '()])
            (return (diagnostic-of 'surface key #:primary-span s #:related related)))
          (define env0 (build-alias-env items base (data-index-decls data-index) fail))
          (define trait-names
            (for/list ([(n d) (in-hash env0)] #:when (eq? d 'trait)) n))
          (define comps (classify-compositions items trait-names))
          (define env
            (for/fold ([env env0]) ([c (in-list comps)])
              (hash-set env (first c) 'trait)))
          (check-alias-definitions items env (map first comps) fail)
          ;; P2l2b1 spec §11 の段 2 から段 4。別名の検査後、trait の lowering 前に置く。
          (check-data-constructors items (data-index-constructors data-index)
                                   gamma0-names fail)
          (check-data-type-parameters items fail)
          (define-values (data-decls data-spans) (lower-data-decls items env fail))
          ;; 段 5 と段 6。基底の宣言を名前順に並べ、原文の宣言を続ける。
          (define all-data
            (append (sort (hash-values (data-index-decls data-index)) symbol<? #:key first)
                    data-decls))
          (define all-index (build-data-index all-data))
          (unless (null? data-decls)
            (validate-data-decls! all-data all-index (data-validation-bail data-spans fail)))
          (define (lower-rest)
            (define-values (decl-rows decl-spans)
              (lower-trait-decls items base env fail))
            (define composite-keys (base-composite-keys base))
            (define (template-of n)
              (trait-template (or (findf (λ (r) (eq? (trait-name r) n)) decl-rows)
                                  (trait-row-by-name n base))))
            (define memo (resolve-composition-keys comps template-of composite-keys fail))
            (define-values (composite-rows intersect-rows composite-spans outputs)
              (emit-compositions comps memo base composite-keys decl-rows))
            (define trait-rows (append decl-rows composite-rows))
            (define trait-spans
              (for/fold ([h decl-spans]) ([(k v) (in-hash composite-spans)])
                (hash-set h k v)))
            (define staged (extend-env base trait-rows '() intersect-rows trait-spans fail))
            (define-values (impl-rows spans core-info)
              (lower-impl-decls items staged trait-spans env outputs fail))
            (lowered (fold-items items e env core-info fail)
                     trait-rows impl-rows intersect-rows data-decls
                     (for/fold ([h spans]) ([(k v) (in-hash data-spans)])
                       (hash-set h k v))))
          (if (eq? all-index empty-data-index)
              (lower-rest)
              (parameterize ([caching-enabled? #f]
                             [data-index-parameter all-index])
                (lower-rest))))])]))

#lang racket

(require "lexer.rkt"
         "diagnostic.rkt")

(provide parse)

;; spec §5.1。lexer の診断は素通りする。呼ぶ側に「lex の結果を場合分けして
;; から parse を呼ぶ」手続きを課すと、その場合分けを忘れた経路が静かに落ちる。
(define (parse tokens)
  (cond
    [(diagnostic? tokens) tokens]
    [else
     (define ts (list->vector tokens))
     (let/ec return
       (define (fail key s)
         (return (diagnostic-of 'surface key #:primary-span s)))
       (let-values ([(program _) (parse-program ts fail)])
         program))]))

(define (tok ts i)
  (vector-ref ts (min i (sub1 (vector-length ts)))))
(define (kind-at ts i) (stok-kind (tok ts i)))
(define (value-at ts i) (stok-value (tok ts i)))
(define (span-at ts i) (stok-span (tok ts i)))

(define (span-id s) (second s))
(define (span-lo s) (third s))
(define (span-hi s) (fourth s))

;; spec §5.3。節点の span は最初のトークンの左端から最後のトークンの右端まで
;; である。区切りの nl は含めない。
(define (hull a b)
  `(#:span ,(span-id a) ,(min (span-lo a) (span-lo b))
           ,(max (span-hi a) (span-hi b))))

;; Surface の節点はすべて (Ctor span ...) の形なので、span は第 2 要素である
;; （spec §5.2）。宣言と式の両方に使う。
(define (node-span n) (second n))

(define (skip-nl ts i)
  (if (eq? (kind-at ts i) 'nl) (add1 i) i))

(define (punct? ts i p)
  (and (eq? (kind-at ts i) 'punct) (eq? (value-at ts i) p)))

(define (kw? ts i k)
  (and (eq? (kind-at ts i) 'kw) (eq? (value-at ts i) k)))

(define (eof? ts i) (eq? (kind-at ts i) 'eof))

(define (fail-at ts fail i)
  (fail (if (eof? ts i) 'surface-unexpected-eof 'surface-unexpected-token)
        (span-at ts i)))

(define (pitem-ahead? ts i)
  (or (kw? ts i 'type)
      (kw? ts i 'trait)
      (kw? ts i 'impl)
      (kw? ts i 'derive)
      (kw? ts i 'const)
      (kw? ts i 'let)
      (and (kw? ts i 'fn) (eq? (kind-at ts (add1 i)) 'ident))))

;; spec §3.2。pitem の後には NL+ が要る。ここを緩めると、宣言と次の式の
;; 境界が消えて曖昧になる。
(define (require-nl ts fail i)
  (if (eq? (kind-at ts i) 'nl)
      (add1 i)
      (fail-at ts fail i)))

(define (parse-pitem ts fail i)
  (cond
    [(kw? ts i 'type) (parse-type-decl ts fail i)]
    [(kw? ts i 'trait) (parse-trait-decl ts fail i)]
    [(kw? ts i 'impl) (parse-impl-decl ts fail i)]
    [(kw? ts i 'derive) (parse-derive-decl ts fail i)]
    [(and (kw? ts i 'fn) (eq? (kind-at ts (add1 i)) 'ident))
     (parse-fn-decl ts fail i)]
    [(or (kw? ts i 'const) (kw? ts i 'let))
     (parse-binding ts fail i)]
    [else (fail-at ts fail i)]))

(define (parse-type-decl ts fail i)
  (define start (span-at ts i))
  (let*-values ([(name name-span name-j) (expect-ident ts fail (add1 i))]
                [(equal equal-j) (expect-punct ts fail name-j '|=|)]
                [(ty ty-j) (parse-ty ts fail equal-j)])
    (values `(STypeDecl ,(hull start (node-span ty))
                        (SName ,name-span ,name) ,ty)
            ty-j)))

(define (parse-trait-decl ts fail i)
  (define start (span-at ts i))
  (let*-values ([(name name-span name-j) (expect-ident ts fail (add1 i))]
                [(_open _open-j) (expect-punct ts fail name-j '|{|)]
                [(ty ty-j) (parse-type-record ts fail name-j)])
    (values `(STraitDecl ,(hull start (node-span ty))
                         (SName ,name-span ,name)
                         ,(third ty))
            ty-j)))

(define (parse-impl-decl ts fail i)
  (define start (span-at ts i))
  (let*-values ([(name name-span name-j) (expect-ident ts fail (add1 i))]
                [(for-j) (expect-kw ts fail name-j 'for)]
                [(ty ty-j) (parse-ty ts fail for-j)]
                [(_open _open-j) (expect-punct ts fail ty-j '|{|)]
                [(body body-j) (parse-record ts fail ty-j)])
    (values `(SImplDecl ,(hull start (node-span body))
                        (SName ,name-span ,name) ,ty ,body)
            body-j)))

(define (parse-derive-decl ts fail i)
  (define start (span-at ts i))
  (let*-values ([(name name-span name-j) (expect-ident ts fail (add1 i))]
                [(for-j) (expect-kw ts fail name-j 'for)]
                [(ty ty-j) (parse-ty ts fail for-j)])
    (values `(SDeriveDecl ,(hull start (node-span ty))
                          (SName ,name-span ,name) ,ty)
            ty-j)))

(define (parse-fn-decl ts fail i)
  (define start (span-at ts i))
  (let*-values ([(name name-span name-j) (expect-ident ts fail (add1 i))]
                [(open open-j) (expect-punct ts fail name-j '|(|)]
                [(params params-j) (parse-params ts fail open-j)]
                [(close close-j) (expect-punct ts fail params-j '|)|)]
                [(_arrow arrow-j) (expect-punct ts fail close-j '->)]
                [(return-type type-j) (parse-ty ts fail arrow-j)]
                [(body body-j) (parse-block ts fail type-j)])
    (values `(SFnDecl ,(hull start (node-span body))
                      (SName ,name-span ,name) ,params ,return-type ,body)
            body-j)))

(define (expect-punct ts fail i p)
  (if (punct? ts i p)
      (values (span-at ts i) (add1 i))
      (fail-at ts fail i)))

(define (expect-kw ts fail i k)
  (if (kw? ts i k) (add1 i) (fail-at ts fail i)))

(define (expect-ident ts fail i)
  (if (eq? (kind-at ts i) 'ident)
      (values (value-at ts i) (span-at ts i) (add1 i))
      (fail-at ts fail i)))

(define (parse-program ts fail)
  (let loop ([i (skip-nl ts 0)] [items '()])
    (cond
      [(eof? ts i)
       (fail 'surface-unexpected-eof (span-at ts i))]
      [(pitem-ahead? ts i)
       (let-values ([(item j) (parse-pitem ts fail i)])
         (loop (require-nl ts fail j) (cons item items)))]
      [else
       (let-values ([(expr j) (parse-expr ts fail i)])
         (define k (skip-nl ts j))
         (if (not (eof? ts k))
             (fail-at ts fail k)
             (let ([first-span
                    (if (null? items)
                        (node-span expr)
                        (node-span (last items)))])
               (values `(SProgram ,(hull first-span (node-span expr))
                                 ,(reverse items) ,expr)
                       k))))])))

(define (parse-expr ts fail i)
  (parse-postfix ts fail i))

(define (parse-postfix ts fail i)
  (let-values ([(base i0) (parse-primary ts fail i)])
    (let loop ([node base] [j i0])
      (cond
        [(punct? ts j '|(|)
         (let*-values ([(args j0) (parse-args ts fail (add1 j))]
                       [(close close-j) (expect-punct ts fail j0 '|)|)])
           (loop `(SApply ,(hull (node-span node) close) ,node ,args) close-j))]
        [(punct? ts j '|.|)
         (define dot-j (add1 j))
         (cond
           ;; spec §3。`.` の直後の `{` は多 field 射影である。
           [(punct? ts dot-j '|{|)
            (let-values ([(labels close-j) (parse-proj-labels ts fail dot-j)])
              (loop `(SProjRec ,(hull (node-span node) (span-at ts close-j))
                               ,node ,labels)
                    (add1 close-j)))]
           [else
            (let-values ([(name s label-j) (expect-ident ts fail dot-j)])
              (define label `(SLabel ,s ,name))
              (loop `(SProj ,(hull (node-span node) s) ,node ,label) label-j))])]
        [else (values node j)]))))

(define (parse-primary ts fail i)
  (cond
    [(eq? (kind-at ts i) 'int)
     (values `(SInt ,(span-at ts i) ,(value-at ts i)) (add1 i))]
    [(eq? (kind-at ts i) 'str)
     (values `(SStr ,(span-at ts i) ,(value-at ts i)) (add1 i))]
    [(kw? ts i 'true)
     (values `(SBool ,(span-at ts i) true) (add1 i))]
    [(kw? ts i 'false)
     (values `(SBool ,(span-at ts i) false) (add1 i))]
    [(eq? (kind-at ts i) 'ident)
     (values `(SVar ,(span-at ts i) ,(value-at ts i)) (add1 i))]
    [(kw? ts i 'fn) (parse-anon-fn ts fail i)]
    [(punct? ts i '|(|)
     (define open (span-at ts i))
     (define j (add1 i))
     (cond
       [(punct? ts j '|)|)
        (values `(SUnit ,(hull open (span-at ts j))) (add1 j))]
       [else
        (let*-values ([(expr j0) (parse-expr ts fail j)]
                      [(close j1) (expect-punct ts fail j0 '|)|)])
          (values expr j1))])]
    [(punct? ts i '|{|) (parse-block-or-record ts fail i)]
    [(eof? ts i) (fail 'surface-unexpected-eof (span-at ts i))]
    [else (fail-at ts fail i)]))

(define (parse-anon-fn ts fail i)
  (define start (span-at ts i))
  (let*-values ([(open open-j) (expect-punct ts fail (add1 i) '|(|)]
                [(params params-j) (parse-params ts fail open-j)]
                [(close close-j) (expect-punct ts fail params-j '|)|)]
                [(_arrow arrow-j) (expect-punct ts fail close-j '->)])
    (let*-values ([(return-type type-j) (parse-ty ts fail arrow-j)]
                 [(body body-j) (parse-block ts fail type-j)])
      (values `(SFn ,(hull start (node-span body)) ,params ,return-type ,body)
              body-j))))

(define (record-ahead? ts i)
  (define j (skip-nl ts (add1 i)))
  (or (punct? ts j '|}|)
      (and (eq? (kind-at ts j) 'ident)
           (punct? ts (add1 j) '|:|))))

(define (parse-block-or-record ts fail i)
  (if (record-ahead? ts i)
      (parse-record ts fail i)
      (parse-block ts fail i)))

(define (parse-record ts fail i)
  (define open (span-at ts i))
  (define j0 (skip-nl ts (add1 i)))
  (if (punct? ts j0 '|}|)
      (values `(SRec ,(hull open (span-at ts j0)) ()) (add1 j0))
      (let loop ([j j0] [fields '()])
        (let*-values ([(label label-span label-j) (expect-ident ts fail j)]
                      [(colon colon-j) (expect-punct ts fail label-j '|:|)])
          (let*-values ([(value value-j) (parse-expr ts fail colon-j)])
            (define field
              `(SField ,(hull label-span (node-span value))
                       (SLabel ,label-span ,label) ,value))
            (define next (skip-nl ts value-j))
            (cond
              [(punct? ts next '|}|)
               (values `(SRec ,(hull open (span-at ts next))
                              ,(reverse (cons field fields)))
                       (add1 next))]
              [(punct? ts next '|,|)
               (define after (skip-nl ts (add1 next)))
               (if (punct? ts after '|}|)
                   (values `(SRec ,(hull open (span-at ts after))
                                  ,(reverse (cons field fields)))
                           (add1 after))
                   (loop after (cons field fields)))]
              [(> next value-j)
               (loop next (cons field fields))]
              [else (fail-at ts fail next)]))))))

;; spec §6.2。label 列は非空であり、重複を含まない。primary span は開き波括弧
;; から閉じ波括弧までである。SProjRec の第 1 欄は r.{a, b} 全体の span であり、
;; 波括弧だけを囲む span はここでしか手に入らない。だから検査は parser が行う。
(define (check-proj-labels labels s fail)
  (define names (for/list ([l (in-list labels)]) (third l)))
  (when (or (null? names) (check-duplicates names eq?))
    (fail 'surface-projection-labels s)))

;; 開き波括弧の位置を受け取り、label の並びと閉じ波括弧の位置を返す。
;; 区切りの規則は parse-record と同じで、読点と改行のどちらでもよく、
;; 末尾の読点を許す。
(define (parse-proj-labels ts fail open-j)
  (define open (span-at ts open-j))
  (let loop ([j (skip-nl ts (add1 open-j))] [labels '()])
    (cond
      [(punct? ts j '|}|)
       (define labs (reverse labels))
       (check-proj-labels labs (hull open (span-at ts j)) fail)
       (values labs j)]
      [else
       (let-values ([(name s label-j) (expect-ident ts fail j)])
         (define next (skip-nl ts label-j))
         (cond
           [(punct? ts next '|,|)
            (loop (skip-nl ts (add1 next)) (cons `(SLabel ,s ,name) labels))]
           [(punct? ts next '|}|)
            (loop next (cons `(SLabel ,s ,name) labels))]
           ;; 読点が無く改行だけで区切った形である。parse-record の
           ;; (> next value-j) の節と同じ判定である。
           [(> next label-j)
            (loop next (cons `(SLabel ,s ,name) labels))]
           [else (fail-at ts fail next)]))])))

(define (parse-block ts fail i)
  (define open (span-at ts i))
  (let loop ([j (skip-nl ts (add1 i))] [bindings '()])
    (if (or (kw? ts j 'const) (kw? ts j 'let))
        (let-values ([(binding binding-j) (parse-binding ts fail j)])
          (if (not (eq? (kind-at ts binding-j) 'nl))
              (fail-at ts fail binding-j)
              (loop (skip-nl ts binding-j) (cons binding bindings))))
        (let*-values ([(body body-j) (parse-expr ts fail j)]
                     [(close close-j)
                      (let ([after-body (skip-nl ts body-j)])
                        (expect-punct ts fail after-body '|}|))])
          (values `(SBlock ,(hull open close) ,(reverse bindings) ,body)
                  close-j)))))

(define (parse-bmode ts fail i)
  (cond
    [(kw? ts i 'const) (values 'const (add1 i))]
    [(kw? ts i 'let)
     (if (kw? ts (add1 i) 'mut)
         (values 'mut (+ i 2))
         (values 'let (add1 i)))]
    [else (fail-at ts fail i)]))

(define (parse-binding ts fail i)
  (define mode-span (span-at ts i))
  (let*-values ([(mode mode-j) (parse-bmode ts fail i)]
               [(name name-span name-j) (expect-ident ts fail mode-j)])
    (define name-node `(SName ,name-span ,name))
    (define-values (annotation annotation-j)
      (if (punct? ts name-j '|:|)
          (let-values ([(ty ty-j) (parse-ty ts fail (add1 name-j))])
            (values ty ty-j))
          (values '#:none name-j)))
    (let*-values ([(equal equal-j) (expect-punct ts fail annotation-j '|=|)]
                  [(value value-j) (parse-expr ts fail equal-j)])
      (values `(SBind ,(hull mode-span (node-span value)) ,mode
                      ,name-node ,annotation ,value)
              value-j))))

(define (parse-ty ts fail i)
  (cond
    [(eq? (kind-at ts i) 'ident)
     (values `(TName ,(span-at ts i) ,(value-at ts i)) (add1 i))]
    [(punct? ts i '|{|) (parse-type-record ts fail i)]
    [(kw? ts i 'fn) (parse-function-type ts fail i)]
    [(eof? ts i) (fail 'surface-unexpected-eof (span-at ts i))]
    [else (fail 'surface-unexpected-token (span-at ts i))]))

(define (parse-type-record ts fail i)
  (define open (span-at ts i))
  (define j0 (skip-nl ts (add1 i)))
  (if (punct? ts j0 '|}|)
      (values `(TRec ,(hull open (span-at ts j0)) ()) (add1 j0))
      (let loop ([j j0] [fields '()])
        (let*-values ([(label label-span label-j) (expect-ident ts fail j)]
                     [(colon colon-j) (expect-punct ts fail label-j '|:|)]
                     [(ty ty-j) (parse-ty ts fail colon-j)])
          (define field
            `(TField ,(hull label-span (node-span ty))
                     (SLabel ,label-span ,label) ,ty))
          (define next (skip-nl ts ty-j))
          (cond
            [(punct? ts next '|}|)
             (values `(TRec ,(hull open (span-at ts next))
                            ,(reverse (cons field fields)))
                     (add1 next))]
            [(punct? ts next '|,|)
             (define after (skip-nl ts (add1 next)))
             (if (punct? ts after '|}|)
                 (values `(TRec ,(hull open (span-at ts after))
                                ,(reverse (cons field fields)))
                         (add1 after))
                 (loop after (cons field fields)))]
            [(> next ty-j) (loop next (cons field fields))]
            [else (fail-at ts fail next)])))))

(define (parse-function-type ts fail i)
  (define start (span-at ts i))
  (let*-values ([(open open-j) (expect-punct ts fail (add1 i) '|(|)]
                [(types types-j) (parse-types ts fail open-j)]
                [(close close-j) (expect-punct ts fail types-j '|)|)]
                [(_arrow arrow-j) (expect-punct ts fail close-j '->)]
                [(result result-j) (parse-ty ts fail arrow-j)])
    (values `(TFn ,(hull start (node-span result)) ,types ,result) result-j)))

(define (parse-params ts fail i)
  (if (punct? ts i '|)|)
      (values '() i)
      (let loop ([j i] [params '()])
        (let*-values ([(name name-span name-j) (expect-ident ts fail j)]
                     [(colon colon-j) (expect-punct ts fail name-j '|:|)]
                     [(ty ty-j) (parse-ty ts fail colon-j)])
          (define param
            `(SParam ,(hull name-span (node-span ty))
                     (SName ,name-span ,name) ,ty))
          (if (punct? ts ty-j '|,|)
              (loop (add1 ty-j) (cons param params))
              (values (reverse (cons param params)) ty-j))))))

(define (parse-types ts fail i)
  (if (punct? ts i '|)|)
      (values '() i)
      (let loop ([j i] [types '()])
        (let-values ([(ty ty-j) (parse-ty ts fail j)])
          (if (punct? ts ty-j '|,|)
              (loop (add1 ty-j) (cons ty types))
              (values (reverse (cons ty types)) ty-j))))))

(define (parse-args ts fail i)
  (if (punct? ts i '|)|)
      (values '() i)
      (let loop ([j i] [args '()])
        (let-values ([(arg arg-j) (parse-expr ts fail j)])
          (if (punct? ts arg-j '|,|)
              (loop (add1 arg-j) (cons arg args))
              (values (reverse (cons arg args)) arg-j))))))

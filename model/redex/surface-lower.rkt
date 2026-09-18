#lang racket

(require racket/match
         "diagnostic.rkt")

(provide lower-surface)

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
(define (lower-sty ty env fail [stack '()])
  (match ty
    [`(TName ,s ,name)
     (cond
       [(memq name primitive-type-names) name]
       [(memq name stack) (fail 'surface-recursive-type-alias s)]
       [(hash-ref env name #f)
        => (λ (definition) (lower-sty definition env fail (cons name stack)))]
       [else (fail 'surface-unknown-type-name s)])]
    [`(TRec ,_ ,fields)
     `(Record ,(lower-ty-fields fields env fail stack))]
    [`(TFn ,_ ,arguments ,result)
     ;; spec §7.2.1。効果行と義務は Surface に表記が無いので空である。
     `(NFn ,(for/list ([a (in-list arguments)]) (lower-sty a env fail stack))
           ,(lower-sty result env fail stack)
           ()
           ())]))

;; spec §7.2.1。TRec の欄の可変性は imm に固定する。Surface に mut の
;; 表記が無いためである。
;; spec §6.1。左から右へ見て、最初の 2 度目で止める。
(define (lower-ty-fields fields env fail stack)
  (for/fold ([seen '()] [row '()] #:result (reverse row))
            ([field (in-list fields)])
    (match field
      [`(TField ,_ (SLabel ,s_l ,label) ,ty)
       (when (memq label seen)
         (fail 'surface-duplicate-field s_l))
       (values (cons label seen)
               (cons (list label (lower-sty ty env fail stack) 'imm) row))])))

;; spec §7.2。Task 6 で残りの形を足す。
(define (lower-sexpr e env fail)
  (match e
    [`(SInt ,s ,n) `(#:lit ,n ,s)]
    [`(SVar ,s ,x) `(#:var ,x ,s)]))

;; spec §7。入口である。parse の診断はそのまま返す。呼ぶ側に
;; 「parse の結果を場合分けしてから lower-surface を呼ぶ」手続きを課すと、
;; その場合分けを忘れた経路が静かに落ちる（parser.rkt:10-13 と同じ理由）。
;; spec §6.1。診断は 1 件だけ返すので、最初の fail で脱出する。
(define (lower-surface program)
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
          ;; Task 7 で spitem の畳み込みへ差し替える。
          (lower-sexpr e env fail))])]))

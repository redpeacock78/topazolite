#lang racket

(require rackunit
         redex/reduction-semantics
         "../annotate.rkt"
         "../borrow-oracle.rkt"
         "../diagnostic.rkt"
         "../diagnostic-render.rkt"
         "../elaborate.rkt"
         "../lang.rkt"
         "../source-map.rkt"
         "../uniquify.rkt")

;; elab は成功したとき (list core type row callables) を、失敗したとき
;; (err diagnostic) を返す。失敗値を core として扱わないよう先に分ける。
(define (elab-core/checked surface)
  (define result (elab surface))
  (unless (and (list? result) (= (length result) 4))
    (fail (format "elab が成功値を返さない: ~s" result)))
  (first result))

;; span-core.rkt が宣言する 7 つの束縛形を 1 つずつ含む core である。
(define fixture-span '(#:span src 0 1))
(define fixture-type '(#:ty Int (#:span src 0 1)))
(define fixture-binder `(#:bind x ,fixture-span))
(define fixture-branch
  `(,fixture-span K (,fixture-binder) -> (#:var x ,fixture-span)))

(define (seven-binding-form-fixtures)
  (list
   `(Lam ,fixture-span User callable0 (,fixture-binder)
         (#:var x ,fixture-span))
   `(Let ,fixture-span (,fixture-binder ,fixture-type)
         1 (#:var x ,fixture-span))
   fixture-branch
   `(,fixture-span (#:bind x ,fixture-span) ->
                   (#:var x ,fixture-span))
   `(Recur ,fixture-span callable0 ,fixture-binder (,fixture-binder)
           (#:var x ,fixture-span) (#:var x ,fixture-span))
   `(RecurVal ,fixture-span callable0 ,fixture-binder (,fixture-binder)
              (#:var x ,fixture-span))
   `(Let ,fixture-span (,fixture-binder let ,fixture-type)
         1 (#:var x ,fixture-span))))

;; SCP-002。同名の入れ子 Let が異なる記号になる。
(test-case "同名の入れ子 Let が異なる識別子を受け取る（SCP-002）"
  (define core
    (elab-core/checked '(Let x 1 (Let x 2 x))))
  (define binders (core-binder-symbols core))
  (check-equal? (length binders) 2)
  (check-false (equal? (first binders) (second binders)))
  (check-equal? (map binder-base binders) '(x x)))

;; SCP-002。7 形すべてで束縛子が識別子を受け取る。
(test-case "7 つの束縛形すべてが識別子を受け取る（SCP-002）"
  (for ([core (in-list (seven-binding-form-fixtures))])
    (for ([binder (in-list (core-binder-symbols
                            (uniquify-binders core)))])
      (check-true (binder-has-identifier? binder)
                  (format "~s" binder)))))

;; SCP-002。束縛子の scope 外は現在の環境、scope 内は拡張後の環境で歩く。
(test-case "scope 外の部分項は外側の記号を保つ"
  (define let-core
    `(Let ,fixture-span ((#:bind x ,fixture-span) Int)
          (#:var x ,fixture-span)
          (#:var x ,fixture-span)))
  (match (uniquify-binders let-core)
    [`(Let ,_ ((#:bind ,binder ,_) Int)
           (#:var ,bound-ref ,_)
           (#:var ,body-ref ,_))
     (check-equal? bound-ref 'x)
     (check-equal? body-ref binder)]
    [_ (fail "Let の scope 境界が変わった")])
  (define eliminate-core
    `(Eliminate (#:var x ,fixture-span)
                ((,fixture-span K ((#:bind x ,fixture-span)) ->
                  (#:var x ,fixture-span)))))
  (match (uniquify-binders eliminate-core)
    [`(Eliminate (#:var ,scrutinee-ref ,_)
                 ((,_ K ((#:bind ,binder ,_)) -> (#:var ,branch-ref ,_))))
     (check-equal? scrutinee-ref 'x)
     (check-equal? branch-ref binder)]
    [_ (fail "Eliminate の scope 境界が変わった")])
  ;; 残りの 5 形も同じ一回の走査で識別子を採番する。
  (for ([core (in-list (seven-binding-form-fixtures))])
    (check-true
     (andmap binder-has-identifier?
             (core-binder-symbols (uniquify-binders core))))))

;; SCP-002。合成された return-value も入力由来の束縛子と同じ counter を共有する。
(test-case "入れ子 Handle の return-value がそれぞれの本体を指す"
  (define core
    `(Handle ,fixture-span
            (Return boundary)
            (,fixture-span (#:bind return-value ,fixture-span) ->
             (Handle ,fixture-span
                     (Return boundary)
                     (,fixture-span (#:bind return-value ,fixture-span) ->
                      (#:var return-value ,fixture-span))))))
  (match (uniquify-binders core)
    [`(Handle ,_ ,_ (,_ (#:bind ,outer ,_) ->
                 (Handle ,_ ,_ (,_ (#:bind ,inner ,_) ->
                              (#:var ,inner-ref ,_)))))
     (check-false (equal? outer inner))
     (check-equal? inner-ref inner)]
    [_ (fail "Handle の合成束縛子が一意化されていない")]))

;; SCP-002。型、effect row、label、origin、callable の記号は束縛子と同じでも触らない。
(test-case "束縛子以外のメタデータは改名しない"
  (define core
    `(Lam ,fixture-span x callable-x ((#:bind x ,fixture-span))
          (Let ,fixture-span ((#:bind y ,fixture-span)
                              (Record ((x Int imm))))
               (#:ef x)
               (#:lbl x))))
  (define result (uniquify-binders core))
  (match-define (list 'Lam _ origin callable parameters body) result)
  (check-equal? origin 'x)
  (check-equal? callable 'callable-x)
  (check-equal? (binder-base (second (first parameters))) 'x)
  (match-define (list 'Let _ binding bound body-contents) body)
  (check-equal? (second binding) '(Record ((x Int imm))))
  (check-equal? bound '(#:ef x))
  (check-equal? body-contents '(#:lbl x))
  (match (elab '(Fn ((x Int)) Int () x))
    [(list _ type row callables)
     (check-equal? type '(NFn (Int) Int () ()))
     (check-equal? row '())
     (check-equal? callables '((callable0 (NFn (Int) Int () ()))))]
    [other (fail (format "メタデータの検査用 Fn が失敗した: ~s" other))]))

;; SCP-002。予約記号を含む束縛子は elaboration の入口で拒否する。
(test-case "予約記号を含む束縛子が落ちる（SCP-002）"
  (check-match (elab '(Let |x⟨1⟩| 1 |x⟨1⟩|))
               `(err ,_))
  (check-match (elab '(Let |x⟩| 1 |x⟩|))
               `(err ,_))
  (check-match
   (elab '(Eliminate value ((K (|x⟨1⟩|) -> |x⟨1⟩|))))
   `(err ,_))
  (check-match
   (elab '(Eliminate value ((K))))
   `(err ,_))
  (check-match
   (elab (annotate-surface
          '(Fn ((|x⟨1⟩| Int)) Int () |x⟨1⟩|)))
   `(err ,_))
  (check-match
   (elab (annotate-surface
          '(Let (|x⟨1⟩| let Int) 1 |x⟨1⟩|)))
   `(err ,_)))

;; SCP-002。置換が付ける添字は末尾からだけ剥がす。
(test-case "正規化が末尾の添字だけを剥がす（SCP-002）"
  (check-equal? (normalize-binder '|x⟨1⟩«0»«1»|) '|x⟨1⟩|)
  (check-equal? (normalize-binder '|x«0»⟨1⟩|) '|x«0»⟨1⟩|))

;; SCP-002。診断の表示から識別子が消え、元の名前が現れる。
(define render-source-map
  (make-source-map (hasheq 'sample "let x = y")))

(define (diagnostic-with-found found)
  (diagnostic-of 'typing 'ill-typed
                 #:primary-span '(#:span sample 4 5)
                 #:expected 'Int
                 #:found found))

(test-case "診断の表示が元の名前を出す（SCP-002）"
  (define d (diagnostic-with-found '|x⟨3⟩|))
  (for ([rendered (in-list (list (render-terminal d render-source-map)
                                 (render-lsp d render-source-map)
                                 (render-json d)))])
    (define text (format "~a" rendered))
    (check-true (regexp-match? #px"x" text))
    (check-false (regexp-match? #px"⟨" text)))
  ;; 置換が付ける添字も同じ経路で消える。
  (check-equal? (format-unfixed '|x⟨3⟩«0»|) "x"))

(test-case "予約記号の診断は入力記号をそのまま表示する（SCP-002）"
  (match (elab '(Let |x⟨1⟩| 1 |x⟨1⟩|))
    [`(err ,diagnostic)
     (define rendered (render-terminal diagnostic render-source-map))
     (check-true (regexp-match? #px"found: \\\"x⟨1⟩\\\"" rendered))]
    [other (fail (format "予約記号の入力が診断にならない: ~s" other))]))

;; SCP-002。末尾を剥がす 3 つの手続きは対象が異なる。合成の順序を固定する。
(test-case "正規化と base 化の合成順序（SCP-002）"
  ;; 単独ではどちらも相手の接尾辞に当たらない。
  (check-equal? (binder-base '|x⟨1⟩«0»|) '|x⟨1⟩«0»|)
  (check-equal? (normalize-binder '|x⟨1⟩«0»|) '|x⟨1⟩|)
  ;; 正規化を先に通すと元の名前へ戻る。
  (check-equal? (binder-base (normalize-binder '|x⟨1⟩«0»|)) 'x)
  ;; 逆順は戻らない。
  (check-equal? (normalize-binder (binder-base '|x⟨1⟩«0»|)) '|x⟨1⟩|))

(define-metafunction G2
  sub : any x any -> any
  [(sub any_1 x any_2) (substitute any_1 x any_2)])

;; SCP-002。substitute が freshen した記号を正規化すると識別子へ戻る。
(test-case "freshen した記号が正規化で識別子へ戻る（SCP-002）"
  (define freshened
    (term (sub (Let (|y⟨2⟩| let Int) x |y⟨2⟩|) x 7)))
  (define binder (first (second freshened)))
  ;; freshen が起きたことそのものを固定する。
  (check-not-equal? binder '|y⟨2⟩|)
  (check-equal? (normalize-binder binder) '|y⟨2⟩|))

(define (let-b binder place)
  (define pre
    `(cfg (Scope (,place)
                 (Let (,binder let (Borrowed Res ,place))
                      (BorrowRef ,place () ,place)
                      (Read ,binder)))
          ((0 (resource 1)) (1 (resource 2)))
          ((0 Available) (1 Available)) () ()))
  (define post
    `(cfg (Scope (,place) (Read (BorrowRef ,place () ,place)))
          ((0 (resource 1)) (1 (resource 2)))
          ((0 Available) (1 Available)) () ()))
  (values pre post))

;; SCP-002。同じ base 名の 2 つの識別子が別々の place へ解決する。
(test-case "shadowing した借用の designator が 1 つの place へ解決する（SCP-002）"
  (define-values (pre1 post1) (let-b '|x⟨1⟩| 0))
  (define-values (pre2 post2) (let-b '|x⟨2⟩| 1))
  (define prov
    (provenance-extend
     (provenance-extend (empty-provenance) 'R-LetB pre1 post1)
     'R-LetB pre2 post2))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov '|x⟨1⟩|) '(0))
  (check-equal? (resolve-designator prov '|x⟨2⟩|) '(1))
  ;; 未束縛の designator は place を返さない。
  (check-equal? (resolve-designator prov '|x⟨3⟩|) '())
  ;; base 名だけでは引けない。一意化前の綴りは鍵ではない。
  (check-equal? (resolve-designator prov 'x) '()))

;; SCP-002。一意化を外すと同じ鍵へ 2 つの place が畳まれる。
(test-case "同じ鍵へ 2 つの place が入ると解決が 1 つに定まらない（SCP-002）"
  (define-values (pre1 post1) (let-b 'x 0))
  (define-values (pre2 post2) (let-b 'x 1))
  (define prov
    (provenance-extend
     (provenance-extend (empty-provenance) 'R-LetB pre1 post1)
     'R-LetB pre2 post2))
  (check-equal? (sort (resolve-designator prov 'x) <) '(0 1)))

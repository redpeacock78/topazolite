#lang racket

(require rackunit
         "../elaborate.rkt"
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
   `(err ,_)))

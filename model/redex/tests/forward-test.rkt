#lang racket

(require rackunit
         racket/set
         racket/match
         redex/reduction-semantics
         "../annotate.rkt"
         "../borrow.rkt"
         "../classify.rkt"
         "../diagnostic.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../type-shape.rkt"
         "../type-equiv.rkt"
         "../typing.rkt"
         "../uniquify.rkt")

(define sink-type '(NFn ((Owned Res)) Int () () () User))
(define sink-two-type '(NFn ((Owned Res) (Owned Res)) Int () () () User))
(define owner-type `(NFn (,sink-type (Owned Res)) Int () () () User))

(define (owner-lambda body [sink sink-type] [latent-row '()])
  (define owner
    `(NFn (,sink (Owned Res)) Int () ,latent-row () User))
  (values
   `(Lam User owner (h p)
      (Handle (Return owner Int) (answer -> answer)
        (Scope () (Let (x let (Owned Res)) p ,body))))
   `((owner ,owner) (sink ,sink))))

(define (typed-owner-lambda input-type body sink)
  (define owner
    `(NFn (,sink ,input-type) Int () () () User))
  (values
   `(Lam User owner (h p)
      (Handle (Return owner Int) (answer -> answer)
        (Scope () (Let (x let ,input-type) p ,body))))
   `((owner ,owner) (sink ,sink))))

(define (two-resource-owner-lambda first-type second-type body sink)
  (define owner
    `(NFn (,sink ,second-type ,first-type) Int () () () User))
  (values
   `(Lam User owner (h q p)
      (Handle (Return owner Int) (answer -> answer)
        (Scope ()
          (Let (z let ,second-type) q
            (Let (x let ,first-type) p ,body)))))
   `((owner ,owner) (sink ,sink))))

(define (typing-key core [places '()] [callables '()] [environment '()])
  (define result (type-of/raw core places callables environment))
  (match result
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (diagnostic-code-of-core core [places '()] [callables '()]
                                 [environment '()])
  (diagnostic-id
   (core-type-of/diagnostic core places callables environment)))

(test-case "R-Forward は Available の place を Moved にする"
  (check-equal?
   (apply-reduction-relation*
    -->g2/rules
    '(cfg (Forward 0) ((0 (resource 0))) ((0 Available)) () ()))
   '((cfg (resource 0) ((0 (resource 0))) ((0 Moved)) () ()))))

(test-case "Available でない place の Forward は停止する"
  (for ([state '(Moved Dropped)])
    (check-equal?
     (apply-reduction-relation
      -->g2/rules
      `(cfg (Forward 0) ((0 (resource 0))) ((0 ,state)) () ()))
     '())))

(test-case "Forward は注釈と消去の往復で保たれる"
  (check-equal? (erase-core (annotate-core '(Forward x))) '(Forward x)))

(test-case "Forward は領域走査で子を持たず自由変数を持つ"
  (check-equal? (core-children '(Forward x)) '())
  (check-equal? (core-with-children '(Forward x) '()) '(Forward x))
  (check-equal? (core-free-vars '(Forward x)) (set 'x)))

(test-case "Forward は一意化で外側の束縛名に追随する"
  (define renamed
    (uniquify-binders (annotate-core '(Let (x Int) 1 (Forward x)))))
  (match renamed
    [`(Let ,_ ((#:bind ,binder ,_) (#:ty Int ,_)) ,_
            (Forward ,_ (#:var ,operand ,_)))
     (check-equal? operand binder)
     (check-true (binder-has-identifier? binder))]
    [_ (fail (format "Forward を含む Let の形を保てない: ~s" renamed))]))

(test-case "Forward を含む構造的な再帰は根を辿って減少する"
  (define loop-type '(NFn ((List Int)) Int () () () User))
  (define core
    '(Recur list-loop-id loop (xs)
       (Eliminate xs
         ((nil () -> 0)
          (cons (head tail) -> (Apply loop (Forward tail)))))
       (Apply loop (Construct (List Int) nil))))
  (check-equal? (classify core '() `((list-loop-id ,loop-type)))
                '(Finite structural)))

(test-case "Forward は Core の型形状走査で受理される"
  (check-true (core-types-normal? '(Forward x))))

(test-case "所有する Lam の転送 Let 内の Forward は空 row で型付けする"
  (define-values (core callables)
    (owner-lambda '(Apply h (Forward x))))
  (check-equal? (core-type-of core '() callables)
                (list owner-type '())))

(test-case "T の Let は Forward の値を次の place へ転送できる"
  (define-values (core callables)
    (owner-lambda
     '(Apply h (Let (y let (Owned Res)) (Forward x) (Forward y)))))
  (check-equal? (core-type-of core '() callables)
                (list owner-type '())))

(test-case "Forward を含む Apply の引数以外に置いた Forward は拒否する"
  (define-values (bound-core bound-callables)
    (owner-lambda
     '(Let (y let (Owned Res)) (Forward x) (Apply h (Forward y)))))
  (check-equal? (diagnostic-code-of-core bound-core '() bound-callables)
                "E-OWN-036")
  (define-values (scrutinee-core scrutinee-callables)
    (typed-owner-lambda
     '(Owned (List Int))
     '(Apply h
             (Eliminate (Forward x)
               ((nil () -> 0)
                (cons (head tail) -> 0))))
     '(NFn (Int) Int () () () User)))
  (check-equal? (diagnostic-code-of-core scrutinee-core '()
                                         scrutinee-callables)
                "E-OWN-036"))

(test-case "Forward を含む Apply の関数位置は変数でなければならない"
  (define-values (core callables)
    (owner-lambda
     '(Apply
       (Lam User consume (argument)
         (Handle (Return consume Int) (answer -> answer)
           (Scope () (Let (owned let (Owned Res)) argument 0))))
       (Forward x))))
  (check-equal? (diagnostic-code-of-core
                 core '() (cons `(consume ,sink-type) callables))
                "E-OWN-036"))

(test-case "生きている借用と競合する Forward は既存の Move の key を先に返す"
  (define aggregate
    '(Record ((n Int imm) (owned (Owned Res) imm))))
  (define sink `(NFn (,aggregate) Int () () () User))
  (define-values (core callables)
    (typed-owner-lambda
     aggregate
     `(Let (borrowed let (Borrowed ,aggregate (RVar 0))) (Borrow x)
        (Let (forwarded let ,aggregate) (Forward x)
          (Let (number let Int) (Read (ProjBorrow borrowed n))
            (Apply h (Forward forwarded)))))
     sink))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw (annotate-regions core ir) '() callables '()
                 (region-ctx ir '() (hash) (hash))))
  (match result
    [(list 'fail key _node _details ...)
     (check-equal? key 'move-borrowed)]
    [_ (fail (format "借用の競合 key を期待したが得た結果は ~s" result))]))

(test-case "Scope で包む T は Forward を運ぶ"
  (define record-owned '(Record ((owned (Owned Res) imm))))
  (define option-record `(Option ,record-owned))
  (define sink `(NFn (,option-record) Int () () () User))
  (define-values (core callables)
    (typed-owner-lambda
     record-owned
     `(Apply h (Scope () (Construct ,option-record some (Forward x))))
     sink))
  (check-equal? (typing-key core '() callables) 'ok))

(test-case "Rec に含む Forward は aggregate 欄へ入る"
  (define inner-record '(Record ((owned (Owned Res) imm))))
  (define outer-record `(Record ((nested ,inner-record imm))))
  (define sink `(NFn (,outer-record) Int () () () User))
  (define-values (core callables)
    (typed-owner-lambda inner-record
                        `(Apply h (Rec ((nested imm (Forward x)))))
                        sink))
  (check-equal? (typing-key core '() callables) 'ok))

(test-case "Construct に含む Forward は aggregate 欄へ入る"
  (define record-owned '(Record ((owned (Owned Res) imm))))
  (define option-record `(Option ,record-owned))
  (define sink `(NFn (,option-record) Int () () () User))
  (define-values (core callables)
    (typed-owner-lambda record-owned
                        `(Apply h (Construct ,option-record some (Forward x)))
                        sink))
  (check-equal? (typing-key core '() callables) 'ok))

(test-case "Record rewrite を含む T は欄を作り直して Forward を渡す"
  (define int-bool (normalize-type '(Union Int Bool)))
  (define input-record
    '(Record ((a Int imm) (owned (Owned Res) imm))))
  (define output-record
    `(Record ((a ,int-bool imm) (owned (Owned Res) imm))))
  (define union-output `(Union ,output-record Bool))
  (define sink `(NFn (,output-record) Int () () () User))
  (define union-sink `(NFn (,union-output) Int () () () User))
  (define rewrite
    `(RecRewrite (Forward x)
       ((a old-a Int imm ,int-bool
         (UnionInject ,int-bool Int old-a)))))
  (define-values (record-core record-callables)
    (typed-owner-lambda input-record `(Apply h ,rewrite) sink))
  (define-values (union-core union-callables)
    (typed-owner-lambda input-record
                        `(Apply h (UnionInject ,union-output
                                               ,output-record ,rewrite))
                        union-sink))
  (check-equal? (typing-key record-core '() record-callables) 'ok)
  (check-equal? (typing-key union-core '() union-callables) 'ok))

(test-case "RecRewrite entry は外側の Forward binder を捕捉しない"
  (define input-record
    '(Record ((keep (Owned Res) imm) (o Int imm opt))))
  (define output-record
    '(Record ((keep (Owned Res) imm) (o (Owned Res) imm opt))))
  (define sink `(NFn (,output-record) Int () () () User))
  (define accepted
    '(Apply h
       (RecRewrite (Forward x)
         ((o old-o Int imm (Owned Res) (Forward z))))))
  (define-values (accepted-core accepted-callables)
    (two-resource-owner-lambda input-record '(Owned Res) accepted sink))
  ;; entry body の環境は旧欄 binder だけで閉じているため、外側の z を参照する
  ;; optional entry は条件 2 の検査より先に unbound-variable になる。
  (check-equal? (typing-key accepted-core '() accepted-callables)
                'unbound-variable)
  (define rejected
    '(Apply h
       (RecRewrite (Forward x)
         ((a old-a Int imm (Owned Res) (Forward z))
          (o old-o Int imm (Owned Res) (Forward z))))))
  (define required-input
    '(Record ((a Int imm) (keep (Owned Res) imm) (o Int imm opt))))
  (define required-output
    '(Record ((a (Owned Res) imm) (keep (Owned Res) imm)
              (o (Owned Res) imm opt))))
  (define required-sink `(NFn (,required-output) Int () () () User))
  (define-values (rejected-core rejected-callables)
    (two-resource-owner-lambda required-input '(Owned Res) rejected required-sink))
  (check-equal? (typing-key rejected-core '() rejected-callables)
                'unbound-variable))

(test-case "UnionEliminate を含む T は各枝で転送できる"
  (define option-owned '(Option (Owned Res)))
  (define source-union `(Union ,option-owned Int))
  (define sink `(NFn (,option-owned) Int () () () User))
  (define body
    `(Apply h
            (UnionEliminate (Forward x)
              ((,option-owned option ->
               (Scope ()
                  (Let (payload let ,option-owned) option (Forward payload))))
               (Int number -> (Construct ,option-owned none))))))
  (define-values (core callables)
    (typed-owner-lambda source-union body sink))
  (check-equal? (typing-key core '() callables) 'ok))

(test-case "UnionEliminate の排他的な各枝で同じ binder を一度ずつ転送できる"
  (define input-union (normalize-type '(Union Int Bool)))
  (define sink sink-type)
  (define accepted
    '(Apply h
       (UnionEliminate source
         ((Int i -> (Forward x))
          (Bool b -> (Forward x))))))
  (define owner `(NFn (,sink ,input-union (Owned Res)) Int () () () User))
  (define-values (accepted-core accepted-callables)
    (values
     `(Lam User owner (h source p)
        (Handle (Return owner Int) (answer -> answer)
          (Scope () (Let (x let (Owned Res)) p ,accepted))))
     `((owner ,owner) (sink ,sink))))
  (check-equal? (typing-key accepted-core '() accepted-callables) 'ok)
  (define duplicate
    '(UnionEliminate source
       ((Int i -> (Apply h (Forward x) (Forward x)))
        (Bool b -> (Apply h (Forward x) (Forward x))))))
  (define duplicate-owner
    `(NFn (,sink-two-type ,input-union (Owned Res)) Int () () () User))
  (define-values (duplicate-core duplicate-callables)
    (values
     `(Lam User owner (h source p)
        (Handle (Return owner Int) (answer -> answer)
          (Scope () (Let (x let (Owned Res)) p ,duplicate))))
     `((owner ,duplicate-owner) (sink ,sink-two-type))))
  (check-equal? (diagnostic-code-of-core duplicate-core '() duplicate-callables)
                "E-OWN-036"))

(test-case "T から外れた効果と Move は E-OWN-036"
  (define-values (perform-core perform-callables)
    (owner-lambda
     '(Apply h (Let (y let Int) (Perform (Return owner Int) 1) (Forward x)))))
  (check-equal? (diagnostic-code-of-core perform-core '() perform-callables)
                "E-OWN-036")
  (define-values (move-core move-callables)
    (owner-lambda
     '(Apply h (Let (y let (Owned Res)) (Forward x) (Move y)))
     sink-type
     '(Own)))
  (check-equal? (diagnostic-code-of-core move-core '() move-callables)
                "E-OWN-036"))

(test-case "所有する Lam の外の Forward は E-OWN-036"
  (check-equal? (diagnostic-code-of-core '(Forward 0) '((0 Res)))
                "E-OWN-036")
  (check-equal? (diagnostic-code-of-core '(Apply h (Forward 0))
                                         '((0 Res))
                                         '()
                                         `((h ,sink-type)))
                "E-OWN-036"))

(test-case "core-check-row も既存の型検査後に Forward を検査する"
  (check-false
   (core-check-row '(Forward 0) '((0 Res)) '() '(Owned Res))))

(test-case "config の Forward は Available の place だけを受理する"
  (define function-type '(NFn ((Owned Res)) Int () () () User))
  (define function
    '(Lam User consume (argument)
       (Handle (Return consume Int) (answer -> answer)
         (Scope () (Let (owned let (Owned Res)) argument 0)))))
  (define core `(Apply ,function (Forward 0)))
  (define scoped-core `(Apply ,function (Scope (0) (Forward 0))))
  (define callables `((consume ,function-type)))
  (for ([state '(Available Moved)])
    (for ([control (in-list (list core scoped-core))])
      (define configuration
        `(cfg ,control
              ((0 (resource 0)))
              ((0 ,state))
              () ()))
      (check-equal? (config-ok? configuration callables 'Int '())
                    (eq? state 'Available)))))

(test-case "Forward の失敗より資源仮引数の符号化を先に診断する"
  (define malformed
    `(Lam User owner (p)
       (Handle (Return owner Int) (answer -> answer)
         (Apply sink (Forward p)))))
  (check-equal? (typing-key malformed '() `((owner (NFn ((Owned Res)) Int () () () User))
                                            (sink ,sink-type)))
                'owned-parameter-missing-binding))

(test-case "Forward を同じ転送 binder に二度使うと E-OWN-036"
  (define-values (core callables)
    (owner-lambda '(Apply h (Forward x) (Forward x)) sink-two-type))
  (check-equal? (diagnostic-code-of-core core '() callables)
                "E-OWN-036"))

(test-case "遅延する値の本体は外側の Forward 文脈を継承しない"
  (define recur-type '(NFn () (Owned Res) () () () User))
  (define receiver-type `(NFn (,recur-type) Int () () () User))
  (define-values (core owner-callables)
    (owner-lambda '(Apply h (RecurVal recur recur-id () (Forward 0)))
                  receiver-type))
  (check-equal? (diagnostic-code-of-core
                 core '((0 Res)) (cons `(recur ,recur-type) owner-callables))
                "E-OWN-036"))

(test-case "T の値に入った資源仮引数なし Lam は外側の Forward 文脈を継承しない"
  (define delayed-type '(NFn (Unit) (Owned Res) () () () User))
  (define receiver-type `(NFn (,delayed-type) Int () () () User))
  (define-values (core owner-callables)
    (owner-lambda '(Apply h (Lam User delayed (arg) (Forward 0)))
                  receiver-type))
  (check-equal? (diagnostic-code-of-core
                 core '((0 Res)) (cons `(delayed ,delayed-type) owner-callables))
                "E-OWN-036"))

(test-case "Recur の本体も外側の Forward 文脈を継承しない"
  (define recur-type '(NFn () (Owned Res) () () () User))
  (define core '(Recur recur-id loop () (Forward 0) unit))
  (check-equal? (diagnostic-code-of-core core '((0 Res))
                                         `((recur-id ,recur-type)))
                "E-OWN-036"))

(test-case "RegionLam 内の遅延本体も static gate が走査する"
  (define body-type '(NFn (Unit) (Owned Res) () () () User))
  (define core '(RegionLam (rho) (Lam User delayed (arg) (Forward 0))))
  (check-equal? (diagnostic-code-of-core
                 core '((0 Res)) `((delayed ,body-type)))
                "E-OWN-036"))

(test-case "T の値に入った所有する Lam は自分の転送 binder を使う"
  (define inner-type `(NFn (,sink-type (Owned Res)) Int () () () User))
  (define receiver-type `(NFn (,inner-type) Int () () () User))
  (define-values (core owner-callables)
    (owner-lambda
     '(Apply h
             (Lam User inner (g q)
               (Handle (Return inner Int) (answer -> answer)
                 (Scope () (Let (z let (Owned Res)) q (Apply g (Forward z)))))))
     receiver-type))
  (check-equal? (typing-key core '()
                            (cons `(inner ,inner-type) owner-callables))
                'ok)
  (check-equal? (core-type-of
                 core '() (cons `(inner ,inner-type) owner-callables))
                (list `(NFn (,receiver-type (Owned Res)) Int () () () User) '())))

(test-case "非資源 binder の shadowing では move-non-owned が先に返る"
  (define-values (core callables)
    (owner-lambda '(Apply h (Let (x let Int) 1 (Forward x)))))
  (check-equal? (typing-key core '() callables) 'move-non-owned))

(test-case "T の資源 binder を Forward 以外で参照すると E-OWN-036"
  (define-values (core callables)
    (owner-lambda
     '(Apply h (Let (y let (Owned Res)) (Forward x) y))))
  (check-equal? (diagnostic-code-of-core core '() callables)
                "E-OWN-036"))

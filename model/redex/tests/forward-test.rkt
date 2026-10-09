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
         "../gen.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../obs.rkt"
         "../pr-obs.rkt"
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

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 120])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule following))
       (loop following (append configs (list following))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (check-config-trace configs callables expected-type)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected-type))
    (check-not-false row
                     (format "config ~a の runtime row が無い: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected-type row)
                (format "config ~a が不正: ~s" index configuration))))

(define (config-core configuration)
  (match configuration [`(cfg ,core ,_ ...) core]))

(define (config-states configuration)
  (match configuration [`(cfg ,_ ,_ ,states ,_ ...) states]))

(define (state-of configuration place)
  (define entry (assoc place (config-states configuration)))
  (and entry (second entry)))

(define (forward-place configuration)
  (let walk ([term (config-core configuration)])
    (match term
      [`(Forward ,(? exact-nonnegative-integer? place)) place]
      [(? pair?) (or (walk (car term)) (walk (cdr term)))]
      [_ #f])))

(define (available-to-moved-count configs place)
  (for/sum ([before (in-list configs)] [after (in-list (cdr configs))])
    (if (and (eq? (state-of before place) 'Available)
             (eq? (state-of after place) 'Moved))
        1
        0)))

(define limits (read-bounds))
(define observation-depth (bounds-observation-depth limits))
(define source-fuel (bounds-fuel limits))
(define fuel-attempts 4)

(define (obs-eval-pr/adaptive target depth start-fuel)
  (let loop ([fuel start-fuel] [remaining fuel-attempts])
    (define result (obs-eval-pr target depth fuel))
    (cond
      [(not (eq? (second result) 'timeout)) result]
      [(<= remaining 1) #f]
      [else (loop (* 2 fuel) (sub1 remaining))])))

(define (lowered-value value)
  (define-values (status result) (lower-value value 'racket-cs))
  (and (eq? status 'ok) result))

;; properties-lowering-test.rkt の compare-observations を公開面を増やさずに写す。
(define (compare-observations core target depth)
  (define source (obs-eval-g2 core depth source-fuel))
  (cond
    [(eq? (second source) 'timeout) 'discard]
    [else
     (define target-result (obs-eval-pr/adaptive target depth source-fuel))
     (cond
       [(not target-result) 'discard]
       [(and (equal? (map lowered-value (first source))
                   (first target-result))
             (eq? (second source) (second target-result)))
        'match]
       [else 'mismatch])]))

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

(test-case "結果位置では UnionEliminate 全体の T を先に判定する"
  (define option-owned '(Option (Owned Res)))
  (define source-union (normalize-type `(Union ,option-owned Int)))
  (define getter-type `(NFn (Unit) ,source-union () () () User))
  (define mapper-type `(NFn (,option-owned) ,option-owned (Suspend) () () User))
  (define result-type option-owned)
  (define owner-type `(NFn (,getter-type Unit) ,result-type () () () User))
  (define branches
    `((,option-owned option ->
       (Scope ()
         (Let (payload let ,option-owned) option (Forward payload))))
      (Int number -> (Construct ,option-owned none))))
  (define owner
    `(Lam User result-owner (get u)
       (Handle (Return result-owner ,result-type) (answer -> answer)
         (Scope ()
           (Let (result let ,source-union) (Apply get unit)
             (UnionEliminate (Forward result) ,branches))))))
  (define getter
    `(Lam User result-getter (argument)
       (Handle (Return result-getter ,source-union) (answer -> answer)
         (Scope () (UnionInject ,source-union Int 7)))))
  (define callables
    `((result-owner ,owner-type) (result-getter ,getter-type)))
  (check-equal? (core-type-of owner '() callables) (list owner-type '()))
  (define program `(Apply ,owner ,getter unit))
  (check-equal? (core-type-of program '() callables) (list result-type '()))
  (define-values (configs rules)
    (trace-g2 `(cfg (Scope () ,program) () () () ())))
  (check-config-trace configs callables result-type)
  (check-equal? (count (lambda (rule) (eq? rule 'R-Forward)) rules) 1)

  ;; 枝の E_tail Let が Apply を評価した後に転送する形は全体として T でない。
  (define bad-branches
    `((,option-owned option ->
       (Scope ()
         (Let (alias let ,option-owned) option
           (Let (mapped let ,option-owned) (Apply mapper (Forward alias))
             (Forward mapped)))))
      (Int number -> (Construct ,option-owned none))))
  (define bad-owner-type
    `(NFn (,getter-type ,mapper-type Unit) ,result-type (Suspend) () () User))
  (define bad-owner
    `(Lam User bad-result-owner (get mapper u)
       (Handle (Return bad-result-owner ,result-type) (answer -> answer)
         (Scope ()
           (Let (result let ,source-union) (Apply get unit)
             (UnionEliminate (Forward result) ,bad-branches))))))
  (define bad-callables
    `((bad-result-owner ,bad-owner-type)
      (result-getter ,getter-type)))
  (check-equal? (diagnostic-code-of-core bad-owner '() bad-callables)
                "E-OWN-036"))

(test-case "結果位置の Let の束縛式は通常の Forward 文脈で走査する"
  (define option-owned '(Option (Owned Res)))
  (define source-union (normalize-type `(Union ,option-owned Int)))
  (define getter-type `(NFn (Unit) ,source-union () () () User))
  (define result-type 'Unit)
  (define owner-type `(NFn (,getter-type Unit) ,result-type () (Own) () User))
  (define branches
    `((,option-owned option ->
       (Scope ()
         (Let (payload let ,option-owned) option (Forward payload))))
      (Int number -> (Construct ,option-owned none))))
  (define owner
    `(Lam User result-bound-owner (get u)
       (Handle (Return result-bound-owner ,result-type) (answer -> answer)
         (Scope ()
           (Let (result let ,source-union) (Apply get unit)
             (Let (mapped let ,option-owned)
               (UnionEliminate (Forward result) ,branches)
               (Drop (Move mapped))))))))
  (define callables `((result-bound-owner ,owner-type)
                      (result-getter ,getter-type)))
  (check-equal? (diagnostic-code-of-core owner '() callables) "E-OWN-036"))

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

(test-case "RecRewriteOpen の欄は外側の Forward binder を捕捉しない"
  (define option-owned '(Option (Owned Res)))
  (define target `(Record ((owned ,option-owned imm))))
  (define sink-type `(NFn (,target) Int () (Own) () User))
  (define sink
    `(Lam User sink (argument)
       (Handle (Return sink Int) (answer -> answer)
         (Scope ()
           (Let (owned let ,target) argument
             (Let (dropped let Unit) (Drop (Move owned)) 0))))))
  (define callables `((sink ,sink-type)))
  (define core
    `(Scope (0)
       (Let (outer let (Owned Res)) (Move 0)
         (Apply ,sink
           (RecRewriteOpen
            ((owned imm
                    (Construct ,option-owned some (Forward outer)))))))))
  (define configuration
    `(cfg ,core ((0 (resource 7))) ((0 Available)) () ()))
  (define safe-core
    `(Scope (0)
       (Let (outer let (Owned Res)) (Move 0)
         (Apply ,sink
           (RecRewriteOpen
            ((owned imm (Construct ,option-owned none))))))))
  (define safe-configuration
    `(cfg ,safe-core ((0 (resource 7))) ((0 Available)) () ()))
  (check-true (config-ok? safe-configuration callables 'Int '(Own)))
  (check-false (config-ok? configuration callables 'Int '(Own))))

(test-case "Union から Record への変換は枝 alias と一時 place を転送する"
  (define field-union (normalize-type '(Union Int Bool)))
  (define owned-field '(Option (Owned Res)))
  (define member-bool
    `(Record ((a Bool imm) (owned ,owned-field imm))))
  (define member-int
    `(Record ((a Int imm) (owned ,owned-field imm))))
  (define input-union (normalize-type `(Union ,member-bool ,member-int)))
  (define target
    `(Record ((a ,field-union imm) (owned ,owned-field imm))))
  (define sink-type `(NFn (,target) Int () (Own) () User))
  (define sink
    `(Lam User sink (argument)
       (Handle (Return sink Int) (answer -> answer)
         (Scope ()
           (Let (owned let ,target) argument
             (Let (dropped let Unit) (Drop (Move owned)) 0))))))
  (define (branch member binder old-field-type)
    `(Scope ()
       (Let (alias let ,member) ,binder
         (Let (temporary let ,target)
           (RecRewrite (Forward alias)
             ((a old-a ,old-field-type imm ,field-union
               (UnionInject ,field-union ,old-field-type old-a))))
           (Forward temporary)))))
  (define body
    `(Apply h
            (UnionEliminate (Forward x)
              ((,member-bool bool-value -> ,(branch member-bool 'bool-value 'Bool))
               (,member-int int-value -> ,(branch member-int 'int-value 'Int))))))
  (define owner-type
    `(NFn (,sink-type ,input-union) Int () (Own) () User))
  (define owner
    `(Lam User owner (h p)
       (Handle (Return owner Int) (answer -> answer)
         (Scope () (Let (x let ,input-union) p ,body)))))
  (define callables `((owner ,owner-type) (sink ,sink-type)))
  (for ([member (in-list (list member-bool member-int))]
        [field-value (in-list (list '(Construct Bool true) 42))]
        [token (in-list '(51 52))])
    (define input
      `(UnionInject ,input-union ,member
                    (Rec ((a imm ,field-value)
                          (owned imm
                                 (Construct (Option (Owned Res)) some
                                   (OwnLeaf (resource ,token))))))))
    (define core `(Apply ,owner ,sink ,input))
    (define expected-type
      (match (core-type-of core '() callables)
        [(list type _row) type]
        [other (fail (format "Union→Record fixture の型を得られない: ~s; key=~s"
                             other (type-of/raw core '() callables)))]))
    (define-values (status target-pr) (lower core 'racket-cs))
    (check-eq? status 'ok)
    (check-eq? (compare-observations core target-pr observation-depth) 'match)
    (define-values (configs rules)
      (trace-g2 `(cfg (Scope () ,core) () () () ())))
    (check-config-trace configs callables expected-type)
    (define forward-transitions
      (for/list ([before (in-list configs)]
                 [rule (in-list rules)]
                 [after (in-list (cdr configs))]
                 #:when (eq? rule 'R-Forward))
        (list before after)))
    (check-equal? (length forward-transitions) 3)
    (define moved-places
      (map (λ (transition) (forward-place (first transition)))
           forward-transitions))
    (check-equal? (length (remove-duplicates moved-places)) 3)
    (for ([place (in-list moved-places)])
      (check-equal? (available-to-moved-count configs place) 1))
    (define (contains-rewrite-forward? term)
      (match term
        [`(RecRewrite (Forward ,(? exact-nonnegative-integer?)) ,_) #t]
        [(? pair?) (or (contains-rewrite-forward? (car term))
                       (contains-rewrite-forward? (cdr term)))]
        [_ #f]))
    (check-equal?
     (count (λ (transition)
              (contains-rewrite-forward? (config-core (first transition))))
            forward-transitions)
     1)
    (for ([before (in-list configs)]
          [rule (in-list rules)]
          [after (in-list (cdr configs))]
          #:when (eq? rule 'R-ScopeValue))
      (check-equal?
       (for/sum ([old (in-list (config-states before))]
                 [new (in-list (config-states after))])
         (if (and (eq? (second old) 'Available)
                  (eq? (second new) 'Dropped))
             1
             0))
       0))))

(test-case "R-Beta 後の転送 Let も R-LetOwned まで構成検査を通る"
  (define-values (owner callables)
    (owner-lambda '(Apply h (Forward x))))
  (define sink
    '(Lam User sink (argument)
       (Handle (Return sink Int) (answer -> answer)
         (Scope () (Let (owned let (Owned Res)) argument 0)))))
  (define program
    `(Apply ,owner ,sink (Apply (PrimVal (Reserved o-acquire) acquire) 0)))
  (check-equal? (core-type-of program '() callables) (list 'Int '()))
  (define start `(cfg (Scope () ,program) () () () ()))
  (define-values (configs rules)
    (let loop ([current start] [configs '()] [rules '()] [fuel 80])
      (when (zero? fuel)
        (error 'forward-config-trace "評価 fuel を使い切った: ~s" current))
      (define next (raw-steps-g2/named current))
      (match next
        ['() (values (append configs (list current)) rules)]
        [(list (list rule following))
         (loop following
               (append configs (list current))
               (append rules (list rule))
               (sub1 fuel))]
        [_ (error 'forward-config-trace "一意な次状態を期待した: ~s" next)])))
  (check-not-false (memq 'R-Beta rules))
  (check-not-false (memq 'R-LetOwnedB rules))
  (check-not-false
   (for/or ([before (in-list rules)] [after (in-list (cdr rules))])
     (equal? (list before after) '(R-Beta R-LetOwnedB))))
  (check-equal? (match (car (reverse configs))
                  [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value])
                0)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables 'Int))
    (check-not-false row
                     (format "runtime row を得られない中間 config ~a: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables 'Int row)
                (format "不正な中間 config ~a: ~s" index configuration))))

(test-case "UnionEliminate を含む trace の runtime-row は config gate を使う"
  (define option-owned '(Option (Owned Res)))
  (define input-union (normalize-type `(Union ,option-owned Int)))
  (define sink-type `(NFn (,option-owned) Int () () () User))
  (define sink
    '(Lam User sink (argument)
       (Handle (Return sink Int) (answer -> answer)
         (Scope () (Let (owned let (Option (Owned Res))) argument 0)))))
  (define body
    `(Apply h
            (UnionEliminate (Forward x)
              ((,option-owned option ->
                (Scope ()
                  (Let (payload let ,option-owned) option (Forward payload))))
               (Int number -> (Construct ,option-owned none))))))
  (define-values (owner callables)
    (typed-owner-lambda input-union body sink-type))
  (for ([argument (in-list
                   (list
                    `(UnionInject ,input-union ,option-owned
                                  (Construct ,option-owned some
                                             (OwnLeaf (resource 41))))
                    `(UnionInject ,input-union Int 42)))])
    (define program `(Apply ,owner ,sink ,argument))
    (define expected-type
      (match (core-type-of program '() callables)
        [(list type _row) type]
        [other (fail (format "Union fixture の型を得られない: ~s; key=~s"
                             other (typing-key program '() callables)))]))
    (define start `(cfg (Scope () ,program) () () () ()))
    (define-values (configs _rules)
      (let loop ([current start] [reversed-configs '()] [rules '()] [fuel 120])
        (when (zero? fuel)
          (error 'union-forward-trace "評価 fuel を使い切った: ~s" current))
        (define next (raw-steps-g2/named current))
        (match next
          ['() (values (reverse (cons current reversed-configs)) rules)]
          [(list (list rule following))
           (loop following (cons current reversed-configs)
                 (append rules (list rule)) (sub1 fuel))]
          [_ (error 'union-forward-trace "一意な次状態を期待した: ~s" next)])))
    (for ([configuration (in-list configs)] [index (in-naturals)])
      (define row (runtime-row configuration callables expected-type))
      (check-not-false row
                       (format "Union config ~a の runtime row が無い: ~s"
                               index configuration))
      (check-true (config-ok? configuration callables expected-type row)
                  (format "Union config ~a が不正: ~s" index configuration)))))

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

(define (replace-place-state configuration place new-state)
  (match configuration
    [`(cfg ,core ,heap ,states ,tokens ,events)
     `(cfg ,core ,heap
           ,(for/list ([entry (in-list states)])
              (if (equal? (first entry) place)
                  (list place new-state)
                  entry))
           ,tokens ,events)]))

(define (replace-forward-with-move term place)
  (match term
    [`(Forward ,(? exact-nonnegative-integer? candidate))
     (if (= candidate place) `(Move ,place) term)]
    [(? pair?)
     (cons (replace-forward-with-move (car term) place)
           (replace-forward-with-move (cdr term) place))]
    [_ term]))

(define (new-place-between before after)
  (for/first ([entry (in-list (config-states after))]
              #:unless (assoc (first entry) (config-states before)))
    (first entry)))

(test-case "所有する Lam の Forward は一度だけ place を移す"
  (define-values (owner callables)
    (owner-lambda '(Apply h (Forward x)) sink-type '(Own)))
  (define sink
    '(Lam User sink (argument)
       (Handle (Return sink Int) (answer -> answer)
         (Scope () (Let (owned let (Owned Res)) argument 0)))))
  (define core `(Apply ,owner ,sink (Move 0)))
  (define expected-type
    (match (core-type-of core '((0 Res)) callables)
      [(list type _row) type]
      [other (fail (format "Apply の型を得られない: ~s" other))]))
  (define start
    `(cfg (Scope (0) ,core) ((0 (resource 0))) ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-config-trace configs callables expected-type)
  (check-equal? (count (λ (rule) (eq? rule 'R-Forward)) rules) 1)
  (define transition
    (for/first ([before (in-list configs)]
                [rule (in-list rules)]
                [after (in-list (cdr configs))]
                #:when (eq? rule 'R-Forward))
      (list before after)))
  (check-not-false transition)
  (define before-forward (first transition))
  (define after-forward (second transition))
  (define place (forward-place before-forward))
  (check-not-false place)
  (check-eq? (state-of before-forward place) 'Available)
  (check-eq? (state-of after-forward place) 'Moved)
  (check-equal? (available-to-moved-count configs place) 1)
  (define row (runtime-row before-forward callables expected-type))
  (check-false
   (config-ok? (replace-place-state before-forward place 'Moved)
               callables expected-type row))
  (define moved-config (replace-place-state before-forward place 'Moved))
  (define move-config
    (match moved-config
      [`(cfg ,control ,heap ,states ,tokens ,events)
       `(cfg ,(replace-forward-with-move control place)
             ,heap ,states ,tokens ,events)]))
  (define move-row (runtime-row move-config callables expected-type))
  (check-not-false move-row)
  (check-true (config-ok? move-config callables expected-type move-row)))

(test-case "Forward より先の Return は転送 place を cleanup する"
  (define return-sink-type '(NFn ((Owned Res)) Unit () () () User))
  (define owner-type
    `(NFn (,return-sink-type (Owned Res)) Unit () ((Return b Unit)) () User))
  (define sink
    '(Lam User sink (argument)
       (Handle (Return sink Unit) (answer -> answer)
         (Scope () (Let (owned let (Owned Res)) argument unit)))))
  (define owner
    '(Lam User owner (h p)
       (Handle (Return owner Unit) (answer -> answer)
         (Scope ()
           (Let (x let (Owned Res)) p
             (Let (u let Unit) (Perform (Return b Unit) unit)
               (Apply h (Forward x))))))))
  (define callables `((owner ,owner-type) (sink ,return-sink-type)))
  (define core
    `(Handle (Return b Unit) (answer -> answer)
       (Scope (0) (Let (h0 let ,return-sink-type) ,sink
                    (Apply ,owner h0 (Move 0))))))
  (define expected-type
    (match (core-type-of core '((0 Res)) callables)
      [(list type _row) type]
      [other (fail (format "Return cleanup の型を得られない: ~s" other))]))
  (define start
    `(cfg ,core ((0 (resource 0))) ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-config-trace configs callables expected-type)
  (define owned-transition
    (for/first ([before (in-list configs)]
                [rule (in-list rules)]
                [after (in-list (cdr configs))]
                #:when (eq? rule 'R-LetOwnedB))
      (list before after)))
  (check-not-false owned-transition)
  (define place (new-place-between (first owned-transition)
                                   (second owned-transition)))
  (check-not-false place)
  (define owner-scope-has-place?
    (let walk ([term (config-core (second owned-transition))])
      (match term
        [`(Handle (Return owner Unit) ,_ (Scope (,places ...) ,_))
         (and (member place places) #t)]
        [(? pair?) (or (walk (car term)) (walk (cdr term)))]
        [_ #f])))
  (check-true owner-scope-has-place?)
  (define scope-abort-position (index-of rules 'R-ScopeAbort))
  (define handle-skip-position (index-of rules 'R-HandleSkip))
  (check-not-false scope-abort-position)
  (check-not-false handle-skip-position)
  (check-true (< scope-abort-position handle-skip-position))
  (check-false (memq 'R-Forward rules))
  (check-equal?
   (for/sum ([before (in-list configs)] [after (in-list (cdr configs))])
     (if (and (eq? (state-of before place) 'Available)
              (eq? (state-of after place) 'Dropped))
         1
         0))
   1)
  (check-eq? (state-of (last configs) place) 'Dropped)
  (check-equal? (config-core (last configs)) 'unit))

(test-case "Forward と T の Let の観測は PR と一致する"
  (define sink
    '(Lam User sink (argument)
       (Handle (Return sink Int) (answer -> answer)
         (Scope () (Let (owned let (Owned Res)) argument 0)))))
  (for ([body (in-list
               (list '(Apply h (Forward x))
                     '(Apply h
                             (Let (y let (Owned Res))
                               (Forward x)
                               (Forward y)))))]
        [label (in-list '("Forward" "Forward と T の Let"))])
    (define-values (owner callables) (owner-lambda body))
    (define core `(Apply ,owner ,sink (resource 23)))
    (define-values (status target) (lower core 'racket-cs))
    (check-eq? status 'ok label)
    (check-eq? (compare-observations core target observation-depth) 'match
               label)))

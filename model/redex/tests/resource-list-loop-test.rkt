#lang racket

(require rackunit
         racket/list
         racket/match
         racket/string
         "../diagnostic.rkt"
         "../borrow.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt"
         "../elaborate.rkt")

(define resource-list '(List (Owned Res)))

(define (owned-list-value numbers)
  (foldr (λ (number tail)
           `(Construct cons (Types (Owned Res))
             (Apply acquire ,number) ,tail))
         '(Construct nil (Types (Owned Res)))
         numbers))

(define (loop-source branch-body [numbers '(1 2)])
  `(Apply
    (Fn ((items ,resource-list)) Unit (Partial Own)
      (Loop walk ((rest #:infer)) Unit #:infer
        (Eliminate (Move rest)
          ((nil () -> unit)
           (cons (head tail) -> ,branch-body)))
        ((Move items))))
    ,(owned-list-value numbers)))

(define (resource-loop branch-body [extra-parameters '()]
                       [extra-arguments '()] [numbers '(1 2)]
                       [nil-body 'unit])
  `(Loop walk ((rest #:infer) ,@extra-parameters) Unit #:infer
     (Eliminate (Move rest)
       ((nil () -> ,nil-body)
        (cons (head tail) -> ,branch-body)))
     ((Move items) ,@extra-arguments)))

(define (resource-loop-program loop [result-type 'Unit]
                               [fn-row '(Partial Own)]
                               [body-prefix #f] [numbers '(1 2)])
  `(Apply
    (Fn ((items ,resource-list)) ,result-type ,fn-row
      ,(if body-prefix
           (body-prefix loop)
           loop))
    ,(owned-list-value numbers)))

(define (for-option-loop loop payload-type)
  `(NarrativeExpr
    (Let (%for-option-resource-test const Unit)
      ,loop
      (Construct none (Types ,payload-type)))) )

(define (run-program program)
  (match (elab program)
    [(list core expected _row callables)
     (define executable (execution-core (erase-core core) callables))
     (define run (bounded-trace-g2 (inject-g2m executable) 1000))
     (check-equal? (execution-outcome run) 'terminal)
     (define configs (execution-configs run))
     (for ([configuration (in-list configs)] [index (in-naturals)])
       (define row (runtime-row configuration callables expected))
       (check-not-false row
                        (format "config ~a に runtime-row がある: ~s"
                                index configuration))
       (check-true (and row (config-ok? configuration callables expected row))
                   (format "config ~a が config-ok? を満たす: ~s"
                           index configuration)))
     (values configs expected callables core)]
    [`(err ,diagnostic)
     (fail-check (format "UCore を elaborate できない: ~a: ~a"
                         (diagnostic-id diagnostic)
                         (diagnostic-message diagnostic)))]
    [other (fail-check (format "UCore を elaborate できない: ~s" other))]))

(define (finish-events configuration)
  (filter (λ (event) (match event [`(fin ,_) #t] [`(finLeaf ,_ ,_) #t] [_ #f]))
          (config-events configuration)))

(define (check-all-dropped configuration token-count)
  (check-equal? (map second (config-tokens configuration))
                (make-list token-count 'Dropped)))

(define (rule-between before after)
  (define named (raw-steps-g2/named before))
  (or (for/or ([step (in-list named)])
        (and (equal? (second step) after) (first step)))
      (let ([rules (remove-duplicates (map first named))])
        (and (= (length rules) 1) (first rules)))))

(define (token-drop-transitions configurations)
  (append*
   (for/list ([before (in-list configurations)]
              [after (in-list (cdr configurations))])
     (for/list ([entry (in-list (config-tokens after))]
                #:when (and (eq? (second entry) 'Dropped)
                            (eq? (token-state before (first entry)) 'Available)))
       (list (first entry) (rule-between before after))))))

(define (token-state configuration token)
  (define entry (assoc token (config-tokens configuration)))
  (and entry (second entry)))

(define (check-dropped-once configurations tokens)
  (define drops (token-drop-transitions configurations))
  (for ([token (in-list tokens)])
    (define token-drops
      (filter (λ (drop) (equal? (first drop) token)) drops))
    (check-equal? (length token-drops) 1
                  (format "~s は Available から Dropped へ一度だけ遷移する" token))
    (when (= (length token-drops) 1)
      (check-not-false (second (first token-drops))
                       (format "~s の drop 規則を trace から特定できる" token)))))

(define (trace-rules configurations)
  (remove-duplicates
   (append*
    (for/list ([configuration (in-list configurations)])
      (map first (raw-steps-g2/named configuration))))))

(define (check-terminal-ledger configurations [carried '()])
  (define terminal (last configurations))
  (define tokens (config-tokens terminal))
  (for ([entry (in-list tokens)])
    (check-equal? (second entry)
                  (if (member (first entry) carried) 'Available 'Dropped)))
  (check-dropped-once
   configurations
   (map first (filter (λ (entry) (eq? (second entry) 'Dropped)) tokens))))

(define (check-finish-counts configurations token-count)
  (define terminal (last configurations))
  (check-equal? (length (finish-events terminal)) token-count)
  (check-equal? (length (remove-duplicates (finish-events terminal) equal?))
                token-count))

(define (loop-shape-error? failure)
  (and (exn:fail? failure)
       (regexp-match? #rx"loop 印の形の違反" (exn-message failure))))

(define (elab-error-id expression)
  (match (elab expression)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define source
  `(Apply
    (Fn ((items ,resource-list)) Unit (Partial Own)
      (Recur walk ((rest ,resource-list)) Unit (Partial Own)
        (Eliminate (Move rest)
          ((nil () -> unit)
           (cons (head tail) ->
             (Apply walk (Move tail)))))
        (Apply walk (Move items))))
    (Construct cons (Types (Owned Res))
      (Apply acquire 1)
      (Construct cons (Types (Owned Res))
        (Apply acquire 2)
        (Construct nil (Types (Owned Res)))))))

(define (elaborated-source [program source])
  (match (elab program)
    [(list core expected _row callables)
     (values (execution-core (erase-core core) callables)
             expected callables)]
    [other (fail-check (format "UCore を elaborate できない: ~s" other))]))

(define (run-source [program source])
  (define-values (core expected callables) (elaborated-source program))
  (define run (bounded-trace-g2 (inject-g2m core) 500))
  (check-equal? (execution-outcome run) 'terminal)
  (values (execution-configs run) expected callables core))

(define (first-recur-unfold configs)
  (for/or ([configuration (in-list configs)])
    (for/or ([step (in-list (raw-steps-g2/named configuration))])
      (and (eq? (first step) 'R-RecurUnfold) (second step)))))

(define (cons-branches term)
  (let walk ([value (erase-core term)])
    (match value
      [`(Eliminate ,scrutinee (,arms ...))
       (append
        (for/list ([arm (in-list arms)]
                   #:when (match arm [`(cons (,head ,tail) -> ,_) #t] [_ #f]))
          (match arm [`(cons (,head ,tail) -> ,body) (list head tail body)]))
        (walk scrutinee)
        (append* (for/list ([arm (in-list arms)]) (walk (last arm)))))]
      [(? pair? parts) (append* (map walk parts))]
      [_ '()])))

(define (first-recurval term)
  (let walk ([value (erase-core term)])
    (match value
      [`(RecurVal ,_ ,_ ,_ ,_) value]
      [(? pair? parts) (for/or ([part (in-list parts)]) (walk part))]
      [_ #f])))

(define (capture-in-recurval term captured)
  (let walk ([value term])
    (match value
      [`(RecurVal ,callable ,function (,parameters ...) ,body)
       (define (insert-after-parameter-lets core)
        (match core
          [`(Scope ,managed ,inner)
           `(Scope ,managed ,(insert-after-parameter-lets inner))]
          [`(Let ,binder ,bound ,next)
            #:when (ormap (lambda (parameter)
                            (equal? (erase-core bound)
                                    (erase-core parameter)))
                          parameters)
            `(Let ,binder ,bound ,(insert-after-parameter-lets next))]
           [_ `(Let (capture-probe let Unit)
                    (Drop (Move ,captured))
                    ,core)]))
       (and captured
            `(RecurVal ,callable ,function ,parameters
                       ,(insert-after-parameter-lets body)))]
      [(? pair? parts)
       (for/or ([part (in-list parts)]) (walk part))]
      [_ #f])))

(define (capture-in-cons-branch term)
  (define changed? #f)
  (define (walk value)
    (if changed?
        value
        (match value
          [`(Eliminate ,scrutinee (,arms ...))
           (define index
             (for/first ([arm (in-list arms)] [i (in-naturals)]
                         #:when
                         (match arm
                           [`(cons (,_ ,_) -> ,body)
                            (and (first-recurval body) #t)]
                           [_ #f]))
               i))
           (if index
               (begin
                 (set! changed? #t)
                 `(Eliminate ,scrutinee
                   ,(for/list ([arm (in-list arms)] [i (in-naturals)])
                      (if (= i index)
                          (match arm
                            [`(cons (,head ,tail) -> ,body)
                             (define injected
                               (for/or ([captured (in-list (list head tail))])
                                 (define candidate
                                   (capture-in-recurval body captured))
                                 (and candidate
                                      (let ([recurval (first-recurval candidate)])
                                        (and recurval
                                             (set-member? (core-free-vars recurval)
                                                          captured)
                                             candidate)))))
                             (and injected
                                  `(cons (,head ,tail) -> ,injected))])
                          arm))))
               `(Eliminate ,(walk scrutinee)
                 ,(for/list ([arm (in-list arms)])
                    (match arm
                      [`(,_ ,_ -> ,body) (append (drop-right arm 1)
                                                 (list (walk body)))]
                      [_ arm]))))]
          [(? pair? parts) (map walk parts)]
          [_ value])))
  (walk (erase-core term)))

;; RecurUnfold 後に消えた branch の canonical Let を補い、同じ raw-use 検査を当てる。
(define (resource-branch-encoding-failure-key control)
  (for/or ([branch (in-list (cons-branches control))])
    (match branch
      [(list head tail body)
       (define inner
         (match body [`(Scope () ,scoped) scoped] [_ body]))
       (define canonical
         (if (equal? body `(Scope () ,inner))
             inner
             `(Let (,(gensym 'probe-head) let (Owned Res)) ,head
                (Let (,(gensym 'probe-tail) let ,resource-list) ,tail
                  ,inner))))
       (let/ec escape
         (check-owned-encoding
          (list head tail)
          (list '(Owned Res) resource-list)
          canonical 'probe
          (lambda (key . _) (escape key))
          #:missing-key (lambda (_) 'resource-binder-missing-binding)
          #:raw-key (lambda (_) 'resource-binder-raw-misuse))
         #f)]
      [_ #f])))

(define (replace-control configuration control)
  (match configuration
    [`(cfg ,_ ,heap ,places ,tokens ,trace)
     `(cfg ,control ,heap ,places ,tokens ,trace)]))

(test-case "B6 loop 印の初回実引数 Move var を受理し Move 式を拒否する"
  (check-not-exn (λ () (elab (loop-source '(Apply walk (Move tail)))))
                 "Move xs は初回実引数として受理する")
  (check-exn
   loop-shape-error?
   (λ ()
     (elab '(Loop walk ((rest #:infer)) Unit #:infer unit ((Apply make-list)))))
   "初回実引数の Apply は既存の shape gate で拒否する")
  (check-equal?
   (elab-error-id
    '(Fn ((items (List (Owned Res)))) Unit (Partial Own)
       (Loop walk ((rest #:infer)) Unit #:infer
         (Eliminate (Move rest)
           ((nil () -> unit)
            (cons (head tail) -> (Apply walk (Move tail)))))
         ((Move (Apply make-list))))))
   "E-SYN-003"))

(test-case "B6b 初回実引数の Move 後の裸読みは拒否し二度目の Move は実行時に失敗する"
  (define (continued-loop continuation)
    `(Apply
      (Fn ((items ,resource-list)) Unit (Partial Own)
        (Let (ignored const Unit)
          ,(resource-loop '(Apply walk (Move tail)))
          ,continuation))
      ,(owned-list-value '(1))))
  (check-equal? (elab-error-id (continued-loop 'items)) "E-OWN-010")
  (match (elab (continued-loop '(Let (again const (List (Owned Res)))
                                     (Move items) unit)))
    [(list core _expected _row callables)
     (define run (bounded-trace-g2
                  (inject-g2m (execution-core (erase-core core) callables)) 300))
     (check-not-false
      (for/or ([configuration (in-list (execution-configs run))])
        (for/or ([step (in-list (raw-steps-g2/named configuration))])
          (eq? (first step) 'R-MoveError))))]
    [other (fail-check (format "二度目の Move は静的に受理する: ~s" other))]))

(test-case "B5 資源 List の再帰走査の全中間 config が型付く"
  (define-values (configs expected callables _core) (run-source))
  (check-not-false
   (for/or ([configuration (in-list configs)])
     (for/or ([step (in-list (raw-steps-g2/named configuration))])
       (eq? (first step) 'R-RecurUnfold))))
  (check-true (pair? configs))
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false
     row (format "config ~a に runtime-row がある: ~s" index configuration))
    (check-true (and row (config-ok? configuration callables expected row))
                (format "config ~a が型付く: ~s" index configuration)))
  (define terminal (last configs))
  (check-equal? (map second (config-tokens terminal)) '(Dropped Dropped)))

(test-case "B7 Loop の正常完了で各要素を一度だけ drop する"
  (define loop (resource-loop '(Apply walk (Move tail))))
  (define-values (configs _type _callables _core)
    (run-program (resource-loop-program loop)))
  (define terminal (last configs))
  (check-all-dropped terminal 2)
  (check-finish-counts configs 2))

(test-case "B8 本体の Drop と反復 Scope は同じ要素を二重 drop しない"
  (define body
    '(Let (dropped const Unit) (Drop (Move head))
       (Apply walk (Move tail))))
  (define loop (resource-loop body))
  (define-values (configs _type _callables _core)
    (run-program (resource-loop-program loop)))
  (define terminal (last configs))
  (check-all-dropped terminal 4)
  (define drops (token-drop-transitions configs))
  (check-equal? (sort (map first drops) < #:key second)
                (sort (map first (config-tokens terminal)) < #:key second))
  (check-equal? (sort (map second drops) string<? #:key symbol->string)
                '(R-Drop R-Drop R-LetOwnedB R-LetOwnedB))
  (check-equal? (finish-events terminal) '()))

(test-case "B9 Leave (Move head) は token を payload に移し未訪問 tail を drop する"
  (define loop (resource-loop '(Leave (Move head))))
  (define program
    (resource-loop-program
     loop '(Option (Owned Res)) '(Partial Own)
     (λ (body) (for-option-loop body '(Owned Res))) '(1 2)))
  (define-values (configs _type _callables _core) (run-program program))
  (define terminal (last configs))
  (define carried (collect-tokens (config-core terminal)))
  (check-equal? (length carried) 1)
  (for ([entry (in-list (config-tokens terminal))])
    (check-equal? (second entry)
                  (if (member (first entry) carried) 'Available 'Dropped)))
  (define dropped
    (map first (filter (λ (entry) (eq? (second entry) 'Dropped))
                       (config-tokens terminal))))
  (check-dropped-once configs dropped)
  (check-not-false (member 'R-ScopeAbort (trace-rules configs)))
  (check-not-false (member 'R-HandleReturn (trace-rules configs)))
  (check-finish-counts configs 2))

(test-case "B10 2 要素目の return は今の head と直前の head を drop する"
  (define loop
    '(Loop walk ((rest #:infer)) Unit #:infer
       (Eliminate (Move rest)
         ((nil () -> unit)
          (cons (head tail) ->
            (Eliminate (Move tail)
              ((nil () -> unit)
               (cons (second rest) -> (Return unit)))))))
       ((Move items))))
  (define-values (configs _type _callables _core)
    (run-program (resource-loop-program loop 'Unit '(Partial Own) #f '(1 2))))
  (check-terminal-ledger configs)
  (check-not-false (member 'R-ScopeAbort (trace-rules configs)))
  (check-not-false (member 'R-HandleReturn (trace-rules configs))))

(test-case "B11 1 要素目の leave は未訪問 tail も一度だけ drop する"
  (define loop (resource-loop '(Leave 0) '() '() '(1 2 3)))
  (define program
    (resource-loop-program
     loop '(Option Int) '(Partial Own)
     (λ (body) (for-option-loop body 'Int)) '(1 2 3)))
  (define-values (configs _type _callables _core) (run-program program))
  (check-terminal-ledger configs)
  (check-equal? (config-core (last configs))
                '(Construct (Option Int) some 0))
  (check-not-false (member 'R-ScopeAbort (trace-rules configs)))
  (check-not-false (member 'R-HandleReturn (trace-rules configs))))

(test-case "B12 内側 Loop の leave は外側の式境界へ届き両方の tail を drop する"
  (define outer-loop
    `(Loop outer ((rest #:infer) (inner-rest #:infer)) Unit #:infer
       (Eliminate (Move rest)
         ((nil () -> unit)
          (cons (outer-head outer-tail) ->
            (Loop inner ((inner-rest #:infer)) Unit #:infer
              (Eliminate (Move inner-rest)
                ((nil () -> unit)
                 (cons (inner-head inner-tail) -> (Leave 0))))
              ((Move inner-rest))))))
       ((Move items) (Move inner-items))))
  (define program
    `(Apply
      (Fn ((items ,resource-list) (inner-items ,resource-list))
          (Option Int) (Partial Own)
        (NarrativeExpr
         (Let (%for-option-nested-test const Unit)
           ,outer-loop (Construct none (Types Int)))))
      ,(owned-list-value '(1 2))
      ,(owned-list-value '(3 4))))
  (define-values (configs _type _callables _core) (run-program program))
  (check-equal? (config-core (last configs))
                '(Construct (Option Int) some 0))
  (check-terminal-ledger configs)
  (check-not-false (member 'R-ScopeAbort (trace-rules configs)))
  (check-not-false (member 'R-HandleReturn (trace-rules configs))))

(test-case "B13 Return (Move head) は token を移送し残りを一度だけ drop する"
  (define loop
    '(Loop walk ((rest #:infer)) (Owned Res) #:infer
       (Eliminate (Move rest)
         ((nil () -> (Return (Apply acquire 0)))
          (cons (head tail) ->
            (Eliminate (Move tail)
              ((nil () -> (Return (Move head)))
               (cons (second rest) -> (Return (Move second))))))))
       ((Move items))))
  (define program
    `(Apply
      (Fn ((items ,resource-list)) (Owned Res) (Partial Own) ,loop)
      ,(owned-list-value '(1 2 3))))
  (define-values (configs _type _callables _core) (run-program program))
  (define terminal (last configs))
  (define carried (collect-tokens (config-core terminal)))
  (check-equal? (length carried) 1)
  (check-terminal-ledger configs carried)
  (check-not-false (member 'R-ScopeAbort (trace-rules configs)))
  (check-not-false (member 'R-HandleReturn (trace-rules configs))))

(define (mut-loop-program loop result-type #:option? [option? #f])
  `(Apply
    (Fn ((items ,resource-list)) ,result-type (Partial Mutation Own)
      (Let (n mut Int) 0
        ,(if option?
             `(NarrativeExpr
               (Let (%for-option-mut-test const Unit)
                 ,loop (Construct none (Types Int))))
             `(Let (result const Unit) ,loop n))))
    ,(owned-list-value '(1 2))))

(test-case "B14 mut accumulator は正常完了で要素数に達する"
  (define loop
    '(Loop walk ((rest #:infer)) Unit #:infer
       (Eliminate (Move rest)
         ((nil () -> unit)
          (cons (head tail) ->
            (Let (incremented const Unit)
              (Reassign n (Apply add n 1))
              (Apply walk (Move tail))))))
       ((Move items))))
  (define-values (configs _type _callables _core)
    (run-program (mut-loop-program loop 'Int)))
  (check-equal? (config-core (last configs)) 2)
  (check-terminal-ledger configs))

(test-case "B14 mut accumulator は 2 要素目の leave で 2 になり全 token を drop する"
  (define loop
    '(Loop walk ((rest #:infer)) Unit #:infer
       (Eliminate (Move rest)
         ((nil () -> unit)
          (cons (head tail) ->
            (Let (incremented const Unit)
              (Reassign n (Apply add n 1))
              (Eliminate (Move tail)
                ((nil () -> (Leave n))
                 (cons (next rest) ->
                   (Let (incremented-again const Unit)
                     (Reassign n (Apply add n 1))
                     (Leave n)))))))))
       ((Move items))))
  (define-values (configs _type _callables _core)
    (run-program (mut-loop-program loop '(Option Int) #:option? #t)))
  (check-equal? (config-core (last configs))
                '(Construct (Option Int) some 2))
  (check-terminal-ledger configs)
  (check-not-false (member 'R-ScopeAbort (trace-rules configs)))
  (check-not-false (member 'R-HandleReturn (trace-rules configs))))

(test-case "B15 #:infer の資源仮引数は Typed Core で Scope と Let に包まれる"
  (define-values (_core _type _callables typed-core)
    (run-program (resource-loop-program
                  (resource-loop '(Apply walk (Move tail))))))
  (define recur-body
    (let walk ([term (erase-core typed-core)])
      (match term
        [`(Recur ,_ ,_ ,_ ,body ,_) body]
        [(? list? parts)
         (for/or ([part (in-list parts)]) (walk part))]
        [_ #f])))
  (check-not-false recur-body)
  (check-not-false
   (let walk ([term recur-body])
     (match term
       [`(Scope ,_ (Let (,_ ,_ (Owned Res)) ,_ ,_)) #t]
       [(? list? parts) (for/or ([part (in-list parts)]) (walk part))]
       [_ #f]))))

(test-case "B5n RecurVal 内の free capture は E-OWN-035 で拒否する"
  (define-values (configs expected callables _core) (run-source))
  (define baseline (first-recur-unfold configs))
  (check-not-false baseline "R-RecurUnfold 直後の config がある")
  (when baseline
    (define baseline-row (runtime-row baseline callables expected))
    (check-not-false baseline-row "基準 config の runtime-row がある")
    (check-true (and baseline-row
                     (config-ok? baseline callables expected baseline-row))
                "基準 config は型付く")
    (define mutated-control (capture-in-cons-branch (config-core baseline)))
    (check-not-false mutated-control "RecurVal を含む cons 枝に tail capture を入れた")
    (when mutated-control
      (define mutated (replace-control baseline mutated-control))
      (check-false (config-ok? mutated callables expected baseline-row))
      (check-false (resource-branch-encoding-failure-key
                    (config-core baseline)))
      (check-equal? (resource-branch-encoding-failure-key mutated-control)
                    'resource-binder-raw-misuse))))

(define generated-loop-name '%for-loop-resource-test)
(define generated-head-name '%for-head-resource-test)
(define generated-tail-name '%for-tail-resource-test)

(define (generated-resource-loop branch-body)
  `(Loop ,generated-loop-name ((%for-rest-resource-test #:infer)) Unit #:infer
     (Eliminate (Move %for-rest-resource-test)
       ((nil () -> unit)
        (cons (,generated-head-name ,generated-tail-name) ->
          (Let (%stmt const Unit)
            ,branch-body
            (Apply ,generated-loop-name (Move ,generated-tail-name))))))
     ((Move items))))

(define (find-let-binding core name)
  (let walk ([term (erase-core core)])
    (match term
      [`(Let (,binder ,_mode ,_type) ,bound ,body)
       (or (and (symbol? binder)
                (string-prefix? (symbol->string binder)
                                (symbol->string name))
                term)
           (walk bound)
           (walk body))]
      [(? pair? parts) (for/or ([part (in-list parts)]) (walk part))]
      [_ #f])))

(test-case "U1 生成形の for の cons 枝は本体だけを内側の Scope で包む"
  (define loop
    (generated-resource-loop
     '(Let (body-result const Unit) unit unit)))
  (define-values (_configs _type _callables core)
    (run-program (resource-loop-program loop)))
  (define statement (find-let-binding core '%stmt))
  (check-not-false statement)
  (when statement
    (match statement
      [`(Let (,stmt const Unit)
             (Scope () (Let (,element let (Owned Res))
                            (Move ,head) ,_body))
             (Apply ,callee (Move ,tail)))
       (check-true (string-prefix? (symbol->string stmt) "%stmt"))
       (check-true (string-prefix? (symbol->string head)
                                  (symbol->string generated-head-name)))
       (check-true (string-prefix? (symbol->string tail)
                                  (symbol->string generated-tail-name)))
       (check-true (string-prefix? (symbol->string callee)
                                  (symbol->string generated-loop-name)))
       (check-not-equal? element head)]
      [_ (fail (format "生成 for の cons 枝が想定形でない: ~s" statement))])))

(test-case "U2 生成した for の Core は資源 branch encoding を通る"
  (define loop
    (generated-resource-loop
     '(Let (body-result const Unit) unit unit)))
  (define-values (_configs expected callables core)
    (run-program (resource-loop-program loop)))
  (check-not-false (core-type-of (erase-core core) '() callables))
  (check-equal? expected 'Unit))

(test-case "U3 生成形の for の正常完了で要素の fin は反復順に出る"
  (define loop (generated-resource-loop 'unit))
  (define-values (configs _type _callables _core)
    (run-program (resource-loop-program loop)))
  (define terminal (last configs))
  (check-equal? (length (config-tokens terminal)) 4)
  (check-all-dropped terminal 4)
  (check-dropped-once configs (map first (config-tokens terminal)))
  (check-equal? (map second (finish-events terminal))
                '(4 8)))

(test-case "U4 %for-loop 接頭辞でも本体が生成形でなければ内側の Scope を作らない"
  (define loop
    `(Loop ,generated-loop-name ((%for-rest-resource-test #:infer)) Unit #:infer
       (Eliminate (Move %for-rest-resource-test)
         ((nil () -> unit)
          (cons (,generated-head-name ,generated-tail-name) -> unit)))
       ((Move items))))
  (define-values (_configs _type _callables core)
    (run-program (resource-loop-program loop)))
  (check-false (find-let-binding core '%stmt)))

(test-case "U4b %stmt の Let でも継続が loop の再帰でなければ内側の Scope を作らない"
  (define loop
    `(Loop ,generated-loop-name ((%for-rest-resource-test #:infer)) Unit #:infer
       (Eliminate (Move %for-rest-resource-test)
         ((nil () -> unit)
          (cons (,generated-head-name ,generated-tail-name) ->
            (Let (%stmt const Unit) unit unit))))
       ((Move items))))
  (define-values (_configs _type _callables core)
    (run-program (resource-loop-program loop)))
  (define statement (find-let-binding core '%stmt))
  (check-not-false statement)
  (when statement
    (match statement
      [`(Let (,stmt const Unit) ,body ,_continuation)
       (check-true (string-prefix? (symbol->string stmt) "%stmt"))
       (check-false (match body [`(Scope . ,_) #t] [_ #f]))]
      [_ (fail (format "非生成形の %stmt が想定外: ~s" statement))])))

(test-case "U5 接頭辞の無い手書き Loop は fin の逆順と Core が変わらない"
  (define loop (resource-loop '(Apply walk (Move tail))))
  (define-values (configs _type _callables _core)
    (run-program (resource-loop-program loop)))
  (define terminal (last configs))
  (check-equal? (length (config-tokens terminal)) 2)
  (check-all-dropped terminal 2)
  (check-equal? (map second (finish-events terminal))
                '(5 2)))

(test-case "U6 生成形の本体が要素を Move すると置換後の Core は elem を Move する"
  (define loop
    (generated-resource-loop '(Drop (Move %for-head-resource-test))))
  (define-values (configs _type _callables core)
    (run-program (resource-loop-program loop)))
  (define statement (find-let-binding core '%stmt))
  (check-not-false statement)
  (when statement
    (match statement
      [`(Let (,stmt const Unit)
             (Scope () (Let (,element let (Owned Res))
                            (Move ,head) (Drop (Move ,used))))
             (Apply ,_callee (Move ,tail)))
       (check-true (string-prefix? (symbol->string stmt) "%stmt"))
       (check-true (string-prefix? (symbol->string head)
                                  (symbol->string generated-head-name)))
       (check-true (string-prefix? (symbol->string tail)
                                  (symbol->string generated-tail-name)))
       (check-not-equal? element head)
       (check-equal? used element)]
      [_ (fail (format "elem の Move が想定形でない: ~s" statement))]))
  (define terminal (last configs))
  (check-equal? (length (config-tokens terminal)) 6)
  (check-terminal-ledger configs))

(test-case "U7 List<Owned<Res>> 要素も反復ごとの内側 Scope で後始末する"
  (define nested-items
    `(Construct cons (Types (List (Owned Res)))
       ,(owned-list-value '(1))
       (Construct cons (Types (List (Owned Res)))
         ,(owned-list-value '(2))
         (Construct nil (Types (List (Owned Res)))))))
  (define loop (generated-resource-loop 'unit))
  (define program
    `(Apply
      (Fn ((items (List (List (Owned Res))))) Unit (Partial Own) ,loop)
      ,nested-items))
  (define-values (configs _type _callables _core) (run-program program))
  (define terminal (last configs))
  (check-equal? (length (config-tokens terminal)) 2)
  (check-terminal-ledger configs)
  (define unfold-indices
    (for/list ([configuration (in-list configs)] [index (in-naturals)]
               #:when (member 'R-RecurUnfold (trace-rules (list configuration))))
      index))
  (check-true (>= (length unfold-indices) 2))
  (when (>= (length unfold-indices) 2)
    (define first-token (first (map first (config-tokens terminal))))
    (check-equal? (token-state (list-ref configs (second unfold-indices)) first-token)
                  'Dropped)))

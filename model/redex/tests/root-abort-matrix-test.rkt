#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../lang.rkt"
         "../borrow.rkt"
         "../machine.rkt"
         "../gen.rkt"
         "../typing.rkt")

(define owned '(Owned Res))
(define option-owned `(Option ,owned))
(define list-option-owned `(List ,option-owned))
(define acquire '(PrimVal (Reserved o-acquire) acquire))

(define (root-owned number)
  `(Apply ,acquire ,number))

(define (leaf-owned number)
  `(OwnLeaf (Apply ,acquire ,number)))

(define (owned-option number)
  `(Construct ,option-owned some ,(leaf-owned number)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (configuration-core configuration)
  (match configuration [`(cfg ,core ,_ ,_ ,_ ,_) core]))
(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))
(define (configuration-events configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,_ ,events) events]))

(define (with-token-state configuration token state)
  (match configuration
    [`(cfg ,core ,heap ,places ,tokens ,events)
     `(cfg ,core ,heap ,places
           ,(for/list ([entry (in-list tokens)])
              (if (equal? (first entry) token)
                  (list token state)
                  entry))
           ,events)]))

(define (available-token-ids configuration)
  (for/list ([entry (in-list (configuration-tokens configuration))]
             #:when (eq? (second entry) 'Available))
    (first entry)))

(define (terminal-carried-token-ids core)
  (match core
    [`(Perform ,_ ,argument) (collect-tokens argument)]
    [`(Error ,_) '()]
    [_ (collect-tokens core)]))

(define (check-configs configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row
                     (format "config ~a の runtime row: ~s" index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "不正な中間 config ~a: ~s" index configuration))))

(define (check-frame-rule-does-not-add-events configs rules name)
  (for ([rule (in-list rules)]
        [before (in-list configs)]
        [after (in-list (cdr configs))]
        #:when (eq? rule name))
    (check-equal? (configuration-events after)
                  (configuration-events before)
                  (format "~a 自体は θ を変えない" name))))

(define (trace-has-rule? rules name)
  (and (member name rules) #t))

(define (contains-rsd? core)
  (match core
    [`(Discharge (ProofRep ,_ (RemainderSafelyDropped ,_ ,_)) ,_) #t]
    [(? list?) (ormap contains-rsd? core)]
    [_ #f]))

(define interruption-kinds
  '(scope-abort scope-error handle-return handle-skip handle-error))
(define owner-shapes
  '(root-only root-and-leaf construct-field curry-fixed discharge-mid
              recrewrite-open-mid))

(define (perform-kind? kind)
  (and (memq kind '(scope-abort handle-return handle-skip)) #t))

(define (interruption-boundary kind)
  (case kind
    [(handle-skip) 'escaped-boundary]
    [else 'interrupted-boundary]))

(define (interruption-term kind result-type)
  (if (perform-kind? kind)
      `(Perform (Return ,(interruption-boundary kind) ,result-type)
                ,(if (equal? result-type list-option-owned)
                     `(Construct ,list-option-owned nil)
                     'unit))
      '(Error 0)))

(define (interrupted-consumer parameter-types)
  (define raw-names
    (for/list ([index (in-range (length parameter-types))])
      (string->symbol (format "raw~a" index))))
  (define signature `(NFn ,parameter-types Unit () () () User))
  (define body
    (for/fold ([next 'unit])
              ([index (in-range (sub1 (length parameter-types)) -1 -1)])
      `(Let (,(string->symbol (format "received~a" index)) let
             ,(list-ref parameter-types index))
         ,(list-ref raw-names index)
         ,next)))
  (values `(Lam User interrupted-consumer ,raw-names
            (Handle (Return function-boundary Unit)
                    (return-value -> return-value)
                    (Scope () ,body)))
          signature
          `((interrupted-consumer ,signature))))

(define (wrap-interruption kind body result-type)
  (case kind
    [(scope-abort)
     `(Handle (Return interrupted-boundary ,result-type)
              (answer -> answer)
        (Scope () ,body))]
    [(scope-error) `(Scope () ,body)]
    [(handle-return)
     `(Handle (Return interrupted-boundary ,result-type)
              (answer -> answer) ,body)]
    [(handle-skip)
     `(Handle (Return handled-boundary ,result-type)
              (answer -> answer) ,body)]
    [(handle-error)
     `(Scope ()
        (Handle (Return handle-error-boundary ,result-type)
                (answer -> answer) ,body))]))

(define rsd-wide
  `(Record ((kept Int imm) (owned ,option-owned imm))))
(define rsd-narrow '(Record ((kept Int imm))))
(define rsd-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,rsd-wide ,rsd-narrow)))

(define rsd-worker
  `(Lam User rsd-worker (raw-owned raw-unit)
     (Handle (Return rsd-worker-boundary ,rsd-wide)
             (return-record -> return-record)
       (Scope ()
         (Let (stored let ,option-owned) raw-owned
           (Let (record let ,rsd-wide)
             (Rec ((kept imm 7)
                   (owned imm (Move stored))))
             (Move record)))))))
(define rsd-worker-type
  `(NFn (,option-owned Unit) ,rsd-wide () (Own) () User))

(struct interrupted-case
  (shape kind core callables places heap states result-type token-count)
  #:transparent)

(define (make-interrupted-case kind shape index)
  (define number (+ 100 (* index 10)))
  (define interrupt-unit (interruption-term kind 'Unit))
  (define-values (body callables result-type token-count)
    (case shape
      [(root-only)
       (define-values (consumer _signature consumer-callables)
         (interrupted-consumer (list owned 'Unit)))
       (values `(Apply ,consumer ,(root-owned number) ,interrupt-unit)
               consumer-callables 'Unit 1)]
      [(root-and-leaf)
       (define-values (consumer _signature consumer-callables)
         (interrupted-consumer (list owned option-owned 'Unit)))
       (values `(Apply ,consumer ,(root-owned number)
                       ,(owned-option (add1 number)) ,interrupt-unit)
               consumer-callables 'Unit 2)]
      [(construct-field)
       (define interrupt-list (interruption-term kind list-option-owned))
       (values `(Construct ,list-option-owned cons ,(owned-option number)
                           ,interrupt-list)
               '() list-option-owned 1)]
      [(curry-fixed)
       (define inner-type `(NFn (,owned Unit) Unit () () () User))
       (define residual-type `(NFn (Unit) Unit () () () User))
       (define closure-type `(Owned ,residual-type))
       (define function
         `(Lam User curried-target (fixed later)
            (Handle (Return curry-boundary Unit)
                    (answer -> answer)
              (Scope () (Let (stored let ,owned) fixed unit)))))
       (define-values (consumer _signature consumer-callables)
         (interrupted-consumer (list closure-type 'Unit)))
       (values `(Apply ,consumer
                       (Curry ,function ,(leaf-owned number))
                       ,interrupt-unit)
               (append `((curried-target ,inner-type)) consumer-callables)
               'Unit 1)]
      [(discharge-mid)
       (define-values (consumer _signature consumer-callables)
         (interrupted-consumer (list option-owned rsd-narrow)))
       (define inner
         `(Apply ,rsd-worker ,(owned-option (add1 number)) ,interrupt-unit))
       (values `(Apply ,consumer
                       ,(owned-option number)
                       (Discharge ,rsd-proof ,inner))
               (append `((rsd-worker ,rsd-worker-type)) consumer-callables)
               'Unit 2)]
      [(recrewrite-open-mid)
       (define record-type
         `(Record ((a ,owned imm) (b Int imm))))
       (define rewrite
         `(RecRewrite
           (Rec ((a imm 1) (b imm 2)))
           ((a x Int imm ,owned (Apply ,acquire x))
            (b y Int imm Int ,(interruption-term kind 'Unit)))))
       (define-values (consumer _signature consumer-callables)
         (interrupted-consumer (list record-type)))
       (values `(Apply ,consumer ,rewrite)
               consumer-callables 'Unit 1)]))
  (define core (wrap-interruption kind body result-type))
  (define error-kind? (memq kind '(scope-error handle-error)))
  (interrupted-case shape kind core callables
                    (if error-kind? '((0 Res)) '())
                    (if error-kind? '((0 (resource 97))) '())
                    (if error-kind? '((0 Available)) '())
                    result-type token-count))

(define (make-moved-root-case kind)
  (define error-kind? (memq kind '(scope-error handle-error)))
  (define moved-place (if error-kind? 1 0))
  (define-values (consumer _signature consumer-callables)
    (interrupted-consumer (list owned 'Unit)))
  (define body
    `(Apply ,consumer (Move ,moved-place) ,(interruption-term kind 'Unit)))
  (interrupted-case
   'root-only kind (wrap-interruption kind body 'Unit)
   consumer-callables
   (if error-kind? '((0 Res) (1 Res)) '((0 Res)))
   (if error-kind?
       '((0 (resource 97)) (1 (resource 81) (declared (Owned Res))))
       '((0 (resource 81) (declared (Owned Res)))))
   (if error-kind?
       '((0 Available) (1 Available))
       '((0 Available)))
   'Unit 1))

(define (start-configuration test-case)
  `(cfg ,(interrupted-case-core test-case)
        ,(interrupted-case-heap test-case)
        ,(interrupted-case-states test-case)
        () ()))

(define (rule-for-interruption-kind kind)
  (case kind
    [(scope-abort) 'R-ScopeAbort]
    [(scope-error) 'R-ScopeError]
    [(handle-return) 'R-HandleReturn]
    [(handle-skip) 'R-HandleSkip]
    [(handle-error) 'R-HandleError]))

(define (token-state-in configuration token)
  (define entry (assoc token (configuration-tokens configuration)))
  (and entry (second entry)))

(define (check-token-drop-once configs)
  (define all-tokens
    (remove-duplicates
     (append-map (lambda (config) (map first (configuration-tokens config)))
                 configs)
     equal?))
  (for ([token (in-list all-tokens)])
    (define drops
      (for/sum ([before (in-list configs)] [after (in-list (cdr configs))])
        (if (and (eq? (token-state-in before token) 'Available)
                 (eq? (token-state-in after token) 'Dropped))
            1 0)))
    (check-true (<= drops 1)
                (format "~s は Available から Dropped へ高々一度遷移する"
                        token))))

(define (check-interrupted-case test-case [additional-rules '()])
  (define core (interrupted-case-core test-case))
  (define callables (interrupted-case-callables test-case))
  (define places (interrupted-case-places test-case))
  (define expected-type (interrupted-case-result-type test-case))
  (define expected-rule
    (rule-for-interruption-kind (interrupted-case-kind test-case)))
  (check-equal? (first (core-type-of core places callables)) expected-type
                (format "~a / ~a は型付けできる"
                        (interrupted-case-kind test-case)
                        (interrupted-case-shape test-case)))
  (define-values (configs rules)
    (trace-g2 (start-configuration test-case)))
  (check-configs configs callables expected-type)
  (check-true (trace-has-rule? rules expected-rule)
              (format "~a が発火する" expected-rule))
  (for ([rule (in-list additional-rules)])
    (check-true (trace-has-rule? rules rule) (format "~a が発火する" rule)))
  (for ([rule (in-list '(R-ScopeAbort R-ScopeError R-HandleReturn
                         R-HandleSkip R-HandleError))])
    (check-frame-rule-does-not-add-events configs rules rule))
  (define terminal (configuration-core (last configs)))
  (check-true (or (redex-match? G2m v terminal)
                  (match terminal
                    [`(Perform ,_ ,_) #t]
                    [`(Error ,_) #t]
                    [_ #f]))
              (format "終端は値、裸の Perform、または Error: ~s" terminal))
  (check-equal?
   (sort (available-token-ids (last configs)) < #:key second)
   (sort (terminal-carried-token-ids terminal) < #:key second)
   "終端の Available token は終端値か Perform 引数だけにある")
  (check-equal? (length (configuration-tokens (last configs)))
                (interrupted-case-token-count test-case))
  (check-true
   (andmap (lambda (entry) (eq? (second entry) 'Dropped))
           (configuration-tokens (last configs)))
   "外へ渡す値が無いので全 token が Dropped")
  (check-token-drop-once configs)
  (when (eq? (interrupted-case-shape test-case) 'discharge-mid)
    (check-false (member 'R-DischargeRemainder rules)
                 "中断で Discharge の本体が値にならず RSD は発火しない")
    (define rule-index (index-of rules expected-rule))
    (check-true (contains-rsd? (configuration-core (list-ref configs rule-index)))
                "中断直前の F_inner に RSD が残る"))
  (when (eq? (interrupted-case-shape test-case) 'recrewrite-open-mid)
    (define open-index (index-of rules 'R-RecRewrite-Open))
    (check-not-false open-index "RecRewriteOpen の遷移がある")
    (define open-configuration (list-ref configs (add1 open-index)))
    (define open-row (runtime-row open-configuration callables expected-type))
    (check-not-false open-row "Open 直後の config は runtime-row を持つ")
    (check-true (config-ok? open-configuration callables expected-type open-row)
                "Open 直後の config は型付きである")
    (define rule-index (index-of rules expected-rule))
    (check-true
     (match (configuration-core (list-ref configs rule-index))
       [`(Scope () (Apply ,_ (RecRewriteOpen
                              ((a imm ,_a-output
                                  (OwnedLeaf ,_ (resource ,_)))
                               (b imm ,_b-output ,_)))))
        #t]
       [`(Scope () (Handle ,_ ,_ (Apply ,_ (RecRewriteOpen
                                            ((a imm ,_a-output
                                                (OwnedLeaf ,_ (resource ,_)))
                                             (b imm ,_b-output ,_))))))
        #t]
       [_ #f])
     "中断直前の Open は処理済み欄に根 token を持つ")))

(define expected-typed-counts
  '((scope-abort 5 1)
    (scope-error 6 0)
    (handle-return 5 1)
    (handle-skip 5 1)
    (handle-error 6 0)))

(test-case "中断 5 種 × 根の所有値 6 種の有限宇宙を検査する"
  (check-equal? (* (length interruption-kinds) (length owner-shapes)) 30)
  (define typed-counts
    (for/list ([kind (in-list interruption-kinds)])
      (define accepted 0)
      (define excluded 0)
      (for ([shape (in-list owner-shapes)] [index (in-naturals)])
        (define test-case (make-interrupted-case kind shape index))
        (define result
          (core-type-of (interrupted-case-core test-case)
                        (interrupted-case-places test-case)
                        (interrupted-case-callables test-case)))
        ;; RecRewrite entry は空 row が必須なので、その途中で Perform する
        ;; 3 組だけは型付けできない。Error の組は row が空なので受理する。
        (define known-exclusion?
          (and (eq? shape 'recrewrite-open-mid)
               (perform-kind? kind)))
        (check-equal? (eq? result 'ill-typed) known-exclusion?
                      (format "想定外の型付け結果: ~a / ~a: ~s"
                              kind shape result))
        (if known-exclusion?
            (set! excluded (add1 excluded))
            (begin
              (set! accepted (add1 accepted))
              (check-interrupted-case test-case))))
      (list kind accepted excluded)))
  (check-equal? typed-counts expected-typed-counts))

(test-case "Move で place から得た根 token は中断 5 種すべてで回収する"
  (define accepted 0)
  (define excluded 0)
  (for ([kind (in-list interruption-kinds)])
    (define test-case (make-moved-root-case kind))
    (define result
      (core-type-of (interrupted-case-core test-case)
                    (interrupted-case-places test-case)
                    (interrupted-case-callables test-case)))
    (if (eq? result 'ill-typed)
        (set! excluded (add1 excluded))
        (begin
          (set! accepted (add1 accepted))
          (check-interrupted-case test-case '(R-Move)))))
  (check-equal? (list accepted excluded) '(5 0)
                "5 種とも place 由来の root-only を型付けして検査する"))

(test-case "RecRewrite Open は根 token を欄に一度だけ残す"
  (define record-type
    `(Record ((a ,owned imm) (b Int imm))))
  (define core
    `(RecRewrite
      (Rec ((a imm 1) (b imm 2)))
      ((a x Int imm ,owned (Apply ,acquire x))
       (b y Int imm Int y))))
  (check-equal? (first (core-type-of core '() '())) record-type)
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-configs configs '() record-type)
  (check-true (trace-has-rule? rules 'R-RecRewrite-Open))
  (check-true (trace-has-rule? rules 'R-RecRewrite-Close))
  (define open-index (index-of rules 'R-RecRewrite-Open))
  (define close-index (index-of rules 'R-RecRewrite-Close))
  (define open-config
    (for/first ([configuration (in-list (drop configs (add1 open-index)))]
                [index (in-naturals (add1 open-index))]
                #:when (and (<= index close-index)
                            (pair? (collect-tokens
                                    (configuration-core configuration)))))
      configuration))
  (check-not-false open-config "Open 中に根 token が発行される")
  (define open-row (runtime-row open-config '() record-type))
  (check-not-false open-row "Open 直後の config は runtime-row を持つ")
  (check-true (config-ok? open-config '() record-type open-row)
              "Open 直後の config は型付きである")
  (define open-ids (collect-tokens (configuration-core open-config)))
  (check-equal? (length open-ids) 1)
  (check-equal? (length (remove-duplicates open-ids equal?)) 1)
  (check-equal? (map first (configuration-tokens open-config)) open-ids)
  (check-equal? (map second (configuration-tokens open-config)) '(Available))
  (check-equal? (collect-tokens (configuration-core (last configs))) open-ids)
  (check-equal? (configuration-tokens (last configs))
                (configuration-tokens open-config)))

(test-case "F_inner の回収を外した偽造 config は拒否する"
  (define root-case (make-interrupted-case 'scope-abort 'root-only 0))
  (define-values (root-configs root-rules)
    (trace-g2 (start-configuration root-case)))
  (define root-before
    (list-ref root-configs (index-of root-rules 'R-ScopeAbort)))
  (define forged-root
    (match root-before
      [`(cfg (Handle (Return interrupted-boundary Unit) ,handler
                     (Scope () (Apply ,_consumer
                                      (OwnedLeaf ,_token (resource ,_))
                                      (Perform ,_op ,_payload))))
            ,heap ,states ,tokens ,events)
       `(cfg (Handle (Return interrupted-boundary Unit) ,handler
                     (Scope () (Perform (Return interrupted-boundary Unit) unit)))
             ,heap ,states ,tokens ,events)]
      [other (fail-check (format "root-only の中断直前の形が変わった: ~s"
                                 other))]))
  (define root-row (runtime-row forged-root
                                (interrupted-case-callables root-case) 'Unit))
  (check-not-false root-row)
  (check-false (config-ok? forged-root
                           (interrupted-case-callables root-case)
                           'Unit root-row))
  (define root-token (first (first (configuration-tokens forged-root))))
  (define root-dropped-control
    (with-token-state forged-root root-token 'Dropped))
  (define root-control-row
    (runtime-row root-dropped-control
                 (interrupted-case-callables root-case) 'Unit))
  (check-not-false root-control-row)
  (check-true (config-ok? root-dropped-control
                          (interrupted-case-callables root-case)
                          'Unit root-control-row)
              "根 token を Dropped にするだけなら forged config は有効")

  (define rewrite-case
    (make-interrupted-case 'scope-error 'recrewrite-open-mid 5))
  (define-values (rewrite-configs rewrite-rules)
    (trace-g2 (start-configuration rewrite-case)))
  (define rewrite-before
    (list-ref rewrite-configs (index-of rewrite-rules 'R-ScopeError)))
  (define forged-rewrite
    (match rewrite-before
      [`(cfg (Scope () (Apply ,_consumer
                              (RecRewriteOpen
                               ((a imm ,_a-output
                                   (OwnedLeaf ,_token (resource ,_)))
                                (b imm ,_b-output (Error 0))))))
            ,heap ,states ,tokens ,events)
       `(cfg (Scope () (Error 0)) ,heap ,states ,tokens ,events)]
      [other (fail-check
              (format "recrewrite-open-mid の中断直前の形が変わった: ~s"
                      other))]))
  (define rewrite-row
    (runtime-row forged-rewrite
                 (interrupted-case-callables rewrite-case) 'Unit))
  (check-not-false rewrite-row)
  (check-false (config-ok? forged-rewrite
                           (interrupted-case-callables rewrite-case)
                           'Unit rewrite-row))
  (define rewrite-token (first (first (configuration-tokens forged-rewrite))))
  (define rewrite-dropped-control
    (with-token-state forged-rewrite rewrite-token 'Dropped))
  (define rewrite-control-row
    (runtime-row rewrite-dropped-control
                 (interrupted-case-callables rewrite-case) 'Unit))
  (check-not-false rewrite-control-row)
  (check-true (config-ok? rewrite-dropped-control
                          (interrupted-case-callables rewrite-case)
                          'Unit rewrite-control-row)
              "根 token を Dropped にするだけなら forged config は有効"))

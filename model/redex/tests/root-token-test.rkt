#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../gen.rkt"
         "../elaborate.rkt"
         "../typing.rkt")

(define acquire '(PrimVal (Reserved o-acquire) acquire))
(define function-type '(NFn () (Owned Res) () () () User))
(define function-callables `((f ,function-type)))

(define (step configuration)
  (match (raw-steps-g2/named configuration)
    [(list (list rule next)) (values rule next)]
    [steps (error 'step "一手だけ進む構成を期待した: ~s" steps)]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (check-config-trace configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row
                     (format "config ~a の runtime row が無い: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "config ~a が不正: ~s" index configuration))))

(define (tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,token-states ,_) token-states]))

(define (states configuration)
  (match configuration [`(cfg ,_ ,_ ,place-states ,_ ,_) place-states]))

(define (control configuration)
  (match configuration [`(cfg ,core ,_ ...) core]))

(define (events configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,_ ,trace) trace]))

(test-case "R-Move は資源の根に一つの token を付ける"
  (define start
    '(cfg (Scope (0) (Drop (Move 0)))
          ((0 (resource 3) (declared (Owned Res))))
          ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-not-false (member 'R-Move rules))
  (check-config-trace configs '() 'Unit)
  (check-equal? (tokens (last configs)) '(((tok 0) Dropped))))

(test-case "R-Forward は資源の根に一つの token を付ける"
  (define-values (rule after)
    (step '(cfg (Forward 0)
                ((0 (resource 3) (declared (Owned Res))))
                ((0 Available)) () ())))
  (check-equal? rule 'R-Forward)
  (check-equal? (control after) '(OwnedLeaf (tok 0) (resource 3)))
  (check-equal? (states after) '((0 Moved)))
  (check-equal? (tokens after) '(((tok 0) Available))))

(test-case "R-Forward の根 token は Scope の終端で回収する"
  (define sink-type '(NFn ((Owned Res)) Unit () () () User))
  (define owner-type `(NFn (,sink-type (Owned Res)) Unit () () () User))
  (define sink
    '(Lam User sink (raw)
       (Handle (Return sink-boundary Unit)
               (return-value -> return-value)
               (Scope () (Let (received let (Owned Res)) raw unit)))))
  (define owner
    '(Lam User owner (h p)
       (Handle (Return owner-boundary Unit)
               (answer -> answer)
               (Scope ()
                 (Let (x let (Owned Res)) p (Apply h (Forward x)))))))
  (define callables `((owner ,owner-type) (sink ,sink-type)))
  (define core `(Scope (0) (Apply ,owner ,sink (Move 0))))
  (check-equal? (core-type-of core '((0 Res)) callables) '(Unit (Own)))
  (define start
    `(cfg ,core ((0 (resource 3) (declared (Owned Res))))
          ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-not-false (member 'R-Forward rules))
  (check-not-false (member 'R-LetOwnedB rules))
  (check-not-false (member 'R-ScopeValue rules))
  (check-equal? (count (lambda (rule) (eq? rule 'R-Forward)) rules) 1)
  (check-config-trace configs callables 'Unit)
  (check-equal? (map second (tokens (last configs))) '(Dropped Dropped)))

(test-case "根の OwnedLeaf を control の値で許し Perform の内側制約を保つ"
  (define-values (scope-configs scope-rules)
    (trace-g2 '(cfg (Scope () (Apply (PrimVal (Reserved o-acquire) acquire) 7))
                   () () () ())))
  (check-not-false (member 'R-ScopeValue scope-rules))
  (check-config-trace scope-configs '() '(Owned Res))
  (match (control (last scope-configs))
    [`(OwnedLeaf ,_token (resource 7)) (void)]
    [other (fail-check (format "ScopeValue が根 OwnedLeaf を返さない: ~s" other))])
  (define terminal
    '(cfg (OwnedLeaf (tok 7) (resource 7)) () () (((tok 7) Available)) ()))
  (define terminal-row (runtime-row terminal '() '(Owned Res)))
  (check-equal? terminal-row '())
  (check-true (config-ok? terminal '() '(Owned Res) terminal-row))
  (define heap-root
    '(cfg unit ((0 (OwnedLeaf (tok 8) (resource 8))
                (declared (Owned Res))))
          ((0 Available)) (((tok 8) Available)) ()))
  (check-false (config-ok? heap-root '() 'Unit '()))
  (define nested-control
    '(cfg (Scope () (OwnedLeaf (tok 9)
                               (OwnedLeaf (tok 10) (resource 9))))
          () () (((tok 9) Available) ((tok 10) Available)) ()))
  (check-false (config-ok? nested-control '() '(Owned Res) '()))
  (define nested-perform
    '(cfg (Perform (Return escaped-boundary (Owned Res))
                   (OwnedLeaf (tok 11)
                              (OwnedLeaf (tok 12) (resource 10))))
          () () (((tok 11) Available) ((tok 12) Available)) ()))
  (check-false (control-leaf-positions-ok? (control nested-perform) #t))
  (check-false
   (config-ok? nested-perform '() 'Never
               '((Return escaped-boundary (Owned Res))))))

(test-case "終端へ処理されずに届く Perform は根 token を運ぶ"
  (define token '(tok 13))
  (define start
    `(cfg (Perform (Return external-boundary (Owned Res))
                  (OwnedLeaf ,token (resource 13)))
          () () ((,token Available)) ()))
  (define row (runtime-row start '() 'Never))
  (check-equal? row '((Return external-boundary (Owned Res)))
                "runtime-row の形")
  (check-true (config-ok? start '() 'Never row))
  (define-values (configs rules) (trace-g2 start))
  (check-equal? rules '())
  (check-equal? (tokens (last configs)) `((,token Available))))

(test-case "R-Move は非資源の値を token で包まない"
  (define-values (_rule after)
    (step '(cfg (Move 0) ((0 7 (declared Int))) ((0 Available)) () ())))
  (check-equal? (control after) 7)
  (check-equal? (tokens after) '()))

(test-case "R-Delta は acquire だけの根に token を付ける"
  (define-values (_rule acquired)
    (step `(cfg (Apply ,acquire 7) () () () ())))
  (match acquired
    [`(cfg (OwnedLeaf ,_ (resource 7)) () () ((,_ Available)) ()) (void)]
    [_ (fail-check (format "acquire の根に token が無い: ~s" acquired))])
  (define-values (_add-rule added)
    (step '(cfg (Apply (PrimVal (Reserved o-add) add) 1 2) () () () ())))
  (check-equal? (control added) 3)
  (check-equal? (tokens added) '()))

(test-case "R-OwnLeafPass は既存 token を保ち二重発行しない"
  (define start
    '(cfg (OwnLeaf (OwnedLeaf (tok 4) (resource 1)))
          () () (((tok 4) Available)) ()))
  (define-values (rule after) (step start))
  (check-equal? rule 'R-OwnLeafPass)
  (check-equal? (control after) '(OwnedLeaf (tok 4) (resource 1)))
  (check-equal? (tokens after) '(((tok 4) Available)))
  (check-false (member 'R-OwnLeaf
                       (map first (raw-steps-g2/named start)))))

(test-case "R-OwnLeafPass の直前も configuration typing が受理する"
  ;; R-Move が producer に OwnedLeaf を渡し、R-OwnLeafPass が包みを剥がす間も構成を型付けする。
  (define configuration
    '(cfg (Scope () (OwnLeaf (OwnedLeaf (tok 4) (resource 1))))
          () () (((tok 4) Available)) ()))
  (define row (runtime-row configuration '() '(Owned Res)))
  (check-equal? row '())
  (check-true (config-ok? configuration '() '(Owned Res) row))
  (check-equal? (core-type-of '(Scope () (OwnLeaf (OwnedLeaf (tok 4) (resource 1))))
                              '() '())
                'ill-typed))

(test-case "OwnLeaf と Move の後は token を一度だけ通す"
  (define start
    '(cfg (OwnLeaf (Move 0))
          ((0 (resource 1) (declared (Owned Res))))
          ((0 Available)) () ()))
  (define-values (after-move-rule after-move) (step start))
  (check-equal? after-move-rule 'R-Move)
  (define-values (after-pass-rule after-pass) (step after-move))
  (check-equal? after-pass-rule 'R-OwnLeafPass)
  (check-equal? (tokens after-pass) '(((tok 0) Available))))

(test-case "inject 系は裸の資源を producer へ書き換える"
  (check-equal? (inject-g2m '(Drop (resource 0)))
                '(cfg (Scope () (Drop (OwnLeaf (resource 0)))) () () () ()))
  (check-equal? (inject-g2m '(OwnLeaf (resource 0)))
                '(cfg (Scope () (OwnLeaf (resource 0))) () () () ()))
  (check-equal? (inject-g2m '(OwnedLeaf (tok 1) (resource 0)))
                '(cfg (Scope () (OwnedLeaf (tok 1) (resource 0))) () () () ()))
  (check-equal? (inject-g2m '(Lam User f () (resource 5)))
                '(cfg (Scope () (Lam User f () (OwnLeaf (resource 5))))
                     () () () ())))

(test-case "configuration の OwnLeaf 契約は static Core へ広がらない"
  (define configuration (inject-g2m '(Drop (resource 0))))
  (check-true (config-ok? configuration '() 'Unit '(Own)))
  (check-equal? (core-type-of '(Scope () (Drop (OwnLeaf (resource 0))))
                              '() '())
                'ill-typed))

(test-case "config-ok? は許可位置以外の裸の資源を拒否する"
  (check-false
   (config-ok? '(cfg (Scope () (resource 7)) () () () ()) '() '(Owned Res) '()))
  (define plan-acceptance
    '(cfg (Scope () (OwnLeaf (resource 7))) () () () ()))
  (define row (runtime-row plan-acceptance '() '(Owned Res)))
  (check-equal? row '())
  (check-true
   (config-ok? plan-acceptance '() '(Owned Res) row))
  (check-true
   (config-ok? '(cfg (Scope () (Drop (OwnLeaf (resource 7)))) () () () ())
               '() 'Unit '(Own))))

(test-case "H の gate は遅延コードの裸の producer を拒否する"
  (define unsafe
    `(cfg (Scope (0) (Drop (Apply (Move 0))))
          ((0 (Lam User f () (resource 5)) (declared ,function-type)))
          ((0 Available)) () ()))
  (define safe
    `(cfg (Scope (0) (Drop (Apply (Move 0))))
          ((0 (Lam User f () (OwnLeaf (resource 5)))
              (declared ,function-type)))
          ((0 Available)) () ()))
  (check-false (config-ok? unsafe function-callables 'Unit '()))
  (define-values (configs _rules) (trace-g2 safe))
  (check-config-trace configs function-callables 'Unit))

(test-case "H の根の資源は受理し入れ子の裸の資源は拒否する"
  (check-true
   (config-ok?
    '(cfg unit ((0 (resource 3) (declared (Owned Res))))
          ((0 Available)) () ())
    '() 'Unit '()))
  (check-false
   (config-ok?
    '(cfg unit
          ((0 (Rec ((a imm (resource 3))))
              (declared (Record ((a (Owned Res) imm))))))
          ((0 Available)) () ())
    '() 'Unit '())))

(test-case "R-ScopeAbort と R-HandleReturn は Move の根資源を回収する"
  (define consumer-type '(NFn ((Owned Res) Unit) Unit () () () User))
  (define consumer
    '(Lam User consumer (raw later)
       (Handle (Return consumer-boundary Unit)
               (return-value -> return-value)
               (Scope ()
                 (Let (received let (Owned Res)) raw unit)))))
  (define core
    `(Handle (Return abort-boundary Unit) (answer -> answer)
       (Scope (0)
         (Apply ,consumer (Move 0)
                (Perform (Return abort-boundary Unit) unit)))))
  (define callables `((consumer ,consumer-type)))
  (check-equal? (core-type-of core '((0 Res)) callables) '(Unit (Own)))
  (define start
    `(cfg ,core ((0 (resource 3) (declared (Owned Res))))
          ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-not-false (member 'R-ScopeAbort rules))
  (check-not-false (member 'R-HandleReturn rules))
  (check-config-trace configs callables 'Unit)
  (check-equal? (control (last configs)) 'unit)
  (check-equal? (tokens (last configs)) '(((tok 0) Dropped)))
  (define after-move
    (for/first ([rule (in-list rules)]
                [next (in-list (cdr configs))]
                #:when (eq? rule 'R-Move))
      next))
  (check-not-false after-move)
  (define forged
    (match after-move
      [`(cfg (Handle ,operation ,handler
                     (Scope (0)
                       (Apply ,_target (OwnedLeaf ,_token (resource 3)) ,later)))
             ,heap ,place-states ,token-states ,trace)
       `(cfg (Handle ,operation ,handler
                     (Scope (0) ,later))
             ,heap ,place-states ,token-states ,trace)]
      [other (fail-check (format "R-Move 後の形が変わった: ~s" other))]))
  (define forged-row (runtime-row forged callables 'Unit))
  (check-not-false forged-row)
  (check-false (config-ok? forged callables 'Unit forged-row)
               "F_inner だけを捨てて Available の根 token を孤立させない"))

(test-case "acquire を引数評価中に失う Surface trace は根を回収する"
  (define source
    '(Apply (Fn ((start Unit)) Unit (Own)
             (Apply (Fn ((owned (Owned Res)) (later Unit)) Unit () unit)
                    (Apply acquire 7)
                    (Return unit)))
            unit))
  (match (elab source)
    [(list core expected _declared-row callables)
     (check-equal? expected 'Unit)
     (define execution (execution-core core callables))
     (define-values (configs rules) (trace-g2 (inject-g2m execution)))
     (check-not-false (member 'R-Delta rules))
     (check-not-false (member 'R-ScopeAbort rules))
     (check-not-false (member 'R-HandleReturn rules))
     (check-not-false (member 'R-ScopeValue rules))
     (check-config-trace configs callables expected)
     (check-equal? (control (last configs)) 'unit)
     (check-true
      (andmap (lambda (entry) (eq? (second entry) 'Dropped))
              (tokens (last configs))))]
    [other (fail-check (format "Surface の反例が elaborate できない: ~s" other))]))

(test-case "R-MoveError の ScopeError と HandleError が root token を回収する"
  (define core
    `(Handle (Return move-error-boundary (Owned Res))
             (answer -> answer)
       (Scope ()
         (Let (x let (Owned Res)) (Apply ,acquire 3)
           (Let (y let (Owned Res)) (Move x) (Move x))))))
  (check-equal? (core-type-of core '() '()) '((Owned Res) (Own)))
  (define executable (execution-core core '()))
  (define-values (configs rules)
    (trace-g2 `(cfg ,executable () () () ())))
  (check-not-false (member 'R-Delta rules))
  (check-not-false (member 'R-LetOwnedB rules))
  (check-not-false (member 'R-MoveError rules))
  (check-not-false (member 'R-ScopeError rules))
  (check-not-false (member 'R-HandleError rules))
  (check-config-trace configs '() '(Owned Res))
  (match (last configs)
    [`(cfg (Error ,_) ,_heap ,_states ,token-states ,_trace)
     (check-true (pair? token-states))
     (check-true (andmap (lambda (entry) (eq? (second entry) 'Dropped))
                         token-states))]
    [other (fail-check (format "MoveError 後に終端 error でない: ~s" other))]))

(test-case "R-LetOwnedB は Move と acquire の根 token を place へ移す"
  (define move-start
    '(cfg (Scope (0)
                 (Let (x let (Owned Res)) (Move 0) (Drop (Move x))))
          ((0 (resource 3) (declared (Owned Res))))
          ((0 Available)) () ()))
  (define-values (move-configs move-rules) (trace-g2 move-start))
  (check-not-false (member 'R-LetOwnedB move-rules))
  (check-config-trace move-configs '() 'Unit)
  (define moved-place
    (for/first ([configuration (in-list move-configs)]
                #:when (and (match configuration
                              [`(cfg (Scope ,_ ,_) ,_ ,_ ,_ ,_) #t]
                              [_ #f])
                            (equal? (tokens configuration)
                                    '(((tok 0) Dropped)))
                            (member '(1 Available) (states configuration))))
      configuration))
  (check-not-false moved-place)
  (check-equal? (states moved-place) '((0 Moved) (1 Available)))
  (check-equal? (tokens moved-place) '(((tok 0) Dropped)))
  (define acquire-start
    `(cfg (Scope ()
                 (Let (x let (Owned Res)) (Apply ,acquire 7) (Drop (Move x))))
          () () () ()))
  (define-values (acquire-configs acquire-rules) (trace-g2 acquire-start))
  (check-not-false (member 'R-LetOwnedB acquire-rules))
  (check-config-trace acquire-configs '() 'Unit)
  (define acquired-place
    (for/first ([configuration (in-list acquire-configs)]
                #:when (and (match configuration
                              [`(cfg (Scope (,_) ,_) ,_ ,_ ,_ ,_) #t]
                              [_ #f])
                            (equal? (tokens configuration)
                                    '(((tok 0) Dropped)))
                            (member '(0 Available) (states configuration))))
      configuration))
  (check-not-false acquired-place)
  (check-equal? (states acquired-place) '((0 Available)))
  (check-equal? (tokens acquired-place) '(((tok 0) Dropped))))

(test-case "R-Drop は根と入れ子の OwnedLeaf token を全て消費する"
  (define start
    '(cfg (Drop (OwnedLeaf (tok 10)
                          (Rec ((nested imm
                                        (OwnedLeaf (tok 11) (resource 3)))))))
          () () (((tok 10) Available) ((tok 11) Available)) ()))
  (define-values (rule after) (step start))
  (check-equal? rule 'R-Drop)
  (check-equal? (control after) 'unit)
  (check-equal? (tokens after)
                '(((tok 10) Dropped) ((tok 11) Dropped))))

(test-case "R-Yield は根 token を観測し終端で回収する"
  (define start
    '(cfg (Yield (OwnedLeaf (tok 12) (resource 3)) unit)
          () () (((tok 12) Available)) ()))
  (define-values (configs rules) (trace-g2 start))
  (check-equal? (take rules 2) '(R-Yield R-RetireValue))
  (check-equal? (tokens (second configs)) '(((tok 12) Observed)))
  (check-equal? (events (second configs))
                '((obs (OwnedLeaf (tok 12) (resource 3)))))
  (check-equal? (tokens (last configs)) '(((tok 12) Dropped)))
  (check-config-trace configs '() 'Unit))

(define (root-token-frame-case kind token)
  (define root `(OwnedLeaf (tok ,token) (resource 3)))
  (case kind
    [(scope-abort)
     `(cfg (Scope ()
                  (Apply (PrimVal (Reserved o-add) add) ,root
                         (Perform (Return interrupted-boundary Unit) unit)))
           () () (((tok ,token) Available)) ())]
    [(scope-error)
     `(cfg (Scope ()
                  (Apply (PrimVal (Reserved o-add) add) ,root (Error 0)))
           () () (((tok ,token) Available)) ())]
    [(handle-return)
     `(cfg (Handle (Return interrupted-boundary Unit)
                   (payload -> unit)
                   (Apply (PrimVal (Reserved o-add) add) ,root
                          (Perform (Return interrupted-boundary Unit) unit)))
           () () (((tok ,token) Available)) ())]
    [(handle-skip)
     `(cfg (Handle (Return handler-boundary Unit)
                   (payload -> unit)
                   (Apply (PrimVal (Reserved o-add) add) ,root
                          (Perform (Return performed-boundary Unit) unit)))
           () () (((tok ,token) Available)) ())]
    [(handle-error)
     `(cfg (Handle (Return handler-boundary Unit)
                   (payload -> unit)
                   (Apply (PrimVal (Reserved o-add) add) ,root (Error 0)))
           () () (((tok ,token) Available)) ())]))

(test-case "5 つの frame cleanup は根 token を落とし finLeaf を出さない"
  (define cases
    '((scope-abort . R-ScopeAbort)
      (scope-error . R-ScopeError)
      (handle-return . R-HandleReturn)
      (handle-skip . R-HandleSkip)
      (handle-error . R-HandleError)))
  (for ([entry (in-list cases)] [token (in-naturals 20)])
    (define kind (car entry))
    (define expected-rule (cdr entry))
    (define start (root-token-frame-case kind token))
    (define-values (rule after) (step start))
    (check-equal? rule expected-rule)
    (check-equal? (tokens after) `(((tok ,token) Dropped)))
    (check-equal? (events after) '()
                  "frame cleanup は根 path が空の finLeaf を出さない")))

(test-case "R-HandleReturn は外へ渡す Perform payload の根 token を保つ"
  (define token '(tok 30))
  (define start
    `(cfg (Handle (Return output-boundary Unit)
                  (payload -> (Drop payload))
                  (Perform (Return output-boundary Unit)
                           (OwnedLeaf ,token (resource 3))))
          () () ((,token Available)) ()))
  (define-values (rule after-handle) (step start))
  (check-equal? rule 'R-HandleReturn)
  (check-equal? (control after-handle)
                `(Drop (OwnedLeaf ,token (resource 3))))
  (check-equal? (tokens after-handle) `((,token Available)))
  (define-values (drop-rule after-drop) (step after-handle))
  (check-equal? drop-rule 'R-Drop)
  (check-equal? (tokens after-drop) `((,token Dropped))))

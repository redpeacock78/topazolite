#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../gen.rkt"
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

#lang racket/base

;; P2m2c2b2o。中断で捨てる評価 frame の Owned leaf を回収する。
;; [REQ: OWN-003] Scope exit の中断 frame は leaf token を回収する。
;; [REQ: OWN-011] Handle escape と中断で捨てる frame も leaf token を回収する。
(require racket/match
         racket/list
         rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../borrow.rkt"
         "../machine.rkt"
         "../gen.rkt"
         "../typing.rkt")

(define option-owned '(Option (Owned Res)))
(define acquire '(PrimVal (Reserved o-acquire) acquire))
(define (owned-option n)
  `(Construct ,option-owned some
              (OwnLeaf (Apply ,acquire ,n))))

(define consumer-unit
  `(Lam User consume (raw later)
     (Handle (Return function-boundary Unit)
             (return-value -> return-value)
             (Scope ()
               (Let (transferred let ,option-owned) raw unit)))))
(define consumer-unit-callables
  `((consume (NFn (,option-owned Unit) Unit () () () User))))

(define consumer-return-owned
  `(Lam User consume-return (raw later)
     (Handle (Return function-boundary ,option-owned)
             (return-value -> return-value)
             (Scope ()
               (Let (first let ,option-owned) raw
                 (Let (second let ,option-owned) later
                   (Move first)))))))
(define consumer-return-owned-callables
  `((consume-return
     (NFn (,option-owned ,option-owned) ,option-owned () (Own) () User))))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 80])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (trace-g1 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 80])
    (when (zero? fuel)
      (error 'trace-g1 "評価 fuel を使い切った: ~s" current))
    (match (apply-reduction-relation/tag-with-names -->g1/rules current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list (string->symbol rule))) (sub1 fuel))]
      [steps (error 'trace-g1 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-configs configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row
                     (format "config ~a の runtime row: ~s" index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "不正な中間 config ~a: ~s" index configuration))))

(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))
(define (configuration-events configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,_ ,events) events]))

(define (trace-has-rule? rules name)
  (and (member name rules) #t))

(define (check-frame-rule-does-not-add-events configs rules name)
  (for ([rule (in-list rules)]
        [before (in-list configs)]
        [after (in-list (cdr configs))]
        #:when (eq? rule name))
    (check-equal? (configuration-events after)
                  (configuration-events before)
                  (format "~a 自体は θ を変えない" name))))

(test-case "OWN-003/OWN-011: ScopeError は捨てる frame の leaf を Dropped にする"
  (define core
    `(Scope (0)
       (Apply ,consumer-unit ,(owned-option 13) (Error 0))))
  (check-equal? (core-type-of core '((0 Res)) consumer-unit-callables)
                '(Unit ()))
  (define start
    `(cfg ,core ((0 (resource 7))) ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-configs configs consumer-unit-callables 'Unit)
  (check-true (trace-has-rule? rules 'R-ScopeError))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-equal? (third (last configs)) '((0 (resource 7))))
  (check-equal? (fourth (last configs)) '((0 Dropped))))

(test-case "G1 の R-ScopeError も捨てる frame の leaf を回収する"
  ;; G1 の評価関係に G2 の Let mode は無い。型検査は G2 の上の回帰で行い、
  ;; ここでは G1 の同名規則を G1 の文法だけで直接通す。
  (define core
    `(Scope (0)
       (Apply (Lam User consume (raw later) unit)
              ,(owned-option 13)
              (Error 0))))
  (define start
    `(cfg ,core ((0 (resource 7))) ((0 Available)) () ()))
  (define-values (configs rules) (trace-g1 start))
  (check-true (trace-has-rule? rules 'R-ScopeError))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-equal? (fourth (last configs)) '((0 Dropped))))

(test-case "OWN-003/OWN-011: ScopeAbort は frame を回収し Perform の引数を渡す"
  (define operation '(Return abort-boundary Unit))
  (define core
    `(Handle ,operation (answer -> answer)
       (Scope ()
         (Apply ,consumer-unit ,(owned-option 17)
                (Perform ,operation unit)))))
  (check-equal? (core-type-of core '() consumer-unit-callables) '(Unit ()))
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-configs configs consumer-unit-callables 'Unit)
  (check-true (trace-has-rule? rules 'R-ScopeAbort))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-equal? (configuration-events (last configs)) '())
  (check-frame-rule-does-not-add-events configs rules 'R-ScopeAbort))

(test-case "G1 の R-ScopeAbort も捨てる frame の leaf を回収する"
  (define operation '(Return abort-boundary Unit))
  (define core
    `(Scope ()
       (Apply (Lam User consume (raw later) unit)
              ,(owned-option 19)
              (Perform ,operation unit))))
  (define-values (configs rules) (trace-g1 `(cfg ,core () () () ())))
  (check-true (trace-has-rule? rules 'R-ScopeAbort))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-frame-rule-does-not-add-events configs rules 'R-ScopeAbort))

(test-case "OWN-011: HandleError は捨てる frame の leaf を回収する"
  (define core
    `(Scope (0)
       (Handle (Return handle-boundary Unit) (answer -> answer)
         (Apply ,consumer-unit ,(owned-option 23) (Error 0)))))
  (check-equal? (core-type-of core '((0 Res)) consumer-unit-callables)
                '(Unit ()))
  (define start `(cfg ,core ((0 (resource 7))) ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-configs configs consumer-unit-callables 'Unit)
  (check-true (trace-has-rule? rules 'R-HandleError))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-frame-rule-does-not-add-events configs rules 'R-HandleError))

(test-case "OWN-011: HandleSkip は frame を回収し Perform の引数を渡す"
  (define handled '(Return handled-boundary Unit))
  (define performed '(Return other-boundary Unit))
  (define core
    `(Scope ()
       (Handle ,handled (answer -> answer)
         (Apply ,consumer-unit ,(owned-option 29)
                (Perform ,performed unit)))))
  (check-equal? (core-type-of core '() consumer-unit-callables)
                '(Unit ((Return other-boundary Unit))))
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-configs configs consumer-unit-callables 'Unit)
  (check-true (trace-has-rule? rules 'R-HandleSkip))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-frame-rule-does-not-add-events configs rules 'R-HandleSkip))

(test-case "OWN-011: HandleReturn は frame を回収し Return 値を handler へ渡す"
  (define operation `(Return return-boundary ,option-owned))
  (define core
    `(Handle ,operation (answer -> answer)
       (Apply ,consumer-return-owned ,(owned-option 31)
              (Perform ,operation ,(owned-option 37)))))
  (check-equal? (core-type-of core '() consumer-return-owned-callables)
                `(,option-owned (Own)))
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-configs configs consumer-return-owned-callables option-owned)
  (check-true (trace-has-rule? rules 'R-HandleReturn))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped) ((tok 1) Available)))
  (check-equal? (collect-tokens (second (last configs))) '((tok 1)))
  (check-frame-rule-does-not-add-events configs rules 'R-HandleReturn))

(test-case "R-HandleSkip と R-ScopeAbort は Perform の引数 leaf を回収しない"
  (define handled '(Return handled-boundary Unit))
  (define performed `(Return other-boundary ,option-owned))
  (define core
    `(Scope ()
       (Handle ,handled (answer -> unit)
         (Apply ,consumer-return-owned ,(owned-option 41)
                (Perform ,performed ,(owned-option 43))))))
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-true (trace-has-rule? rules 'R-HandleSkip))
  (check-true (trace-has-rule? rules 'R-ScopeAbort))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped) ((tok 1) Available)))
  (check-equal? (collect-tokens (second (last configs))) '((tok 1))))

(test-case "G2 の ScopeAbort は Perform 引数の leaf を外へ渡す"
  (define operation `(Return abort-boundary ,option-owned))
  (define core
    `(Handle ,operation (answer -> answer)
       (Scope ()
         (Apply ,consumer-return-owned ,(owned-option 47)
                (Perform ,operation ,(owned-option 53))))))
  (check-equal? (core-type-of core '() consumer-return-owned-callables)
                `(,option-owned (Own)))
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-configs configs consumer-return-owned-callables option-owned)
  (check-true (trace-has-rule? rules 'R-ScopeAbort))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped) ((tok 1) Available)))
  (check-equal? (collect-tokens (second (last configs))) '((tok 1))))

(test-case "捨てる frame の未評価な後続欄に置かれた leaf も回収する"
  (define option-union `(Union ,option-owned Int))
  (define input
    `(UnionInject ,option-union ,option-owned ,(owned-option 59)))
  (define result-type
    `(Record ((early Int imm) (later ,option-owned imm))))
  (define alternate
    `(Rec ((early imm 0) (later imm (Construct ,option-owned none)))))
  (define branch-body
    `(Rec ((early imm
                    (Perform (Return pending-boundary ,result-type)
                             ,alternate))
          (later imm raw))))
  (define core
    `(Handle (Return pending-boundary ,result-type) (answer -> answer)
       (Scope ()
         (UnionEliminate ,input
           ((,option-owned raw -> ,branch-body)
            (Int ignored -> ,alternate))))))
  (check-equal? (core-type-of core '() '()) `(,result-type ()))
  (define start `(cfg ,core () () () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-configs configs '() result-type)
  (check-true (trace-has-rule? rules 'R-UnionEliminate))
  (check-true (trace-has-rule? rules 'R-ScopeAbort))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-equal? (collect-tokens (second (last configs))) '()))

(test-case "CurryVal の固定引数に入った leaf も frame とともに回収する"
  (define inner-type `(NFn ((Owned Res) Int) Unit () () () User))
  (define residual-type `(NFn (Int) Unit () () () User))
  (define closure-type `(Owned ,residual-type))
  (define consumer-type `(NFn (,closure-type Int) Int () () () User))
  (define function
    `(Lam User curried (fixed later)
       (Handle (Return inner-boundary Unit) (value -> value)
         (Scope () (Let (stored let (Owned Res)) fixed unit)))))
  (define consumer
    `(Lam User consume-curry (captured later)
       (Handle (Return consumer-boundary Int) (answer -> answer)
         (Scope () (Let (stored-closure let ,closure-type) captured 7)))))
  (define core
    `(Scope ()
       (Handle (Return curry-boundary Int) (answer -> answer)
         (Apply ,consumer
                (Curry ,function (OwnLeaf (Apply ,acquire 61)))
                (Perform (Return curry-boundary Int) 2)))))
  (define callables `((curried ,inner-type) (consume-curry ,consumer-type)))
  (check-equal? (core-type-of core '() callables) '(Int ()))
  (define start `(cfg ,core () () () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-configs configs callables 'Int)
  (check-true (trace-has-rule? rules 'R-HandleReturn))
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped)))
  (check-equal? (collect-tokens (second (last configs))) '()))

(test-case "fail-closed: frame の token 重複または非 Available は中断を止める"
  (define duplicate
    `(OwnedLeaf (tok 0) (resource 1)))
  (define repeated
    `(Rec ((left imm ,duplicate) (right imm ,duplicate))))
  (define (scope-error-with value tokens)
    `(cfg (Scope ()
           (Apply (PrimVal User add) ,value (Error 0)))
          () () ,tokens ()))
  (define duplicate-config
    (scope-error-with repeated '(((tok 0) Available))))
  (check-false
   (ormap (lambda (entry) (eq? (first entry) 'R-ScopeError))
          (raw-steps-g2/named duplicate-config)))
  (define unavailable-config
    (scope-error-with
     '(Rec ((left imm (OwnedLeaf (tok 0) (resource 1)))))
     '(((tok 0) Dropped))))
  (check-false
   (ormap (lambda (entry) (eq? (first entry) 'R-ScopeError))
          (raw-steps-g2/named unavailable-config))))

(test-case "fail-closed: frame と heap が token を共有すると ScopeError は止まる"
  (define leaf `(OwnedLeaf (tok 0) (resource 71)))
  (define config
    `(cfg (Scope (0)
           (Apply (PrimVal User add)
                  (Rec ((frame imm ,leaf)))
                  (Error 0)))
          ((0 (Rec ((heap imm ,leaf))))
          )
          ((0 Available)) (((tok 0) Available)) ()))
  (check-false
   (ormap (lambda (entry) (eq? (first entry) 'R-ScopeError))
          (raw-steps-g2/named config))))

#lang racket

(require rackunit
         racket/list
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define (success expression)
  (match (elab expression)
    [(list core type row callables)
     (define erased (erase-core core))
     (check-equal? (core-type-of/diagnostic erased '() callables)
                   (list type row))
     (list erased type row callables)]
    [other (fail-check (format "elaboration success を期待したが ~s" other))]))

(define (run-success result)
  (match result
    [(list core _type _row callables)
     (run-g2 (inject-g2m (execution-core core callables)) 10000)]
    [_ (fail-check "成功結果を期待した")]))

(define (return-boundaries tree)
  (append
   (match tree
     [`(Perform (Return ,boundary ,_) ,_) (list boundary)]
     [_ '()])
   (if (list? tree)
       (append-map return-boundaries tree)
       '())))

(define (return-performs tree)
  (append
   (match tree
     [`(Perform (Return ,boundary ,type) ,_) (list (list boundary type))]
     [_ '()])
   (if (list? tree)
       (append-map return-performs tree)
       '())))

(define (without-perform-boundary tree)
  (match tree
    [`(Perform (Return ,_ ,type) ,payload)
     `(Perform (Return ,type) ,(without-perform-boundary payload))]
    [(? list? parts) (map without-perform-boundary parts)]
    [_ tree]))

(define (leave-error expression)
  (match (elab expression)
    [`(err ,diagnostic) diagnostic]
    [other (fail-check (format "E-RET-006 を期待したが ~s" other))]))

(define (elab-error-id expression)
  (match (elab expression)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (check-leave-error expression [expected-span #f])
  (define diagnostic (leave-error expression))
  (check-equal? (diagnostic-id diagnostic) "E-RET-006")
  (check-equal?
   (diagnostic-code-key (diagnostic-code-row (diagnostic-id diagnostic)))
   'leave-outside-expression-boundary)
  (when expected-span
    (check-equal? (diagnostic-primary-span diagnostic) expected-span)))

(test-case "[REQ: RET-001, RET-002] 式境界の Leave は局所、Return は関数境界へ届く"
  (define leave
    (success '(Apply (Fn () Int () (NarrativeExpr (Leave 1))))))
  (define returned
    (success '(Apply (Fn () Int () (NarrativeExpr (Return 1))))))
  (check-equal? (without-perform-boundary (first leave))
                (without-perform-boundary (first returned)))
  (check-equal? (return-boundaries (first leave)) '(boundary1))
  (check-equal? (return-boundaries (first returned)) '(boundary0))
  (check-equal? (run-success leave) '(cfg 1 () () () ()))
  (define span '(#:span synthetic 0 0))
  (check-false (mentions-return? `(Leave ,span (#:lit 1 ,span))))
  (check-true (mentions-return? `(Return ,span (#:lit 1 ,span)))))

(test-case "[REQ: RET-001] 式境界より内側の FunctionBoundary は Leave を捕まえる"
  (check-leave-error '(Fn () Int () (NarrativeExpr (Fn () Int () (Leave 1)))))
  (check-leave-error '(Fn () Int () (Leave 1)))
  (check-leave-error '(Leave 1)))

(test-case "[REQ: RET-001] Leave は外側の ExpressionBoundary を越えて FunctionBoundary を越えない"
  (define span '(#:span src 20 30))
  (define payload-span '(#:span src 26 27))
  (define fn-span '(#:span src 0 40))
  (define type-span '(#:span src 10 13))
  (define row-span '(#:span src 14 16))
  (check-leave-error
   `(Fn ,fn-span () (#:ty Int ,type-span) (#:ef () ,row-span)
        (Leave ,span (#:lit 1 ,payload-span)))
   span)

  (define nested
    (success
     '(Apply (Fn () Int ()
                 (NarrativeExpr (NarrativeExpr (Leave 1)))))))
  (check-equal? (return-boundaries (first nested)) '(boundary2))
  (check-equal? (run-success nested) '(cfg 1 () () () ())))

(test-case "[REQ: RET-001] Loop 本体の Leave は外側の式境界へ解決する"
  (define result
    (success
     '(Apply (Fn ((value Int)) Int ()
                 (NarrativeExpr
                  (Loop loop () Int (Leave) (Leave value) ())))
             7)))
  (check-equal? (return-boundaries (first result)) '(boundary1))
  (check-equal? (run-success result) '(cfg 7 () () () ())))

(test-case "[REQ: RET-001] Loop row は Return と Leave を個別に宣言する"
  (define (expression flag row)
    `(Apply
      (Fn ((flag Bool)) Int ()
        (Let (answer const Int)
             (NarrativeExpr
              (Loop loop () Int ,row
                (Eliminate flag
                  ((true () -> (Return 1))
                   (false () -> (Leave 2))))
                ()))
          (Return answer)))
      (Construct ,flag (Types))))
  (define both (success (expression 'true '(Return Leave))))
  (check-equal? (run-success both) '(cfg 1 () () () ()))
  (define other-branch (success (expression 'false '(Return Leave))))
  (check-equal? (run-success other-branch) '(cfg 2 () () () ()))
  (for ([row (in-list '((Return) (Leave)))])
    (check-equal? (diagnostic-id
                   (match (elab (expression 'true row))
                     [`(err ,diagnostic) diagnostic]
                     [other (fail-check (format "E-EFF-003 を期待したが ~s" other))]))
                  "E-EFF-003")))

(test-case "[REQ: RET-001] Loop 内で消費される Leave は Loop row を要しない"
  (define result
    (success '(Loop loop () Int () (NarrativeExpr (Leave 5)) ())))
  (check-equal? (second result) 'Int))

(test-case "[REQ: RET-001] Loop の Leave row は probe では Never に仮置きされる"
  (define result
    (success '(NarrativeExpr (Loop loop () Int (Leave) (Leave 5) ()))))
  (check-equal? (second result) 'Int))

(test-case "[REQ: RET-001] 式境界の無い Loop Leave row は E-RET-006"
  (check-leave-error '(Loop loop () Int (Leave) (Leave 1) ())))

(test-case "[REQ: RET-001] Loop 以外の宣言 row は Leave を受け付けない"
  (for ([expression
         (in-list
          (list '(Fn () Int (Leave) 1)
                '(FnDecl f () Int (Leave) unit unit)
                '(Recur f () Int (Leave) unit (Apply f))))])
    (check-equal? (elab-error-id expression) "E-SYN-003")))

(test-case "[REQ: RET-001] Leave の NarrativeExpr payload は自身の境界へ戻らない"
  (define result
    (success
     '(Apply (Fn () Int ()
                 (NarrativeExpr
                  (Leave (NarrativeExpr (Leave 2))))))))
  (check-equal? (return-boundaries (first result)) '(boundary1 boundary2))
  (check-equal? (run-success result) '(cfg 2 () () () ())))

(test-case "[REQ: RET-002] probe と型付き境界は到達不能な Leave を合流しない"
  ;; 合成位置では後続 Leave が probe の候補へ混ざらず、境界型は Int のままになる。
  (define probed (success '(NarrativeExpr (Let x (Leave 1) (Leave "s")))))
  (check-equal? (second probed) 'Int)
  (check-equal? (third probed) '())
  (check-equal? (return-boundaries (first probed)) '(boundary0))
  (check-equal? (run-success probed) '(cfg 1 () () () ()))

  ;; 期待型付き境界でも後続 Leave は pending escape に登録されない。
  (define checked
    (success
     '(Apply (Fn () Int ()
                 (NarrativeExpr (Let x (Leave 1) (Leave "s")))))))
  (check-equal? (second checked) 'Int)
  (check-equal? (third checked) '())
  (check-equal? (return-boundaries (first checked)) '(boundary1))
  (check-equal? (run-success checked) '(cfg 1 () () () ())))

(test-case "[REQ: RET-001, RET-002] 省略戻り型の dead Return は候補に混ざらない"
  (define inferred
    (success
     '(Apply
       (Fn () #:infer ()
           (NarrativeExpr (Let ignored (Return 1) (Return "s")))))))
  (check-equal? (second inferred) 'Int)
  (check-equal? (length (return-boundaries (first inferred))) 1)
  (check-equal? (run-success inferred) '(cfg 1 () () () ())))

(test-case "[REQ: RET-001, RET-002] 注釈付き関数の dead Return は脱出にならない"
  (define checked
    (success
     '(Apply
       (Fn () Int ()
           (NarrativeExpr (Let ignored (Return 1) (Return "s")))))))
  (check-equal? (second checked) 'Int)
  (check-equal? (return-performs (first checked)) '((boundary0 Int)))
  (check-equal? (run-success checked) '(cfg 1 () () () ())))

(test-case "[REQ: RET-001, RET-002] 到達する Return none は境界型との不一致になる"
  (define result
    (compile-source/string 'src
                           "fn f() -> Int { return none }\nf()"))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-DAT-002")))

(test-case "[REQ: RET-001, RET-002] synth できない dead Return payload は E-TYP-003"
  (define result
    (compile-source/string 'src
                           "fn f() -> Int { return 1\n return none }\nf()"))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-003")))

(test-case "[REQ: RET-001, RET-002] synth できない dead Leave payload は E-TYP-003"
  (define result
    (elab
     '(Apply (Fn () Int ()
                 (NarrativeExpr
                  (Let ignored (Leave 1) (Leave (Construct none))))))))
  (match result
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-TYP-003")]
    [other (fail-check (format "E-TYP-003 を期待したが ~s" other))]))

(test-case "[REQ: RET-001, RET-002] dead Return none は Option 戻り値で受理される"
  (define checked
    (success
     '(Apply
       (Fn () (Option Int) ()
           (NarrativeExpr
            (Let ignored
                 (Return (Construct some (Types Int) 1))
                 (Return (Construct none))))))))
  (check-equal? (second checked) '(Option Int))
  (check-equal? (return-performs (first checked)) '((boundary0 (Option Int))))
  (check-equal? (run-success checked)
                '(cfg (Construct (Option Int) some 1) () () () ())))

(test-case "[REQ: RET-001, RET-002] Never の後の厳格な operand と arm の Leave は境界に混ざらない"
  (define (check-order expression)
    (define probed (success `(NarrativeExpr ,expression)))
    (check-equal? (second probed) 'Int)
    (check-equal? (third probed) '())
    (check-equal? (length (return-boundaries (first probed))) 1)
    (check-equal? (run-success probed) '(cfg 1 () () () ()))

    (define checked
      (success
       `(Apply (Fn () Int () (NarrativeExpr ,expression)))))
    (check-equal? (second checked) 'Int)
    (check-equal? (third checked) '())
    (check-equal? (length (return-boundaries (first checked))) 1)
    (check-equal? (run-success checked) '(cfg 1 () () () ())))

  (check-order
   '(Apply (Fn ((first Int) (second String)) Int () first)
           (Leave 1) (Leave "s")))
  (check-order
   '(Let x
         (Construct cons (Types Int)
                    (Leave 1) (Leave (Construct nil (Types Int))))
      1))
  (check-order
   '(Let x
         (Rec ((first imm (Leave 1)) (second imm (Leave "s"))))
      1))
  (check-order
   '(Let (record const (Record ((first Int imm) (second String imm))))
         (Rec ((first imm (Leave 1)) (second imm (Leave "s"))))
      1))
  (check-order
   '(Let x
         (Eliminate (Construct some (Types Int) (Leave 1))
                    ((some (value) -> (Leave "s"))
                     (none () -> (Leave "t"))))
      1))

  ;; dead payload は境界の型で check できる場合、synth の失敗に巻き戻さない。
  (define dead-contextual-payload
    (success
     '(Apply (Fn () (Option Int) ()
                 (NarrativeExpr
                  (Let x
                       (Leave (Construct some (Types Int) 1))
                       (Leave (Construct none))))))))
  (check-equal? (second dead-contextual-payload) '(Option Int))
  (check-equal? (run-success dead-contextual-payload)
                '(cfg (Construct (Option Int) some 1) () () () ()))

  ;; probe 中も先行する候補を局所的に使えるため、dead の none は synth 不要である。
  (define dead-probed-payload
    (success
     '(NarrativeExpr
       (Let x
            (Leave (Construct some (Types Int) 1))
            (Leave (Construct none))))))
  (check-equal? (second dead-probed-payload) '(Option Int))
  (check-equal? (run-success dead-probed-payload)
                '(cfg (Construct (Option Int) some 1) () () () ())))

(test-case "[REQ: RET-001, RET-002] Never の TryBind 右辺と Union scrutinee の後の Leave は境界に混ざらない"
  (define (check-option-order expression)
    (define probed (success `(NarrativeExpr ,expression)))
    (check-equal? (second probed) '(Option Int))
    (check-equal? (third probed) '())
    (check-equal? (length (return-boundaries (first probed))) 1)
    (check-equal? (run-success probed)
                  '(cfg (Construct (Option Int) some 1) () () () ()))

    (define checked
      (success
       `(Apply (Fn () (Option Int) () (NarrativeExpr ,expression)))))
    (check-equal? (second checked) '(Option Int))
    (check-equal? (third checked) '())
    (check-equal? (length (return-boundaries (first checked))) 1)
    (check-equal? (run-success checked)
                  '(cfg (Construct (Option Int) some 1) () () () ())))

  (check-option-order
   '(TryBind x
             (Let y (Leave (Construct some (Types Int) 1)) y)
             (Leave (Construct some (Types Int) 2))))

  (define union-body
    '(Let (x const (Union Int String)) (Leave u)
          (Eliminate x
            ((Int i -> (Leave u))
             (String s -> (Leave u))))))
  (define union-application
    `(Apply (Fn ((u (Union Int String))) (Union Int String) ()
                (NarrativeExpr ,union-body))
            1))
  (define union-order (success `(NarrativeExpr ,union-application)))
  (check-equal? (second union-order) '(Union Int String))
  (check-equal? (third union-order) '())
  (check-equal? (length (return-boundaries (first union-order))) 1)
  (check-equal? (run-success union-order)
                '(cfg (UnionVal (Union Int String) Int 1) () () () ()))

  (define checked-union-order
    (success
     union-application))
  (check-equal? (second checked-union-order) '(Union Int String))
  (check-equal? (third checked-union-order) '())
  (check-equal? (length (return-boundaries (first checked-union-order))) 1)
  (check-equal? (run-success checked-union-order)
                '(cfg (UnionVal (Union Int String) Int 1) () () () ())))

(test-case "[REQ: RET-001] 外側の式境界を越える Recur の Leave は拒否する"
  (check-leave-error
   '(NarrativeExpr (Recur f () Int () (Leave 1) unit))))

(test-case "[REQ: RET-001] 推論 Recur 本体は Leave の宛先探索を止める"
  (check-leave-error
   '(NarrativeExpr (Recur f () #:infer () (Leave 1) unit))))

(test-case "[REQ: RET-001] 外側の式境界を越える FnDecl の Leave は拒否する"
  (check-leave-error
   '(NarrativeExpr (FnDecl f () Int () (Leave 1) unit))))

(test-case "[REQ: RET-001] Recur 本体内の式境界は Leave を捕まえる"
  (define result
    (success '(NarrativeExpr
               (Recur f () Int () (NarrativeExpr (Leave 1)) unit))))
  (check-equal? (second result) 'Unit))

(test-case "[REQ: RET-001, RET-002] Leave の探索停止印は TryBind の関数宛先を遮らない"
  (define result
    (success
     '(Apply
       (Fn () (Option Int) ()
         (Recur loop () #:infer (Return)
           (TryBind x (Construct some (Types Int) 1) x)
           (Construct some (Types Int) 2))))))
  (check-equal? (return-boundaries (first result)) '(boundary0)))

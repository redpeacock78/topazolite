#lang racket

(require rackunit
         racket/list
         racket/match
         "../diagnostic.rkt"
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

(define (leave-error expression)
  (match (elab expression)
    [`(err ,diagnostic) diagnostic]
    [other (fail-check (format "E-RET-006 を期待したが ~s" other))]))

(define (check-leave-error expression [expected-span #f])
  (define diagnostic (leave-error expression))
  (check-equal? (diagnostic-id diagnostic) "E-RET-006")
  (check-equal?
   (diagnostic-code-key (diagnostic-code-row (diagnostic-id diagnostic)))
   'leave-outside-expression-boundary)
  (when expected-span
    (check-equal? (diagnostic-primary-span diagnostic) expected-span)))

(test-case "[REQ: RET-001, RET-002] 式境界直下の Leave は Return と同じ Core になる"
  (define leave
    (success '(Apply (Fn () Int () (NarrativeExpr (Leave 1))))))
  (define returned
    (success '(Apply (Fn () Int () (NarrativeExpr (Return 1))))))
  (check-equal? (take leave 3) (take returned 3))
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
                  (Loop loop () Int (Return) (Leave value) ())))
             7)))
  (check-equal? (return-boundaries (first result)) '(boundary1))
  (check-equal? (run-success result) '(cfg 7 () () () ())))

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

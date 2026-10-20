#lang racket

(require racket/match
         rackunit
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (elaborated core)
  (match (elab core)
    [(list core type row callables) (list core type row callables)]
    [other (fail-check (format "elaboration success を期待したが ~s" other))]))

(define (run-elaborated core callables)
  (run-g2 (inject-g2m (execution-core core callables)) 10000))

(test-case "A1 %op-add は正規の PrimVal へ解決される"
  (match-define (list core type _row _callables)
    (elaborated '(Apply %op-add 1 2)))
  (check-equal? (erase-core core)
                '(Apply (PrimVal (Reserved o-add) add) 1 2))
  (check-equal? type 'Int))

(test-case "A2 同名の局所束縛 add は %op-add を捕獲しない"
  (match-define (list core _type _row callables)
    (elaborated
     '(Let (add const Int) 9 (Apply %op-add 1 2))))
  (check-equal? (run-elaborated core callables)
                '(cfg 3 () () () ())))

(test-case "A3 6 個の alias は元の primitive と同じ型と値を持つ"
  (for ([pair (in-list '((%op-add add) (%op-sub sub) (%op-mul mul)
                         (%op-lt lt) (%op-le le) (%op-eq eq)))])
    (define alias-entry (assoc (first pair) Γ0))
    (define primitive-entry (assoc (second pair) Γ0))
    (check-not-false alias-entry (format "Γ0 に ~a がある" (first pair)))
    (check-equal? (and alias-entry (cadr alias-entry))
                  (cadr primitive-entry))))

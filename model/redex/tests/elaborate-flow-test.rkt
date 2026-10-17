#lang racket

(require rackunit
         racket/match
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt")

(define outer-record-type '(Record ((name String imm))))

(define (elab-type expression)
  (match (elab expression)
    [(list _ type _ _) type]
    [other (fail-check (format "elaboration 成功を期待したが ~s" other))]))

(define (run-source source)
  (define result (compile-source/string 'src source))
  (unless (compiled? result)
    (fail-check (format "compile 成功を期待したが ~s" result)))
  (call-with-trait-ledger
   (compiled-ledger result)
   (λ ()
     (match
         (run-g2 (inject-g2m
                  (erase-core (compiled-execution-core result)))
                 10000)
       [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
       [other (fail-check (format "terminal config を期待したが ~s" other))]))))

(test-case "非 mut の仮引数は外側の mut flow key を遮蔽する"
  (check-equal?
   (elab-type
    `(Let (x mut ,outer-record-type)
         (Rec ((name imm "outer")))
       (Fn ((x Int)) Int () x)))
   '(NFn (Int) Int () () () User)))

(test-case "内側の let mut の key は scope 外へ漏れない"
  (define inner-record-type '(Record ((active Int imm))))
  (define expression
    `(Let (x mut ,outer-record-type)
         (Rec ((name imm "outer")))
       (Let (saved const Int)
            (Let (x mut ,inner-record-type)
                 (Rec ((active imm 7)))
              (Proj x active))
         (Proj x name))))
  (check-equal? (elab-type expression) 'String))

(test-case "繰り返す再代入の実行結果は従来どおり"
  (check-equal?
   (run-source "let mut c = 0\nc = add(c, 1)\nc = add(c, 1)\nc")
   2))

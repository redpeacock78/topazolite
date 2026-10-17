#lang racket

(require rackunit
         racket/match
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define outer-record-type '(Record ((name String imm))))

(define (elab-type expression)
  (match (elab expression)
    [(list _ type _ _) type]
    [other (fail-check (format "elaboration 成功を期待したが ~s" other))]))

(define (elab-core expression)
  (match (elab expression)
    [(list core _ _ _) (erase-core core)]
    [other (fail-check (format "elaboration 成功を期待したが ~s" other))]))

(define (find-mut-let-parts core)
  (match core
    [`(Let (,_ mut ,_) ,bound ,body) (list bound body)]
    [(? list? parts)
     (for/or ([part (in-list parts)]) (find-mut-let-parts part))]
    [_ #f]))

(define (find-reassign-view core)
  (match core
    [`(Reassign ,_ ,view ,_) view]
    [(? list? parts)
     (for/or ([part (in-list parts)]) (find-reassign-view part))]
    [_ #f]))

(define (checked-core-type core)
  (match (core-type-of core '() '())
    [(list type _) type]
    [other (fail-check (format "Core の型付け成功を期待したが ~s" other))]))

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

(test-case "再代入後は新しい record shape で読み出せる"
  (check-equal?
   (run-source
    (string-append
     "type Named = { name: String }\n"
     "fn f() -> Bool ! Mutation {\n"
     "  let mut value: Named = { name: \"A\", id: 1 }\n"
     "  value = { name: \"B\", active: true }\n"
     "  return value.active\n"
     "}\nf()"))
   '(Construct Bool true)))

(test-case "同じ RHS の初期 C と再代入 C は Record、Union、optional で一致する"
  (for ([example
         (in-list
          (list
           (list '(Record ((name String imm)))
                 '(Rec ((name imm "A") (active imm 1))))
           (list '(Union Int String) 1)
           (list '(Record ((age Int imm opt) (name String imm)))
                 '(Rec ((name imm "A"))))))])
    (define declared (first example))
    (define rhs (second example))
    (define initial-core
      (elab-core `(Let (value mut ,declared) ,rhs value)))
    (define initial-parts (find-mut-let-parts initial-core))
    (check-not-false initial-parts)
    (define initial-flow-type (checked-core-type (first initial-parts)))
    (define reassignment-core
      (elab-core `(Let (value mut ,declared) ,rhs (Reassign value ,rhs))))
    (define reassigned-flow-type (find-reassign-view reassignment-core))
    (check-not-false reassigned-flow-type)
    (check-true (type-equiv? initial-flow-type reassigned-flow-type)
                (format "initial C ~s と Reassign C ~s が異なる"
                        initial-flow-type reassigned-flow-type))))

(test-case "Never RHS は view を保ち、Reassign 自身の Mutation を足さない"
  (define source
    (string-append
     "fn f() -> Int ! {} {\n"
     "  let mut value = 0\n"
     "  value = return 7\n"
     "}\nf()"))
  (define result (compile-source/string 'src source))
  (check-true (compiled? result)
              (format "compile 成功を期待したが ~s" result))
  (when (compiled? result)
    (check-equal? (compiled-row result) '())
    (check-equal? (find-reassign-view (erase-core (compiled-core result))) 'Int)
    (check-equal? (run-source source) 7)))

(test-case "Never RHS 内で先行した再代入の view は残る"
  (define source
    (string-append
     "type Named = { name: String }\n"
     "fn f() -> Bool ! Mutation {\n"
     "  let mut value: Named = { name: \"A\" }\n"
     "  value = { value = { name: \"B\", active: true }\n"
     "    return value.active }\n"
     "}\nf()"))
  (define result (compile-source/string 'src source))
  (check-true (compiled? result)
              (format "compile 成功を期待したが ~s" result))
  (when (compiled? result)
    (match (find-reassign-view (erase-core (compiled-core result)))
      [`(Record ,row) (check-not-false (assoc 'active row))]
      [other (fail-check (format "outer Reassign の更新後 view を期待したが ~s"
                                 other))])
    (check-equal? (run-source source) '(Construct Bool true))))

(test-case "Apply の実引数は左から flow view を受け渡す"
  (check-equal?
   (run-source
    (string-append
     "fn combineValues(first: Unit, second: Bool) -> Bool { return second }\n"
     "fn f() -> Bool ! {Mutation, Partial} {\n"
     "  let mut value: { name: String } = { name: \"A\" }\n"
     "  return combineValues({ value = { name: \"B\", active: true }\n    () }, (fn() => value.active)())\n"
     "}\nf()"))
   '(Construct Bool true)))

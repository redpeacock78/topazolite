#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../rows.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))
(define (code source)
  (match (compile source)
    [(? diagnostic? diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result)))
                    10000)
       [`(cfg ,value () () () ()) value]
       [other (fail-check (format "純粋な整数値の終端状態を期待したが ~s" other))]))))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 10000])
    (when (zero? fuel) (error 'trace-g2 "fuel exhausted at ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _rule next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "expected one step, got ~s" steps)])))

(define (find-form tree wanted)
  (cond [(and (pair? tree) (eq? (car tree) wanted)) tree]
        [(pair? tree)
         (for/or ([child (in-list tree)]) (find-form child wanted))]
        [else #f]))

(define (find-let-with-return tree)
  (cond
    [(and (pair? tree)
          (eq? (car tree) 'Let)
          (match (third tree)
            [`(Perform (Return ,_ ,_) ,_) #t]
            [_ #f]))
     tree]
    [(pair? tree)
     (for/or ([child (in-list tree)]) (find-let-with-return child))]
    [else #f]))

(test-case "束縛値の Return は異なる型の到達不能な末尾を許す"
  (define result
    (compile "fn f(x: Int) -> Int { let a = return x\n \"s\" }\nf(7)"))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) 7)))

(test-case "注釈付き Let の Return も異なる型の末尾を許す"
  (define result
    (compile "fn f(x: Int) -> Int { let a: Int = return x\n \"s\" }\nf(7)"))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-equal? (run-value result) 7)))

(test-case "const Let は Never の束縛値を受け、mut の事前拒否を保つ"
  (check-equal?
   (code "fn f(x: Int) -> Int { const a: Int = return x\n \"s\" }\nf(7)")
   'ok)
  (check-equal?
   (code (string-append
          "fn f(x: Owned<Int>) -> Owned<Int> ! Own {\n"
          " let mut a: Owned<Int> = return x\n"
          " \"s\"\n"
          "}\n0"))
   "E-VAR-012"))

(test-case "到達不能な Let 本体の型誤りも報告する"
  (check-equal?
   (code (string-append
          "fn takes(x: Int) -> Int { return x }\n"
          "fn f() -> Int { let a = return 1\n takes(\"s\") }\nf()"))
   "E-TYP-012"))

(test-case "到達不能でも型引数が必要な none は合成できない"
  (check-equal?
   (code "fn f() -> Int { let a = return 1\n none }\nf()")
   "E-TYP-003"))

(test-case "Core の Never Let は synth と check の両方で Never になる"
  (define core '(Let (x Int) (Perform (Return boundary Int) 1) 2))
  (check-equal? (core-type-of core '() '())
                '(Never ((Return boundary Int))))
  (check-true (core-check core '() '() 'Int '((Return boundary Int))))
  (check-true (core-check core '() '() 'Unit '((Return boundary Int)))))

(test-case "Owned を保持した scope から Return すると終端で token を drop する"
  (define surface-result
    (compile (string-append
              "fn f(value: Int, payload: Owned<Int>) -> Int ! Own {\n"
              " let a = return value\n"
              " \"unreachable\"\n"
              "}\n"
              "0")))
  (check-true (compiled? surface-result)
              (if (diagnostic? surface-result)
                  (format "~a: ~a" (diagnostic-id surface-result)
                          (diagnostic-message surface-result))
                  (format "unexpected result: ~s" surface-result)))
  (define result
    (elab '(Apply
            (Fn ((value Int) (payload (Owned Res))) Int (Own)
              (Let (a const Int) (Return value) "unreachable"))
            7 (Apply acquire 1))))
  (match result
    [(list core expected _row callables)
     (call-with-trait-ledger
      (current-trait-ledger)
      (lambda ()
       (define start (inject-g2m (erase-core core)))
       (define configs (trace-g2 start))
       (define initial-row (runtime-row start callables expected))
       (check-not-false initial-row)
       (for ([configuration (in-list configs)] [index (in-naturals)])
         (define runtime (runtime-row configuration callables expected))
         (check-not-false runtime (format "config ~a has a runtime row" index))
         (when (and runtime initial-row)
           (check-true (row-subset? runtime initial-row))
           (check-true (config-ok? configuration callables expected runtime))))
       (check-equal? (match (last configs)
                       [`(cfg ,control ,_ ...) control])
                     7)
       (check-equal? (match (last configs)
                       [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens])
                     '(((tok 0) Dropped))))) ]
    [other (fail-check (format "Owned な関数引数を使う UCore trace を作れなかった: ~s"
                               other))]))

(test-case "束縛値と本体の effect row は合併する"
  (define expression
    '(Fn () Unit ((Yield Int) (Yield String))
         (Let x (Return (Yield 1 unit)) (Yield "s" unit))))
  (match (elab expression)
    [(list _ type _ _)
     (check-equal? type
                   '(NFn () Unit () ((Yield Int) (Yield String)) () User))]
    [other (fail-check (format "row を合併した Fn を期待したが ~s" other))]))

(test-case "資源型 identity Let は synth と check で Never を保つ"
  (define cases
    (list
     (list '(Owned Res) 'x)
     (list '(Record ((a (Owned Res) imm))) 'record)))
  (for ([case (in-list cases)])
    (define type (first case))
    (define name (second case))
    (define synthesized
      (elab `(Fn ((payload ,type)) #:infer (Own)
                 (Let (,name const ,type) (Return (Move payload)) ,name))))
    (check-true (and (list? synthesized) (= (length synthesized) 4))
                (format "synth が成功する for ~s: ~s" type synthesized))
    (when (and (list? synthesized) (= (length synthesized) 4))
      (define core (erase-core (first synthesized)))
      (define let-core (find-let-with-return core))
      (check-not-false let-core)
      (check-equal? (core-type-of (first synthesized) '() (fourth synthesized))
                    (list (second synthesized) (third synthesized)))
      (check-true (core-check (first synthesized) '() (fourth synthesized)
                              (second synthesized) (third synthesized))))
    (define checked
      (elab `(Fn ((payload ,type)) ,type (Own)
                 (Let (,name const ,type) (Return (Move payload)) ,name))))
    (check-true (and (list? checked) (= (length checked) 4))
                (format "check が成功する for ~s: ~s" type checked))
    (when (and (list? checked) (= (length checked) 4))
      (define core (erase-core (first checked)))
      (define let-core (find-let-with-return core))
      (check-not-false let-core)
      (check-equal? (core-type-of (first checked) '() (fourth checked))
                    (list (second checked) (third checked)))
      (check-true (core-check (first checked) '() (fourth checked)
                              (second checked) (third checked))))))

(test-case "注釈付き Let の check 経路で全 Return の Eliminate は Never"
  (define expression
    '(Fn () Int ()
         (Let (x const Int)
              (Eliminate (Construct true (Types))
                ((true () -> (Return 1))
                 (false () -> (Return 2))))
              "unreachable")))
  (match (elab expression)
    [(list core _type _row callables)
     (define let-core (find-form (erase-core core) 'Let))
     (check-not-false let-core)
     (when let-core
       (check-equal? (first (core-type-of let-core '() callables)) 'Never))]
    [other (fail-check (format "check 経路の Never Let を受理しなかった: ~s"
                               other))]))

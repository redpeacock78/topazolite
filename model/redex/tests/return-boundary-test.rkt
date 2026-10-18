#lang racket

(require rackunit
         racket/list
         racket/match
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))

(define (code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))

(define (run-configs start callables expected)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 10000])
    (when (zero? fuel) (error 'run-configs "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps (error 'run-configs "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-configs configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define runtime (runtime-row configuration callables expected))
    (check-not-false runtime (format "config ~a に runtime-row がある" index))
    (when runtime
      (check-true (config-ok? configuration callables expected runtime)
                  (format "config ~a が config-ok? を満たす" index)))))

(define (trace-compiled result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (define callables (compiled-callables result))
     (define expected (compiled-type result))
     (define start
       (inject-g2m (erase-core (compiled-execution-core result))))
     (define-values (configs rules) (run-configs start callables expected))
     (check-configs configs callables expected)
     (values configs rules))))

(define (trace-core core callables expected)
  (define start (inject-g2m (erase-core core)))
  (define-values (configs rules) (run-configs start callables expected))
  (check-configs configs callables expected)
  (values configs rules))

(define (run-value result)
  (define-values (configs _rules) (trace-compiled result))
  (match (last configs)
    [`(cfg ,value () () () ()) value]
    [other (fail-check (format "空の終端台帳を期待したが ~s" other))]))

(define (config-control configuration)
  (match configuration [`(cfg ,control ,_heap ,_states ,_tokens ,_events) control]))

(define (config-tokens configuration)
  (match configuration [`(cfg ,_control ,_heap ,_states ,tokens ,_events) tokens]))

(define (config-events configuration)
  (match configuration [`(cfg ,_control ,_heap ,_states ,_tokens ,events) events]))

(define (return-boundaries tree)
  (append
   (match tree
     [`(Perform (Return ,boundary ,_) ,_) (list boundary)]
     [`(Return ,boundary ,_) (list boundary)]
     [_ '()])
   (if (list? tree) (append-map return-boundaries tree) '())))

(define (return-handler-boundaries tree)
  (append
   (match tree
     [`(Handle (Return ,boundary ,_) ,_ ,_) (list boundary)]
     [`(Handle ,_ (Return ,boundary ,_) ,_ ,_) (list boundary)]
     [_ '()])
   (if (list? tree) (append-map return-handler-boundaries tree) '())))

(define (literal-return-boundary tree value)
  (or
   (match tree
     [`(Perform ,_ (Return ,boundary ,_) (#:lit ,actual ,_))
      (and (equal? actual value) boundary)]
     [`(Perform (Return ,boundary ,_) (#:lit ,actual ,_))
      (and (equal? actual value) boundary)]
     [_ #f])
   (and (list? tree)
        (for/or ([part (in-list tree)])
          (literal-return-boundary part value)))))

(define (contains-tree? tree wanted)
  (or (equal? tree wanted)
      (and (list? tree) (ormap (lambda (part) (contains-tree? part wanted)) tree))))

(define (compile-ok source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a ~s: ~a" (diagnostic-id result)
                          (diagnostic-primary-span result)
                          (diagnostic-message result))
                  (format "予期しない結果: ~s" source)))
  result)

(test-case "[REQ: RET-001, RET-002] return は if・when と別の Return handler を越える"
  (for ([variable? (in-list '(#t #f))])
    (define source
      (string-append
       (if variable? "" "fn get_flag() -> Bool { return true }\n")
       "fn choose(c: Bool" (if variable? ", flag: Bool" "") ") -> Int {\n"
       "  let value = when " (if variable? "flag" "get_flag()") " {\n"
       "    true => if c { return 11 } else { 12 }\n"
       "    false => 13\n"
       "  }\n  return add(value, 100)\n}\n"
       (if variable? "choose(true, true)" "choose(true)")))
    (define result (compile-ok source))
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) 11))

  (for ([c (in-list '(true false))] [expected (in-list '(21 22))])
    (define source
      (format "fn f(c: Bool) -> Int { let ignored: Option<Int> = if c { return 21 }\n return 22 }\nf(~a)"
              c))
    (define result (compile-ok source))
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) expected))

  ;; G1 の handler は Return のみなので、異なる境界 ID を別の op として試す。
  (define expression
    '(Handle (Return outer Int) (answer -> answer)
       (Handle (Return inner Int) (ignored -> ignored)
         (Perform (Return outer Int) 7))))
  (check-equal? (core-type-of expression '() '()) '(Int ()))
  (define-values (configs rules) (trace-core expression '() 'Int))
  (check-not-false (member 'R-HandleSkip rules))
  (check-equal? (config-control (last configs)) 7))

(test-case "[REQ: RET-001] leave は最寄りの式境界、内側関数の return はその関数へ届く"
  (define source
    (string-append
     "fn outer() -> Int {\n"
     "  let inner = fn() -> Int {\n"
     "    let value = when true { true => leave 3\n false => 0 }\n"
     "    return add(value, 100)\n"
     "  }\n"
     "  return add(inner(), 1)\n"
     "}\nouter()"))
  (define result (compile-ok source))
  (check-equal? (compiled-type result) 'Int)
  (check-equal? (run-value result) 104)
  (check-equal?
   (code "fn f(c: Bool) -> Int { let x = if c { let h = fn(y: Int) => { leave y }\n 1 } else { 2 }\n x }\n0")
   "E-RET-006"))

(test-case "[REQ: RET-001] 関数境界の外の値位置 when の return は E-RET-002"
  (for ([scrutinee (in-list '("flag" "get_flag()"))])
    (define variable? (string=? scrutinee "flag"))
    (define prefix (if variable? "let flag = true\n"
                       "fn get_flag() -> Bool { return true }\n"))
    (check-equal?
     (code (string-append prefix "let value = when " scrutinee
                          " { true => return 1\n false => 0 }\n0"))
     "E-RET-002")))

(test-case "[REQ: RET-001, RET-002] when arm の ?= は関数戻り型で検査する"
  (for ([scrutinee (in-list '("flag" "get_flag()"))])
    (define variable? (string=? scrutinee "flag"))
    (define prefix (if variable? ""
                       "fn get_flag() -> Bool { return true }\n"))
    (define parameters (if variable? "flag: Bool, " ""))
    (define arguments (if variable? "true, none" "none"))
    (define source
      (string-append
       prefix "fn f(" parameters "value: Option<Int>) -> Int {\n"
       "  let answer = when " scrutinee " {\n"
       "    true => { let item ?= value\n 1 }\n"
       "    false => 0\n"
       "  }\n  return answer\n}\nf(" arguments ")"))
    (define result (compile source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-TYP-033")
      (check-equal? (diagnostic-expected result) 'Int)
      (check-equal? (diagnostic-found result) '(Option Int))
      (check-equal? (map first (diagnostic-related result)) '(return-boundary))
      (match (second (first (diagnostic-related result)))
        [`(#:span src ,start ,end) (check-true (< start end))]
        [other (fail-check (format "関数境界の related span を期待したが ~s" other))])))

  (for ([scrutinee (in-list '("a" "get_option(a)"))])
    (define prefix (if (string=? scrutinee "a") ""
                       "fn get_option(x: Option<Int>) -> Option<Int> { return x }\n"))
    (define source
      (string-append
       prefix "fn f(a: Option<Int>, b: Option<Int>, fallback: Option<Int>) -> Option<Int> {\n"
       "  let answer: Option<Int> = when " scrutinee " {\n"
       "    some x => { let item ?= b\n let wrapped: Option<Int> = some(x)\n leave wrapped }\n"
       "    none => fallback\n"
       "  }\n  return answer\n}\nf(some(4), none, some(9))"))
    (define result (compile-ok source))
    (check-equal? (compiled-type result) '(Option Int))
    (check-equal? (run-value result) '(Construct (Option Int) none)))

  (check-equal?
   (code "let option: Option<Int> = some(1)\nlet item ?= option\nitem")
   "E-RET-002"))

(test-case "[REQ: RET-001] when arm の関数 row Return は外側関数へ、外では拒否する"
  (for ([scrutinee (in-list '("flag" "get_flag()"))])
    (define prefix (if (string=? scrutinee "flag") ""
                       "fn get_flag() -> Bool { return true }\n"))
    (define source
      (string-append
       prefix "fn f(flag: Bool) -> Int {\n"
       "  let g = when " scrutinee " {\n"
       "    true => fn() ! Return => 0\n"
       "    false => fn() ! Return => 1\n"
       "  }\n  return 2\n}\nf(true)"))
    (define result (compile-ok source))
    (define target-boundary
      (if (string=? scrutinee "flag") 'boundary0 'boundary1))
    (define local-boundary
      (if (string=? scrutinee "flag") 'boundary1 'boundary2))
    (check-equal? (compiled-type result) 'Int)
    (check-equal? (run-value result) 2)
    (check-true
     (contains-tree? (compiled-core result)
                     `(NFn () Int () ((Return ,target-boundary Int)) () User)))
    (check-false
     (contains-tree? (compiled-core result)
                     `(NFn () Int () ((Return ,local-boundary Int)) () User))))
  (check-equal? (code "fn() ! Return => 0") "E-RET-001"))

(test-case "[REQ: RET-001] if 条件と when scrutinee の return は関数へ届く"
  (check-equal?
   (run-value
    (compile-ok
     "fn identity(x: Bool) -> Bool { return x }\nfn f() -> Int { let ignored = if identity(return 7) { true } else { false }\n return 8 }\nf()"))
   7)
  (check-equal?
   (run-value
    (compile-ok
     "fn identity(x: Bool) -> Bool { return x }\nfn f() -> Int { let ignored = when identity(return 9) { true => 1\n false => 2 }\n return 8 }\nf()"))
   9))

(test-case "[REQ: RET-001, RET-002] outer return の枝は候補にならず合成と検査を区別する"
  (for ([scrutinee (in-list '("flag" "get_flag()"))])
    (define variable? (string=? scrutinee "flag"))
    (define prefix (if variable? "" "fn get_flag() -> Bool { return true }\n"))
    (define parameters (if variable? "flag: Bool" ""))
    (define arguments (if variable? "true" ""))
    (define arms
      (string-append "when " scrutinee " {\n"
                     "    true => { return 1 }\n"
                     "    false => { return 2 }\n"
                     "  }"))
    (check-equal?
     (code (string-append prefix "fn f(" parameters ") -> Int { let answer = "
                         arms "\n return 3 }\nf(" arguments ")"))
     "E-TYP-010")
    (define checked
      (compile-ok
       (string-append prefix "fn f(" parameters ") -> Int { let answer: Int = "
                      arms "\n return 3 }\nf(" arguments ")")))
    (check-equal? (compiled-type checked) 'Int)
    (check-equal? (run-value checked) 1)))

(test-case "[REQ: RET-001, RET-002] 一部だけ return する when も脱出枝を合成候補から除外する"
  (for ([scrutinee (in-list '("flag" "get_flag()"))])
    (define variable? (string=? scrutinee "flag"))
    (define prefix (if variable? ""
                       "fn get_flag() -> Bool { return true }\n"))
    (define source
      (string-append
       prefix
       "fn f(" (if variable? "flag: Bool" "") ") -> Int {\n"
       "  let answer: Bool = when " scrutinee " {\n"
       "    true => return 1\n"
       "    false => false\n"
       "  }\n"
       "  if answer { return 2 } else { return 3 }\n"
       "}\nf(" (if variable? "true" "") ")"))
    (define synth-source
      (string-replace source "let answer: Bool = when" "let answer = when"))
    (if variable?
        (let ([inferred (compile-ok synth-source)])
          (check-equal? (run-value inferred) 1)
          (check-equal?
           (run-value (compile-ok (string-replace synth-source "f(true)" "f(false)")))
           3))
        (check-equal? (code synth-source) "E-TYP-010"))
    (define true-result (compile-ok source))
    (check-equal? (compiled-type true-result) 'Int)
    (check-equal? (run-value true-result) 1)
    (when variable?
      (define false-result (compile-ok (string-replace source "f(true)" "f(false)")))
      (check-equal? (run-value false-result) 3))))

(test-case "[REQ: RET-001] Loop の row は Return と Leave を別境界へ解決する"
  (for ([flag (in-list '(true false))] [expected (in-list '(1 12))])
    (define expression
      `(Apply
        (Fn ((flag Bool)) Int ()
          (Let (answer const Int)
               (NarrativeExpr
                (Loop loop () Int (Return Leave)
                  (Eliminate flag
                    ((true () -> (Return 1))
                     (false () -> (Leave 2))))
                  ()))
            (Return (Apply add answer 10))))
        (Construct ,flag (Types))))
    (match (elab expression)
      [(list core type row callables)
       (check-equal? type 'Int)
       (check-equal? (core-type-of core '() callables) (list type row))
       (define handlers (return-handler-boundaries core))
       (define function-boundary (first handlers))
       (define expression-boundary (second handlers))
       (check-equal? function-boundary 'boundary0)
       (check-equal? expression-boundary 'boundary1)
       (check-equal? (literal-return-boundary core 1) function-boundary)
       (check-equal? (literal-return-boundary core 2) expression-boundary)
       (define boundaries (return-boundaries core))
       (check-not-false (member function-boundary boundaries))
       (check-not-false (member expression-boundary boundaries))
       (define start (inject-g2m (erase-core core)))
       (define-values (configs _rules) (run-configs start callables type))
       (check-configs configs callables type)
       (check-equal? (config-control (last configs)) expected)]
      [other (fail-check (format "Loop を elaborate できなかった: ~s" other))])))

(test-case "[REQ: RET-001, RET-002] Owned の return と leave は Scope token を一度だけ移送または破棄する"
  (define option-owned '(Option (Owned Res)))
  (define acquire-callables
    '((consume-unit
       (NFn ((Option (Owned Res)) Unit) Unit () () () User))
      (consume-return
       (NFn ((Option (Owned Res)) (Option (Owned Res)))
            (Option (Owned Res)) () (Own) () User))))
  (define (owned-option n)
    `(Construct ,option-owned some
                (OwnLeaf (Apply (PrimVal (Reserved o-acquire) acquire) ,n))))
  (define consumer-unit
    `(Lam User consume-unit (raw later)
       (Handle (Return unit-boundary Unit) (returned -> returned)
         (Scope () (Let (transferred let ,option-owned) raw unit)))))
  (define consumer-return
    `(Lam User consume-return (raw later)
       (Handle (Return function-boundary ,option-owned) (returned -> returned)
         (Scope ()
           (Let (first let ,option-owned) raw
             (Let (second let ,option-owned) later (Move first)))))))
  (define return-core
    `(Handle (Return function-boundary ,option-owned) (returned -> returned)
       (Scope ()
         (Apply ,consumer-return ,(owned-option 47)
                (Perform (Return function-boundary ,option-owned)
                         ,(owned-option 53))))))
  (define leave-core
    `(Handle (Return function-boundary ,option-owned) (returned -> returned)
       (Handle (Return expression-boundary ,option-owned) (left -> left)
         (Scope ()
           (Apply ,consumer-unit ,(owned-option 59)
                  (Perform (Return expression-boundary ,option-owned)
                    (Construct ,option-owned none)))))))
  (check-equal? (core-type-of return-core '() acquire-callables)
                `(,option-owned (Own)))
  (check-equal? (core-type-of leave-core '() acquire-callables)
                `(,option-owned ()))
  (define-values (return-configs return-rules)
    (trace-core return-core acquire-callables option-owned))
  (define-values (leave-configs leave-rules)
    (trace-core leave-core acquire-callables option-owned))
  (check-not-false (member 'R-ScopeAbort return-rules))
  (check-not-false (member 'R-ScopeAbort leave-rules))
  (define return-final (last return-configs))
  (define return-value (config-control return-final))
  (check-equal? (length (collect-tokens return-value)) 1)
  (check-equal? (map second (config-tokens return-final)) '(Dropped Available))
  (define leave-final (last leave-configs))
  (check-equal? (config-control leave-final) `(Construct ,option-owned none))
  (check-equal? (map second (config-tokens leave-final)) '(Dropped)))

(test-case "[REQ: RET-001, RET-002] ?= の失敗枝は途中の式境界を越えて関数へ戻り Scope を cleanup する"
  ;; TryBind の失敗枝の Return が式境界を飛び越えて関数境界へ届く Core を trace する。
  (define expression
    '(Handle (Return function-boundary (Option Int)) (returned -> returned)
       (Scope ()
         (Let (held let (Owned Res))
              (Apply (PrimVal (Reserved o-acquire) acquire) 2)
           (Handle (Return expression-boundary (Option Int)) (local -> local)
             (Eliminate (Construct (Option Int) none)
               ((some (item) -> (Construct (Option Int) some item))
                (none () ->
                (Perform (Return function-boundary (Option Int))
                    (Construct (Option Int) none))))))))))
  (check-equal? (core-type-of expression '() '()) '((Option Int) ()))
  (define-values (configs rules) (trace-core expression '() '(Option Int)))
  (check-not-false (member 'R-HandleSkip rules))
  (check-not-false (member 'R-ScopeAbort rules))
  (check-equal? (config-control (last configs)) '(Construct (Option Int) none))
  (check-equal? (map second (config-tokens (last configs))) '(Dropped))
  (check-equal? (length (config-tokens (last configs))) 1))

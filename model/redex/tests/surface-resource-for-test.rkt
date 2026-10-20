#lang racket

(require rackunit
         racket/list
         racket/match
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (compile source)
  (compile-source/string 'src source))

(define (trace-compiled result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (λ ()
     (define run
       (bounded-trace-g2
        (inject-g2m (erase-core (compiled-execution-core result)))
        10000))
     (check-equal? (execution-outcome run) 'terminal)
     (define configurations (execution-configs run))
     (for ([configuration (in-list configurations)] [index (in-naturals)])
       (define row
         (runtime-row configuration (compiled-callables result)
                      (compiled-type result)))
       (check-not-false row (format "config ~a に runtime-row がある" index))
       (check-true
        (and row (config-ok? configuration (compiled-callables result)
                              (compiled-type result) row))
        (format "config ~a が config-ok? を満たす" index)))
     configurations)))

(define (trace-surface source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a" (diagnostic-id result))
                  "compiled result expected"))
  (and (compiled? result) (trace-compiled result)))

(define (check-accepted source expected-type expected-value)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compile failed with ~a" (diagnostic-id result))
                  "compiled result expected"))
  (when (compiled? result)
    (check-equal? (compiled-type result) expected-type)
    (define configurations (trace-compiled result))
    (match (last configurations)
      [`(cfg ,value ,_heap ,_states ,_tokens ,_events)
       (check-equal? value expected-value)]
      [other (fail-check (format "terminal config expected, got ~s" other))])
    configurations))

(define (check-rejected source expected-id)
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)))

(define (config-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (config-value configuration)
  (match configuration [`(cfg ,value ,_ ,_ ,_ ,_) value]))

(define (fin-events configuration)
  (filter (λ (event) (match event [`(fin ,_) #t] [_ #f]))
          (match configuration [`(cfg ,_ ,_ ,_ ,_ ,events) events])))

(define (token-state configuration token)
  (define entry (assoc token (config-tokens configuration)))
  (and entry (second entry)))

(define (check-terminal-ledger configurations expected-token-count [carried '()])
  (define terminal (last configurations))
  (define tokens (config-tokens terminal))
  (check-equal? (length tokens) expected-token-count)
  (for ([entry (in-list tokens)])
    (check-equal? (second entry)
                  (if (member (first entry) carried) 'Available 'Dropped)))
  (define drops
    (append*
     (for/list ([before (in-list configurations)]
                [after (in-list (cdr configurations))])
       (for/list ([entry (in-list (config-tokens after))]
                  #:when (and (eq? (second entry) 'Dropped)
                              (eq? (token-state before (first entry)) 'Available)))
         (first entry)))))
  (for ([entry (in-list tokens)]
        #:unless (member (first entry) carried))
    (define token-drops
      (filter (λ (drop) (equal? drop (first entry))) drops))
    (check-equal? (length token-drops) 1
                  (format "~s は Available から Dropped へ一度だけ遷移する"
                          (first entry)))))

(test-case "S1 Res を型注釈に書けて資源 List を注釈つき let で作れる"
  (define source
    "let xs: List<Owned<Res>> = cons(acquire(1), cons(acquire(2), nil()))\n()")
  (define configurations (check-accepted source 'Unit 'unit))
  (check-terminal-ledger configurations 2 '()))

(test-case "S2 利用者による Res の宣言は予約名の衝突として拒否する"
  (check-rejected "type Res = Int\n()" "E-SUR-011")
  (check-rejected "trait Res { }\n()" "E-SUR-023")
  (check-rejected "type Res =\n  | mk\n()" "E-SUR-028"))

(define mk
  (string-append
   "fn mk() -> List<Owned<Res>> ! Own { return cons(acquire(1), cons(acquire(2), nil())) }\n"))

(test-case "S3 本体が要素を使わずに正常完了すると全 token が一度だけ drop される"
  (define source
    (string-append mk
                   "fn f() -> Unit ! {Own, Partial} { for x in mk() { () }\n () }\n"
                   "f()"))
  (define configs (check-accepted source 'Unit 'unit))
  (check-terminal-ledger configs 4))

(test-case "S4 return と leave の早期脱出で全 token が一度だけ drop される"
  (define returned
    (string-append mk
                   "fn f() -> Int ! {Own, Partial} { for x in mk() { return 7 }\n return 0 }\n"
                   "f()"))
  (define return-configs (check-accepted returned 'Int 7))
  (check-terminal-ledger return-configs 3)
  (define left
    (string-append mk
                   "fn f() -> Option<Int> ! {Own, Partial} {\n"
                   " return for x in mk() { leave 7 }\n}\nf()"))
  (define leave-configs
    (check-accepted left '(Option Int) '(Construct (Option Int) some 7)))
  (check-terminal-ledger leave-configs 3))

(test-case "S5 式位置 for の leave acquire は資源 token を値へ移送する"
  (define source
    (string-append mk
                   "fn f() -> Option<Owned<Res>> ! {Own, Partial} {\n"
                   " return for x in mk() { leave acquire(9) }\n}\nf()"))
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result) (diagnostic-id result)
                  "compiled result expected"))
  (when (compiled? result)
    (check-equal? (compiled-type result) '(Option (Owned Res)))
    (define configs (trace-compiled result))
    (define terminal (last configs))
    (check-true
     (match (config-value terminal)
       [`(Construct (Option (Owned Res)) some (OwnedLeaf ,_ (resource 9))) #t]
       [_ #f]))
    (define carried (collect-tokens (config-value terminal)))
    (check-equal? (length carried) 1)
    (check-terminal-ledger configs 4 carried)))

(test-case "S6 入れ子 for の内側から外側の式境界へ leave する"
  (define source
    (string-append mk
                   "fn f() -> Option<Int> ! {Own, Partial} {\n"
                   " return for x in mk() { for y in mk() { leave 7 }\n () }\n"
                   "}\nf()"))
  (define configs
    (check-accepted source '(Option Int) '(Construct (Option Int) some 7)))
  ;; 6 = 2 回の mk() の acquire token 4 個 + 各回の head Move で作る root token 2 個。
  (check-terminal-ledger configs 6))

(test-case "S7 資源型の変数を反復対象にする for は E-OWN-010"
  (check-rejected
   (string-append mk
                  "fn f() -> Unit ! {Own, Partial} { let xs: List<Owned<Res>> = mk()\n"
                  " for x in xs { () }\n () }\nf()")
   "E-OWN-010"))

(test-case "S8 正常完了時の fin は反復順に出る"
  (define source
    (string-append mk
                   "fn f() -> Unit ! {Own, Partial} { for x in mk() { () }\n () }\n"
                   "f()"))
  (define configs (check-accepted source 'Unit 'unit))
  (define terminal (last configs))
  (check-terminal-ledger configs 4)
  (check-equal? (fin-events terminal)
                '((fin 4) (fin 8))))

(test-case "S9 非資源 List の for に Move を追加しない"
  (define result
    (compile "fn f(xs: List<Int>) -> Unit { for x in xs { () }\n () }\nf(cons(1, nil))"))
  (define resource-result
    (compile
     (string-append mk
                    "fn f() -> Unit ! {Own, Partial} { for x in mk() { () }\n () }\nf()")))
  (define (has-generated-move? term)
    (match term
      [`(Move ,place)
       (or (match place
             [(? symbol? name)
              (regexp-match? #px"^%for-(list|tail|rest)" (symbol->string name))]
             [_ #f])
           (has-generated-move? place))]
      [(? pair? parts) (ormap has-generated-move? parts)]
      [_ #f]))
  (check-true (compiled? result))
  (when (compiled? result)
    (check-false
     (has-generated-move? (erase-core (compiled-execution-core result)))))
  (check-true (compiled? resource-result))
  (when (compiled? resource-result)
    (check-true
     (has-generated-move?
      (erase-core (compiled-execution-core resource-result))))))

(test-case "S11 外側の mut accumulator と資源 List for の正常完了・早期脱出"
  (define completed
    (string-append mk
                   "fn f() -> Int ! {Own, Partial, Mutation} {\n"
                   " let mut total = 0\n for x in mk() { total = add(total, 1) }\n"
                   " return total\n}\nf()"))
  (define completed-configs (check-accepted completed 'Int 2))
  (check-terminal-ledger completed-configs 4)
  (define escaped
    (string-append mk
                   "fn f() -> Option<Int> ! {Own, Partial, Mutation} {\n"
                   " let mut total = 0\n"
                   " let answer = for x in mk() { total = add(total, 1)\n leave total }\n"
                   " return answer\n}\nf()"))
  (define escaped-configs
    (check-accepted escaped '(Option Int) '(Construct (Option Int) some 1)))
  (check-terminal-ledger escaped-configs 3))

(test-case "S12 要素型が List<Owned<Res>> の List も各反復で drop する"
  (define mk2
    (string-append
     "fn mk2() -> List<List<Owned<Res>>> ! Own {\n"
     " return cons(cons(acquire(1), nil()), cons(cons(acquire(2), nil()), nil()))\n}\n"))
  (define completed
    (string-append mk2
                   "fn f() -> Unit ! {Own, Partial} { for xs in mk2() { () }\n () }\n"
                   "f()"))
  (define configs (check-accepted completed 'Unit 'unit))
  (check-terminal-ledger configs 2)
  (define terminal-tokens (config-tokens (last configs)))
  (define first-token (first (first terminal-tokens)))
  (define second-token (first (second terminal-tokens)))
  (define (generated-loop-recur-apply? term)
    (match term
      [`(Apply (RecurVal ,_ ,(? symbol? function) ,_ ,_) ,_ ...)
       (string-prefix? (symbol->string function) "%for-loop")]
      [(? pair? parts) (ormap generated-loop-recur-apply? parts)]
      [_ #f]))
  (define before-second-iteration
    (for/first ([configuration (in-list configs)]
                #:when
                (and (match configuration
                       [`(cfg ,control ,_ ...) (generated-loop-recur-apply? control)]
                       [_ #f])
                     (eq? (token-state configuration first-token) 'Dropped)
                     (eq? (token-state configuration second-token) 'Available)))
      configuration))
  (check-not-false before-second-iteration
                   "一要素目は次の再帰反復が進む前に drop 済み")
  (define escaped
    (string-append mk2
                   "fn f() -> Unit ! {Own, Partial} { for xs in mk2() { return () }\n () }\n"
                   "f()"))
  (check-terminal-ledger (check-accepted escaped 'Unit 'unit) 2))

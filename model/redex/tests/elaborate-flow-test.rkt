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

(define (check-config-trace source [required-rules '()])
  (define result (compile-source/string 'src source))
  (check-true (compiled? result)
              (format "compile 成功を期待したが ~s" result))
  (when (compiled? result)
    (call-with-trait-ledger
     (compiled-ledger result)
     (λ ()
       (define initial
         (inject-g2m (erase-core (compiled-execution-core result))))
       (define-values (configs rules)
         (let loop ([current initial] [seen '()] [fuel 10000])
           (when (zero? fuel)
             (error 'check-config-trace "評価 fuel を使い切った: ~s" current))
           (match (raw-steps-g2/named current)
             ['() (values (reverse (cons current seen)) '())]
             [(list (list rule next))
              (define-values (configs rules)
                (loop next (cons current seen) (sub1 fuel)))
              (values configs (cons rule rules))]
             [steps
              (error 'check-config-trace
                     "一意な次状態を期待したが複数ある: ~s" steps)])))
       (for ([rule (in-list required-rules)])
         (check-not-false (member rule rules)
                          (format "trace に ~a があること" rule)))
       (for ([configuration (in-list configs)] [index (in-naturals)])
         (define row
           (runtime-row configuration (compiled-callables result)
                        (compiled-type result)))
         (check-not-false row
                          (format "config ~a の runtime row を期待した: ~s"
                                  index configuration))
         (check-true
          (config-ok? configuration (compiled-callables result)
                      (compiled-type result) row)
          (format "config ~a の保存を期待した: ~s" index configuration)))))))

(define (check-rsd-config-trace source expected)
  (define result (compile-source/string 'src source))
  (check-true (compiled? result)
              (format "compile 成功を期待したが ~s" result))
  (when (compiled? result)
    (check-true
     (regexp-match? #rx"RemainderSafelyDropped"
                    (format "~s" (erase-core (compiled-core result))))
     "elaborated core に RSD があること")
    ;; 全ての中間 config を再型付けする。R-DischargeRemainder の直後も含む。
    (check-config-trace source '(R-DischargeRemainder))
    (check-equal? (run-source source) expected)))

(define (count-form tree wanted)
  (cond
    [(and (pair? tree) (eq? (car tree) wanted))
     (add1 (apply + (map (λ (child) (count-form child wanted)) (cdr tree))))]
    [(pair? tree)
     (apply + (map (λ (child) (count-form child wanted)) tree))]
    [else 0]))

(define (elab-diagnostic-id expression)
  (match (elab expression)
    [(list 'err diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (check-elab-core-typing expression expected-type)
  (match (elab expression)
    [(list core type row callables)
     (check-equal? type expected-type)
     (check-equal? (core-type-of/diagnostic (erase-core core) '() callables)
                   (list type row))]
    [other (fail-check (format "elaboration success expected: ~s" other))]))

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

(test-case "flow-join-type は同値、record、fallback の経路を選ぶ"
  (define union-type '(Union Int String))
  (define-values (union-join union-path)
    (flow-join-type (list union-type union-type) union-type '()))
  (check-equal? union-path 'equiv)
  (check-true (type-equiv? union-join union-type))
  (define-values (record-join record-path)
    (flow-join-type
     '((Record ((id Int imm) (name String imm)))
       (Record ((active Bool imm) (name String imm))))
     '(Record ((name String imm))) '()))
  (check-equal? record-path 'merge)
  (check-true (type-equiv? record-join '(Record ((name String imm)))))
  (define-values (union-fallback union-fallback-path)
    (flow-join-type '(Int String) union-type '()))
  (check-equal? union-fallback-path 'fallback)
  (check-true (type-equiv? union-fallback union-type))
  ;; Owned 欄を合流できない入力で fallback の防御経路を通す。
  (define owned-a '(Record ((f (Owned (Record ((a Int imm)))) imm))))
  (define owned-b '(Record ((f (Owned (Record ((b Int imm)))) imm))))
  (define-values (owned-fallback owned-path)
    (flow-join-type (list owned-a owned-b) '(Record ()) '()))
  (check-equal? owned-path 'fallback)
  (check-true (type-equiv? owned-fallback '(Record ())))
  (check-equal?
   (flow-join-decision (list owned-a owned-b) '(() ()) '(Record ()) '()
                       (λ (_from _to) #f))
   'reassign-type-mismatch))

(test-case "flow-join-type は欄の互換性を T へ補正する"
  (define expected
    '(Record ((f (NFn (Int) Int () (Partial Suspend) () User) imm))))
  (define narrower
    '(Record ((f (NFn (Int) Int () (Partial) () User) imm))))
  (define-values (joined path)
    (flow-join-type (list narrower expected) expected '()))
  (check-equal? path 'merge)
  (check-true (type-equiv? joined expected)))

(test-case "flow-join-type は nested row、Union、optional、可変性を補正する"
  (define cases
    (list
     (list
      '(Record ((data (Record ((name String imm))) imm)))
      '(Record ((data (Record ((left Int imm) (name String imm))) imm)
                (id Int imm)))
      '(Record ((active Bool imm)
                (data (Record ((name String imm) (right Bool imm))) imm)))
      '(Record ((data (Record ((name String imm))) imm))))
     (list
      '(Record ((value (Union Int String) imm)))
      '(Record ((value Int imm)))
      '(Record ((value String imm)))
      '(Record ((value (Union Int String) imm))))
     (list
      '(Record ((age Int imm opt) (name String imm)))
      '(Record ((name String imm)))
      '(Record ((age Int imm opt) (name String imm)))
      '(Record ((age Int imm opt) (name String imm))))
     (list
      '(Record ((count Int imm)))
      '(Record ((count Int mut)))
      '(Record ((count Int imm)))
      '(Record ((count Int imm))))))
  (for ([case (in-list cases)])
    (match-define (list declared left right expected) case)
    (define-values (joined path)
      (flow-join-type (list left right) declared '()))
    (check-equal? path 'merge)
    (check-true (type-equiv? joined expected))))

(test-case "flow-join-decision は pin の同値性と再構成可能性を検査する"
  (define pinned '(Record ((name String imm))))
  (define-values (result _path)
    (flow-join-type (list pinned pinned) pinned '()))
  (check-true (type-equiv? result pinned))
  (check-true
   (type-equiv?
    (flow-join-decision (list pinned pinned) (list '() (list pinned))
                        pinned '() (λ (_from _to) #t)) pinned))
  (check-equal?
   (flow-join-decision
    (list pinned '(Record ((active Bool imm))))
    (list (list pinned) '()) pinned '() (λ (_from _to) #f))
   'reassign-type-mismatch))

(test-case "Eliminate の両方の scrutinee 形で同じ欄を持つ shape が合流する"
  (for ([condition (in-list '("b" "yes(b)"))])
    (define prefix
      (if (string=? condition "b")
          ""
          "fn yes(value: Bool) -> Bool { return value }\n"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       prefix
       "fn f(b: Bool) -> Bool ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  if " condition " { value = { name: \"B\", active: true } } else { value = { name: \"C\", active: false } }\n"
       "  return value.active\n"
       "}\nf(true)"))
    (check-equal? (run-source source) '(Construct Bool true))
    (check-true
     (compiled? (compile-source/string 'src (string-replace source "f(true)" "f(false)"))))
    (check-equal?
     (run-source (string-replace source "f(true)" "f(false)"))
     '(Construct Bool false))))

(test-case "Eliminate の片側 shape 変更は合流後に共有欄だけ公開する"
  (for ([condition (in-list '("b" "yes(b)"))])
    (define prefix
      (if (string=? condition "b")
          ""
          "fn yes(value: Bool) -> Bool { return value }\n"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       prefix
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  if " condition " { value = { name: \"B\" } } else { () }\n"
       "  return value.name\n"
       "}\nf(true)"))
    (define result (compile-source/string 'src source))
    (check-true (compiled? result))
    (when (compiled? result)
      ;; 片側の初期 view だけが join より広く、そこでのみ再構成が要る。
      (check-equal? (count-form (erase-core (compiled-core result)) 'Reassign) 2))
    (check-equal? (run-source source) "B")
    ;; Q-f の未回収経路（view より広い実値）を含む未選択枝は実行しない。
    (when (string=? condition "b") (check-config-trace source))
    (for ([label (in-list '("id" "active"))])
      (define invalid
        (string-replace source "value.name" (format "value.~a" label)))
      (define result (compile-source/string 'src invalid))
      (check-true (diagnostic? result)
                  (format "合流後の value.~a は不明な欄で拒否" label))
      (when (diagnostic? result)
        (check-equal? (diagnostic-id result) "E-RCD-004")))))

(test-case "UnionEliminate の両方の scrutinee 形で shape を合流する"
  (for ([scrutinee (in-list '("choice" "getChoice()"))])
    (define source
      (string-append
       "type Named = { name: String }\n"
       "fn getChoice() -> Int | String { return \"s\" }\n"
       "fn f(choice: Int | String) -> Bool ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  when " scrutinee " {\n"
       "    (number: Int) => { value = { name: \"B\", active: true } }\n"
       "    (text: String) => { value = { name: \"C\", active: false } }\n"
       "  }\n"
       "  return value.active\n"
       "}\nf(1)"))
    (check-equal? (run-source source)
                  (if (string=? scrutinee "choice")
                      '(Construct Bool true)
                      '(Construct Bool false)))
    (when (string=? scrutinee "choice")
      (check-equal?
       (run-source (string-replace source "f(1)" "f(\"s\")"))
       '(Construct Bool false)))))

(test-case "IfSome の両方の condition 形で片側の shape を安全に合流する"
  (for ([condition (in-list '("b" "yes(b)"))])
    (define prefix
      (if (string=? condition "b")
          ""
          "fn yes(value: Bool) -> Bool { return value }\n"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       prefix
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  if " condition " { value = { name: \"B\", active: true } }\n"
       "  return value.name\n"
       "}\nf(true)"))
    (check-equal? (run-source source) "B")
    (check-equal?
     (run-source (string-replace source "f(true)" "f(false)")) "A")))

(test-case "Union slot の枝ごとの member 代入は共通 Union view へ注入する"
  (for ([condition (in-list '("b" "yes(b)"))])
    (define prefix
      (if (string=? condition "b")
          ""
          "fn yes(value: Bool) -> Bool { return value }\n"))
    (define source
      (string-append
       prefix
       "fn f(b: Bool) -> Int ! Mutation {\n"
       "  let mut value: Int | String = 0\n"
       "  if " condition " { value = 1 } else { value = \"s\" }\n"
       "  return when value { (number: Int) => 0\n (text: String) => 1 }\n"
       "}\nf(true)"))
    (check-equal? (run-source source) 0)
    (check-equal?
     (run-source (string-replace source "f(true)" "f(false)")) 1)))

(test-case "全枝 Never の Eliminate は出口 flow を更新せず Return 先で完了する"
  (define source
    (string-append
     "type Named = { name: String }\n"
     "fn f(b: Bool) -> String ! Mutation {\n"
     "  let mut value: Named = { name: \"A\", id: 1 }\n"
     "  if b { value = { name: \"B\", active: true }\n return value.name } else { value = { name: \"C\", active: false }\n return value.name }\n"
     "}\nf(true)"))
  (define result (compile-source/string 'src source))
  (check-true (compiled? result)
              (format "compile 成功を期待したが ~s" result))
  (when (compiled? result)
    (check-equal? (run-source source) "B")
    (check-equal? (run-source (string-replace source "f(true)" "f(false)")) "C")
    (check-equal?
     (count-form (erase-core (compiled-core result)) 'Reassign) 2)))

(test-case "片枝だけの代入でも合流の再構成は宣言 row の Mutation を要する"
  (define source
    (string-append
     "type Named = { name: String }\n"
     "fn f(b: Bool) -> String ! {} {\n"
     "  let mut value: Named = { name: \"A\", id: 1 }\n"
     "  if b { value = { name: \"B\", active: true } } else { () }\n"
     "  return value.name\n"
     "}\nf(true)"))
  (define result (compile-source/string 'src source))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-EFF-002")))

(test-case "局所 Narrative の match 脱出は変数と呼出しの両経路で flow を合流する"
  (for ([scrutinee (in-list '("b" "yes(b)"))])
    (define variable? (string=? scrutinee "b"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       (if variable? "" "fn yes(value: Bool) -> Bool { return value }\n")
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  let ignored = when " scrutinee " {\n"
       "    true => { value = { name: \"B\", active: true }\n leave 1 }\n"
       "    false => { value = { name: \"C\", active: false }\n leave 2 }\n"
       "  }\n"
       "  return value.name\n"
       "}\n"
       "f(true)"))
    (check-equal? (run-source source) "B")
    (check-equal?
     (run-source (string-replace source "f(true)" "f(false)"))
     "C")))

(test-case "局所 Narrative の IfSome 脱出は変数と呼出しの両経路で flow を合流する"
  (for ([condition (in-list '("b" "yes(b)"))])
    (define variable? (string=? condition "b"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       (if variable? "" "fn yes(value: Bool) -> Bool { return value }\n")
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  let ignored: Option<Int> = if " condition " { value = { name: \"B\", active: true }\n leave 1 }\n"
       "  return value.name\n"
       "}\n"
       "f(true)"))
    (check-equal? (run-source source) "B")
    (check-equal?
     (run-source (string-replace source "f(true)" "f(false)"))
     "A")))

(test-case "TryBind の失敗値は関数境界の型で検査する"
  (for* ([scrutinee (in-list '("b" "yes(b)"))]
         [right (in-list '("maybe" "identityOption(maybe)"))])
    (define variable? (string=? scrutinee "b"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       (if variable? "" "fn yes(value: Bool) -> Bool { return value }\n")
       "fn identityOption(value: Option<Int>) -> Option<Int> { return value }\n"
       "fn f(b: Bool, maybe: Option<Int>) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  let answer: Option<String> = when " scrutinee " {\n"
       "    true => { value = { name: \"B\", active: true }\n let picked ?= " right "\n return some(value.name) }\n"
       "    false => { value = { name: \"C\", active: false }\n return some(value.name) }\n"
       "  }\n"
       "  return value.name\n"
       "}\n"
       "f(true, none)"))
    (define result (compile-source/string 'src source))
    (check-true (diagnostic? result))
    (when (diagnostic? result)
      (check-equal? (diagnostic-id result) "E-TYP-033"))))

(test-case "関数境界の早期 Return は正常出口と別の局所 flow を使う"
  (for ([scrutinee (in-list '("b" "yes(b)"))])
    (define variable? (string=? scrutinee "b"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       (if variable? "" "fn yes(value: Bool) -> Bool { return value }\n")
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  when " scrutinee " {\n"
       "    true => { value = { name: \"B\", active: true }\n return value.name }\n"
       "    false => { value = { name: \"C\", active: false } }\n"
       "  }\n"
       "  return value.name\n"
       "}\n"
       "f(true)"))
    (check-equal? (run-source source) "B")
    (check-equal?
     (run-source (string-replace source "f(true)" "f(false)"))
     "C")))

(test-case "Leave payload の評価後に境界の view を再構成する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define expression
      `(Apply
        (Fn ((flag Bool) (g (NFn () Bool () ()))) String (Mutation)
          (Let (value mut (Record ((name String imm))))
               (Rec ((name imm "A") (id imm 1)))
            (Let (answer const Int)
                 (NarrativeExpr
                  (Eliminate ,scrutinee
                    ((true () ->
                       (Leave
                        (Let (tmp const Unit)
                             (Reassign value
                                       (Rec ((name imm "B")
                                             (id imm 2)
                                             (active imm
                                                     (Construct true (Types))))))
                             (Proj value id))))
                     (false () -> (Leave 3)))))
              (Proj value name))))
        (Construct true (Types))
        (Fn () Bool () (Construct true (Types)))))
    (match (elab expression)
      [(list core type row callables)
       (define erased (erase-core core))
       (define (has-form? tree wanted)
         (cond
           [(and (pair? tree) (eq? (car tree) wanted)) #t]
           [(pair? tree)
            (or (has-form? (car tree) wanted)
                (has-form? (cdr tree) wanted))]
           [else #f]))
       (define (payload-before-reassign? tree)
         (or (match tree
               [`(Perform (Return ,_ ,_)
                          (Let (,temporary const ,_) ,payload
                            (Let (,unit-name const Unit)
                              (Reassign ,_ ,_ ,_) ,tail)))
                (and (eq? tail temporary)
                     (has-form? payload 'Reassign))]
               [_ #f])
             (and (pair? tree)
                  (or (payload-before-reassign? (car tree))
                      (payload-before-reassign? (cdr tree))))))
       (check-true (payload-before-reassign? erased)
                   (format "脱出 payload の後に境界 Reassign があること: ~s" erased))
       (check-equal? (core-type-of/diagnostic erased '() callables)
                     (list type row))]
      [other (fail-check (format "elaboration success expected: ~s" other))])))

(test-case "Never の Return payload は脱出 table に登録しない"
  (check-true
   (match (elab '(Fn () Int () (NarrativeExpr (Return (Return 7)))))
     [(list core _ _ _)
      (define (return-with-let-operand? tree)
        (or (match tree
              [`(Perform (Return ,_ ,_) (Let ,_ ,_ ,_)) #t]
              [_ #f])
            (and (pair? tree)
                 (or (return-with-let-operand? (car tree))
                     (return-with-let-operand? (cdr tree))))))
      (not (return-with-let-operand? (erase-core core)))]
     [_ #f])))

(test-case "資源 Leave operand 内で view を再構成して token を一度だけ返す"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define expression
      `(Apply
        (Fn ((flag Bool) (g (NFn () Bool () ())) (payload (Owned Res)))
            (Owned Res) (Mutation Own)
          (Let (value mut (Record ((name String imm))))
               (Rec ((name imm "A") (id imm 1)))
            (NarrativeExpr
             (Eliminate ,scrutinee
               ((true () ->
                  (Let (rebuilt const Unit)
                       (Reassign value
                                 (Rec ((name imm "B")
                                       (id imm 2)
                                       (active imm (Construct true (Types))))))
                (Leave (Move payload))))
                (false () -> (Leave (Move payload))))))))
        (Construct true (Types))
        (Fn () Bool () (Construct true (Types)))
        (Apply acquire 1)))
    (match (elab expression)
      [(list core type row callables)
       (check-equal? type '(Owned Res))
       (check-not-false (member 'Own row))
       (check-not-false (member 'Mutation row))
       (define (resource-return-with-rebuild? tree)
         (or (match tree
               [`(Perform (Return ,_ (Owned Res))
                          (Let (,temporary let (Owned Res)) (Move ,_)
                            (Let (,_ const Unit) (Reassign ,_ ,_ ,_)
                              (Move ,moved))))
                (eq? temporary moved)]
               [_ #f])
             (and (pair? tree)
                  (or (resource-return-with-rebuild? (car tree))
                      (resource-return-with-rebuild? (cdr tree))))))
       (define erased (erase-core core))
       (check-true (resource-return-with-rebuild? erased))
       (define typed (core-type-of/diagnostic erased '() callables))
       (check-equal? typed (list type row))
       (call-with-trait-ledger
        (current-trait-ledger)
        (λ ()
          (define terminal (run-g2 (inject-g2m erased) 10000))
          (match terminal
            [`(cfg ,value ,_heap ,_states ,tokens ,_events)
             (define carried (collect-tokens value))
             (define available
               (filter (λ (entry) (eq? (second entry) 'Available)) tokens))
             (check-equal? (length carried) 1)
             (check-equal? (map first available) carried)]
            [other (fail-check (format "terminal config expected, got ~s" other))])))]
      [other (fail-check (format "UCore elaboration expected, got ~s" other))])))

(test-case "局所 Narrative からの脱出で内側 mut shadow が外側 flow に混ざらない"
  (for ([scrutinee (in-list '("b" "yes(b)"))])
    (define variable? (string=? scrutinee "b"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       (if variable? "" "fn yes(value: Bool) -> Bool { return value }\n")
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut x: Named = { name: \"outer\", id: 1 }\n"
       "  let ignored = when " scrutinee " {\n"
       "    true => { let mut x: Named = { name: \"inner\", id: 2 }\n x = { name: \"changed\", active: true }\n leave true }\n"
       "    false => { leave false }\n"
       "  }\n"
       "  return x.name\n"
       "}\n"
       "f(true)"))
    (check-equal? (run-source source) "outer")
    (check-equal? (run-source (string-replace source "f(true)" "f(false)"))
                  "outer")))

(test-case "synth probe の Return 候補は本番 Narrative flow へ漏れない"
  (for ([scrutinee (in-list '("b" "yes(b)"))])
    (define variable? (string=? scrutinee "b"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       (if variable? "" "fn yes(value: Bool) -> Bool { return value }\n")
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  let ignored = when " scrutinee " {\n"
       "    true => { value = { name: \"B\", active: true }\n leave 1 }\n"
       "    false => 2\n"
       "  }\n"
       "  return value.name\n"
       "}\n"
       "f(true)"))
    (define result (compile-source/string 'src source))
    (check-true (compiled? result)
                (format "compile expected, got ~s" result))
    (when (compiled? result)
      (check-equal? (count-form (erase-core (compiled-core result)) 'Perform)
                    (+ 2 (if variable? 0 1)))
      (check-equal? (run-source source) "B")
      (check-equal?
       (run-source (string-replace source "f(true)" "f(false)"))
       "A"))))

(test-case "Never で τ° を持つ Leave payload は脱出として登録しない"
  ;; Return は Never だが、T-Ctx-Never の τ° は通常型を保つ。
  (define (escaping-branch name active)
    `(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm ,name)
                          (active imm (Construct ,(if active 'true 'false)
                                                 (Types))))))
       (Leave (Return (Construct ,(if active 'true 'false) (Types))))))
  (define normal-branch
    '(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm "C")
                          (active imm (Construct false (Types))))))
       (Construct false (Types))))
  (for ([scrutinee (in-list (list 'flag '(Apply g)))])
    (define expression
      `(Apply
        (Fn ((flag Bool) (g (NFn () Bool () ()))) Bool (Mutation)
          (Let (value mut (Record ((name String imm))))
               (Rec ((name imm "A") (id imm 1)))
            (Let (ignored const Bool)
                 (NarrativeExpr
                  (Eliminate ,scrutinee
                    ((true () -> ,(escaping-branch "B" #t))
                     (false () -> ,normal-branch))))
              (Proj value active))))
        (Construct true (Types))
        (Fn () Bool () (Construct true (Types)))))
    (match (elab expression)
      [(list core type row callables)
       (define erased (erase-core core))
       (check-equal? type 'Bool)
       (check-not-false (member 'Mutation row))
       ;; payload 内の Return は関数境界へ届き、外側 Leave は記録しない。
       (check-equal? (count-form erased 'Perform) 2)
       (check-equal? (core-type-of/diagnostic erased '() callables)
                     (list type row))]
      [other (fail-check (format "elaboration success expected: ~s" other))])))

(define pinned-name-type '(Record ((name String imm))))
(define pinned-name-id-type '(Record ((id Int imm) (name String imm))))
(define pinned-name-initial '(Rec ((name imm "A") (id imm 1))))
(define pinned-name-active
  '(Rec ((active imm (Construct true (Types))) (name imm "B"))))
(define pinned-name-id-active
  '(Rec ((active imm (Construct true (Types))) (id imm 2) (name imm "B"))))

(test-case "closure 後の再代入は pin と一致する view へ再構成できる"
  (for ([right-hand-side
         (in-list
          (list
           '(Rec ((name imm "B") (id imm 2)))
           pinned-name-id-active))])
    (define expression
      `(Let (value mut ,pinned-name-type) ,pinned-name-initial
         (Let (saved const (NFn () Int () ()))
              (Fn () Int () (Proj value id))
           (Let (changed const Unit)
                (Reassign value ,right-hand-side)
             (Proj value id)))))
    (check-elab-core-typing expression 'Int)))

(test-case "closure pin に P の欄が欠けるか欄型が違う右辺は拒否する"
  (define missing-field
    `(Let (value mut ,pinned-name-type) ,pinned-name-initial
       (Let (saved const (NFn () Int () ()))
            (Fn () Int () (Proj value id))
         (Let (changed const Unit)
              (Reassign value ,pinned-name-active)
           (Proj value name)))))
  (define wrong-field-type
    '(Let (value mut (Record ((name String imm))))
          (Rec ((name imm "A") (id imm 1)))
       (Let (saved const (NFn () Int () ()))
            (Fn () Int () (Proj value id))
         (Let (changed const Unit)
              (Reassign value (Rec ((name imm "B") (id imm "x"))))
           (Proj value name)))))
  (check-equal? (elab-diagnostic-id missing-field) "E-VAR-013")
  (check-equal? (elab-diagnostic-id wrong-field-type) "E-VAR-013"))

(test-case "closure pin の枝合流は同じ pin を保ち、片側の pin も引き継ぐ"
  (define function-type '(NFn () String () ()))
  (define (branch-expression scrutinee true-branch false-branch)
    `(Apply
      (Fn ((flag Bool) (g (NFn () Bool () ()))) String (Mutation)
        (Let (value mut ,pinned-name-type) ,pinned-name-initial
          (Let (saved const ,function-type)
               (Eliminate ,scrutinee
                 ((true () -> ,true-branch)
                  (false () -> ,false-branch)))
            (Proj value name))))
      (Construct true (Types))
      (Fn () Bool () (Construct true (Types)))))
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define captures-value '(Fn () String () (Proj value name)))
    (define no-capture '(Fn () String () "constant"))
    (check-elab-core-typing
     (branch-expression scrutinee captures-value no-capture) 'String)
    (check-elab-core-typing
     (branch-expression scrutinee captures-value captures-value) 'String)))

(test-case "異なる closure pin と pin へ作り直せない枝は枝合流で拒否する"
  (define function-type '(NFn () String () ()))
  (define (branch-expression scrutinee true-branch false-branch)
    `(Apply
      (Fn ((flag Bool) (g (NFn () Bool () ()))) String (Mutation)
        (Let (value mut ,pinned-name-type) ,pinned-name-initial
          (Let (saved const ,function-type)
               (Eliminate ,scrutinee
                 ((true () -> ,true-branch)
                  (false () -> ,false-branch)))
            (Proj value name))))
      (Construct true (Types))
      (Fn () Bool () (Construct true (Types)))))
  (define (assign-then-closure rhs)
    `(Let (changed const Unit) (Reassign value ,rhs)
       (Fn () String () (Proj value name))))
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define no-pin-branch
      `(Apply
        (Fn ((flag Bool) (g (NFn () Bool () ()))) String (Mutation)
          (Let (value mut ,pinned-name-type) ,pinned-name-initial
            (Let (result const String)
                 (Eliminate ,scrutinee
                   ((true () ->
                      (Let (saved const (NFn () Int () ()))
                           (Fn () Int () (Proj value id))
                        "captured"))
                    (false () ->
                      (Let (changed const Unit)
                           (Reassign value ,pinned-name-active)
                        "not captured"))))
              (Proj value name))))
        (Construct true (Types))
        (Fn () Bool () (Construct true (Types)))))
    (check-equal?
     (elab-diagnostic-id
      (branch-expression
       scrutinee
       (assign-then-closure pinned-name-id-active)
       (assign-then-closure
        '(Rec ((enabled imm (Construct true (Types))) (id imm 3) (name imm "C"))))))
     "E-VAR-013")
    (check-equal?
     (elab-diagnostic-id
      (branch-expression
       scrutinee
       '(Fn () String () (Proj value name))
       (assign-then-closure pinned-name-active)))
     "E-VAR-013")
    (check-equal? (elab-diagnostic-id no-pin-branch) "E-VAR-013")))

(test-case "closure 本体は pin view で再代入し、内部 flow を外へ漏らさない"
  (define expression
    `(Let (value mut ,pinned-name-type) ,pinned-name-initial
       (Let (saved const (NFn () Int (Mutation) ()))
            (Fn () Int (Mutation)
                (Let (changed const Unit)
                     (Reassign value ,pinned-name-id-active)
                  (Proj value id)))
         (Proj value active))))
  (check-equal? (elab-diagnostic-id expression) "E-RCD-004"))

(test-case "pin 入口の RSD 後の再代入は変数・呼出し scrutinee の両方で保たれる"
  (for ([condition (in-list '("flag" "g()"))])
    (define prefix
      (if (string=? condition "flag")
          ""
          "fn g() -> Bool { return true }\n"))
    (define source
      (string-append
       prefix
       "fn f(flag: Bool) -> Int ! Mutation {\n"
       "  let mut value: { name: String } = { name: \"A\", id: 1 }\n"
       "  let reader = fn() => value.id\n"
       "  if " condition " { value = { name: \"B\", id: 2, active: true } } else { () }\n"
       "  return reader()\n"
       "}\nf(true)"))
    (check-rsd-config-trace source 2)))

(test-case "join 入口の RSD 後の再代入は変数・呼出し scrutinee の両方で保たれる"
  (for ([condition (in-list '("flag" "g()"))])
    (define prefix
      (if (string=? condition "flag")
          ""
          "fn g() -> Bool { return true }\n"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       prefix
       "fn f(flag: Bool) -> Int ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  if " condition " { value = { name: \"B\", id: 2, active: true } } else { () }\n"
       "  return value.id\n"
       "}\nf(true)"))
    (check-rsd-config-trace source 2)))

(test-case "escape 入口の RSD 後の再代入は変数・呼出し scrutinee の両方で保たれる"
  (for ([condition (in-list '("flag" "g()"))])
    (define prefix
      (if (string=? condition "flag")
          ""
          "fn g() -> Bool { return true }\n"))
    (define source
      (string-append
       "type Named = { name: String }\n"
       prefix
       "fn f(flag: Bool) -> String ! Mutation {\n"
       "  let mut value: Named = { name: \"A\", id: 1 }\n"
       "  let answer: Option<String> = when " condition " {\n"
       "    true => { value = { name: \"B\", id: 2, active: true }\n"
       "                leave some(value.name) }\n"
       "    false => { leave some(value.name) }\n"
       "  }\n"
       "  return value.name\n"
       "}\nf(true)"))
    (check-rsd-config-trace source "B")))

(test-case "Recur と FnDecl は捕捉時に pin し、呼出しの row と flow を保つ"
  (for ([constructor (in-list '(Recur FnDecl))])
    (define expression
      `(Let (value mut ,pinned-name-type) ,pinned-name-initial
         (,constructor loop () Int (Mutation)
           (Let (changed const Unit)
                (Reassign value ,pinned-name-id-active)
             (Proj value id))
           (Let (changed const Unit)
                (Reassign value ,pinned-name-id-active)
             (Apply loop)))))
    (match (elab expression)
      [(list core type row callables)
       (check-equal? type 'Int)
       (check-equal? row '(Mutation))
       (check-equal? (find-reassign-view (erase-core core))
                     pinned-name-id-type)
       (check-equal? (core-type-of/diagnostic (erase-core core) '() callables)
                     (list type row))]
      [other (fail-check (format "Recur の elaboration success expected: ~s" other))])))

(test-case "Curry の固定引数は mut binder を pin しない"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define expression
      `(Apply
        (Fn ((flag Bool) (g (NFn () Bool () ()))) Bool (Mutation)
          (Let (value mut ,pinned-name-type) ,pinned-name-initial
            (Let (saved const (NFn (Bool) Int () ()))
                 (Curry
                  (Fn ((captured ,pinned-name-id-type) (unused Bool)) Int ()
                      (Proj captured id))
                  value)
              (Eliminate ,scrutinee
                ((true () ->
                   (Let (changed const Unit)
                        (Reassign value ,pinned-name-active)
                     (Proj value active)))
                 (false () ->
                   (Let (changed const Unit)
                        (Reassign value ,pinned-name-active)
                     (Proj value active))))))))
        (Construct true (Types))
        (Fn () Bool () (Construct true (Types)))))
    (check-elab-core-typing expression 'Bool)))

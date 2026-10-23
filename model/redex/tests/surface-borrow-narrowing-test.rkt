#lang racket

(require rackunit
         racket/list
         racket/match
         "../borrow.rkt"
         "../compat.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../elaborate.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../ownership.rkt"
         "../region.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))

(define (source-span source needle [occurrence 0])
  (match (list-ref (regexp-match-positions* (regexp (regexp-quote needle)) source)
                   occurrence)
    [(cons start end) `(#:span src ,start ,end)]))

(define (compile-accepted source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "compiled source expected, got ~a at ~s"
                          (diagnostic-id result)
                          (diagnostic-primary-span result))
                  (format "unexpected result: ~s" result)))
  result)

(define (compile-rejected source expected-id needle [occurrence 0])
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)
    (check-equal? (diagnostic-primary-span result)
                  (source-span source needle occurrence)))
  (void))

(define (count-form tree wanted)
  (if (pair? tree)
      (+ (if (eq? (car tree) wanted) 1 0)
         (for/sum ([part (in-list tree)]) (count-form part wanted)))
      0))

(define (trace-compiled result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (define trace
       (bounded-trace-g2
        (inject-g2m (erase-core (compiled-execution-core result)))
        10000))
     (check-equal? (execution-outcome trace) 'terminal)
     (for ([config (in-list (execution-configs trace))] [index (in-naturals)])
       (define row
         (runtime-row config (compiled-callables result) (compiled-type result)))
       (check-not-false row (format "config ~a has runtime-row" index))
       (when row
         (check-true
          (config-ok? config (compiled-callables result) (compiled-type result) row)
          (format "config ~a passes config-ok?" index))))
     (execution-configs trace))))

(define (trace-value result)
  (match (last (trace-compiled result))
    [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
    [other (fail-check (format "terminal config expected, got ~s" other))]))

(test-case "借用の欄を落とす幅の narrowing は RSD を一つ挿入して受理する"
  (define result
    (compile-accepted
     (string-append
      "let x: Owned<Int> = 1\n"
      "let y: Owned<Int> = 2\n"
      "let bx = &x\n"
      "let by = &y\n"
      "let r: {a: &Int} = {a: bx, b: by}\n"
      "deref(r.a)")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-equal? (trace-value result) 1)))

(test-case "identity-conversion? は借用残余の narrowing を恒等扱いしない"
  (define actual
    '(Record ((a Int imm)
              (b (Borrowed Int (RParam %omitted)) imm))))
  (define expected '(Record ((a Int imm))))
  (check-true (compat? actual expected))
  (check-match (borrow-hiding-kind/for-elaboration actual expected compat?)
    `(drop-obligation ,_ ,_))
  ;; Surface の let/if/when/reassign probe はすべて RSD を挿入したため、直接の判定契約を固定する。
  (check-false (identity-conversion? actual expected '() '())))

(test-case "if の一方だけにある借用残余を merge で RSD し実行する"
  (define result
    (compile-accepted
     (string-append
      "let owner: Owned<Int> = 41\n"
      "let borrowed = &owner\n"
      "let result = if true { {a: 1, b: borrowed} } else { {a: 2} }\n"
      "result.a")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-equal? (trace-value result) 1)))

(test-case "when の一方だけにある借用残余を decompose で RSD し実行する"
  (define result
    (compile-accepted
     (string-append
      "let owner: Owned<Int> = 41\n"
      "let borrowed = &owner\n"
      "let condition: Option<Bool> = some(true)\n"
      "let result = when condition { some flag => {a: 1, b: borrowed}\n"
      " none => {a: 2} }\n"
      "result.a")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-equal? (trace-value result) 1)))

(test-case "再代入の narrowing は RSD を挿入し借用を隠さない"
  (define result
    (compile-accepted
     (string-append
      "let owner: Owned<Int> = 41\n"
      "let borrowed = &owner\n"
      "let mut result: {a: Int} = {a: 0}\n"
      "result = {a: 2, b: borrowed}\n"
      "result.a")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-equal? (trace-value result) 2)))

(test-case "reassign-narrowing? は借用残余を除く Record 対を通さない"
  (define actual
    '(Record ((a Int imm)
              (b (Borrowed Int (RParam %omitted)) imm))))
  (define expected '(Record ((a Int imm))))
  (check-false (reassign-narrowing? actual expected))
  (check-match (borrow-hiding-kind actual expected compat?)
    `(drop-obligation ,_ ,_)))

(test-case "借用型の mut slot は再代入 flow より先に E-VAR-012 で拒否する"
  (define source
    (string-append
     "let owner: Owned<Int> = 41\n"
     "let borrowed = &owner\n"
     "let mut result: {a: Int, b: &Int} = {a: 1, b: borrowed}\n"
     "result = {a: 2, b: borrowed}\n"
     "0"))
  (compile-rejected source "E-VAR-012"
                   (string-append
                    "let mut result: {a: Int, b: &Int} = {a: 1, b: borrowed}\n"
                    "result = {a: 2, b: borrowed}\n"
                    "0")))

(test-case "if merge の不適格な借用残余は E-TYP-012 と operand span を保つ"
  (define source
    (string-append
     "let owner: Owned<Int> = 7\n"
     "let borrowed = &owner\n"
     "let broad: Option<{a: Int, b: &Int}> = some({a: 1, b: borrowed})\n"
     "let narrow: {u: Option<{a: Int}>} = if true { {u: broad} } else { {u: some({a: 2})} }\n"
     "0"))
  (compile-rejected source "E-TYP-012" "broad" 1))

(test-case "when decompose の不適格な借用残余は E-TYP-012 と operand span を保つ"
  (define source
    (string-append
     "let owner: Owned<Int> = 7\n"
     "let borrowed = &owner\n"
     "let broad: Option<{a: Int, b: &Int}> = some({a: 1, b: borrowed})\n"
     "let condition: Option<Bool> = some(true)\n"
     "let narrow: {u: Option<{a: Int}>} = when condition { some flag => {u: broad}\n"
     " none => {u: some({a: 2})} }\n"
     "0"))
  (compile-rejected source "E-TYP-012" "broad" 1))

(test-case "check-against-expected は借用残余だけを RSD で除き非借用欄を保つ"
  (define result
    (compile-accepted
     (string-append
      "let x: Owned<Int> = 1\n"
      "let bx = &x\n"
      "let r: {a: Int} = {a: 1, b: bx, c: 2}\n"
      "r")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-match (trace-value result)
      `(Rec ((a imm 1) (c imm 2))))))

(test-case "Construct の check は適格な借用残余に RSD を入れて実行する"
  (define result
    (compile-accepted
     (string-append
      "let owner: Owned<Int> = 1\n"
      "let bx = &owner\n"
      "let boxed: Option<{a: Int}> = some({a: 1, b: bx})\n"
      "when boxed { some r => r.a\n none => 0 }")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-equal? (trace-value result) 1)))

(test-case "Core の期待型 argument check は borrow-reject を E-BOR-027 と span で返す"
  (define wide
    '(Untrusted (Record ((a Int imm) (b (Borrowed Int 0) imm)))))
  (define narrow '(Untrusted (Record ((a Int imm)))))
  (define function-type `(NFn (,narrow) Unit () () () User))
  (define function-span '(#:var consume (#:span src 0 7)))
  (define argument-span '(#:var p (#:span src 8 9)))
  (define result
    (core-type-of/regions
     `(Apply (#:span src 0 9) ,function-span ,argument-span)
     '() `((consume ,function-type))
     `((consume ,function-type) (p ,wide))))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-027")
    (check-equal? (diagnostic-primary-span result) '(#:span src 8 9))))

(test-case "Core の Construct check は borrow-reject を E-BOR-027 と payload span で返す"
  (define wide
    '(Untrusted (Record ((a Int imm) (b (Borrowed Int 0) imm)))))
  (define narrow '(Untrusted (Record ((a Int imm)))))
  (define expected `(Option ,narrow))
  (define node-span '(#:span src 0 5))
  (define payload-span '(#:var p (#:span src 6 7)))
  (define result
    (core-type-of/regions
     `(Construct ,node-span (#:ty ,expected ,node-span) some ,payload-span)
     '() '() `((p ,wide))))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-027")
    (check-equal? (diagnostic-primary-span result) '(#:span src 6 7))))

(test-case "Return payload の check-against-expected は適格な借用残余を RSD で除く"
  (define result
    (compile-accepted
     (string-append
      "fn f() -> {a: Int} {\n"
      " let x: Owned<Int> = 1\n"
      " let bx = &x\n"
      " let broad: {a: Int, b: &Int} = {a: 1, b: bx}\n"
      " return broad\n"
      "}\n"
      "f().a")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-equal? (trace-value result) 1)))

(test-case "Option に包まれた非互換な narrowing は E-TYP-012 と式 span を保つ"
  (define source
    (string-append
     "let x: Owned<Int> = 1\n"
     "let bx = &x\n"
     "let broad: Option<{a: Int, b: &Int}> = some({a: 1, b: bx})\n"
     "let narrow: {u: Option<{a: Int}>} = {u: broad}\n"
     "0"))
  (compile-rejected source "E-TYP-012" "broad" 1))

(test-case "Construct の check で Option 内の非互換な narrowing は E-TYP-012 と span を保つ"
  (define source
    (string-append
     "let x: Owned<Int> = 1\n"
     "let bx = &x\n"
     "let broad: Option<{a: Int, b: &Int}> = some({a: 1, b: bx})\n"
     "let boxed: Option<{u: Option<{a: Int}>}> = some({u: broad})\n"
     "0"))
  (compile-rejected source "E-TYP-012" "broad" 1))

(test-case "mut の注釈付き let は elaborate-mut-compatible-value で RSD を使う"
  (define result
    (compile-accepted
     (string-append
      "let owner: Owned<Int> = 1\n"
      "let bx = &owner\n"
      "let mut r: {a: Int} = {a: 1, b: bx}\n"
      "r.a")))
    (when (compiled? result)
      (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
      (check-equal? (trace-value result) 1)))

(test-case "Surface の関数借用型は convert-adapter-value より前に E-SUR-005 で拒否する"
  (define source "fn f(p: &Int) -> Int { return deref(p) }\n0")
  (compile-rejected source "E-SUR-005" "&"))

(test-case "merge-branches と decompose の narrowing 試行は host error にならない"
  (for ([source
         (in-list
          (list
           (string-append
            "let owner: Owned<Int> = 1\n"
            "let bx = &owner\n"
            "let r: {a: Int} = if true { {a: 1, b: bx} } else { {a: 2, b: bx} }\n"
            "r.a")
           (string-append
            "let owner: Owned<Int> = 1\n"
            "let bx = &owner\n"
            "let wide = if true { {a: 1, b: bx} } else { \"s\" }\n"
            "let narrow: {a: Int} | String = wide\n"
            "0")
           (string-append
            "let owner: Owned<Int> = 1\n"
            "let bx = &owner\n"
            "let wide = if true { {a: 1, b: bx} } else { \"s\" }\n"
            "let boxed: Option<{a: Int} | String> = some(wide)\n"
            "0")))])
    (check-not-exn (lambda () (compile source)))))

(test-case "借用と Owned の残余を同時に落とす Core は RSD を一つ要求する"
  (define borrowed-core '(Borrowed Int (RParam r)))
  (define actual-core
    `(Record ((a ,borrowed-core imm) (b ,borrowed-core imm) (c (Owned Int) imm))))
  (define expected-core `(Record ((a ,borrowed-core imm))))
  (check-match (borrow-hiding-kind/for-elaboration
                actual-core expected-core compat?)
    `(drop-obligation ,_ ,_))
  (check-match (owned-narrowing-kind/for-elaboration
                actual-core expected-core compat?)
    `(drop-obligation ,_ ,_))
  (define borrowed-ucore '(Borrowed Int Omitted))
  (define actual-ucore
    `(Record ((a ,borrowed-ucore imm) (b ,borrowed-ucore imm) (c (Owned Int) imm))))
  (define expected-ucore `(Record ((a ,borrowed-ucore imm))))
  (match (elab `(Fn ((source ,actual-ucore)) Int (Own)
                    (Let (r let ,expected-ucore) (Move source) 0)))
    [(list core _type _row _callables)
     (check-equal? (count-form (erase-core core) 'RemainderSafelyDropped) 1)]
    [other (fail-check (format "combined RSD fixture was rejected: ~s" other))]))

(test-case "入れ子 record の RSD は外側と内側の余剰借用を除く"
  (define result
    (compile-accepted
     (string-append
      "let x: Owned<Int> = 1\n"
      "let y: Owned<Int> = 2\n"
      "let bx = &x\n"
      "let by = &y\n"
      "let r: {a: {x: Int}} = {a: {x: 1, y: bx}, b: by}\n"
      "r")))
  (when (compiled? result)
    (check-equal? (count-form (compiled-core result) 'RemainderSafelyDropped) 1)
    (check-match (trace-value result)
      `(Rec ((a imm (Rec ((x imm 1)))))))))

(test-case "RSD で除去欄だけが借りた owner の再利用は E-BOR-003 になる（残件）"
  ;; shortcut: RSD が除去欄の loan request を Ψ から消さない。欄別 loan 終了を扱う段階で解消する。
  (define result
    (compile
     (string-append
      "let y: Owned<Int> = 2\n"
      "let r: {a: Int} = {a: 1, b: &mut y}\n"
      "deref(&mut y) = 3\n"
      "r.a")))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-003")))

(test-case "互換な Union 候補の借用残余は Core の E-BOR-027 と operand span を返す"
  (define wide
    '(Untrusted (Record ((x Int imm) (y (Borrowed Int 0) imm)))))
  (define narrow '(Untrusted (Record ((x Int imm)))))
  (define node-span '(#:span src 10 20))
  (define payload-span '(#:span src 21 27))
  (check-true (compat? wide narrow))
  (define result
    (core-type-of/regions
     `(UnionInject ,node-span (#:ty (Union ,narrow Bool) ,node-span)
                   (#:ty ,narrow ,node-span) (#:var source ,payload-span))
     '() '() `((source ,wide))))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-027")
    (check-equal? (diagnostic-primary-span result) payload-span)))

(test-case "RSD で処理できない関数結果の借用 narrowing は拒否候補になる"
  (define actual
    '(NFn () (Record ((x Int imm) (y (Borrowed Int (RParam r)) imm)))
          () () () User))
  (define expected
    '(NFn () (Record ((x Int imm))) () () () User))
  (check-true (compat? actual expected))
  (check-eq? (borrow-hiding-kind/for-elaboration actual expected compat?)
             'reject))

(test-case "decompose は借用拒否でも非互換な Union 候補を選ばず E-TYP-012 と span を保つ"
  (define source
    (string-append
     "let owner: Owned<Int> = 1\n"
     "let bx = &owner\n"
     "let wide = if true { { x: 1, y: bx } } else { \"s\" }\n"
     "let actual = { u: wide }\n"
     "let bad: { u: { x: Int } | Bool } | Int = actual\n"
     "0"))
  (compile-rejected source "E-TYP-012"
                   "let bad: { u: { x: Int } | Bool } | Int = actual\n0"))

(test-case "RSD の retained 欄は outlive しない concrete region へ置き換えない"
  (define skeleton
    '(Scope ()
       (Scope ()
         (Discharge
          (ProofRep (Reserved o-narrow)
                    (RemainderSafelyDropped
                     (Record ((a (Borrowed Int 0) imm) (z Int imm)))
                     (Record ((a (Borrowed Int 0) imm)))))
          (Rec ((a imm borrowed) (z imm 1)))))))
  (define ir (build-region-ir skeleton))
  (define long (region->rho ir (region-at ir '())))
  (define short (region->rho ir (region-at ir '(0))))
  (check-false (region-outlives? ir (rho->region ir short)
                                (rho->region ir long)))
  (define actual `(Record ((a (Borrowed Int ,short) imm) (z Int imm))))
  (define expected `(Record ((a (Borrowed Int ,long) imm))))
  (define core
    `(Scope ()
       (Scope ()
         (Discharge
          (ProofRep (Reserved o-narrow)
                    (RemainderSafelyDropped ,actual ,expected))
          (Rec ((a imm borrowed) (z imm 1)))))))
  (define result
    (type-of/raw core '() '() `((borrowed (Borrowed Int ,short)))
                 (region-ctx ir '() (hash) (hash))))
  (check-match result `(fail owned-narrowing-rejected ,_ ,_ ...)))

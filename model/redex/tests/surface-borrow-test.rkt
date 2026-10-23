#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt"
         (prefix-in backend: "../lowering.rkt"))

(define (compile source) (compile-source/string 'src source))

(define (source-span source needle [occurrence 0])
  (define matches (regexp-match-positions* (regexp (regexp-quote needle)) source))
  (match (list-ref matches occurrence)
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
  (when (and (diagnostic? result)
             (string=? (diagnostic-id result) expected-id))
    (check-equal? (diagnostic-primary-span result)
                  (source-span source needle occurrence)))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id))
  result)

(define (contains-form? tree wanted)
  (or (and (pair? tree) (eq? (car tree) wanted))
      (and (pair? tree) (ormap (lambda (part) (contains-form? part wanted)) tree))))

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

(test-case "共有借用の読み出しと可変借用の書込みを関数本体で型検査する"
  (define shared
    (compile-accepted
     (string-append
      "fn read(p: Owned<Int>) -> Int {\n"
      "  let b: &Int = &p\n"
      "  return deref(b)\n"
      "}\n0")))
  (when (compiled? shared)
    (check-true (contains-form? (compiled-core shared) 'Borrow))
    (check-true (contains-form? (compiled-core shared) 'Read)))
  (define mutable
    (compile-accepted
     (string-append
      "fn set(p: Owned<Int>) -> Int ! {Own, Mutation} {\n"
      "  let b: &mut Int = &mut p\n"
      "  deref(b) = 42\n"
      "  return deref(b)\n"
      "}\n0")))
  (when (compiled? mutable)
    (check-true (contains-form? (compiled-core mutable) 'BorrowMut))
    (check-true (contains-form? (compiled-core mutable) 'Assign)))
  (define child
    (compile-accepted
     (string-append
      "fn read(p: Owned<Int>) -> Int {\n"
      "  let b: &mut Int = &mut p\n"
      "  let child: &Int = reborrow(b)\n"
      "  return deref(child)\n"
      "}\n0")))
  (when (compiled? child)
    (check-true (contains-form? (compiled-core child) 'Reborrow))))

(test-case "Owned の局所値を借りて読み書きし全 config を検査する"
  (for ([source+value
         (in-list
          (list
           (cons (string-append
                  "let owner: Owned<{ n: Int }> = { n: 41 }\n"
                  "let borrowed = &owner\n"
                  "deref(borrowed.n)")
                 41)
           (cons (string-append
                  "let owner: Owned<Int> = 1\n"
                  "let borrowed = &mut owner\n"
                  "deref(borrowed) = 42\n"
                  "deref(borrowed)")
                 42)
           (cons (string-append
                  "let owner: Owned<Int> = 41\n"
                  "let borrowed = &mut owner\n"
                  "let child = reborrow(borrowed)\n"
                  "deref(child)")
                 41)
           (cons (string-append
                  "let owner: Owned<Int> = 41\n"
                  "let boxed: Option<&Int> = some(&owner)\n"
                  "when boxed { some borrowed => deref(borrowed)\n"
                  " none => 0 }")
                 41)
           (cons (string-append
                  "type BorrowBox<A> =\n | box<A>\n"
                  "let owner: Owned<Int> = 43\n"
                  "let boxed: BorrowBox<&Int> = box(&owner)\n"
                  "when boxed { box borrowed => deref(borrowed) }")
                 43)))])
    (define result (compile-accepted (car source+value)))
    (when (compiled? result)
      (check-equal? (trace-value result) (cdr source+value)))))

(test-case "借用値の if と when の合流を読み、可変側は再借用する"
  (for ([source
         (in-list
          (list
           (string-append
            "fn choose(c: Bool) -> Int ! {Own, Partial} {\n"
            "  let p: Owned<Int> = 11\n  let q: Owned<Int> = 22\n"
            "  let bp = &p\n  let bq = &q\n"
            "  let b = if c { bp } else { bq }\n"
            "  return deref(b)\n}\nchoose(true)")
           (string-append
            "fn choose(c: Bool) -> Int ! {Own, Partial} {\n"
            "  let p: Owned<Int> = 11\n  let q: Owned<Int> = 22\n"
            "  let bp = &p\n  let bq = &q\n"
            "  let b = when c { true => bp\n false => bq }\n"
            "  return deref(b)\n}\nchoose(true)")
           (string-append
            "fn choose(c: Bool) -> Int ! {Own, Partial} {\n"
            "  let p: Owned<Int> = 11\n  let q: Owned<Int> = 22\n"
            "  let bp = &mut p\n  let bq = &mut q\n"
            "  let b = if c { bp } else { bq }\n"
            "  let child = reborrow(b)\n"
            "  return deref(child)\n}\nchoose(true)")))])
    (define result (compile-accepted source))
    (when (compiled? result)
      (check-true (or (contains-form? (compiled-core result) 'Borrow)
                      (contains-form? (compiled-core result) 'BorrowMut)))
      (check-true (contains-form? (compiled-core result) 'Eliminate))
      (check-equal? (trace-value result) 11))))

(test-case "借用の生成だけの呼出しは実行でき trace の config を検査できる"
  (define result
    (compile-accepted
     (string-append
      "fn hold(p: Owned<Res>) -> Unit ! {Own, Partial} {\n"
      "  let b = &p\n  ()\n}\n"
      "hold(acquire(9))")))
  (when (compiled? result)
    (check-true (contains-form? (compiled-core result) 'Borrow))
    (check-equal? (trace-value result) 'unit)))

(test-case "借用は関数仮引数でなく束縛した局所 Owned を越えて逃がせない"
  (compile-rejected "{ let owner: Owned<Int> = 1\n &owner }"
                    "E-BOR-004" "&owner"))

(test-case "二つ目の可変借用を拒否し Move の判定は Core で担う"
  ;; Surface の Owned Move は未実装で E-OWN-010 が先行する。
  ;; E-BOR-008 の Core 側は construct-borrow-lifetime-test.rkt で検査する。
  (define mut-source
    (string-append
     "fn bad(p: Owned<Int>) -> Unit {\n"
     "  let b = &mut p\n"
     "  let c = &mut p\n"
     "  ()\n}\n0"))
  (compile-rejected mut-source "E-BOR-003" "&mut p" 1))

(test-case "借用を捕捉する無名関数と共有借用の再借用を拒否する"
  (define closure-source
    (string-append
     "fn bad(p: Owned<Int>) -> Unit {\n"
     "  let b = &p\n"
     "  let g = fn() => deref(b)\n"
     "  ()\n}\n0"))
  (compile-rejected closure-source "E-BOR-011" "fn() => deref(b)")
  (define reborrow-source
    (string-append
     "fn bad(p: Owned<Int>) -> Unit {\n"
     "  let b = &p\n"
     "  let child = reborrow(b)\n"
     "  ()\n}\n0"))
  (compile-rejected reborrow-source "E-BOR-009" "reborrow(b)"))

(test-case "deref と書込みは借用種別と対象に応じた診断を返す"
  (compile-rejected "deref(1)" "E-BOR-018" "deref(1)")
  (define non-borrow-write
    (string-append "fn bad() -> Unit {\n"
                   "  deref(1) = 2\n"
                   "  ()\n}\n0"))
  (compile-rejected non-borrow-write "E-BOR-019" "deref(1)")
  (define shared-write
    (string-append
     "fn bad(p: Owned<Int>) -> Unit {\n"
     "  let b = &p\n"
     "  deref(b) = 1\n"
     "  ()\n}\n0"))
  (compile-rejected shared-write "E-BOR-015" "deref(b)"))

(test-case "借用した record の未知の欄射影は節点 span で拒否する"
  (define source
    (string-append
     "fn bad(p: Owned<{ n: Int }>) -> Int {\n"
     "  let b: &{ n: Int } = &p\n"
     "  return deref(b.missing)\n"
     "}\n0"))
  (compile-rejected source "E-BOR-017" "b.missing"))

(test-case "非 Owned binding と MutSlot は借用できない"
  (compile-rejected
   "fn bad() -> Unit { let x = 1\n let b = &x\n () }\n0"
   "E-BOR-005" "&x")
  (compile-rejected
   "fn bad() -> Unit { let mut x = 1\n let b = &x\n () }\n0"
   "E-BOR-005" "&x")
  (compile-rejected
   "fn bad() -> Unit { let mut x = 1\n let b = &mut x\n () }\n0"
   "E-BOR-005" "&mut x"))

(test-case "異なる owner の共有借用を if で合流して読み取る"
  (define result
    (compile-accepted
     (string-append
      "fn choose(c: Bool) -> Int ! {Own, Partial} {\n"
      " let x: Owned<Int> = 41\n"
      " let y: Owned<Int> = 42\n"
      " let borrowed = if c { &x } else { &y }\n"
      " return deref(borrowed)\n"
      "}\nchoose(true)")))
  (when (compiled? result)
    (check-equal? (trace-value result) 41)))

(test-case "Option の Borrowed Union member に some(bx) を入れ全 config を検査する"
  (define result
    (compile-accepted
     (string-append
      "fn read() -> Int ! {Own, Partial} {\n"
      " let x: Owned<Int> = 43\n"
      " let bx = &x\n"
      " let value: Option<&Int | &Bool> = some(bx)\n"
      " return when value { some borrowed => 43\n none => 0 }\n"
      "}\nread()")))
  (when (compiled? result)
    (check-equal? (trace-value result) 43)))

(test-case "Option の BorrowedMut Union member を trace の config で検査する"
  (define result
    (compile-accepted
     (string-append
      "fn read() -> Int ! {Own, Partial} {\n"
      " let x: Owned<Int> = 47\n"
      " let bx = &mut x\n"
      " let value: Option<&mut Int | &mut Bool> = some(bx)\n"
      " return when value { some borrowed => 47\n none => 0 }\n"
      "}\nread()")))
  (when (compiled? result)
    (check-equal? (trace-value result) 47)))

(test-case "Option と利用者 data の constructor payload に借用を保持する"
  (define option-read
    (compile-accepted
     (string-append
     "fn read(p: Owned<Int>) -> Int {\n"
      "  let o: Option<&Int> = some(&p)\n"
      "  return when o { some b => deref(b)\n none => 0 }\n"
      "}\n0")))
  (when (compiled? option-read)
    (check-true (contains-form? (compiled-core option-read) 'Construct))
    (check-true (contains-form? (compiled-core option-read) 'Eliminate)))
  (define data-read
    (compile-accepted
     (string-append
      "type BorrowBox<A> =\n | box<A>\n"
      "fn read(p: Owned<Int>) -> Int {\n"
      "  let boxed: BorrowBox<&Int> = box(&p)\n"
      "  return when boxed { box b => deref(b) }\n"
      "}\n0")))
  (when (compiled? data-read)
    (check-true (contains-form? (compiled-core data-read) 'Construct))
    (check-true (contains-form? (compiled-core data-read) 'Eliminate)))
  (define option-escape
    (string-append
     "fn bad() -> Unit {\n"
     "  let o: Option<&Int> = { let x: Owned<Int> = 1\n some(&x) }\n"
     "  ()\n}\n0"))
  (compile-rejected option-escape "E-BOR-004" "&x")
  (define option-move
    (string-append
     "fn bad(p: Owned<Int>) -> Unit {\n"
     "  let o: Option<&mut Int> = some(&mut p)\n"
     "  let moved = p\n"
     "  ()\n}\n0"))
  ;; Surface の Owned Move が未実装なので E-OWN-010 が先行する。
  ;; 借用中 Move の E-BOR-008 は Core の construct-borrow-lifetime-test.rkt で検査する。
  (compile-rejected option-move "E-OWN-010" "p" 3))

(test-case "借用を含む Surface program は compiled backend で E-LOW-003 になる"
  (define result
    (compile-accepted
     (string-append
      "fn hold(p: Owned<Res>) -> Unit ! {Own, Partial} {\n"
      "  let b = &p\n  ()\n}\n"
      "hold(acquire(9))")))
  (when (compiled? result)
    (define-values (status lowered)
      (backend:lower (compiled-execution-core result) 'racket-cs))
    (check-eq? status 'capability)
    (check-equal? (diagnostic-id lowered) "E-LOW-003")))

(test-case "Task 4 の record fixture は Surface の resource field 制約で表せない"
  (define result
    (compile
     (string-append
      "fn read(p: { n: Int, owned: Owned<Res> }) -> Int ! {Own, Partial} {\n"
      "  return p.n\n}\n"
      "read({ n: 41, owned: acquire(9) })")))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-OWN-007")))

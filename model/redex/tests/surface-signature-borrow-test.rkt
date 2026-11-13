#lang racket

;; SUR-004b1。関数署名の借用型と region 省略を固定する。

(require rackunit
         racket/list
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../region.rkt"
         "../typing.rkt")

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

(define (compile-rejected source expected-id [needle #f] [occurrence 0])
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" expected-id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)
    (when needle
      (check-equal? (diagnostic-primary-span result)
                    (source-span source needle occurrence))))
  result)

(define (only-callable-type result)
  (match (compiled-callables result)
    [(list (list _ type)) type]
    [other (fail-check (format "callable が 1 件の形を期待した: ~s" other))]))

(define (forall-binders result)
  (match (only-callable-type result)
    [`(ForallRegion (,binders ...) ,_) binders]
    [_ #f]))

(define (return-type result)
  (match (only-callable-type result)
    [`(ForallRegion ,_ (NFn ,_ ,type . ,_)) type]
    [`(NFn ,_ ,type . ,_) type]
    [other (fail-check (format "NFn 署名を期待した: ~s" other))]))

(define (contains-form? tree wanted)
  (or (and (pair? tree) (eq? (car tree) wanted))
      (and (pair? tree) (ormap (lambda (part) (contains-form? part wanted)) tree))))

(define (trace-compiled artifact)
  (define core (compiled-core artifact))
  (define callables (compiled-callables artifact))
  (define ir (build-region-ir core))
  (define typed (core-type-of/regions core '() callables #:ir ir))
  (check-true (region-typed? typed)
              (format "Surface Core の region 型付け成功: ~s" typed))
  (if (not (region-typed? typed))
      '()
      (call-with-trait-ledger
       (compiled-ledger artifact)
       (lambda ()
         (define start
           (inject-g2m (erase-core (compiled-execution-core artifact))))
         (define trace (bounded-trace-g2 start 10000))
         (check-equal? (execution-outcome trace) 'terminal)
         (define expected (region-typed-type typed))
         (for ([config (in-list (execution-configs trace))]
               [index (in-naturals)])
           (define row
             (runtime-row config callables expected #:region-ir ir))
           (check-not-false row (format "config ~a has runtime-row" index))
           (when row
             (check-true
              (config-ok? config callables expected row #:region-ir ir)
              (format "config ~a passes config-ok?" index))))
         (execution-configs trace)))))

(define (trace-value artifact)
  (match (last (trace-compiled artifact))
    [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
    [other (fail-check (format "terminal config expected, got ~s" other))]))

(define (region-app-arguments tree)
  (match tree
    [`(RegionApp ,callee (,regions ...))
     (append (list regions)
             (region-app-arguments callee)
             (append-map region-app-arguments regions))]
    [(? pair? parts) (append-map region-app-arguments parts)]
    [_ '()]))

(test-case "借用位置ごとに別の region 束縛子を割り当てる"
  (define result
    (compile-accepted
     "fn f(x: &{a: &Int}, y: &Int, z: &mut Int) -> Int { return 0 }\n0"))
  (define binders (forall-binders result))
  (check-equal? (length binders) 4)
  (check-equal? (length (remove-duplicates binders)) 4)
  (check-true (contains-form? (compiled-core result) 'Recur))
  (match (only-callable-type result)
    [`(ForallRegion (,outer ,inner ,third ,fourth)
        (NFn ((Borrowed (Record ((a (Borrowed Int (RParam ,inner)) imm)))
                          (RParam ,outer))
              (Borrowed Int (RParam ,third))
              (BorrowedMut Int (RParam ,fourth))) Int . ,_))
     (check-equal? binders (list outer inner third fourth))]
    [other (fail-check (format "leaf ごとの ForallRegion を期待した: ~s" other))]))

(test-case "型適用と Union の内側の借用位置も個別に束縛する"
  (define result
    (compile-accepted "fn f(x: List<&Int> | &Int) -> Int { return 0 }\n0"))
  (check-equal? (length (forall-binders result)) 2))

(test-case "入力の借用位置が一つなら戻りの借用にその束縛子を割り当てる"
  (define result
    (compile-accepted
     "fn head(p: &Int) -> &Int { return p }\n0"))
  (match-define (list binder) (forall-binders result))
  (check-equal? (return-type result) `(Borrowed Int (RParam ,binder))))

(test-case "戻り型の推論でも入力の借用位置が一つならその寿命を使う"
  (define result
    (compile-accepted
     "fn head(p: &{head: Int, tail: Int}) { return p.head }\n0"))
  (match-define (list binder) (forall-binders result))
  (check-equal? (return-type result) `(Borrowed Int (RParam ,binder))))

(test-case "注釈付き let は右辺の省略 region を採る"
  (compile-accepted
   "fn f(p: &Int) -> &Int { let q: &Int = p\nreturn q }\n0")
  (compile-accepted
   "fn f(p: &Int) -> &Int { let q = p\nreturn q }\n0")
  (compile-accepted
   "fn f(p: &{h: Int, t: Int}) -> &Int { let q: &{h: Int, t: Int} = p\nreturn q.h }\n0"))

(test-case "局所 owner の借用は入力寿命の戻りに偽装できない"
  (compile-rejected
   "fn f(p: &Int) -> &Int { let x: Owned<Int> = 1\nreturn &x }\n0"
   "E-TYP-012")
  (compile-rejected
   "fn f(p: &Int) { let x: Owned<Int> = 1\nreturn &x }\n0"
   "E-TYP-012"))

(test-case "捕捉の無い入れ子 RegionLam は外側からの borrowed 引数を受け取れる"
  (compile-accepted
   "fn f(p: &Int) -> Int ! {Own, Partial} { let g = fn(q: &Int) -> &Int { return q }\nreturn 0 }\n0"))

(test-case "内側 RegionLam が外側の借用引数を読むだけの捕捉も E-BOR-027 で拒否する"
  (define source
    "fn outer(p: &Int) -> Int ! {Own, Partial} { let inner = fn(q: &Int) -> Int { return deref(p) }\nreturn inner(p) }\n0")
  (define diagnostic (compile-rejected source "E-BOR-027"))
  (check-equal?
   (diagnostic-title diagnostic)
   "借用を view から隠す narrowing に RSD が無いか、RegionLam が binder 外の借用 region を捕捉する"))

(test-case "借用を持たない関数は ForallRegion で包まない"
  (define result
    (compile-accepted "fn g(x: Int) -> Int { return x }\n0"))
  (check-false (forall-binders result))
  (check-equal? (only-callable-type result) '(NFn (Int) Int () () () User)))

(test-case "入力の借用位置が複数で戻りに借用があると E-BOR-020"
  (define diagnostic
    (compile-rejected
     "fn f(x: &Int, y: &Int) -> &Int { return x }\n0"
     "E-BOR-020" "&Int" 2))
  (check-equal?
   (diagnostic-found diagnostic)
   "入力の借用位置が複数あるため戻りの region を省略できない。明示の region を指定する"))

(test-case "推論戻り型に借用があり入力位置が複数なら E-BOR-020"
  (define diagnostic
    (compile-rejected
     "fn f(x: &Int, y: &Int) { return x }\n0" "E-BOR-020"))
  (check-equal?
   (diagnostic-found diagnostic)
   "入力の借用位置が複数あるため戻りの region を省略できない。明示の region を指定する"))

(test-case "一つの仮引数に借用位置が二つあり戻りに借用があると E-BOR-020"
  (void
   (compile-rejected
    "fn f(x: &{a: &Int}) -> &Int { return x.a }\n0"
    "E-BOR-020" "&Int" 1)))

(test-case "入力に借用が無く戻りに借用があると E-BOR-020"
  (define diagnostic
    (compile-rejected
     "fn f(x: Int) -> &Int { return x }\n0"
     "E-BOR-020" "&Int"))
  (check-equal?
   (diagnostic-found diagnostic)
   "戻りの借用に対応する入力の借用位置が無い"))

(test-case "入れ子の戻り借用の E-BOR-020 は戻り型全体を指す"
  (void
   (compile-rejected
    "fn f(x: &Int, y: &Int) -> {a: &Int} { return x }\n0"
    "E-BOR-020" "{a: &Int}")))

(test-case "関数型、型別名、data 欄、trait 要求欄の借用は E-SUR-005"
  (compile-rejected
   "fn f(k: fn(&Int) -> Int) -> Int { return 0 }\n0" "E-SUR-005")
  (compile-rejected "type A = &Int\n0" "E-SUR-005")
  (compile-rejected "data D { a: &Int }\n0" "E-SUR-005")
  (compile-rejected "trait T { f: fn(&Int) -> Int }\n0" "E-SUR-005")
  (void))

(test-case "型注釈付き無名関数の借用の仮引数と戻りを lowering する"
  (define result
    (compile-accepted
     "let h = fn(p: &Int) -> &Int { return p }\n0"))
  (check-true (contains-form? (compiled-core result) 'RegionLam))
  (match-define (list binder) (forall-binders result))
  (check-equal? (return-type result) `(Borrowed Int (RParam ,binder))))

(test-case "BorrowedMut から Reborrow した値は共有署名の region を継ぐ"
  (define result
    (compile-accepted
     "fn f(p: &mut Int) -> &Int { return reborrow(p) }\n0"))
  (check-equal? (length (forall-binders result)) 1))

(test-case "BorrowedMut record の共有欄借用は共有署名の region を継ぐ"
  (define result
    (compile-accepted
     "fn f(p: &mut {h: Int, t: Int}) -> &Int { return p.h }\n0"))
  (check-equal? (length (forall-binders result)) 1))

(test-case "BorrowedMut の値を返す署名は同じ region binder を使う"
  (define result
    (compile-accepted
     "fn f(p: &mut Int) -> &mut Int { return p }\n0"))
  (check-equal? (length (forall-binders result)) 1))

(test-case "BorrowedMut から Reborrow した推論戻り型は受理する"
  (define result
    (compile-accepted "fn f(p: &mut Int) { return reborrow(p) }\n0"))
  (check-equal? (length (forall-binders result)) 1))

(test-case "BorrowedMut record の共有欄借用を推論戻り型へ結ぶ"
  (define result
    (compile-accepted "fn f(p: &mut {h: Int, t: Int}) { return p.h }\n0"))
  (check-equal? (length (forall-binders result)) 1))

(test-case "BorrowedMut の値を返す推論戻り型は受理する"
  (define result
    (compile-accepted "fn f(p: &mut Int) { return p }\n0"))
  (check-equal? (length (forall-binders result)) 1))

(test-case "BorrowedMut record の共有欄は再借用できない"
  (compile-rejected
   "fn f(p: &mut {h: Int, t: Int}) -> &Int { return reborrow(p.h) }\n0"
   "E-BOR-009"))

(test-case "借用署名の呼出しを Apply で暗黙に実体化する"
  (define result
    (compile-accepted
     (string-append
      "fn head(p: &Int) -> &Int { return p }\n"
      "let owner: Owned<Int> = 1\n"
      "let value = head(&owner)\n"
      "deref(value)")))
  (check-true (contains-form? (compiled-execution-core result) 'RegionApp)))

(test-case "借用署名の forwarding 呼出しは束縛子をそのまま伝える"
  (define result
    (compile-accepted
     (string-append
      "fn head(p: &Int) -> &Int { return p }\n"
      "fn forward(p: &Int) -> &Int ! {Own, Partial} { return head(p) }\n"
      "0")))
  (check-true (contains-form? (compiled-execution-core result) 'RegionApp)))

(test-case "record 欄から取り出した借用署名を呼ぶ"
  (define result
    (compile-accepted
     (string-append
      "fn get(p: {a: &Int}) -> &Int ! {Own, Partial} { return p.a }\n"
      "let holder = {h: get}\n"
      "let owner: Owned<Int> = 1\n"
      "deref(holder.h({a: &owner}))")))
  (check-true (contains-form? (compiled-execution-core result) 'RegionApp))
  (check-equal? (trace-value result) 1))

(test-case "借用した record の欄を返す署名を呼んで値を読む"
  (define result
    (compile-accepted
     (string-append
      "fn head(p: &{head: Int, tail: Int}) -> &Int { return p.head }\n"
      "let pair: Owned<{head: Int, tail: Int}> = {head: 1, tail: 2}\n"
      "deref(head(&pair))")))
  (check-equal? (trace-value result) 1))

(test-case "BorrowedMut から共有を再借用し可変借用を転送する"
  (define shared
    (compile-accepted
     (string-append
      "fn share(p: &mut Int) -> &Int { return reborrow(p) }\n"
      "let owner: Owned<Int> = 1\n"
      "deref(share(&mut owner))")))
  (check-equal? (trace-value shared) 1)
  (define mutable
    (compile-accepted
     (string-append
      "fn forward(p: &mut Int) -> &mut Int { return p }\n"
      "let owner: Owned<Int> = 1\n"
      "{ let r = forward(&mut owner)\n"
      "  deref(r) = 9\n"
      "  () }\n"
      "deref(&owner)")))
  (check-equal? (trace-value mutable) 9))

(test-case "欄の内側の借用を署名から返す"
  (define result
    (compile-accepted
     (string-append
      "fn get(p: {a: &Int}) -> &Int ! {Own, Partial} { return p.a }\n"
      "let owner: Owned<Int> = 7\n"
      "deref(get({a: &owner}))")))
  (check-equal? (trace-value result) 7))

(test-case "複数の借用入力でも借用を返さない署名を呼ぶ"
  (define result
    (compile-accepted
     (string-append
      "fn ignore(p: &Int, q: &Int) -> Int { return 3 }\n"
      "let left: Owned<Int> = 1\n"
      "let right: Owned<Int> = 2\n"
      "ignore(&left, &right)")))
  (check-equal? (trace-value result) 3))

(test-case "型注釈付き無名関数の借用署名を呼ぶ"
  (define result
    (compile-accepted
     (string-append
      "let id = fn(p: &Int) -> &Int { return p }\n"
      "let owner: Owned<Int> = 4\n"
      "deref(id(&owner))")))
  (check-equal? (trace-value result) 4))

(test-case "借用署名の自己再帰を実体化して呼ぶ"
  (define result
    (compile-accepted
     (string-append
      "fn choose(p: &Int, again: Bool) -> &Int ! {Own, Partial} {\n"
      "  return if again { p } else { choose(p, true) }\n"
      "}\n"
      "let owner: Owned<Int> = 5\n"
      "deref(choose(&owner, false))")))
  (check-equal? (trace-value result) 5))

(test-case "let で別名にした region 多相関数を呼ぶ"
  (define result
    (compile-accepted
     (string-append
      "fn id(p: &Int) -> &Int { return p }\n"
      "let g = id\n"
      "let owner: Owned<Int> = 6\n"
      "deref(g(&owner))")))
  (check-equal? (trace-value result) 6))

(test-case "record 欄から取り出した record borrow callable を呼ぶ"
  (define result
    (compile-accepted
     (string-append
      "fn head(p: &{head: Int, tail: Int}) -> &Int { return p.head }\n"
      "let holder = {h: head}\n"
      "let pair: Owned<{head: Int, tail: Int}> = {head: 8, tail: 9}\n"
      "deref(holder.h(&pair))")))
  (check-equal? (trace-value result) 8))

(test-case "同じ関数を二度呼ぶ一式は呼出しごとの region を保つ"
  (define result
    (compile-accepted
     (string-append
      "fn head(p: &{head: Int, tail: Int}) -> &Int { return p.head }\n"
      "let right: Owned<{head: Int, tail: Int}> = {head: 2, tail: 0}\n"
      "add({ let inner: Owned<{head: Int, tail: Int}> = {head: 1, tail: 0}\n"
      "  deref(head(&inner)) }, deref(head(&right)))")))
  (check-equal? (trace-value result) 3)
  (define rhos (region-app-arguments (compiled-execution-core result)))
  (check-equal? (length rhos) 2)
  (check-not-equal? (first rhos) (second rhos)))

(test-case "入れ子の借用位置を別々に束縛する署名を定義だけで検査する（呼出しは実行しない）"
  (define result
    (compile-accepted
     (string-append
      "fn ignore(x: &{a: &Int}) -> Int { return 11 }\n"
      "0")))
  (define binders (forall-binders result))
  (check-equal? (length binders) 2)
  (check-not-equal? (first binders) (second binders))
  (check-equal? (trace-value result) 0))

(test-case "Scope を越える借用戻りは E-BOR-004"
  (compile-rejected
   (string-append
    "fn id(p: &Int) -> &Int { return p }\n"
    "let result = { let owner: Owned<Int> = 7\n id(&owner) }\n"
    "deref(result)")
   "E-BOR-004"))

(test-case "返した可変借用の生存中の owner write は E-BOR-003"
  (compile-rejected
   (string-append
    "fn idm(p: &mut Int) -> &mut Int { return p }\n"
    "fn bad() -> Unit ! {Own, Partial, Mutation} {\n"
    "  let owner: Owned<Int> = 1\n"
    "  let result = idm(&mut owner)\n"
    "  deref(&mut owner) = 2\n"
    "  ()\n"
    "}\n"
    "bad()")
   "E-BOR-003"))

(test-case "共有借用を受け可変借用を返す署名は E-TYP-012"
  (compile-rejected
   "fn bad(p: &Int) -> &mut Int { return p }\n0"
   "E-TYP-012"))

(test-case "捕捉の無い複数入力からの省略戻りは E-BOR-020"
  (compile-rejected
   "fn bad(p: &Int, q: &Int) -> Int { let f = fn(x: &Int, y: &Int) -> &Int { return x }\nreturn 0 }\n0"
   "E-BOR-020"))

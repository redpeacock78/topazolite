#lang racket

;; SUR-004b1。関数署名の借用型と region 省略を固定する。

(require rackunit
         racket/list
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt")

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

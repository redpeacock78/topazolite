#lang racket

(require rackunit
         racket/match
         "../classify.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../surface-lower.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (lambda ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
       [other (fail-check (format "terminal config expected, got ~s" other))]))))

(define (check-accepted source type value)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (when (compiled? result)
    (check-equal? (compiled-type result) type)
    (check-equal? (run-value result) value)))

(define (check-rejected source id)
  (define result (compile source))
  (check-true (diagnostic? result)
              (format "expected ~a, got ~s" id result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) id)))

(define (loop-rows result)
  (define (loop-callables tree)
    (match tree
      [`(Recur ,_ ,callable (#:bind ,function ,_) ,_ ,body ,continuation)
       (append (if (regexp-match? #rx"^%for-loop" (symbol->string function))
                   (list callable)
                   '())
               (loop-callables body)
               (loop-callables continuation))]
      [(? pair? parts) (append-map loop-callables parts)]
      [_ '()]))
  (define generated (loop-callables (compiled-core result)))
  (for/list ([entry (in-list (compiled-callables result))]
             #:when (member (first entry) generated))
    (match (second entry)
      [`(NFn ,_ ,_ ,_ ,row ,_ ,_) row]
      [other (fail-check (format "loop の NFn signature を期待したが ~s" other))])))

(define (loop-rows-of source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result) (diagnostic-id result) "compiled result expected"))
  (if (compiled? result) (loop-rows result) '()))

(define list-123 "cons(1, cons(2, cons(3, nil)))")
(define list-12 "cons(1, cons(2, nil))")

(test-case "S1 文の位置の for が本体を要素ごとに実行し mut の累積を更新する"
  (check-accepted
   (string-append
    "fn main() -> Int ! Mutation {\n"
    " let mut total = 0\n"
    " let xs: List<Int> = " list-123 "\n"
    " for x in xs { total = add(total, x) }\n"
    " return total\n}\nmain()")
   'Int 6))

(test-case "S2 式の位置の for の leave v は some(v) になる（検査の位置）"
  (check-accepted
   (string-append
    "fn main() -> Option<Int> {\n"
    " let xs: List<Int> = " list-123 "\n"
    " let found: Option<Int> = for x in xs { if lt(1, x) { leave x } }\n"
    " return found\n}\nmain()")
   '(Option Int) '(Construct (Option Int) some 2)))

(test-case "S3 式の位置の for は走査を終えると none になる"
  (check-accepted
   (string-append
    "fn main() -> Option<Int> {\n"
    " let xs: List<Int> = " list-123 "\n"
    " let found: Option<Int> = for x in xs { x }\n"
    " return found\n}\nmain()")
   '(Option Int) '(Construct (Option Int) none)))

(test-case "S4 合成位置の for は leave payload から Option の型を決める"
  (check-accepted
   (string-append
    "fn main() -> Option<Int> {\n"
    " let xs: List<Int> = " list-123 "\n"
    " let found = for x in xs { if lt(1, x) { leave x } }\n"
    " return found\n}\nmain()")
   '(Option Int) '(Construct (Option Int) some 2)))

(test-case "S5 for の some payload を ?= で束縛する"
  (check-accepted
   (string-append
    "fn main() -> Option<Int> {\n"
    " let xs: List<Int> = " list-123 "\n"
    " let first ?= for x in xs { if lt(1, x) { leave x } }\n"
    " return some(first)\n}\nmain()")
   '(Option Int) '(Construct (Option Int) some 2)))

(test-case "S6 合成の位置で leave が無いと E-TYP-010 になる"
  (check-rejected
   "fn f(xs: List<Int>) -> Unit { let found = for x in xs { () }\n return () }\n()"
   "E-TYP-010"))

(test-case "S6 for 本体の別の none は E-TYP-003 のまま報告する"
  (define source
    (string-append
     "fn f(xs: List<Int>) -> Option<Int> { let found = for x in xs { let y = none\n () }\n return found }\nf("
     list-12 ")"))
  (define result (compile source))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-TYP-003")
    (match-define (list (cons start end)) (regexp-match-positions #rx"none" source))
    (check-equal? (diagnostic-primary-span result) `(#:span src ,start ,end))))

(test-case "S6b 注釈付き Let の leave の無い for は none として受理する"
  (check-accepted
   "fn f(xs: List<Int>) -> Option<Int> { let found: Option<Int> = for x in xs { () }\n return found }\nf(cons(1, nil))"
   '(Option Int) '(Construct (Option Int) none)))

(test-case "S7 for 本体の return は関数から脱出し loop row に残る"
  (define source
    (string-append
     "fn first(xs: List<Int>) -> Int { for x in xs { return x }\n return 0 }\n"
     "first(" list-12 ")"))
  (check-accepted source 'Int 1)
  (check-true
   (for/or ([row (in-list (loop-rows-of source))])
     (for/or ([label (in-list row)])
       (match label [`(Return ,_ Int) #t] [_ #f])))))

(test-case "S8 文の位置の for と when の leave は外側の式境界へ届く"
  (check-accepted
   (string-append
    "fn find(xs: List<Int>, flag: Bool, c: Bool) -> Int {\n"
    " return if c {\n"
    "  when flag { true => { for x in xs { leave x }\n leave 8 }\n false => () }\n"
    "  leave 9\n"
    " } else { leave 3 }\n"
    "}\nfind(" list-12 ", true, true)")
   'Int 1)
  (check-accepted
   (string-append
    "fn get_flag(c: Bool) -> Bool { return c }\n"
    "fn find(xs: List<Int>, flag: Bool, c: Bool) -> Int {\n"
    " return if c {\n"
    "  when get_flag(flag) { true => { for x in xs { leave x }\n leave 8 }\n false => () }\n"
    "  leave 9\n"
    " } else { leave 3 }\n"
    "}\nfind(" list-12 ", true, true)")
   'Int 1)
  (check-rejected
   (string-append "const xs: List<Int> = " list-12 "\nfor x in xs { leave x }\n0")
   "E-RET-006"))

(test-case "S9 入れ子 for の内側の文位置 leave は外側の式境界へ届く"
  (define source
    (string-append
     "fn find(xs: List<Int>) -> Option<Int> { return for x in xs { for y in xs { leave x } } }\n"
     "find(" list-12 ")"))
  (check-accepted source '(Option Int) '(Construct (Option Int) some 1))
  (check-equal? (length (loop-rows-of source)) 2)
  (check-equal?
   (count (lambda (row) (for/or ([label (in-list row)]) (match label [`(Return ,_ (Option Int)) #t] [_ #f])))
          (loop-rows-of source))
   2))

(test-case "S9 入れ子の式位置 for の leave は内側で止まる"
  (define source
    (string-append
     "fn f(xs: List<Int>) -> Option<Int> {\n"
     " let outer: Option<Int> = for x in xs { let inner = for y in xs { leave y }\n () }\n"
     " return outer\n}\nf(" list-12 ")"))
  (check-accepted source '(Option Int) '(Construct (Option Int) none))
  (define rows (loop-rows-of source))
  (check-equal? (length rows) 2)
  (check-equal?
   (count (lambda (row) (for/or ([label (in-list row)]) (match label [`(Return ,_ (Option Int)) #t] [_ #f]))) rows)
   1))

(test-case "S9 return は入れ子 for を越えて関数へ届く"
  (define source
    (string-append
     "fn first(xs: List<Int>) -> Int { for x in xs { for y in xs { return y } }\n return 0 }\n"
     "first(" list-12 ")"))
  (check-accepted source 'Int 1)
  (check-equal? (length (loop-rows-of source)) 2)
  (check-equal?
   (count (lambda (row) (for/or ([label (in-list row)]) (match label [`(Return ,_ Int) #t] [_ #f])))
          (loop-rows-of source))
   2))

(test-case "S10 for を含む構造的再帰の分類は for 無しと一致し余剰 label を持たない"
  (define base
    (string-append
     "fn walk(xs: List<Int>) -> Int { when xs { nil => return 0\n cons x tail => return walk(tail) } }\n"
     "walk(" list-12 ")"))
  (define with-for
    (string-append
     "fn walk(xs: List<Int>) -> Int { when xs { nil => return 0\n cons x tail => { for y in tail { () }\n return walk(tail) } } }\n"
     "walk(" list-12 ")"))
  (define base-result (compile base))
  (define for-result (compile with-for))
  (check-true (compiled? base-result))
  (check-true (compiled? for-result))
  (when (and (compiled? base-result) (compiled? for-result))
    (check-equal? (classify (compiled-core base-result) '() (compiled-callables base-result))
                  (classify (compiled-core for-result) '() (compiled-callables for-result)))
    (check-equal? (loop-rows for-result) '(()))))

(test-case "S11 List 以外の走査対象は E-TYP-012"
  (check-rejected "fn f() -> Unit { for x in 1 { () }\n () }\n()" "E-TYP-012"))

(test-case "S11b List の別名も for の走査対象として受理する"
  (check-accepted
   (string-append
    "type Xs = List<Int>\n"
    "fn f(xs: Xs) -> Int ! Mutation { let mut total = 0\n for x in xs { total = add(total, x) }\n return total }\n"
    "f(" list-12 ")")
   'Int 3))

(test-case "S12 for 本体の末尾式は文として捨てられる"
  (check-accepted
   (string-append "fn f(xs: List<Int>) -> Unit { for x in xs { x }\n () }\nf(" list-12 ")")
   'Unit 'unit)
  (check-accepted
   (string-append "fn f(xs: List<Int>) -> Option<Int> { return for x in xs { x } }\nf(" list-12 ")")
   '(Option Int) '(Construct (Option Int) none)))

(test-case "S13 for の外では in を識別子として使える"
  (check-accepted "let in = 1\nin" 'Int 1))

(test-case "S14a 014c1b で反転する Owned<List<Int>> の現行診断は E-OWN-010"
  (check-rejected
   "fn f(xs: Owned<List<Int>>) -> Unit { for x in xs { () }\n () }\n()"
   "E-OWN-010"))

(test-case "S14a 014c1b で反転する List<Owned<Int>> の現行診断は E-OWN-010"
  (check-rejected
   "fn f(xs: List<Owned<Int>>) -> Unit { for x in xs { () }\n () }\n()"
   "E-OWN-010"))

(test-case "S15 式位置 for の走査対象は for の境界の外で評価される"
  (check-rejected
   (string-append "fn f() -> Unit { let answer = for x in leave " list-12 " { leave x }\n () }\nf()")
   "E-RET-006"))

(test-case "S16 effect 無しと Mutation だけの for は Finite structural で Partial を持たない"
  (define no-effect (loop-rows-of (string-append "fn f(xs: List<Int>) -> Unit { for x in xs { () }\n () }\nf(" list-12 ")")))
  (define mutation (loop-rows-of (string-append "fn f(xs: List<Int>) -> Unit ! Mutation { let mut n = 0\n for x in xs { n = add(n, x) }\n () }\nf(" list-12 ")")))
  (check-equal? no-effect '(()))
  (check-equal? mutation '((Mutation))))

(test-case "S17 外側 mut の更新対象に for の束縛名は加わらない"
  (define result (compile (string-append "fn f(xs: List<Int>) -> Int ! Mutation { let mut total = 0\n for x in xs { total = add(total, x) }\n return total }\nf(" list-12 ")")))
  (check-true (compiled? result))
  (when (compiled? result)
    (define reassign-names
      (let walk ([tree (erase-origin-core (compiled-core result))])
        (match tree
          [`(Reassign ,name ,_ ,_) (list name)]
          [(? list? items) (append-map walk items)]
          [_ '()])))
    (check-equal? (remove-duplicates reassign-names) '(total))))

(test-case "S18 入れ子 Fn の return は for の row と leave 包みに入らない"
  (define source
    (string-append
     "fn f(xs: List<Int>) -> Option<Int> { let found: Option<Int> = for x in xs { let nested = fn() -> Int { return 9 }\n leave x }\n return found }\n"
     "f(" list-12 ")"))
  (check-accepted source '(Option Int) '(Construct (Option Int) some 1))
  (define rows (loop-rows-of source))
  (check-equal? (length rows) 1)
  (check-false
   (for/or ([label (in-list (first rows))])
     (match label [`(Return ,_ Int) #t] [_ #f]))))

(test-case "S19 入れ子と文位置の for の leave payload は一度だけ some で包まれる"
  (check-accepted
   (string-append
    "fn f(xs: List<Int>) -> Option<Int> { let found: Option<Int> = for x in xs { let inner = for y in xs { leave y }\n for z in xs { leave x } }\n return found }\nf(" list-12 ")")
   '(Option Int) '(Construct (Option Int) some 1)))

(test-case "S20 最上位 for の本体の return は E-RET-002"
  (check-rejected
   (string-append "const xs: List<Int> = " list-12 "\nfor x in xs { return x }\n0")
   "E-RET-002"))

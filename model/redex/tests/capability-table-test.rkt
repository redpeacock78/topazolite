#lang racket

;; [REQ: BOR-006] 構築子の label ごとの capability 表。

(require rackunit
         racket/set
         "../borrow.rkt"
         "../diagnostic.rkt")

;; 表の値は (cons ws tbl) の組である。ws は capability の集合、tbl は
;; (cons K i) から同じ組への hash か #f である。

(test-case
 "region-ctx-field-table は fields 欄を出し入れする"
 (define tbl (hash (cons 'some 0) (cons (set '(1)) #f)))
 (define Λ (region-ctx-add-token (empty-region-ctx) 'o (set) #f #f tbl))
 (check-equal? (region-ctx-field-table Λ 'o) tbl)
 ;; 項目そのものが無い。
 (check-false (region-ctx-field-table (empty-region-ctx) 'o))
 ;; fields を渡さない既定の呼出し。
 (define Λ_plain (region-ctx-add-token (empty-region-ctx) 'b (set '(1))))
 (check-false (region-ctx-field-table Λ_plain 'b))
 ;; ws の側は既定の呼出しでも従来どおり読める。
 (check-equal? (region-ctx-token Λ_plain 'b) (set '(1))))

;; --- capability-of の枝ごとの確認 ---

(test-case
 "Construct は欄ごとの表を作る"
 (define c '(Construct (Option (Borrowed Res (RVar 0))) some (Borrow 1)))
 (define tbl (capability-field-table (empty-region-ctx) c))
 (check-equal? (hash-keys tbl) (list (cons 'some 0)))
 (check-equal? (car (hash-ref tbl (cons 'some 0))) (set '(1)))
 (check-false (cdr (hash-ref tbl (cons 'some 0)))))

(test-case
 "Let は束縛の表を本体へ運ぶ"
 (define c '(Let (o let (Option (Borrowed Res (RVar 0))))
                 (Construct (Option (Borrowed Res (RVar 0))) some (Borrow 1))
                 o))
 (define tbl (capability-field-table (empty-region-ctx) c))
 (check-equal? (car (hash-ref tbl (cons 'some 0))) (set '(1))))

(test-case
 "Scope は本体の表を通す"
 (define c '(Scope () (Construct (Option Int) some 0)))
 (check-true (hash-has-key? (capability-field-table (empty-region-ctx) c)
                            (cons 'some 0))))

(test-case
 "Yield は継続側の表を通す"
 (define c '(Yield (Scope () 0) (Construct (Option Int) some 0)))
 (check-true (hash-has-key? (capability-field-table (empty-region-ctx) c)
                            (cons 'some 0))))

(test-case
 "span 付きの RegionApp は RegionLam の本体の表を通す"
 (define c '(RegionApp (#:span src 0 10)
                       (RegionLam (#:span src 1 9) (a)
                                  (Construct (Option Int) some 0))
                       ((RVar 0))))
 (check-true (hash-has-key? (capability-field-table (empty-region-ctx) c)
                            (cons 'some 0)))
 ;; ws は空のままである。RegionApp は借用を作らない。
 (check-equal? (borrow-token-key (empty-region-ctx) c) (set)))

(test-case
 "designator は Λ から表を引く"
 (define tbl (hash (cons 'some 0) (cons (set '(1)) #f)))
 (define Λ (region-ctx-add-token (empty-region-ctx) 'o (set) #f #f tbl))
 (check-equal? (capability-field-table Λ 'o) tbl))

(test-case
 "Eliminate は分岐の表を合併する"
 (define c '(Eliminate (Construct Bool true)
                       ((true () ->
                              (Construct (Option (Borrowed Res (RVar 0)))
                                         some (Borrow 1)))
                        (false () ->
                               (Construct (Option (Borrowed Res (RVar 0)))
                                          some (Borrow 2))))))
 (define tbl (capability-field-table (empty-region-ctx) c))
 (check-equal? (car (hash-ref tbl (cons 'some 0))) (set '(1) '(2))))

(test-case
 "入れ子の Construct は内側の表を欄の値に持つ"
 (define c '(Construct (Result (Option (Borrowed Res (RVar 0))) Int) ok
                       (Construct (Option (Borrowed Res (RVar 0)))
                                  some (Borrow 1))))
 (define outer (capability-field-table (empty-region-ctx) c))
 (define inner (cdr (hash-ref outer (cons 'ok 0))))
 (check-equal? (car (hash-ref inner (cons 'some 0))) (set '(1))))

(test-case
 "Eliminate の束縛子は scrutinee の表から capability を受ける"
 (define c '(Eliminate (Construct (Option (Borrowed Res (RVar 0)))
                                  some (Borrow 1))
                       ((none () -> 0)
                        (some (y) -> (Reborrow y)))))
 (check-equal? (borrow-token-key (empty-region-ctx) c) (set '(1))))

(test-case
 "値が構築子であるとは限らない式の表は #f である"
 (check-false (capability-field-table (empty-region-ctx) '(Proj (Rec ((a const 0))) a)))
 (check-false (capability-field-table (empty-region-ctx) '(Rec ((a const 0)))))
 (check-false (capability-field-table (empty-region-ctx) '(Suspend 0)))
 (check-false (capability-field-table (empty-region-ctx) '(Borrow 1))))

(test-case
 "borrow-token-key の返り値は組み替えの前後で変わらない"
 (define Λ (region-ctx-add-token (empty-region-ctx) 'b (set '(1))))
 (check-equal? (borrow-token-key Λ '(Reborrow b)) (set '(1)))
 (check-equal? (borrow-token-key (empty-region-ctx)
                                 '(ProjBorrowAt (RVar 0) (RVar 1) (Borrow 1) a))
               (set '(1 a)))
 (check-equal? (borrow-token-key
                (empty-region-ctx)
                '(Let (y let (BorrowedMut Int (RVar 0))) (BorrowMut 1) y))
               (set '(1)))
 ;; 宣言型が借用でない束縛は空集合を張る。整数リテラルを place と取り違えない。
 (check-equal? (borrow-token-key (empty-region-ctx)
                                 '(Let (y let Int) 1 y))
               (set)))

(test-case
 "locals へ生の集合を渡しても読める"
 (check-equal? (borrow-token-key (empty-region-ctx) 'y (hash 'y (set '(1))))
               (set '(1)))
 (check-false (capability-field-table (empty-region-ctx) 'y
                                      (hash 'y (set '(1))))))

(test-case
 "未知の designator の表取得は E-BOR-020 になる"
 (define reason
   (let/ec return
     (capability-field-table (empty-region-ctx) 'z
                             #:fail (lambda (key . _) (return key)))
     'no-fail))
 (check-equal? reason 'unresolved-borrow-owner)
 (check-equal? (diagnostic-code-of 'typing reason) "E-BOR-020"))

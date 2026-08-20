#lang racket

;; [REQ: BOR-001] 分岐で合流した借用は両分岐の寿命に収まる。

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; merge-record-types/impl を直接呼ぶので、fresh-lifetime! が読む lifetime-counter と
;; emit-constraint! が読む lifetime-collector を試験の側で張る。
(define (merge/fresh types)
  (parameterize ([lifetime-counter (box 0)]
                 [lifetime-collector (box '())]
                 [alpha-table (box (hash))]
                 [merge-alpha-sources (make-hash)])
    (merge-record-types/impl types)))

;; 制約まで見る版。merge-position を張り、立った制約を型と witness に添えて返す。
(define merge-ir (build-region-ir `(Scope () (Scope () (resource 1)))))
(define merge-point '(0))
(define merge-here (region-at merge-ir merge-point))
(define merge-outer (region-at merge-ir '()))
(define merge-outer-rho (region->rho merge-ir merge-outer))
(define merge-here-rho (region->rho merge-ir merge-here))

(define (merge/positioned types)
  (parameterize ([lifetime-counter (box 0)]
                 [lifetime-collector (box '())]
                 [alpha-table (box (hash))]
                 [merge-alpha-sources (make-hash)]
                 [merge-position (list merge-ir merge-point 0)])
    (define-values (merged witnesses) (merge-record-types/impl types))
    (list merged witnesses (collected-constraints))))

(define (merge-constraints cs)
  (filter (lambda (c) (eq? (region-constraint-kind c) 'merge)) cs))

(define (contains-constraints cs)
  (filter (lambda (c) (eq? (region-constraint-kind c) 'contains)) cs))

;; 位置の無い呼び出しでは制約を立てない。
(let ()
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed Int (RVar 1)) imm))))
  (define cs
    (parameterize ([lifetime-counter (box 0)]
                   [lifetime-collector (box '())]
                   [alpha-table (box (hash))]
                   [merge-alpha-sources (make-hash)])
      (merge-record-types/impl (list left right))
      (collected-constraints)))
  (check-equal? cs '()))

;; 両分岐が同じ型の借用を返すとき、合流の結果は 1 つの寿命を持つ。
(let ()
  (define (rvar? t) (match t [`(RVar ,_) #t] [_ #f]))
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed Int (RVar 1)) imm))))
  (define-values (merged witnesses) (merge/fresh (list left right)))
  (check-true (and merged #t))
  (define merged-field (first (second merged)))
  (check-true (rvar? (third (second merged-field))))
  (check-equal? (first (second merged-field)) 'Borrowed))

;; 借用だけの合流は FieldType witness を 1 本も作らない。
(let ()
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed Int (RVar 1)) imm))))
  (define-values (_merged witnesses) (merge/fresh (list left right)))
  (check-equal? (map (lambda (w) (first (first (second w)))) witnesses)
                (list 'Presence)))

;; memo が効いていることを制約の側で見る。
(let ()
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed Int (RVar 1)) imm))))
  (match-define (list merged _witnesses cs) (merge/positioned (list left right)))
  (define merged-alpha (third (second (first (second merged)))))
  (define merge-cs (merge-constraints cs))
  (check-equal? (length merge-cs) 2)
  (check-equal? (remove-duplicates (map region-constraint-right merge-cs))
                (list merged-alpha))
  (check-equal? (sort (map (lambda (c) (second (region-constraint-left c))) merge-cs) <)
                (list 0 1)))

;; 枝が 3 つ以上でも α_m は 1 つである。
(let ()
  (define types
    (for/list ([k (in-range 3)])
      `(Record ((a (Borrowed Int (RVar ,k)) imm)))))
  (match-define (list merged _witnesses cs) (merge/positioned types))
  (define merged-field (first (second merged)))
  (check-equal? (first (second merged-field)) 'Borrowed)
  (define merged-alpha (third (second merged-field)))
  (define merge-cs (merge-constraints cs))
  (check-equal? (length merge-cs) 3)
  (check-equal? (remove-duplicates (map region-constraint-right merge-cs))
                (list merged-alpha)))

;; 可変借用の合流も同じ形である。
(let ()
  (define left `(Record ((a (BorrowedMut Int (RVar 0)) mut))))
  (define right `(Record ((a (BorrowedMut Int (RVar 1)) mut))))
  (define-values (merged _w) (merge/fresh (list left right)))
  (check-equal? (first (second (first (second merged)))) 'BorrowedMut))

;; payload が違えば合流しない。G5b の Union の経路のままである。
(let ()
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed String (RVar 1)) imm))))
  (define-values (merged _w) (merge/fresh (list left right)))
  (check-equal? (first (second (first (second merged)))) 'Union))

;; α の採番差で結果が変わらない。
(let ()
  (define (verdict types)
    (match-define (list merged _witnesses cs) (merge/positioned types))
    (define merged-field (first (second merged)))
    (define merged-alpha (third (second merged-field)))
    (define merge-cs (merge-constraints cs))
    (list (first (second merged-field))
          (length merge-cs)
          (equal? (remove-duplicates (map region-constraint-right merge-cs))
                  (list merged-alpha))))
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed Int (RVar 1)) imm))))
  (check-equal? (verdict (list left right)) (verdict (list right left)))
  (check-equal? (verdict (list left right)) (list 'Borrowed 2 #t)))

;; 片方が具体的な region のときは、具体の側を下限として扱う。
(let ()
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed Int ,merge-outer-rho) imm))))
  (match-define (list merged _witnesses cs) (merge/positioned (list left right)))
  (define merged-field (first (second merged)))
  (check-equal? (first (second merged-field)) 'Borrowed)
  (define merged-alpha (third (second merged-field)))
  (check-equal? (for/list ([c (in-list (contains-constraints cs))])
                  (list (region-constraint-left c) (region-constraint-right c)))
                (list (list merged-alpha merge-here)
                      (list merged-alpha merge-outer)))
  (check-equal? (map region-constraint-left (merge-constraints cs))
                (list '(RVar 0))))

;; 全ての枝が寿命変数でも α_m は解ける。§10.1。
(let ()
  (define left `(Record ((a (Borrowed Int (RVar 0)) imm))))
  (define right `(Record ((a (Borrowed Int (RVar 1)) imm))))
  (match-define (list merged _witnesses cs) (merge/positioned (list left right)))
  (define merged-alpha (third (second (first (second merged)))))
  (check-equal? (for/list ([c (in-list (contains-constraints cs))])
                  (list (region-constraint-left c) (region-constraint-right c)))
                (list (list merged-alpha merge-here)))
  (define lowers
    (list (region-constraint 'contains `(RVar 0) merge-here merge-point #f)
          (region-constraint 'contains `(RVar 1) merge-here merge-point #f)))
  (check-equal? (first (region-solve merge-ir (append lowers cs))) 'ok))

;; 両方が具体的な region のときは合流しない。G5b の Union の経路のままである。
(let ()
  (define left `(Record ((a (Borrowed Int ,merge-outer-rho) imm))))
  (define right `(Record ((a (Borrowed Int ,merge-here-rho) imm))))
  (match-define (list merged _witnesses cs) (merge/positioned (list left right)))
  (check-equal? (first (second (first (second merged)))) 'Union)
  (check-equal? cs '()))

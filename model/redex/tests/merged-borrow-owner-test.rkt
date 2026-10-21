#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow-gen.rkt"
         "../borrow.rkt"
         "../borrow-oracle.rkt"
         "../diagnostic.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define (replace-symbol term target replacement)
  (cond
    [(eq? term target) replacement]
    [(pair? term)
     (cons (replace-symbol (car term) target replacement)
           (replace-symbol (cdr term) target replacement))]
    [else term]))

(define (find-borrow-point core)
  (let walk ([term core] [point '()])
    (cond
      [(match term
         [(or `(Borrow ,_) `(BorrowMut ,_)) #t]
         [_ #f])
       point]
      [else
       (for/or ([child (in-list (core-children term))]
                [index (in-naturals)])
         (walk child (append point (list index))))])))

(define (prepare core)
  (define ir (build-region-ir core))
  (define filled (fill-region-placeholders core ir))
  (define point (find-borrow-point core))
  (check-not-false point "借用 point がある")
  (define rho (region->rho ir (region-at ir point)))
  (define annotated (annotate-regions (replace-symbol filled 'ph rho) ir))
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (match (type-of/raw*+borrows annotated '() '() '()
                                (region-ctx ir '() (hash) (hash))
                                #:mut-types mut-types
                                #:callable-contexts callable-contexts)
    [(list 'ok (list type _row table sigma renamed sidecar))
     (define materialized (materialize-regions ir renamed table sigma))
     (define machine-core
       (annotate-callable-contexts
        (annotate-mut-binding-types materialized (unbox mut-types))
        (unbox callable-contexts) 'renamed))
     (values (inject-g2m machine-core) sidecar ir type)]
    [other (fail (format "Core が型検査されなかった: ~s; typed=~s"
                         other annotated))]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 300])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (cfg-core cfg)
  (match cfg [`(cfg ,core ,_ ...) core]))

(define (cfg-fields cfg)
  (match cfg
    [`(cfg ,core ,heap ,states ,tokens ,events)
     (values core heap states tokens events)]))

(define (borrow-refs term)
  (cond
    [(match term
       [(or `(BorrowRef ,_ ,_ ,_) `(BorrowMutRef ,_ ,_ ,_)) #t]
       [_ #f])
     (list term)]
    [(pair? term)
     (append (borrow-refs (car term)) (borrow-refs (cdr term)))]
    [else '()]))

(define (check-live-trace configs rules expected)
  (define rows
    (for/list ([config (in-list configs)])
      (runtime-row config '() expected)))
  (define start-index
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
  (define scope-exit-index
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (eq? rule 'R-ScopeValue))
      index))
  (check-not-false start-index "trace に runtime-row がある config がある")
  (check-not-false scope-exit-index "trace に Scope 終端がある")
  (for ([config (in-list (drop configs start-index))]
        [row (in-list (drop rows start-index))]
        [index (in-naturals start-index)])
    (check-not-false row (format "config ~a の runtime-row: ~s" index config))
    (check-true (config-ok? config '() expected row)
                (format "config ~a の config-ok?" index)))
  (check-true (redex-match? G2m v (cfg-core (last configs)))
              "trace の終端が値")
  (check-false (pair? (borrow-refs (cfg-core (last configs))))
               "終端値に BorrowRef が残らない"))

(define (config-after configs rules rule-name)
  (define index (index-of rules rule-name))
  (check-not-false index)
  (list-ref configs (add1 index)))

(define (heap-field heap root label)
  (match (assoc root heap)
    [`(,_ (Rec ,fields) (declared ,_))
     (match (assoc label fields)
       [`(,_ ,_ ,value) value]
       [_ (fail (format "heap に欄 ~a がない: ~s" label heap))])]
    [_ (fail (format "heap に place ~a の record がない: ~s" root heap))]))

(define (merged-shared-core branch left right)
  `(Scope ()
     (Let (x let (Owned (Record ((n Int imm))))) (Rec ((n imm 1)))
       (Let (y let (Owned (Record ((n Int imm))))) (Rec ((n imm 2)))
         (Let (b let (Borrowed (Record ((n Int imm))) ph))
              (Eliminate (Construct Bool ,branch)
                ((true () -> (Borrow ,left)) (false () -> (Borrow ,right))))
              (Read (ProjBorrow b n)))))))

(test-case "合流した共有借用からの射影は走った枝の root と path を保つ"
  (for ([branch '(true false)]
        [expected-root '(0 1)]
        [expected-value '(1 2)])
    (define-values (start _sidecar _ir type)
      (prepare (merged-shared-core branch 'x 'y)))
    (check-equal? type 'Int)
    (define-values (configs rules) (trace-g2 start))
    (check-live-trace configs rules 'Int)
    (define-values (core heap _states _tokens _events)
      (cfg-fields (config-after configs rules 'R-ProjBorrow)))
    (match (borrow-refs core)
      [(list `(BorrowRef ,root ,path ,_))
       (check-equal? root expected-root)
       (check-equal? path '(n))
       (check-equal? (heap-field heap root 'n) expected-value)]
      [refs (fail (format "BorrowRef 一つを期待した: ~s" refs))])))

(define (merged-mut-core branch)
  `(Scope ()
     (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
       (Let (y let (Owned (Record ((n Int mut))))) (Rec ((n mut 2)))
         (Scope ()
           (Let (b let (BorrowedMut (Record ((n Int mut))) ph))
                (Eliminate (Construct Bool ,branch)
                  ((true () -> (BorrowMut x)) (false () -> (BorrowMut y))))
                (Let (ignored const Unit) (Assign (ProjBorrow b n) 5)
                     (Read (ProjBorrow b n)))))))))

(test-case "合流した可変借用からの射影は選んだ field だけを書き換える"
  (for ([branch '(true false)]
        [expected-root '(0 1)]
        [expected-before '(1 2)]
        [expected-final '((5 2) (1 5))])
    (define-values (start _sidecar _ir type) (prepare (merged-mut-core branch)))
    (define-values (configs rules) (trace-g2 start))
    (check-live-trace configs rules type)
    (define-values (core heap _states _tokens _events)
      (cfg-fields (config-after configs rules 'R-ProjBorrowMut)))
    (match (borrow-refs core)
      [(list `(BorrowMutRef ,root (n) ,token)
             `(BorrowMutRef ,same-root () ,same-token))
       (check-equal? root expected-root)
       (check-equal? same-root root)
       (check-equal? same-token token)
       (check-equal? (heap-field heap root 'n) expected-before)]
      [refs (fail (format "射影先と元の BorrowMutRef を期待した: ~s" refs))])
    (define-values (_final-core final-heap _final-states _final-tokens _final-events)
      (cfg-fields (last configs)))
    (check-equal? (list (heap-field final-heap 0 'n)
                        (heap-field final-heap 1 'n))
                  expected-final)))

(test-case "同じ owner の合流後の射影も実行できる"
  (define-values (start _sidecar _ir type)
    (prepare (merged-shared-core 'true 'x 'x)))
  (define-values (configs rules) (trace-g2 start))
  (check-equal? type 'Int)
  (check-live-trace configs rules 'Int)
  (check-equal? (cfg-core (last configs)) 1))

(test-case "再借用と射影の machine rule は入力借用値から capability を作る"
  (check-equal?
   (apply-reduction-relation
    -->g2
    '(cfg (ReborrowAt 0 (BorrowMutRef 7 () 1)) () () () ()))
   '((cfg (BorrowRef 7 () 0) () () () ())))
  (check-equal?
   (apply-reduction-relation
    -->g2
    '(cfg (ProjBorrowAt 0 (BorrowRef 7 () 1) n) () () () ()))
   '((cfg (BorrowRef 7 (n) 1) () () () ())))
  (check-equal?
   (apply-reduction-relation
    -->g2
    '(cfg (ProjBorrowAt 0 (BorrowMutRef 7 () 1) n)
          ((7 (Rec ((n mut 1))) (declared (Owned (Record ((n Int mut)))))))
          ((7 Available)) () ()))
   '((cfg (BorrowMutRef 7 (n) 1)
          ((7 (Rec ((n mut 1))) (declared (Owned (Record ((n Int mut)))))))
          ((7 Available)) () ()))))

(test-case "直接の BorrowAt と BorrowMutAt の own 不一致は E-BOR-023 のまま拒否する"
  (for ([form '(BorrowAt BorrowMutAt)])
    (define core `(Scope (1) (,form 0 (Own 7 ()) 1)))
    (define result
      (type-of/raw core '((1 Int)) '() '() (empty-region-ctx)))
    (check-equal? (first result) 'fail)
    (check-equal? (second result) 'own-designator-mismatch))
  (for ([form '(BorrowAt BorrowMutAt)])
    (define cfg
      `(cfg (Read (,form 4 (Own 1 ()) 0))
            ((0 7 (declared Int)) (1 8 (declared Int)))
            ((0 Available) (1 Available)) () ()))
    (check-false (config-ok? cfg '() 'Int '()))))

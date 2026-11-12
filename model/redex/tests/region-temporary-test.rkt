#lang racket

(require rackunit
         racket/list
         racket/match
         racket/set
         "../machine.rkt"
         "../region.rkt")

(define (checked-ir core)
  (define ir (build-region-ir core))
  (check-true (lexical-region-ir-ok? ir) (format "不正な lexical IR: ~s" core))
  ir)

(define (temporary ir point)
  (define result (region-at/temporary ir point))
  (unless result
    (fail (format "point ~s に一時 region が無い" point)))
  result)

(define (borrowing-expression? node)
  (match node
    [`(,(or 'Borrow 'BorrowMut 'Reborrow) ,_ ...) #t]
    [_ #f]))

(define (temporary-consumer? node)
  (match node
    [`(Apply ,_ ,args ...)
     (ormap borrowing-expression? args)]
    [`(Read ,operand) (borrowing-expression? operand)]
    [`(Assign ,target ,_) (borrowing-expression? target)]
    [_ #f]))

(define (ordinary-regions ir core)
  (for*/list ([point (in-list (core-points core))]
              [ρ (in-list (list (region-at ir point)
                                (region-at/branch ir point)
                                (region-at/eliminate ir point)))])
    ρ))

(define (collect-temporary-regions ir core)
  (for/list ([point (in-list (core-points core))]
             #:when (region-at/temporary ir point))
    (region-at/temporary ir point)))

(test-case "一時region_同じApplyの実引数は共有する"
  (define ir (checked-ir '(Apply f (BorrowMut x) (BorrowMut y))))
  (check-equal? (temporary-consumer-point ir '(1)) '())
  (check-equal? (temporary-consumer-point ir '(2)) '())
  (check-equal? (temporary ir '())
                (region-at/temporary ir (temporary-consumer-point ir '(1))))
  (check-equal? (region-at/temporary ir (temporary-consumer-point ir '(1)))
                (region-at/temporary ir (temporary-consumer-point ir '(2)))))

(test-case "一時region_別のApplyは別"
  (define core
    '(Let (u const Unit)
       (Apply f (BorrowMut x))
       (Apply g (BorrowMut y))))
  (define ir (checked-ir core))
  (define first (temporary ir '(0)))
  (define second (temporary ir '(1)))
  (check-not-equal? first second)
  (check-false (regions-overlap? ir first second)))

(test-case "一時region_内側先は兄弟"
  (define core '(Apply h (Apply g (BorrowMut x)) (BorrowMut x)))
  (define ir (checked-ir core))
  (define outer (temporary ir '()))
  (define inner (temporary ir '(1)))
  (check-equal? (region-parent ir inner) (region-parent ir outer))
  (check-false (regions-overlap? ir inner outer)))

(test-case "一時region_内側後は子"
  (define core '(Apply h (BorrowMut x) (Apply g (BorrowMut x))))
  (define ir (checked-ir core))
  (define outer (temporary ir '()))
  (define inner (temporary ir '(2)))
  (check-equal? (region-parent ir inner) outer)
  (check-true (regions-overlap? ir inner outer)))

(test-case "一時region_後のScope内ownerはNをoutliveする"
  (define core
    '(Apply h (BorrowMut x)
       (Scope ()
         (Let (o let (Owned Int)) 1
           (Apply g (BorrowMut o))))))
  (define ir (checked-ir core))
  (define outer (temporary ir '()))
  (define nested (temporary ir '(2 0 1)))
  (define owner-region (region-at/branch ir '(2 0 1)))
  (check-equal? (region-parent ir nested) outer)
  (check-true (region-outlives? ir owner-region nested)))

(test-case "一時region_後の子の枝内NはCと重なる"
  (define core
    '(Apply h (BorrowMut x)
       (Eliminate y
         ((none () -> (Apply g (BorrowMut x)))
          (some (v) -> unit)))))
  (define ir (checked-ir core))
  (define outer (temporary ir '()))
  (define nested (temporary ir '(2 1)))
  (define branch-region (branch-region-of ir '(2) 0))
  (check-equal? (region-parent ir nested) outer)
  (check-true (regions-overlap? ir outer nested))
  (check-true (region-outlives? ir branch-region nested)))

(test-case "一時region_後のLamではCの退場がNを終えない"
  (define core
    '(Let (f const Unit)
       (Apply h (BorrowMut x)
         (Scope ()
           (Lam User c0 (p) (Apply g (BorrowMut p)))))
       (Apply f 0)))
  (define ir (checked-ir core))
  (define outer (temporary ir '(0)))
  (define nested (temporary ir '(0 2 0 0)))
  (define callable-region (region-at/branch ir '(0 2 0 0)))
  (check-equal? (region-parent ir nested) outer)
  (check-true (region-outlives? ir callable-region nested))
  (check-true (set-member? (regions-exiting-at ir '(0)) outer))
  (check-false (set-member? (regions-exiting-at ir '(0)) nested))
  (check-true (set-member? (regions-exiting-at ir '(0 2 0 0)) nested)))

(test-case "一時region_Assignの値は子"
  (define ir
    (checked-ir '(Assign (BorrowMut x) (Apply g (BorrowMut y)))))
  (define outer (temporary ir '()))
  (define inner (temporary ir '(1)))
  (check-equal? (region-parent ir inner) outer)
  (check-true (regions-overlap? ir inner outer)))

(test-case "一時region_Reborrowのoperandは兄弟"
  (define core '(Apply f (Reborrow (Read (BorrowMut p)))))
  (define ir (checked-ir core))
  (define outer (temporary ir '()))
  (define inner (temporary ir '(1 0)))
  (check-equal? (temporary-consumer-point ir '(1)) '())
  (check-equal? (temporary-consumer-point ir '(1 0 0)) '(1 0))
  (check-equal? (region-parent ir inner) (region-parent ir outer))
  (check-false (regions-overlap? ir inner outer)))

(test-case "一時region_枝本体とLam本体"
  (define core
    '(Eliminate y
       ((none () -> (Apply f (BorrowMut x)))
        (some (v) -> (Lam User c0 (p) (Apply g (BorrowMut p)))))))
  (define ir (checked-ir core))
  (define branch-consumer (temporary ir '(1)))
  (define lambda-consumer (temporary ir '(2 0)))
  (define branch-region (branch-region-of ir '() 0))
  (define callable-base (region-at/branch ir '(2 0)))
  (check-equal? (region-parent ir branch-consumer) branch-region)
  (check-equal? (region-parent ir lambda-consumer) callable-base)
  (check-not-equal? callable-base (branch-region-of ir '() 1)))

(test-case "一時region_通常のregion-atは返さない"
  (define core
    '(Eliminate y
       ((none () -> (Apply f (BorrowMut x)))
        (some (v) -> (Lam User c0 (p) (Apply g (BorrowMut p)))))))
  (define ir (checked-ir core))
  (define temporary-regions (collect-temporary-regions ir core))
  (for* ([ρ (in-list (ordinary-regions ir core))]
         [temporary-ρ (in-list temporary-regions)])
    (check-false (equal? ρ temporary-ρ))))

(test-case "一時region_既存の識別子は不変"
  (define core
    '(Eliminate y
       ((none () -> (Apply f (BorrowMut x)))
        (some (v) -> (Lam User c0 (p) (Apply g (BorrowMut p)))))))
  (define ir (checked-ir core))
  (define ordinary
    (remove-duplicates (ordinary-regions ir core) equal?))
  (define temporary-regions (collect-temporary-regions ir core))
  (for* ([ρ (in-list ordinary)]
         [temporary-ρ (in-list temporary-regions)])
    (check-true (< (region->rho ir ρ) (region->rho ir temporary-ρ)))))

(test-case "一時region_退場"
  (for ([core (in-list
               (list '(Apply f (BorrowMut x))
                     '(Read (Borrow x))
                     '(Assign (BorrowMut x) 0)))])
    (define ir (checked-ir core))
    (check-true
     (set-member? (regions-exiting-at ir '())
                  (temporary ir '())))))

(test-case "一時region_Readの直接借用"
  (for ([core (in-list (list '(Read (Borrow x))
                             '(Read (BorrowMut x))))])
    (define ir (checked-ir core))
    (check-equal? (temporary-consumer-point ir '(0)) '())
    (check-not-false (region-at/temporary ir '())))
  (define plain-read (checked-ir '(Read x)))
  (check-false (region-at/temporary plain-read '()))
  (define bare-borrow (checked-ir '(Borrow x)))
  (check-false (temporary-consumer-point bare-borrow '())))

(test-case "一時region_Applyのcalleeと通常引数は対象外"
  (define apply-core '(Apply (BorrowMut f) (BorrowMut x) y))
  (define apply-ir (checked-ir apply-core))
  (check-not-false (region-at/temporary apply-ir '()))
  (check-false (temporary-consumer-point apply-ir '(0)))
  (check-equal? (temporary-consumer-point apply-ir '(1)) '())
  (check-false (temporary-consumer-point apply-ir '(2))))

(test-case "一時region_Assignの値は対象外"
  (define assign-core '(Assign (BorrowMut x) (BorrowMut y)))
  (define assign-ir (checked-ir assign-core))
  (check-not-false (region-at/temporary assign-ir '()))
  (check-equal? (temporary-consumer-point assign-ir '(0)) '())
  (check-false (temporary-consumer-point assign-ir '(1))))

(test-case "一時region_C3"
  (define core
    '(Scope ()
       (Eliminate x
         ((none () -> (Apply f (Borrow x)))
          (some (v) -> (Read (BorrowMut y)))))))
  (define ir (checked-ir core))
  (define old-count
    (for/sum ([point (in-list (core-points core))])
      (match (core-node core point)
        [`(Scope ,_ ,_) 1]
        [`(,(or 'Eliminate 'UnionEliminate) ,_ (,branches ...))
         (+ 1 (length branches))]
        [_ 0])))
  (define consumer-count
    (for/sum ([point (in-list (core-points core))])
      (if (temporary-consumer? (core-node core point)) 1 0)))
  (check-equal? (sub1 (set-count (region-ir-regions ir)))
                (+ old-count consumer-count)))

(test-case "一時region_非lexicalなIRでは返さない"
  (define root (region 0))
  (define ir (region-ir (set root) (set) (hash root '())))
  (check-false (region-at/temporary ir '()))
  (check-false (temporary-consumer-point ir '(0))))

(define (machine-trace-to-final initial)
  (let loop ([config initial] [trace (list initial)] [fuel 20])
    (when (zero? fuel)
      (fail "machine trace が fuel 内に停止しない"))
    (match (raw-steps-g2 config)
      ['() trace]
      [(list next) (loop next (append trace (list next)) (sub1 fuel))]
      [steps (fail (format "machine trace が非決定的: ~s" steps))])))

(define (contains-borrow-ref? term)
  (match term
    [`(,(or 'BorrowRef 'BorrowMutRef) ,_ ,_ ,_) #t]
    [(? list?) (ormap contains-borrow-ref? term)]
    [_ #f]))

(define (no-borrow-in-control-or-available-heap? config)
  (match config
    [`(cfg ,control ,heap ,states ,_ ,_)
     (and (not (contains-borrow-ref? control))
          (for/and ([entry (in-list heap)]
                    #:when (match (assoc (first entry) states)
                             [(list _ 'Available) #t]
                             [_ #f]))
            (not (contains-borrow-ref? (second entry)))))]))

(test-case "一時region_評価完了後に出現が残らない"
  (define configs
    (list
     '(cfg (Apply (Lam User c0 (arg) unit)
                  (ReborrowAt 17 (BorrowMutRef 0 () 16)))
           ((0 1)) ((0 Available)) () ())
     '(cfg (Read (BorrowAt 17 (Own 0 ()) 0))
           ((0 1)) ((0 Available)) () ())
     '(cfg (Assign (BorrowMutAt 17 (Own 0 ()) 0) 2)
           ((0 1)) ((0 Available)) () ())))
  (for ([initial (in-list configs)])
    (define trace (machine-trace-to-final initial))
    (check-true (>= (length trace) 2))
    (check-true
     (no-borrow-in-control-or-available-heap? (last trace)))))

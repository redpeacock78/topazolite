#lang racket

(require rackunit
         racket/match
         "../borrow-oracle.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define nested-forward-type
  '(ForallRegion (a)
     (NFn ((Record ((a (Borrowed Int (RParam a)) imm))))
          Int () () () User)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 10000])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (collect-region-app-arguments term)
  (match term
    [`(RegionApp ,callee (,rhos ...))
     (cons rhos (collect-region-app-arguments callee))]
    [(? pair? pair)
     (append (collect-region-app-arguments (car pair))
             (collect-region-app-arguments (cdr pair)))]
    [_ '()]))

(define (collect-region-lam-binders term)
  (match term
    [`(RegionLam (,rps ...) ,body)
     (append rps (collect-region-lam-binders body))]
    [(? pair? pair)
     (append (collect-region-lam-binders (car pair))
             (collect-region-lam-binders (cdr pair)))]
    [_ '()]))

(test-case "nested borrowed field を forward から ignore へ実行時に転送する"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 7
         (Apply
          (RegionLam (a)
            (Lam User forward (p)
              (Let (result const Int)
                   (Apply
                    (RegionLam (a) (Lam User ignore (q) 11))
                    p)
                result)))
          (Rec ((a imm (Borrow owner))))))))
  (define callables
    `((forward ,nested-forward-type)
      (ignore ,nested-forward-type)))
  (define ir (build-region-ir core))
  (define typed (core-type-of/regions core '() callables #:ir ir))
  (check-true (region-typed? typed)
              (format "nested forwarding Core の region 型付け: ~s" typed))
  (when (region-typed? typed)
    (define machine-core (region-execution-core typed))
    (define apps (collect-region-app-arguments machine-core))
    (check-true (>= (length apps) 2)
                "forward と内部 ignore の暗黙 RegionApp を実行用 Core に含む")
    (match* ((collect-region-app-arguments machine-core)
             (collect-region-lam-binders machine-core))
      [((list _ (list `(RParam ,inner-rp))) (list outer-rp _))
       (check-equal? inner-rp outer-rp
                     "内側 RegionApp は σ の region でなく外側の RParam を使う")]
      [(_ _) (fail "nested forwarding の RegionApp 構造が不正")])
    (define start (inject-g2m (erase-core machine-core)))
    (define configs (trace-g2 start))
    (for ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config callables (region-typed-type typed)
                               #:region-ir ir))
      (check-not-false row (format "config ~a runtime-row" index))
      (when row
        (check-true (config-ok? config callables (region-typed-type typed) row
                                #:region-ir ir)
                    (format "config ~a config-ok?" index))))
    (check-equal? (check-borrow-execution start (region-typed-sidecar typed)
                                          ir 300 (make-bcounters))
                  'ok
                  "nested forwarding trace passes borrow oracle")
    (match (last configs)
      [`(cfg 11 ,_heap ,_states ,_tokens ,_events) (void)]
      [other (fail (format "forward -> implicit RegionApp ignore trace expected 11, got ~s"
                           other))])))

(test-case "外側借用と欄内借用の異なる region を持つ実引数を受ける"
  (define sink-type
    '(NFn ((Borrowed
            (Record ((a (Borrowed Int 4) imm)))
            2))
          Int () () () User))
  (define core
    '(Apply
      (RegionApp
       (RegionLam (outer inner) (Lam User ignore (q) 11))
       (2 4))
      (BorrowRef 0 () 2)))
  (define callables `((ignore ,sink-type)))
  (define heap
    '((0 (Rec ((a imm (BorrowRef 1 () 4))))
         (declared (Record ((a (Borrowed Int 4) imm)))))))
  (define states '((0 Available) (1 Available)))
  (define start `(cfg ,core ,(append heap '((1 7 (declared Int)))) ,states () ()))
  (define configs (trace-g2 start))
  (check-equal? (collect-region-app-arguments core) '((2 4)))
  (define initial-row (runtime-row start callables 'Int))
  (check-not-false initial-row "initial config has runtime-row")
  (for ([config (in-list configs)] [index (in-naturals)])
    (define row (runtime-row config callables 'Int))
    (check-not-false
     row
     (format "config ~a has runtime-row: ~s" index config))
    (when row
      (check-true (config-ok? config callables 'Int row)
                  (format "config ~a passes config-ok?" index))
      (check-equal? row initial-row
                    (format "config ~a preserves runtime-row" index))))
  (check-equal? (check-borrow-execution start #f #f 300 (make-bcounters))
                'ok
                "different outer and field regions pass the borrow oracle")
  (match (last configs)
    [`(cfg 11 ,_heap ,_states ,_tokens ,_events) (void)]
    [other (fail (format "expected result 11, got ~s" other))]))

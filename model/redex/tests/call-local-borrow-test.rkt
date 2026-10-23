#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow-gen.rkt"
         "../diagnostic.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define sink-callables
  '((sink (ForallRegion (a)
           (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))
    (sink2 (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a))
                  (BorrowedMut Int (RParam a)))
                 Int () () () User)))
    (sink-shared (ForallRegion (a)
                   (NFn ((Borrowed Int (RParam a))) Int () () () User)))))

(define (sink-call argument [region 'owner-ph])
  `(Apply (RegionApp (RegionLam (a) (Lam User sink (p) 0)) (,region))
          ,argument))

(define (sink2-call left right)
  `(Apply (RegionApp (RegionLam (a) (Lam User sink2 (p q) 0)) (scope-ph))
          ,left ,right))

(define (sink-shared-call argument [region 'owner-ph])
  `(Apply (RegionApp (RegionLam (a) (Lam User sink-shared (p) 0))
                     (,region))
          ,argument))

(define (scoped-sink-call owner)
  `(Scope ()
     (Let (temporary let (BorrowedMut Int ph))
          (BorrowMut ,owner)
       ,(sink-call 'temporary))))

(define (type-core core [places '()])
  (define ir (build-region-ir core))
  (define (contains-marker? term marker)
    (or (eq? term marker)
        (and (pair? term)
             (or (contains-marker? (car term) marker)
                 (contains-marker? (cdr term) marker)))))
  (define owner-rho
    (and (contains-marker? core 'owner-ph)
         (region->rho ir (owner-let-body-region ir '(0)))))
  (define scope-rho (region->rho ir (region-at ir '())))
  (define filled
    (let replace ([term (fill-region-placeholders core ir)])
      (cond
        [(eq? term 'owner-ph) owner-rho]
        [(eq? term 'scope-ph) scope-rho]
        [(pair? term) (cons (replace (car term)) (replace (cdr term)))]
        [else term])))
  (values ir filled
          (core-type-of/regions filled places sink-callables #:ir ir)))

(define (failure-code core)
  (define-values (_ir _filled typed) (type-core core))
  (and (diagnostic? typed) (diagnostic-id typed)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 300])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (check-live-trace typed expected)
  (define start (inject-g2m (region-execution-core typed)))
  (define configs (trace-g2 start))
  (define rows
    (for/list ([config (in-list configs)])
      (runtime-row config sink-callables expected)))
  (define first-live
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
  (check-not-false first-live "trace に runtime-row がある config がある")
  (for ([config (in-list (drop configs first-live))]
        [row (in-list (drop rows first-live))]
        [index (in-naturals first-live)])
    (check-not-false row (format "config ~a の runtime-row" index))
    (check-true (config-ok? config sink-callables expected row)
                (format "config ~a の config-ok?" index)))
  (check-true (redex-match? G2m v (match (last configs)
                                   [`(cfg ,value ,_ ...) value]))
              "trace の終端が値"))

(test-case "裸の呼出しを同じ lexical Scope で続けると二度目の BorrowMut は E-BOR-003"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (first const Int) ,(sink-call '(BorrowMut x))
           ,(sink-call '(BorrowMut x))))))
  (check-equal? (failure-code core) "E-BOR-003"))

(test-case "裸の呼出しの lexical loan は Scope 全体に残り Move は E-BOR-008"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (called const Int) ,(sink-call '(BorrowMut x))
           (Move x)))))
  (check-equal? (failure-code core) "E-BOR-008"))

(test-case "兄弟 Scope で呼出しを包むと loan が終わり Move できる"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (first const Int) ,(scoped-sink-call 'x)
           (Let (second const Int) ,(scoped-sink-call 'x)
             (Move x))))))
  (define-values (_ir _filled typed) (type-core core))
  (check-true (region-typed? typed) (format "region typing: ~s" typed))
  (check-equal? (region-typed-type typed) '(Owned Int))
  (check-live-trace typed '(Owned Int)))

(test-case "一つ目だけ呼出しを包むと裸の二つ目は E-BOR-003"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (first const Int) ,(scoped-sink-call 'x)
           ,(sink-call '(BorrowMut x))))))
  (check-equal? (failure-code core) "E-BOR-003"))

(define (two-argument-core right-owner)
  `(Scope (1 2)
     (Scope ()
       (Let (left let (BorrowedMut Int ph)) (BorrowMut 1)
         (Let (right let (BorrowedMut Int ph)) (BorrowMut ,right-owner)
           ,(sink2-call 'left 'right))))))

(test-case "一つの Scope の同じ Apply へ異なる owner の二借用を渡せる"
  (define-values (_ir _filled typed)
    (type-core (two-argument-core 2) '((1 Int) (2 Int))))
  (check-true (region-typed? typed) (format "region typing: ~s" typed)))

(test-case "一つの Apply へ同じ owner の二借用を渡すと E-BOR-003"
  (define-values (_ir _filled typed)
    (type-core (two-argument-core 1) '((1 Int) (2 Int))))
  (check-true (diagnostic? typed))
  (check-equal? (diagnostic-id typed) "E-BOR-003"))

(test-case "RegionApp に包んだ Scope の region を渡すと E-TYP-023"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Scope ()
           (Let (temporary let (BorrowedMut Int ph)) (BorrowMut x)
             ,(sink-call 'temporary 'ph))))))
  (check-equal? (failure-code core) "E-TYP-023"))

(test-case "既存の BorrowedMut を包んで渡しても元の loan は短くならない"
  (define core
    `(Scope (1)
       (Let (parent let (BorrowedMut Int ph)) (BorrowMut 1)
           (Let (called const Int)
                (Scope () ,(sink-call 'parent 'scope-ph))
             (Let (again let (BorrowedMut Int ph)) (BorrowMut 1)
               0)))))
  (define-values (_ir _filled typed) (type-core core '((1 Int))))
  (check-true (diagnostic? typed))
  (check-equal? (diagnostic-id typed) "E-BOR-003"))

(test-case "一時の Reborrow を包んで渡すと呼出し後に親経由で書ける"
  (define core
    `(Scope (1)
       (Let (parent let (BorrowedMut Int ph)) (BorrowMut 1)
           (Let (called const Int)
                (Scope ()
                  (Let (temporary let (Borrowed Int ph)) (Reborrow parent)
                    ,(sink-shared-call 'temporary 'scope-ph)))
             (Assign parent 7)))))
  (define-values (_ir _filled typed) (type-core core '((1 Int))))
  (check-true (region-typed? typed) (format "region typing: ~s" typed)))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../erase.rkt"
         "../span-core.rkt"
         "../typing.rkt"
         "../region.rkt")

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 200])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (span-node head start end . fields)
  `(,head (#:span src ,start ,end) ,@fields))

(define (contains-subterm? term wanted)
  (or (equal? term wanted)
      (and (list? term) (ormap (lambda (child) (contains-subterm? child wanted)) term))))

(define (proj-borrow-label term)
  (match (peel-node term)
    [`(ProjBorrowAt ,_ ,_ ,label) label]
    [(? pair?) (or (proj-borrow-label (car term))
                   (proj-borrow-label (cdr term)))]
    [_ #f]))

(define region-app-callables
  '((readb (ForallRegion (a)
            (NFn ((Borrowed Int (RParam a))) Int () () () User)))))

(define region-app-function
  '(RegionLam (a) (Lam User readb (p) (Read p))))

(test-case "空の region 文脈では owner の無い借用として拒否される"
  (define core '(Scope () (Borrow 1)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal? (diagnostic-id
                 (core-type-of/diagnostic
                  annotated '((1 Res)) '() '()
                  (region-ctx ir '() (hash) (hash))))
                "E-BOR-006"))

(test-case "region 文脈の下で借用を通した射影が受理される"
  (define res-record '(Record ((n Int imm))))
  (define core
    `(Scope ()
       (Let (x let (Owned ,res-record)) (Rec ((n imm 1)))
         (Read (ProjBorrow (Borrow x) n)))))
  (define typed (core-type-of/regions core '() '()))
  (check-true (region-typed? typed))
  (check-equal? (region-typed-type typed) 'Int))

(test-case "借用を含む Core と型だけを判定する"
  (check-true (borrow-bearing-core? '(Borrow x)))
  (check-true (borrow-bearing-core? '(Let (b let (Borrowed Int 0)) 1 2)))
  (check-false (borrow-bearing-core? '(Scope () (Let (x let Int) 1 (Apply f x)))))
  (check-false (borrow-bearing-core? '(FromRawPtr p 0)))
  (check-false (borrow-bearing-core? '(RegionLam (r) (Lam User f () unit))))
  (check-true (borrow-bearing-core? '(BorrowAt 0 (Own x ()) x)))
  (check-true (borrow-bearing-core? '(ReborrowAt 0 x)))
  (check-true (borrow-bearing-core? '(ProjBorrowAt 0 x n)))
  (check-true (borrow-bearing-core? '(Read x)))
  (check-true (borrow-bearing-core? '(Assign x 1))))

(test-case "region 注釈が元の節点 span を保つ"
  (define core
    (span-node 'Scope 0 40 '()
      (span-node 'Let 1 39 '(x let Int)
        '(#:lit 1 (#:span src 8 9))
        (span-node 'ProjBorrow 10 30
          (span-node 'Borrow 16 22 '(#:var x (#:span src 20 21))) 'n))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal? (erase-core annotated)
                (annotate-regions (erase-core core) ir))
  (check-true
   (match annotated
     [`(Scope (#:span src 0 40) ()
         (Let (#:span src 1 39) (x let Int) (#:lit 1 (#:span src 8 9))
           (ProjBorrowAt (#:span src 10 30) ,_
             (BorrowAt (#:span src 16 22) ,_ ,_ (#:var x (#:span src 20 21)))
             n))) #t]
     [_ #f])))

(test-case "span 付き射影 label を保ったまま region 型付けする"
  (define label '(#:lbl n (#:span src 25 26)))
  (define core
    (span-node 'Scope 0 40 '()
      (span-node 'Let 1 39 '(x let (Owned (Record ((n Int imm)))))
        '(Rec ((n imm 7)))
        (span-node 'Read 9 31
          (span-node 'ProjBorrow 10 30
            (span-node 'Borrow 16 22 '(#:var x (#:span src 20 21)))
            label)))))
  (define typed (core-type-of/regions core '() '()))
  (check-true (region-typed? typed) (format "region 型付け: ~s" typed))
  (check-equal? (region-typed-type typed) 'Int)
  (check-equal? (proj-borrow-label (annotate-regions core (build-region-ir core)))
                label))

(test-case "region helper は失敗した Core 節点の span を返す"
  (define core
    (span-node 'Scope 0 50 '()
      (span-node 'Let 1 49 '(x let (Owned Int))
        '(#:lit 7 (#:span src 8 9))
        (span-node 'Let 12 45
          '(b let (Borrowed Int (RParam %omitted)))
          (span-node 'Borrow 20 28 '(#:var x (#:span src 25 26)))
          (span-node 'Move 31 38 '(#:var x (#:span src 34 35)))))))
  (define result (core-type-of/regions core '() '()))
  (check-true (diagnostic? result))
  (check-equal? (diagnostic-id result) "E-BOR-008")
  (check-equal? (diagnostic-primary-span result) '(#:span src 31 38)))

(test-case "region 実行 Core の trace は config 検査を通る"
  (define core
    '(Scope ()
       (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 7)))
         (Read (ProjBorrow (Borrow x) n)))))
  (define typed (core-type-of/regions core '() '()))
  (check-true (region-typed? typed))
  (check-equal? (region-typed-type typed) 'Int)
  (define configs (trace-g2 (inject-g2m (region-execution-core typed))))
  (check-true (redex-match? G2m v (match (last configs)
                                  [`(cfg ,value ,_ ...) value])))
  (for ([cfg (in-list configs)] [index (in-naturals)])
    (define row (runtime-row cfg '() 'Int))
    (check-not-false row (format "config ~a の runtime-row" index))
    (check-true (config-ok? cfg '() 'Int row)
                (format "config ~a の config-ok?" index))))

(test-case "record の省略寿命を残した実行 Core は config 検査を通る"
  (define core
    '(Scope ()
       (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 7)))
         (Let (r let
                 (Record ((b (Borrowed Int (RParam %omitted)) imm))))
              (Rec ((b imm (ProjBorrow (Borrow x) n))))
           (Read (Proj r b))))))
  (define typed (core-type-of/regions core '() '()))
  (check-true (region-typed? typed))
  (check-equal? (region-typed-type typed) 'Int)
  (define executable (region-execution-core typed))
  (check-true (contains-subterm? executable '(RParam %omitted)))
  (define configs (trace-g2 (inject-g2m executable)))
  (for ([cfg (in-list configs)] [index (in-naturals)])
    (define row (runtime-row cfg '() 'Int))
    (check-not-false row (format "config ~a の runtime-row" index))
    (check-true (config-ok? cfg '() 'Int row)
                (format "config ~a の config-ok?" index))))

(test-case "同じ IR で埋めた RegionApp の trace は全構成で検査を通る"
  (define source
    `(Scope ()
       (Let (x let (Owned Int)) 7
         (Let (b let (Borrowed Int ph)) (Scope () (Borrow x))
           (Apply (RegionApp ,region-app-function (ph)) b)))))
  (define ir (build-region-ir source))
  (define filled (fill-region-placeholders source ir))
  (define typed (core-type-of/regions filled '() region-app-callables #:ir ir))
  (check-true (region-typed? typed) (format "shared IR typing: ~s" typed))
  (check-equal? (region-typed-type typed) 'Int)
  (define unshared (core-type-of/regions filled '() region-app-callables))
  (check-true (diagnostic? unshared)
              (format "別の IR を再構築した結果: ~s" unshared))
  (check-equal? (diagnostic-id unshared) "E-TYP-023")
  (define configs (trace-g2 (inject-g2m (region-execution-core typed))))
  (for ([cfg (in-list configs)] [index (in-naturals)])
    (define row (runtime-row cfg region-app-callables 'Int))
    (check-not-false row (format "config ~a の runtime-row" index))
    (check-true (config-ok? cfg region-app-callables 'Int row)
                (format "config ~a の config-ok?" index))))

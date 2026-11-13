#lang racket

(require rackunit
         racket/list
         racket/match
         racket/set
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../region-param.rkt"
         "../typing.rkt")

(define temporary-callables
  '((sink (ForallRegion (a)
           (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))
    (shared-sink (ForallRegion (a)
                   (NFn ((Borrowed Int (RParam a))) Int () () () User)))
    (sink2 (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a))
                  (BorrowedMut Int (RParam a))) Int () () () User)))
    (return-second
     (ForallRegion (a b)
       (NFn ((BorrowedMut Int (RParam a))
             (BorrowedMut Int (RParam b)))
            (Borrowed Int (RParam b)) () () () User)))
    (return-one
     (ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)))
            (Borrowed Int (RParam a)) () () () User)))
    (inner-first-sink
     (ForallRegion (a)
       (NFn (Int (BorrowedMut Int (RParam a))) Int () () () User)))
    (payload-sink
     (ForallRegion (a)
       (NFn ((BorrowedMut (Borrowed Int (RParam a)) (RParam a)))
            Int () () () User)))
    (outer-generic
     (ForallRegion (r)
       (NFn ((BorrowedMut Int (RParam r))) Int () () () User)))
    (shared-generic
     (ForallRegion (r)
       (NFn ((Borrowed Int (RParam r))) Int () () () User)))
    (outer-sink (ForallRegion (a)
                 (NFn ((BorrowedMut Int (RParam a)) Int) Int () () () User)))))

(define (sink-call argument [region 'owner-ph])
  `(Apply (RegionApp (RegionLam (a) (Lam User sink (p) 0)) (,region))
          ,argument))

(define (shared-sink-call argument [region 'owner-ph])
  `(Apply (RegionApp (RegionLam (a) (Lam User shared-sink (p) 0)) (,region))
          ,argument))

(define (type-core core [places '()] [callables temporary-callables]
                   [owner-points (hash 'owner-ph '(0))]
                   [environment '()])
  (define ir (build-region-ir core))
  (define (contains-marker? term marker)
    (or (eq? term marker)
        (and (pair? term)
             (or (contains-marker? (car term) marker)
                 (contains-marker? (cdr term) marker)))))
  (define owner-rhos
    (for/hash ([(marker point) (in-hash owner-points)]
               #:when (contains-marker? (list core places) marker))
      (values marker
              (region->rho ir (owner-let-body-region ir point)))))
  (define scope-rho (region->rho ir (region-at ir '())))
  (define (fill-markers term)
    (let replace ([term term])
      (cond
        [(hash-ref owner-rhos term #f) => values]
        [(eq? term 'scope-ph) scope-rho]
        [(pair? term) (cons (replace (car term)) (replace (cdr term)))]
        [else term])))
  (define filled (fill-markers (fill-region-placeholders core ir)))
  (define filled-places (fill-markers places))
  (values ir filled
          (core-type-of/regions filled filled-places callables environment
                                #:ir ir)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 300])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (check-runtime typed ir callables expected label)
  (check-true (region-typed? typed) (format "~a: 型検査 ~s" label typed))
  (when (region-typed? typed)
    (define execution-core (region-execution-core typed))
    (define start (inject-g2m execution-core))
    (define configs (trace-g2 start))
    (define rows
      (for/list ([config (in-list configs)] [index (in-naturals)])
        (with-handlers
            ([exn:fail?
              (lambda (exception)
                (error 'check-runtime "~a: runtime-row config ~a: ~a"
                       label index (exn-message exception)))])
          (runtime-row config callables expected #:region-ir ir))))
    (define first-live
      (for/first ([row (in-list rows)] [index (in-naturals)] #:when row)
        index))
    (check-not-false
     first-live
     (format "~a: runtime-row がある; rows ~s; start ~s; end ~s"
             label rows (first configs) (last configs)))
    (for ([config (in-list (if first-live (drop configs first-live) '()))]
          [row (in-list (if first-live (drop rows first-live) '()))]
          [index (in-naturals (or first-live 0))])
      (check-not-false row (format "~a config ~a: runtime-row" label index))
      (check-true (config-ok? config callables expected row #:region-ir ir)
                  (format "~a config ~a: config-ok?" label index)))
    (define oracle-result
      (check-borrow-execution start (region-typed-sidecar typed)
                              ir 300 (make-bcounters)))
    (check-equal? oracle-result 'ok
                  (format "~a: borrow oracle ~s; static ~s; requests ~s; sigma ~s"
                          label oracle-result
                          (static-borrow-set (region-typed-sidecar typed) ir)
                          (borrow-sidecar-requests
                           (region-typed-sidecar typed))
                          (borrow-sidecar-sigma
                           (region-typed-sidecar typed))))))

(define (core-point core predicate)
  (let walk ([node (erase-core core)] [point '()])
    (if (predicate node)
        point
        (for/or ([child (in-list (core-children node))]
                 [index (in-naturals)])
          (walk child (append point (list index)))))))

(define (alpha-region typed point)
  (define alpha (hash-ref (region-typed-table typed) point))
  (hash-ref (region-typed-σ typed) (lifetime-var-index alpha)))

(define (diagnostic-code core [places '()] [callables temporary-callables]
                        [owner-points (hash 'owner-ph '(0))])
  (define-values (ir _filled typed)
    (type-core core places callables owner-points))
  (if (diagnostic? typed) (diagnostic-id typed) typed))

(test-case "一時借用_ApplyのReborrow直後に親へAssign"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (parent let (BorrowedMut Int owner-ph)) (BorrowMut owner)
           (Let (called const Int)
             ,(shared-sink-call '(Reborrow parent) 'scope-ph)
             (Assign parent 7))))))
  (define-values (ir _filled typed) (type-core core))
  (check-runtime typed ir temporary-callables 'Unit "Apply/Reborrow"))

(test-case "一時借用_Read(Reborrow)直後に親へAssign"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (parent let (BorrowedMut Int owner-ph)) (BorrowMut owner)
           (Let (read-result const Int) (Read (Reborrow parent))
             (Assign parent 7))))))
  (define-values (ir _filled typed) (type-core core))
  (check-runtime typed ir temporary-callables 'Unit "Read/Reborrow"))

(test-case "名前付き借用_計算式の親式のBorrowMutはlexicalに残る"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (parent let (BorrowedMut Int owner-ph)) (BorrowMut owner)
           (Let (read-result const Int)
             (Read (Reborrow (Let (observed const Int) 0 parent)))
             (Move owner))))))
  (check-equal? (diagnostic-code core) "E-BOR-008"))

(test-case "一時借用_計算式の親をReborrowしたReadの後で親の源へ書込み"
  (define signature
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))) Unit () (Mutation) () User)))
  (define callables (cons (list 'computed-read-write signature)
                          temporary-callables))
  (define core
    '(RegionLam (a)
       (Lam User computed-read-write (p)
         (Let (read-result const Int)
           (Read (Reborrow (Let (seen const Int) 0 p)))
           (Assign p 7)))))
  (define-values (ir _filled typed) (type-core core '() callables))
  (check-true (region-typed? typed)
              (format "computed Reborrow Read then parent write: ~s" typed))
  (when (region-typed? typed)
    (define borrow-point
      (core-point core
                  (lambda (node)
                    (match node [`(Reborrow ,_) #t] [_ #f]))))
    (define consumer-point (temporary-consumer-point ir borrow-point))
    (define read-point
      (core-point core
                  (lambda (node)
                    (match node [`(Read ,_) #t] [_ #f]))))
    (check-true
     (lifetime-var? (hash-ref (region-typed-table typed) borrow-point)))
    (check-equal? consumer-point read-point)
    (check-not-false (region-at/temporary ir consumer-point))))

(test-case "一時借用_計算式の親のReborrowでReadの結果にβを残す"
  (define core
    '(RegionLam (a b)
       (Lam User nested-reader (parent)
         (Read
          (Reborrow
           (Let (alias let
                      (BorrowedMut (Borrowed Int (RParam b)) (RParam a)))
                parent
             alias))))))
  (define callables
    '((nested-reader
       (ForallRegion (a b)
         (NFn ((BorrowedMut (Borrowed Int (RParam b)) (RParam a)))
              (Borrowed Int (RParam b)) () () () User)))))
  (define-values (ir _filled typed)
    (type-core core '() callables))
  (check-true (region-typed? typed)
              (format "computed nested Borrowed Read: ~s" typed))
  (when (region-typed? typed)
    (define borrow-point
      (core-point core
                  (lambda (node)
                    (match node [`(Reborrow ,_) #t] [_ #f]))))
    (check-true (hash-has-key? (region-typed-table typed) borrow-point)
                "Reborrow の寿命が型付け結果に記録される")
    (match (region-typed-type typed)
      [`(ForallRegion (,a ,b)
          (NFn ((BorrowedMut (Borrowed Int (RParam ,payload-rp))
                              (RParam ,owner-rp)))
               (Borrowed Int (RParam ,result-rp)) ,_ ,_ ,_ User))
       (check-equal? payload-rp b)
       (check-equal? owner-rp a)
       (check-equal? result-rp b)]
      [type (check-true #f (format "computed nested Borrowed Read type: ~s"
                                   type))]))
  ;; Runtime 側でも Read/Reborrow の一時 region は α だけに使い、
  ;; pointee の共有借用 β は結果と trace に残す。
  (define source
    '(Scope (0)
       (Read
        (Reborrow
         (Let (parent let (BorrowedMut (Borrowed Int 0) 0))
              (BorrowMut 1)
           parent)))))
  (define runtime-ir (build-region-ir source))
  (define runtime-borrow-point
    (core-point source
                (lambda (node) (match node [`(Reborrow ,_) #t] [_ #f]))))
  (define consumer-point
    (temporary-consumer-point runtime-ir runtime-borrow-point))
  (define beta (region->rho runtime-ir (region-owning runtime-ir 0)))
  (define alpha
    (region->rho runtime-ir (region-at/temporary runtime-ir consumer-point)))
  (define start
    `(cfg (Read
           (ReborrowAt ,alpha
             (Let (parent let (BorrowedMut (Borrowed Int ,beta) ,beta))
                  (BorrowMutRef 1 () ,beta)
               parent)))
          ((0 7 (declared Int))
           (1 (BorrowRef 0 () ,beta)
              (declared (Borrowed Int ,beta))))
          ((0 Available) (1 Available)) () ()))
  (define configs (trace-g2 start))
  (define rows
    (for/list ([config (in-list configs)])
      (runtime-row config '() `(Borrowed Int ,beta) #:region-ir runtime-ir)))
  (check-not-false (first rows) (format "runtime-row rows: ~s" rows))
  (for ([config (in-list configs)] [row (in-list rows)] [index (in-naturals)])
    (check-not-false row (format "config ~a runtime-row" index))
    (when row
      (check-true (config-ok? config '() `(Borrowed Int ,beta) row
                              #:region-ir runtime-ir)
                  (format "config ~a config-ok?" index))))
  (check-false (member alpha (flatten rows)) "α が runtime-row に漏れない")
  (match (last configs)
    [`(cfg ,core ,_heap ,_states ,_tokens ,_trace)
     (check-equal? core `(BorrowRef 0 () ,beta))]
    [config (check-true #f (format "terminal config: ~s" config))]))

(test-case "一時借用_計算式の親を読むReborrow pointへ以前のReturn escapeを記録しない"
  (define callables
    `((earlier-return (NFn () Int () ((Return prior-boundary Int)) () User))
      (escape-before-read
       (ForallRegion (a)
         (NFn ((BorrowedMut Int (RParam a))) Int ()
              ((Return prior-boundary Int)) () User)))))
  (define core
    '(RegionLam (a)
       (Lam User escape-before-read (parent)
         (Let (earlier-return const
                              (NFn () Int ()
                                   ((Return prior-boundary Int)) () User))
              (Lam User earlier-return ()
                (Perform (Return prior-boundary Int) 0))
           (Let (prior const Int) (Apply earlier-return)
             (Read
              (Reborrow
               (Let (seen const Int) 0 parent))))))))
  (define results (make-hash))
  (define-values (_ir _filled typed)
    (parameterize
        ([current-typing-normal-result-probe
          (lambda (point result) (hash-set! results point result))])
      (type-core core '() callables)))
  (check-true (region-typed? typed) (format "escape/read typing: ~s" typed))
  (when (region-typed? typed)
    (define earlier-apply-point
      (core-point core
                  (lambda (node) (equal? node '(Apply earlier-return)))))
    (define reborrow-point
      (core-point core
                  (lambda (node)
                    (match node [`(Reborrow ,_) #t] [_ #f]))))
    (check-not-false (pair? (fourth (hash-ref results earlier-apply-point)))
                     "先行する latent Return は Apply point に記録される")
    (check-equal? (fourth (hash-ref results reborrow-point)) '()
                  "Reborrow point の escape 欄は局所分だけである")))

(test-case "一時借用_計算式の親は一度だけ型付けする"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (parent let (BorrowedMut Int owner-ph)) (BorrowMut owner)
           (Let (scratch let (Owned Int)) 2
             (Let (read-result const Int)
               (Read
                (Reborrow
                 (Let (dropped const Unit) (Drop (Move scratch)) parent)))
               (Assign parent 7)))))))
  (define-values (ir _filled typed)
    (type-core core))
  (check-runtime typed ir temporary-callables 'Unit
                 "single synthesis of computed Reborrow parent"))

(test-case "一時借用_計算式の親がBorrowedMutでない"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Read
          (Reborrow
           (Let (parent let (Borrowed Int owner-ph))
                (Borrow owner)
             parent))))))
  (check-equal? (diagnostic-code core) "E-BOR-009"))

(test-case "一時借用_Applyの実引数に計算式の親のReborrow"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (parent let (BorrowedMut Int owner-ph)) (BorrowMut owner)
           (Let (called const Int)
             ,(shared-sink-call
               '(Reborrow
                 (Let (observed const Int) (Read parent) parent))
               'scope-ph)
             (Assign parent 7))))))
  (define-values (ir _filled typed) (type-core core))
  (check-runtime typed ir temporary-callables 'Unit
                 "Apply computed Reborrow parent"))

(test-case "一時借用_Read(BorrowとBorrowMut)直後にMove"
  (for ([borrow (in-list (list '(Borrow 1) '(BorrowMut 1)))])
    (define operation
      (match borrow
        [(list 'Borrow _) `(Borrow owner)]
        [(list 'BorrowMut _) `(BorrowMut owner)]))
    (define core
      `(Scope ()
         (Let (owner let (Owned Int)) 1
           (Let (read-result const Int) (Read ,operation)
             (Move owner)))))
    (define-values (ir _filled typed) (type-core core))
    (check-runtime typed ir temporary-callables '(Owned Int)
                   (format "Read ~s" borrow))))

(test-case "一時借用_Assign(BorrowMut)直後にMove"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (assigned const Unit) (Assign (BorrowMut owner) 7)
           (Move owner)))))
  (define-values (ir _filled typed) (type-core core))
  (check-runtime typed ir temporary-callables '(Owned Int) "Assign/BorrowMut"))

(test-case "一時借用_後の子Scope内ownerを借りても短縮できる"
  (define callables
    (append '((inner-sink
               (ForallRegion (a)
                 (NFn ((BorrowedMut Int (RParam a))) Int () () () User))))
            temporary-callables))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Apply
          (RegionApp
           (RegionLam (a) (Lam User outer-sink (first second) 0))
           (owner-ph))
          (BorrowMut owner)
          (Scope ()
            (Let (inner-owner let (Owned Int)) 2
              (Apply
               (RegionApp
                (RegionLam (a) (Lam User inner-sink (p) 0))
                (inner-ph))
               (BorrowMut inner-owner))))))))
  (define-values (ir _filled typed)
    (type-core core '() callables
               (hash 'owner-ph '(0) 'inner-ph '(0 1 2 0))))
  (check-true (region-typed? typed) (format "nested Scope owner: ~s" typed))
  (when (region-typed? typed)
    (define borrow-point
      (core-point core
                  (lambda (node)
                    (equal? node '(BorrowMut inner-owner)))))
    (define consumer-point (temporary-consumer-point ir borrow-point))
    (define temporary-region (region-at/temporary ir consumer-point))
    (define owner-region (owner-let-body-region ir '(0 1 2 0)))
    (check-equal? (alpha-region typed borrow-point) temporary-region)
    (check-true (region-outlives? ir owner-region temporary-region))
    (check-runtime typed ir callables 'Int "nested Scope owner")))

(test-case "一時借用_後の子Apply内側先は受理"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Apply
          (RegionApp
           (RegionLam (a) (Lam User inner-first-sink (first second) 0))
           (owner-ph))
          (Apply
           (RegionApp
            (RegionLam (a) (Lam User sink (p) 0))
            (owner-ph))
           (BorrowMut owner))
          (BorrowMut owner)))))
  (define-values (ir _filled typed)
    (type-core core '() temporary-callables))
  (check-runtime typed ir temporary-callables 'Int "nested Apply, inner first"))

(test-case "一時借用_後の子Apply内側後は E-BOR-003"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Apply
          (RegionApp
           (RegionLam (a) (Lam User outer-sink (first second) 0))
           (owner-ph))
          (BorrowMut owner)
          (Apply
           (RegionApp
            (RegionLam (a) (Lam User sink (p) 0))
            (owner-ph))
           (BorrowMut owner))))))
  (define pairs '())
  (define-values (ir _filled typed)
    (parameterize
        ([current-borrow-conflict-probe
          (lambda (left right)
            (set! pairs (cons (list left right) pairs))
            (void))])
      (type-core core)))
  (check-not-false (pair? pairs) "静的 checker が重複要求を検出する")
  (when (pair? pairs)
    (define first-request (first (first pairs)))
    (define second-request (second (first pairs)))
    (check-not-equal? (borrow-request-point first-request)
                      (borrow-request-point second-request))
    (check-true
     (regions-overlap? ir
                       (borrow-request-rho-borrow first-request)
                       (borrow-request-rho-borrow second-request))))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed)) "E-BOR-003"))

(test-case "一時借用_同じApplyの二つのMut loanは重なる"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Apply
          (RegionApp
           (RegionLam (a) (Lam User sink2 (left right) 0))
           (owner-ph))
          (BorrowMut owner)
          (BorrowMut owner)))))
  (define pairs '())
  (define-values (ir _filled typed)
    (parameterize
        ([current-borrow-conflict-probe
          (lambda (left right) (set! pairs (cons (list left right) pairs)))])
      (type-core core)))
  (check-not-false (pair? pairs) "静的 checker が重複要求を検出する")
  (when (pair? pairs)
    (define first-request (first (first pairs)))
    (define second-request (second (first pairs)))
    (check-not-equal? (borrow-request-point first-request)
                      (borrow-request-point second-request))
    (check-equal? (borrow-request-rho-borrow first-request)
                  (borrow-request-rho-borrow second-request)))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed)) "E-BOR-003"))

(test-case "一時借用_同じApplyのlocal引数だけを短縮する"
  (define callables temporary-callables)
  (define core
    `(Scope ()
       (Let (left-owner let (Owned Int)) 1
         (Let (right-owner let (Owned Int)) 2
           (Let (result let (Borrowed Int right-ph))
             (Apply
              (RegionApp
               (RegionLam (a b)
                 (Lam User return-second (left right) (Reborrow right)))
               (left-ph right-ph))
              (BorrowMut left-owner)
              (BorrowMut right-owner))
             (Let (_ const Unit) (Assign (BorrowMut left-owner) 3)
               (Let (_ const Int) (Read result)
                 0)))))))
  (define-values (ir _filled typed)
    (type-core core '() callables
               (hash 'left-ph '(0) 'right-ph '(0 1))))
  (check-true (region-typed? typed) (format "mixed local/result: ~s" typed))
  (when (region-typed? typed)
    (define left-point
      (core-point core (lambda (node) (equal? node '(BorrowMut left-owner)))))
    (define right-point
      (core-point core (lambda (node) (equal? node '(BorrowMut right-owner)))))
    (check-equal?
     (alpha-region typed left-point)
     (region-at/temporary
      ir (temporary-consumer-point ir left-point)))
    (check-equal? (alpha-region typed right-point)
                  (region-at ir right-point))
    (check-runtime typed ir callables 'Int "mixed local/result")))

(test-case "一時借用_result引数のlexical loanは後続Mut借用とE-BOR-003"
  (define callables temporary-callables)
  (define core
    `(Scope ()
       (Let (left-owner let (Owned Int)) 1
         (Let (right-owner let (Owned Int)) 2
           (Let (result let (Borrowed Int right-ph))
             (Apply
              (RegionApp
               (RegionLam (a b)
                 (Lam User return-second (left right) (Reborrow right)))
               (left-ph right-ph))
              (BorrowMut left-owner)
              (BorrowMut right-owner))
             (Assign (BorrowMut right-owner) 3))))))
  (check-equal? (diagnostic-code core '() callables
                                (hash 'left-ph '(0) 'right-ph '(0 1)))
                "E-BOR-003"))

(test-case "一時借用_結果へ流れる直接borrowはlexical extentを保つ"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (result let (Borrowed Int owner-ph))
           (Apply
            (RegionApp
             (RegionLam (a)
               (Lam User return-one (p) (Reborrow p)))
             (owner-ph))
            (BorrowMut owner))
           (Let (_ const Int) (Read result) 0)))))
  (define-values (ir _filled typed) (type-core core '()
                                                temporary-callables))
  (check-true (region-typed? typed) (format "result-flow: ~s" typed))
  (when (region-typed? typed)
    (define point
      (core-point core (lambda (node) (equal? node '(BorrowMut owner)))))
    (check-equal? (alpha-region typed point) (region-at ir point))
    (check-runtime typed ir temporary-callables 'Int "result-flow")))

(test-case "一時借用_summary の無い callee は署名 fallback で借用引数を呼出しで終える"
  (define signature
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Apply (RegionApp f (owner-ph)) (BorrowMut owner)))))
  (define-values (ir _filled typed)
    (type-core core '() `((f ,signature))
               (hash 'owner-ph '(0))
               `((f ,signature))))
  (check-true (region-typed? typed) (format "signature fallback: ~s" typed))
  (when (region-typed? typed)
    (define point
      (core-point core (lambda (node) (equal? node '(BorrowMut owner)))))
    (check-equal? (alpha-region typed point) (region-at ir point))))

(test-case "一時借用_summary の無い callee が返す借用は owner access と衝突する"
  (define signature
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () () () User)))
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (result let (BorrowedMut Int owner-ph))
              (Apply (RegionApp f (owner-ph)) (BorrowMut owner))
           (Let (written const Unit) (Assign (BorrowMut owner) 2)
             (Read (Reborrow result)))))))
  (define-values (_ir _filled typed)
    (type-core core '() `((f ,signature))
               (hash 'owner-ph '(0))
               `((f ,signature))))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed))
                "E-BOR-003"))

(test-case "一時借用_summary の無い callee の Yield payload は fail-closed"
  (define signature
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))) Int ()
            ((Yield (Borrowed Int (RParam a)))) () User)))
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Apply (RegionApp f (owner-ph)) (BorrowMut owner)))))
  (define-values (_ir _filled typed)
    (type-core core '() `((f ,signature))
               (hash 'owner-ph '(0))
               `((f ,signature))))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed))
                "E-BOR-020"))

(test-case "一時借用_summary の無い callee の Return payload は fail-closed"
  (define signature
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))) Int ()
            ((Return boundary (Borrowed Int (RParam a)))) () User)))
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Apply (RegionApp f (owner-ph)) (BorrowMut owner)))))
  (define-values (_ir _filled typed)
    (type-core core '() `((f ,signature))
               (hash 'owner-ph '(0))
               `((f ,signature))))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed))
                "E-BOR-020"))

(test-case "一時借用_ReadのBorrowed payload寿命βを保つ"
  (define core
    '(RegionLam (a b)
       (Lam User nested-reader (parent)
         (Read (Reborrow parent)))))
  (define callables
    '((nested-reader
       (ForallRegion (a b)
         (NFn ((BorrowedMut (Borrowed Int (RParam b)) (RParam a)))
              (Borrowed Int (RParam b)) () () () User)))))
  (define-values (ir _filled typed)
    (type-core core '() callables))
  (check-true (region-typed? typed) (format "nested Borrowed Read: ~s" typed))
  (when (region-typed? typed)
    (define point
      (core-point core (lambda (node) (equal? node '(Reborrow parent)))))
    (check-not-false (temporary-consumer-point ir point))
    (check-equal? (alpha-region typed point)
                  (region-at/temporary
                   ir (temporary-consumer-point ir point)))
    (match (region-typed-type typed)
      [`(ForallRegion (,a ,b)
          (NFn ((BorrowedMut (Borrowed Int (RParam ,payload-rp))
                              (RParam ,owner-rp)))
               (Borrowed Int (RParam ,result-rp)) ,_ ,_ ,_ User))
       (check-equal? payload-rp b)
       (check-equal? owner-rp a)
       (check-equal? result-rp b)]
      [type (check-true #f (format "nested Borrowed Read の型: ~s" type))])))

(test-case "一時借用_ReadのReborrow結果はpayloadのβを保つruntime-row"
  (define source '(Scope (0) (Read (Reborrow parent))))
  (define ir (build-region-ir source))
  (define beta (region->rho ir (region-owning ir 0)))
  (define alpha
    (region->rho ir (region-at/temporary ir '(0))))
  (define start
    `(cfg (Read (ReborrowAt ,alpha (BorrowMutRef 1 () ,beta)))
          ((0 7 (declared Int))
           (1 (BorrowRef 0 () ,beta) (declared (Borrowed Int ,beta))))
          ((0 Available) (1 Available)) () ()))
  (define expected `(Borrowed Int ,beta))
  (define configs (trace-g2 start))
  (define row (runtime-row start '() expected #:region-ir ir))
  (check-not-false row
                   (format "runtime-row failure config=~s" start))
  (for ([config (in-list configs)] [index (in-naturals)])
    (check-true (config-ok? config '() expected row #:region-ir ir)
                (format "config ~a: ~s" index config))
    (check-equal? (runtime-row config '() expected #:region-ir ir) row))
  (match (last configs)
    [`(cfg ,core ,_heap ,_states ,_tokens ,_trace)
     (check-equal? core `(BorrowRef 0 () ,beta))]
    [config (check-true #f (format "terminal config: ~s" config))]))

(test-case "一時借用_RegionAppのRParam置換後もlocal Reborrowは短縮"
  (define core
    '(RegionLam (r)
       (Lam User outer-generic (parent)
         (Apply
          (RegionApp
           (RegionLam (s) (Lam User shared-generic (child) 0))
           ((RParam r)))
          (Reborrow parent)))))
  (define-values (ir _filled typed)
    (type-core core '() temporary-callables))
  (check-true (region-typed? typed) (format "RegionApp RParam: ~s" typed))
  (when (region-typed? typed)
    (define point
      (core-point core (lambda (node) (equal? node '(Reborrow parent)))))
    (check-equal? (alpha-region typed point)
                  (region-at/temporary ir
                                       (temporary-consumer-point ir point)))))

(test-case "一時借用_BorrowedMut実引数のadoptionはpayload寿命を保つ"
  (define core
    '(Apply
      (RegionApp
       (RegionLam (r)
         (Lam User outer-payload-generic ()
           (Scope (1)
             (Apply
              (RegionApp
               (RegionLam (a) (Lam User payload-sink (p) 0))
               ((RParam r)))
              (BorrowMut 1)))))
       (scope-ph))))
  (define places '((1 (Borrowed Int scope-ph))))
  (define callables
    '((outer-payload-generic
       (ForallRegion (r) (NFn () Int () () () User)))
      (payload-sink
       (ForallRegion (a)
         (NFn ((BorrowedMut (Borrowed Int (RParam a)) (RParam a)))
              Int () () () User)))))
  (define-values (ir _filled typed) (type-core core places callables))
  (check-true (region-typed? typed) (format "BorrowedMut adoption: ~s" typed))
  (when (region-typed? typed)
    (define point
      (core-point core (lambda (node) (equal? node '(BorrowMut 1)))))
    (check-equal?
     (alpha-region typed point)
     (region-at/temporary ir (temporary-consumer-point ir point)))
    (define root-rho (region->rho ir (region-at ir '())))
    (define start
      (match (inject-g2m (region-execution-core typed))
        [`(cfg ,machine-core ,_heap ,_states ,tokens ,events)
         `(cfg ,machine-core
               ((0 7 (declared Int))
                (1 (BorrowRef 0 () ,root-rho)
                   (declared (Borrowed Int ,root-rho))))
               ((0 Available) (1 Available)) ,tokens ,events)]))
    (define configs (trace-g2 start))
    (define rows
      (for/list ([config (in-list configs)])
        (runtime-row config callables 'Int #:region-ir ir)))
    (define first-live
      (for/first ([row (in-list rows)] [index (in-naturals)] #:when row)
        index))
    (check-not-false first-live
                     (format "BorrowedMut adoption runtime-row: rows=~s"
                             rows))
    (for ([config (in-list (if first-live (drop configs first-live) '()))]
          [row (in-list (if first-live (drop rows first-live) '()))]
          [index (in-naturals (or first-live 0))])
      (check-not-false row (format "config ~a runtime-row" index))
      (check-true (config-ok? config callables 'Int row #:region-ir ir)
                  (format "config ~a config-ok?" index)))
    (check-equal? (check-borrow-execution
                   start (region-typed-sidecar typed) ir 300 (make-bcounters))
                  'ok)
    (define (contains-borrow-mut-ref? term)
      (or (match term [`(BorrowMutRef ,_ ,_ ,_) #t] [_ #f])
          (and (pair? term)
               (or (contains-borrow-mut-ref? (car term))
                   (contains-borrow-mut-ref? (cdr term))))))
    (match (last configs)
      [`(cfg ,core ,heap ,states ,_tokens ,_trace)
       (define available-values
         (for/list ([entry (in-list heap)]
                    #:when (equal? (second (assoc (first entry) states))
                                   'Available))
           (second entry)))
       (check-false (contains-borrow-mut-ref? (list core available-values))
                    "Apply 完了後に BorrowMutRef が残らない")]
      [config (check-true #f (format "終端構成: ~s" config))])))

(test-case "一時借用_incomplete summary のApplyはlexical loanを保つ"
  (define callables
    '((incomplete-reader
       (ForallRegion (a)
         (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))))
  (define (run core)
    (define reader-failed? #f)
    (define-values (ir _filled typed)
      (parameterize
          ([current-leaf-exit-capability-reader
            (lambda (_Λ _expression)
              (set! reader-failed? #t)
              (error 'forced-incomplete-summary "probe"))])
        (type-core core '() callables)))
    (check-true reader-failed? "summary の capability 記録を失敗させる")
    (values ir typed))
  (define call
    '(Apply
      (RegionApp
       (RegionLam (a)
         (Lam User incomplete-reader (p) (Read p)))
       (owner-ph))
      (BorrowMut owner)))
  (define accepted-core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (called const Int) ,call 0))))
  (define-values (ir accepted) (run accepted-core))
  (check-true (region-typed? accepted)
              (format "incomplete summary Apply: ~s" accepted))
  (when (region-typed? accepted)
    (define point
      (core-point accepted-core
                  (lambda (node) (equal? node '(BorrowMut owner)))))
    (check-equal? (alpha-region accepted point) (region-at ir point)))
  (define rejected-core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (called const Int) ,call (Move owner)))))
  (define-values (_rejected-ir rejected) (run rejected-core))
  (check-equal? (and (diagnostic? rejected) (diagnostic-id rejected))
                "E-BOR-008"))

(test-case "一時借用_Assignは生きた共有aliasとの衝突を保つ"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (alias let (Borrowed Int owner-ph)) (Borrow owner)
           (Assign (BorrowMut owner) 7)))))
  (define-values (_ir _filled typed) (type-core core))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed))
                "E-BOR-003"))

(test-case "一時借用_結果summaryを持つApply実引数は外側region差を迂回しない"
  (define core
    '(RegionLam (r)
       (Lam User outer-payload-generic ()
         (Scope (1)
           (Apply
            (RegionApp
             (RegionLam (a)
               (Lam User payload-return (p) (Read p)))
             ((RParam r)))
            (BorrowMut 1))))))
  (define renamed-r
    (call-with-region-params
     (lambda ()
       (match (alpha-rename-all-region-lams core)
         [`(RegionLam (,rp) ,_) rp]))))
  (define places `((1 (Borrowed Int (RParam ,renamed-r)))))
  (define callables
    '((outer-payload-generic
       (ForallRegion (r)
         (NFn () (Borrowed Int (RParam r)) () () () User)))
      (payload-return
       (ForallRegion (a)
         (NFn ((BorrowedMut (Borrowed Int (RParam a)) (RParam a)))
              (Borrowed Int (RParam a)) () () () User)))))
  (define-values (_ir _filled typed) (type-core core places callables))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed))
                "E-TYP-023"))

(define callable-temporary-read-write-signature
  '(ForallRegion (a)
     (NFn ((BorrowedMut Int (RParam a))) Unit () (Mutation) () User)))

(define callable-temporary-read-write-callables
  (cons (list 'callable-temporary-read-write
              callable-temporary-read-write-signature)
        temporary-callables))

(define (callable-temporary-read-write-core read-expression)
  `(Scope ()
     (Let (owner let (Owned Int)) 1
       (Let (called const Unit)
         (Apply
          (RegionApp
           (RegionLam (a)
             (Lam User callable-temporary-read-write (p)
               (Let (read-result const Int) ,read-expression
                 (Assign p 7))))
           (owner-ph))
         (BorrowMut owner))
         unit))))

(test-case "一時借用_callable本体の直接ReborrowのReadの後で仮引数へAssignしApply"
  (define core
    (callable-temporary-read-write-core '(Read (Reborrow p))))
  (define-values (ir _filled typed)
    (type-core core '() callable-temporary-read-write-callables))
  (check-runtime typed ir callable-temporary-read-write-callables 'Unit
                 "callable direct Reborrow Read then Assign"))

(test-case "一時借用_callable本体の計算式の親のReborrowのReadの後で仮引数へAssignしApply"
  (define core
    (callable-temporary-read-write-core
     '(Read (Reborrow (Let (seen const Int) 0 p)))))
  (define-values (ir _filled typed)
    (type-core core '() callable-temporary-read-write-callables))
  (check-runtime typed ir callable-temporary-read-write-callables 'Unit
                 "callable computed-parent Reborrow Read then Assign"))

(define reusable-temporary-read-write-signature
  '(ForallRegion (a)
     (NFn ((BorrowedMut Int (RParam a))) Unit () (Mutation) () User)))

(define (reusable-temporary-read-write-value name)
  `(RegionLam (a)
     (Lam User ,name (p)
       (Let (read-result const Int)
         (Read (Reborrow (Let (seen const Int) 0 p)))
         (Assign p 7)))))

(define (reusable-temporary-read-write-apply)
  '(Apply (RegionApp reusable (owner-ph)) (BorrowMut owner)))

(test-case "一時借用_Let束縛したcallableを後の位置でApply"
  (define callables
    (cons (list 'reusable-temporary-read-write
                reusable-temporary-read-write-signature)
          temporary-callables))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (reusable const ,reusable-temporary-read-write-signature)
           ,(reusable-temporary-read-write-value
             'reusable-temporary-read-write)
           ,(reusable-temporary-read-write-apply)))))
  (define-values (ir _filled typed)
    (type-core core '() callables))
  (check-runtime typed ir callables 'Unit "Let-bound callable Apply"))

(test-case "一時借用同じLet束縛callableを二度Apply"
  (define callables
    (cons (list 'reusable-temporary-read-write
                reusable-temporary-read-write-signature)
          temporary-callables))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (reusable const ,reusable-temporary-read-write-signature)
           ,(reusable-temporary-read-write-value
             'reusable-temporary-read-write)
           (Let (first-call const Unit)
             ,(reusable-temporary-read-write-apply)
             ,(reusable-temporary-read-write-apply))))))
  (define-values (ir _filled typed)
    (type-core core '() callables))
  (check-runtime typed ir callables 'Unit "same Let-bound callable twice"))

(test-case "一時借用_callable本体でLet束縛したReborrowの生存中に仮引数へAssignしApply"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (called const Unit)
           (Apply
            (RegionApp
             (RegionLam (a)
               (Lam User callable-temporary-read-write (p)
                 (Let (child let (Borrowed Int (RParam a))) (Reborrow p)
                   (Let (read-result const Int) (Read child)
                     (Assign p 7)))))
             (owner-ph))
           (BorrowMut owner))
         unit))))
  (define-values (_ir _filled typed)
    (type-core core '() callable-temporary-read-write-callables))
  (check-equal?
   (and (diagnostic? typed) (diagnostic-id typed)) "E-BOR-025"))

(test-case "一時借用_callable本体の短縮しないReborrowの停止窓はcall-body root"
  (define callables
    (cons '(callable-named-reborrow
            (ForallRegion (a)
              (NFn ((BorrowedMut Int (RParam a))) Unit () (Mutation) () User)))
          temporary-callables))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (called const Unit)
           (Apply
            (RegionApp
             (RegionLam (a)
               (Lam User callable-named-reborrow (p)
                 (Let (child let (Borrowed Int (RParam a))) (Reborrow p)
                   (Let (read-result const Int) (Read child) unit))))
             (owner-ph))
           (BorrowMut owner))
         unit))))
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-local-exit-window-probe
          (lambda args (set! observations (cons args observations)))])
      (type-core core '() callables)))
  (check-true (region-typed? typed)
              (format "named Reborrow Apply: ~s" typed))
  (when (region-typed? typed)
    (define apply-point
      (core-point core
                  (lambda (node) (match node [`(Apply . ,_) #t] [_ #f]))))
    (define apply-node
      (let walk ([node (erase-core core)])
        (or (and (match node [`(Apply . ,_) #t] [_ #f]) node)
            (for/or ([child (in-list (core-children node))]) (walk child)))))
    (define call-body-root
      (append apply-point (list (length (core-children apply-node)))))
    (define matched
      (findf (lambda (observation)
               (and (set? (list-ref observation 4))
                    (not (set-empty? (list-ref observation 4)))
                    (deferred-leaf-exit? (list-ref observation 6))))
             observations))
    (check-not-false matched
                     (format "formal local event window: ~s" observations))
    (when matched
      (check-equal? (list-ref matched 5) call-body-root
                    "extent の無い Reborrow は call-body root のまま"))))

#lang racket

(require rackunit
         racket/list
         racket/match
         racket/set
         redex/reduction-semantics
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../borrow.rkt"
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
                   (NFn ((Borrowed Int (RParam a))) Int () () () User)))
    (nested (NFn () Int () () () User))))

(define test-callables
  (cons '(recur-reader
          (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a))) Unit () (Mutation) () User)))
        (cons '(return-child
                (ForallRegion (a)
                  (NFn ((BorrowedMut Int (RParam a)))
                       (Borrowed Int (RParam a)) () (Mutation) () User)))
              (cons '(inner-scope
                      (ForallRegion (a)
                        (NFn ((BorrowedMut Int (RParam a))) Unit () (Mutation) () User)))
                    sink-callables))))

(define yield-callables
  (cons '(inner-scope-yield
          (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a))) Unit ()
                 ((Yield Int) Mutation) () User)))
        test-callables))

(define borrowed-row-callables
  (cons '(inner-scope-latent-borrow
          (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a))) Unit ()
                 ((Yield (Borrowed Int (RParam a))) Mutation) () User)))
        test-callables))

(define (inner-scope-call body argument [region 'owner-ph]
                          [callable 'inner-scope])
  `(Apply
    (RegionApp
     (RegionLam (a) (Lam User ,callable (p) ,body))
     (,region))
    ,argument))

(define (scoped-inner-scope-call body owner)
  `(Scope ()
     (Let (temporary let (BorrowedMut Int ph)) (BorrowMut ,owner)
       ,(inner-scope-call body 'temporary))))

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

(define (type-core core [places '()] [callables test-callables])
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
          (core-type-of/regions filled places callables #:ir ir)))

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

(define (check-live-trace typed expected [callables test-callables])
  (define start (inject-g2m (region-execution-core typed)))
  (define configs (trace-g2 start))
  (define rows
    (for/list ([config (in-list configs)])
      (runtime-row config callables expected)))
  (define first-live
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
  (check-not-false first-live "trace に runtime-row がある config がある")
  (for ([config (in-list (drop configs first-live))]
        [row (in-list (drop rows first-live))]
        [index (in-naturals first-live)])
    (check-not-false row (format "config ~a の runtime-row" index))
    (check-true (config-ok? config callables expected row)
                (format "config ~a の config-ok?" index)))
  (check-true (redex-match? G2m v (match (last configs)
                                   [`(cfg ,value ,_ ...) value]))
              "trace の終端が値"))

(define record-owner-type '(Record ((o (Option Int) mut))))
(define record-owner-value
  '(Rec ((o mut (Construct (Option Int) some 1)))))
(define record-reader-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,record-owner-type (RParam a)))
          Unit () () () User)))
(define record-reader-callables `((record-reader ,record-reader-type)))
(define record-reader-return-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,record-owner-type (RParam a)))
          (BorrowedMut (Option Int) (RParam a)) () () () User)))
(define record-reader-return-callables
  `((record-reader-return ,record-reader-return-type)))
(define record-reader-body
  '(Eliminate (ProjBorrow p o)
     ((some (child) -> (Let (read const Int) (Read child) unit))
      (none () -> unit))))
(define (record-reader-call argument)
  `(Apply
    (RegionApp
     (RegionLam (a) (Lam User record-reader (p) ,record-reader-body))
     (owner-ph))
    ,argument))
(define (record-reader-return-call argument)
  `(Apply
    (RegionApp
     (RegionLam
      (a) (Lam User record-reader-return (p) (ProjBorrow p o)))
     (owner-ph))
    ,argument))
(define nested-record-owner-type
  `(Record ((f ,record-owner-type mut))))
(define nested-record-owner-value
  `(Rec ((f mut ,record-owner-value))))
(define record-reader-core
  `(Scope ()
     (Let (owner let (Owned ,record-owner-type)) ,record-owner-value
       (Let (argument let (BorrowedMut ,record-owner-type ph))
            (BorrowMut owner)
         (Let (called const Unit) ,(record-reader-call 'argument)
           (Assign (ProjBorrow argument o)
                   (Construct (Option Int) none)))))))
(define nested-record-reader-core
  `(Scope ()
     (Let (owner let (Owned ,nested-record-owner-type))
          ,nested-record-owner-value
       (Let (root let (BorrowedMut ,nested-record-owner-type ph))
            (BorrowMut owner)
         (Let (argument let (BorrowedMut ,record-owner-type ph))
              (ProjBorrow root f)
           (Let (called const Unit) ,(record-reader-call 'argument)
             (Assign (ProjBorrow argument o)
                     (Construct (Option Int) none))))))))
(define nested-record-reader-escape-core
  `(Scope ()
     (Let (owner let (Owned ,nested-record-owner-type))
          ,nested-record-owner-value
       (Let (root let (BorrowedMut ,nested-record-owner-type ph))
            (BorrowMut owner)
         (Let (argument let (BorrowedMut ,record-owner-type ph))
              (ProjBorrow root f)
           (Let (escaped let (BorrowedMut (Option Int) owner-ph))
                ,(record-reader-return-call 'argument)
             (Assign (ProjBorrow argument o)
                     (Construct (Option Int) none))))))))

(test-case "Record 欄を親にする出口は実引数の source alpha に対応する"
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-local-exit-window-probe
          (lambda (cap index alpha origins source-alphas window event)
            (set! observations
                  (cons (list cap index alpha origins source-alphas window event)
                        observations)))])
      (type-core record-reader-core '() record-reader-callables)))
  (check-true (region-typed? typed)
              (format "型検査: ~s; observations: ~s" typed observations))
  (when (region-typed? typed)
    (define mapped
      (findf (lambda (observation)
               (and (set? (list-ref observation 4))
                    (not (set-empty? (list-ref observation 4)))
                    (deferred-leaf-exit? (list-ref observation 6))))
             observations))
    (check-not-false mapped (format "欄の source alpha が対応する: ~s" observations))
    (check-live-trace typed 'Unit record-reader-callables)
    (define start (inject-g2m (region-execution-core typed)))
    (check-equal? (check-borrow-execution start (region-typed-sidecar typed)
                                          _ir 300 (make-bcounters))
                  'ok "Apply 後の親欄への Assign を oracle が承認する")))

(test-case "Union Payload と constructor path は寿命に合う葉の capability を一意に選ぶ"
  (define union-type
    '(Union (BorrowedMut Int (RParam a))
            (BorrowedMut Bool (RParam b))))
  (define-values (union-entry union-leaves)
    (formal-capability-entry union-type 'formal))
  (define union-a-path
    (unique-formal-leaf-path-for-exit
     union-leaves '(Payload) (set '(RParam a))))
  (check-equal? union-a-path '((BorrowedMut Int (RParam a))))
  (check-true (set-member? (capability-entry-keys union-entry)
                           '(formal Payload)))
  (check-equal? (instantiate-capability-path union-type union-a-path (hash))
                union-a-path)
  (check-true
   (set-member? (capability-entry-keys
                 (hash-ref (capability-entry-fields union-entry)
                           (first union-a-path)))
                '(formal Payload)))
  (check-false
   (unique-formal-leaf-path-for-exit
    union-leaves '(Payload) (set '(RParam a) '(RParam b)))
   "Union の葉が曖昧なら照合しない")
  (check-false
   (unique-formal-leaf-path-for-exit
    union-leaves '(Payload) (set '(RParam missing)))
   "Union の葉候補が無ければ照合しない")
  (check-false
   (and (unique-formal-leaf-path-for-exit
         union-leaves '(Payload) (set '(RParam a) '(RParam b)))
        (event-access-path-matches? '(union-root) '(Payload) '(Payload)))
   "Union の候補が曖昧なら path が合っても fail closed")
  (define-values (option-entry option-leaves)
    (formal-capability-entry
     '(Option (BorrowedMut Int (RParam a))) 'formal))
  (check-equal?
   (unique-formal-leaf-path-for-exit
    option-leaves '(0) (set '(RParam a)))
   '((some . 0)))
  (check-true (set-member? (capability-entry-keys option-entry)
                           '(formal 0)))
  (define option-path
    (unique-formal-leaf-path-for-exit
     option-leaves '(0) (set '(RParam a))))
  (check-equal? (instantiate-capability-path
                 '(Option (BorrowedMut Int (RParam a))) option-path (hash))
                '((some . 0)))
  (check-true
   (set-member? (capability-entry-keys
                 (hash-ref (capability-entry-fields option-entry)
                           (first option-path)))
                '(formal 0)))
  (check-true
   (event-access-path-matches? '(union-root) '(Payload) '(Payload)))
  (check-true (event-access-path-matches? '(option-root) '(0) '(0)))
  (define-values (_result-entry result-leaves)
    (formal-capability-entry
     '(Result (BorrowedMut Int (RParam a))
              (BorrowedMut Int (RParam a)))
     'formal))
  (define result-candidates
    (formal-leaf-paths-for-exit result-leaves '(0) (set '(RParam a))))
  (check-equal? (list->set result-candidates)
                (set '((ng . 0)) '((ok . 0))))
  (check-false
   (unique-formal-leaf-path-for-exit result-leaves '(0) (set '(RParam a)))
   "同じ位置と寿命を持つ別 constructor は tag 除去後に曖昧となり fail closed"))

(test-case "Union payload の実要求 path は形式側の出口と一致せず窓を開かない"
  (define union-type
    '(Union (BorrowedMut Int (RParam a))
            (BorrowedMut Bool (RParam a))))
  (define callable-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut ,union-type (RParam a))) Unit () () () User)))
  (define callable-body
    '(UnionEliminate p
       (((BorrowedMut Int (RParam a)) payload ->
          (Let (child let
                     (Borrowed (BorrowedMut Int (RParam a)) (RVar 0)))
               (Reborrow payload)
            unit))
        ((BorrowedMut Bool (RParam a)) other ->
          (Let (child2 let
                       (Borrowed (BorrowedMut Bool (RParam a)) (RVar 1)))
               (Reborrow other)
            unit)))))
  (define callables `((union-reader ,callable-type)))
  (define core
    `(RegionLam (a) (Lam User union-reader (p) ,callable-body)))
  (define ir (build-region-ir core))
  (define inferred
    (typing-inference core '() callables '()
                      (region-ctx ir '() (hash) (hash))))
  (define summaries (filter callable-summary? (sixth inferred)))
  (check-equal? (length summaries) 1)
  (define request-paths
    (for/list ([request (in-list
                         (callable-summary-deferred (first summaries)))]
               #:when (borrow-request? request))
      (borrow-request-fp request)))
  (check-not-false (member '((Payload)) request-paths equal?)
                   (format "実際の Union payload request path: ~s"
                           request-paths))
  (check-false
   (event-access-path-matches? '(union-root) '((Payload)) '(Payload))
   "実要求の list segment は形式側の symbol segment に一致せず、過剰拒否になる"))

(test-case "出口の access path は cap path と parent path を連結し、ずれは拒否する"
  (check-true (event-access-path-matches? '(owner f) '(f o) '(o)))
  (check-false (event-access-path-matches? '(owner f) '(f other) '(o)))
  (check-false (event-access-path-matches? '(owner f) '(f o) '(other))
               "child-fp の再試行でも兄弟欄の出口は一致しない")
  (check-false (event-access-path-matches? '(owner f) '(o) '(o))))

(test-case "同じ仮引数 capability の局所再借用と結果へ逃げる再借用は窓を開かない"
  (define callable-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)))
            (Borrowed Int (RParam a)) () () () User)))
  (define callables `((two-exits ,callable-type)))
  (define body
    '(Let (ignored const Int)
          (Scope ()
            (Let (child let (Borrowed Int (RVar 0))) (Reborrow p)
              (Read child)))
       (Reborrow p)))
  (define definition `(RegionLam (a) (Lam User two-exits (p) ,body)))
  (define definition-ir (build-region-ir definition))
  (define inferred
    (typing-inference definition '() callables '()
                      (region-ctx definition-ir '() (hash) (hash))))
  (define definition-summaries
    (filter callable-summary? (sixth inferred)))
  (check-equal? (length definition-summaries) 1)
  (define summary-events
    (callable-summary-leaf-exits (first definition-summaries)))
  (check-equal?
   (list->set
    (map deferred-leaf-exit-exit-kind summary-events))
   (set 'local 'result)
   "同じ仮引数 capability に局所出口と逃避出口が記録される")
  (check-equal? (list->set (map deferred-leaf-exit-source summary-events))
                (set '(formal 0 ()))
                "両方の出口が同じ仮引数の同じ path を指す")
  (check-true
   (andmap (lambda (event)
             (event-access-path-matches?
              '(owner) '() (deferred-leaf-exit-parent-path event)))
           summary-events)
   "両出口は同じ実引数 capability path と照合される")
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (p let (BorrowedMut Int owner-ph)) (BorrowMut owner)
           (Let (escaped let (Borrowed Int owner-ph))
                (Apply (RegionApp
                        (RegionLam (a) (Lam User two-exits (p) ,body))
                        (owner-ph))
                       p)
             (Assign p 2))))))
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-local-exit-window-probe
          (lambda args (set! observations (cons args observations)))])
      (type-core core '() callables)))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed))
                "E-BOR-025"
                (format "局所出口と逃避出口が同じ capability に属する: ~s; ~s"
                        typed observations))
  (define call-observations
    (filter (lambda (observation)
              (equal? (list-ref observation 0) '(owner)))
            observations))
  (check-true (pair? call-observations)
              (format "呼出し側の照合を観測する: ~s" observations))
  (check-true (andmap (lambda (observation) (not (list-ref observation 5)))
                      call-observations)
              (format "escape を含む候補集合では local 窓を許さない: ~s"
                      call-observations)))

(test-case "非空の実引数 cap path でも parent path と照合し、後続の親書込みを受理する"
  (define observations '())
  (define-values (ir _filled typed)
    (parameterize
        ([current-local-exit-window-probe
          (lambda (cap index alpha origins source-alphas window event)
            (set! observations
                  (cons (list cap index alpha origins source-alphas window event)
                        observations)))])
      (type-core nested-record-reader-core '() record-reader-callables)))
  (check-true (region-typed? typed)
              (format "型検査: ~s; observations: ~s" typed observations))
  (when (region-typed? typed)
    (define matched
      (findf (lambda (observation)
               (and (equal? (cdar observation) '(f))
                    (set? (list-ref observation 4))
                    (not (set-empty? (list-ref observation 4)))
                    (list-ref observation 5)
                    (deferred-leaf-exit? (list-ref observation 6))))
             observations))
    (check-not-false matched (format "cap path が f の出口照合: ~s" observations))
    (when matched
      (define cap (first matched))
      (define event (list-ref matched 6))
      (check-equal? (cdr cap) '(f))
      (check-equal? (deferred-leaf-exit-parent-path event)
                    '(o))
      (check-equal? (append (cdar matched)
                            '(o))
                    '(f o))
      (check-true (event-access-path-matches? cap '(f o) '(o)))
      (check-false (event-access-path-matches? cap '(f other) '(o))
                   "観測した出口 path と異なる要求は probe で照合しない"))
    (check-live-trace typed 'Unit record-reader-callables)
    (define start (inject-g2m (region-execution-core typed)))
    (check-equal? (check-borrow-execution start (region-typed-sidecar typed)
                                          ir 300 (make-bcounters))
                  'ok "非空 cap path の Apply 後も親欄の書込みを oracle が承認する")))

(test-case "非空の実引数 cap path から子を逃がすと親欄への書込みを拒否する"
  (define-values (_ir _filled typed)
    (type-core nested-record-reader-escape-core '()
               record-reader-return-callables))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed))
                "E-BOR-025"
                (format "type-core result: ~s" typed)))

(define (window-function-body post-scope)
  `(Let (read const Int)
        (Scope ()
          (Let (child let (Borrowed Int ph)) (Reborrow p)
            (Read child)))
     ,post-scope))

(define (inner-scope-core body [wrapped? #f] [continuation 'unit])
  `(Scope ()
     (Let (owner let (Owned Int)) 1
       (Let (called const Unit)
            ,(if wrapped?
                 (scoped-inner-scope-call body 'owner)
                 (inner-scope-call body '(BorrowMut owner)))
         ,continuation))))

(define (window-failure-code core [callables test-callables])
  (define result (window-result core callables))
  (and (diagnostic? result) (diagnostic-id result)))

(define (window-type core [callables test-callables])
  (define ir (build-region-ir core))
  (define owner-rho
    (region->rho ir (owner-let-body-region ir '(0))))
  (define filled
    (let replace ([term (fill-region-placeholders core ir)])
      (cond
        [(eq? term 'owner-ph) owner-rho]
        [(pair? term) (cons (replace (car term)) (replace (cdr term)))]
        [else term])))
  (values ir filled
          (core-type-of/regions filled '() callables #:ir ir)))

(define (window-result core [callables test-callables])
  (define-values (_ir _filled result) (window-type core callables))
  result)

(test-case "窓のある関数を裸と Scope 包みの双方で呼べる"
  (define body (window-function-body '(Assign p 7)))
  (define observations '())
  (parameterize
      ([current-local-exit-window-probe
        (lambda (_cap _index alpha origins source-alphas window event)
          (set! observations
                (cons (list alpha origins source-alphas window event)
                      observations)))])
    (for ([wrapped? (in-list '(#f #t))])
      (define-values (_ir _filled typed)
        (window-type (inner-scope-core body wrapped?)))
      (check-true (region-typed? typed)
                  (format "wrapped=~s: ~s; core=~s" wrapped? typed _filled))
      (check-live-trace typed 'Unit)))
  (define mapped
    (findf (lambda (observation)
             (and (set? (third observation))
                  (not (set-empty? (third observation)))
                  (fourth observation)
                  (deferred-leaf-exit? (fifth observation))))
           observations))
  (check-not-false mapped (format "alpha の対応付け: ~s" observations))
  (when mapped
    (check-equal? (first mapped)
                  (deferred-leaf-exit-alpha (fifth mapped)))
    (check-true (set-empty? (set-intersect (second mapped) (third mapped)))
                "定義時 alpha と実引数の source alpha の添字一致に依存しない")))

(test-case "Scope の再借用を関数結果へ返す形は窓を付けず親 Assign を拒む"
  (define body
    '(Scope ()
       (Let (child let (Borrowed Int (RVar 0))) (Reborrow p)
         (Let (written const Unit) (Assign p 7) child))))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         ,(inner-scope-call body '(BorrowMut owner) 'owner-ph 'return-child))))
  (check-equal? (failure-code core) "E-BOR-025"))

(test-case "最内の nested Scope を抜けた後の親の書込みは窓の外"
  (define body
    '(Scope ()
       (Let (read const Int)
            (Scope ()
              (Scope ()
                (Let (child let (Borrowed Int ph)) (Reborrow p)
                  (Read child))))
         (Assign p 7))))
  (check-false (window-failure-code (inner-scope-core body #t))))

(test-case "兄弟 Scope の後でそれぞれ親を書き込める"
  (define body
    '(Let (first const Int)
          (Scope ()
            (Let (child let (Borrowed Int ph)) (Reborrow p)
              (Read child)))
       (Let (first-write const Unit) (Assign p 7)
         (Let (second const Int)
              (Scope ()
                (Let (child2 let (Borrowed Int ph)) (Reborrow p)
                  (Read child2)))
           (Assign p 8)))))
  (check-false (window-failure-code (inner-scope-core body #t))))

(test-case "包んだ呼出し後は再借用でき、裸の呼出し後は lexical loan が残る"
  (define body (window-function-body '(Assign p 7)))
  (define wrapped
    (inner-scope-core
     body #t '(Let (again let (BorrowedMut Int ph)) (BorrowMut owner) unit)))
  (check-false (window-failure-code wrapped)
               (format "~s" (window-result wrapped)))
  (define bare
    (inner-scope-core
     body #f '(Let (again let (BorrowedMut Int ph)) (BorrowMut owner) unit)))
  (check-equal? (window-failure-code bare) "E-BOR-003"))

(test-case "子が生きている Scope 内の二つ目の Reborrow は拒否"
  (define body
    '(Scope ()
       (Let (first let (Borrowed Int ph)) (Reborrow p)
         (Let (second let (Borrowed Int ph)) (Reborrow p)
           (Let (read-first const Int) (Read first)
             (Let (read-second const Int) (Read second) unit))))))
  (define core (inner-scope-core body #t))
  (check-equal? (window-failure-code core) "E-BOR-025"
                (format "~s" (window-result core))))

(test-case "先行する親の書込みは Reborrow の開始窓に止められない"
  (define body
    '(Scope ()
       (Let (written const Unit) (Assign p 7)
         (Let (child let (Borrowed Int ph)) (Reborrow p)
           (Let (read const Int) (Read child) unit)))))
  (define core (inner-scope-core body #t))
  (check-false (window-failure-code core) (format "~s" (window-result core))))

(test-case "Scope の結果へ逃がす子には停止窓を付けず、親の書込みを拒否"
  (define body
    '(Let (escaped let (Borrowed Int ph))
          (Scope ()
            (Let (child let (Borrowed Int ph)) (Reborrow p) child))
       (Assign p 7)))
  (define core (inner-scope-core body #t))
  (check-equal? (window-failure-code core) "E-BOR-025"
                (format "~s" (window-result core))))

(test-case "Yield を含む窓の Scope では親停止を保つ"
  (define body
    '(Let (read const Int)
          (Scope ()
            (Let (child let (Borrowed Int (RParam a))) (Reborrow p)
              (Yield (Read child) (Read child))))
       (Assign p 7)))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (called const Unit)
              ,(inner-scope-call body '(BorrowMut owner) 'owner-ph
                                 'inner-scope-yield)
           unit))))
  (check-equal? (window-failure-code core yield-callables) "E-BOR-025"
                (let-values ([(_ir _filled result)
                              (window-type core yield-callables)])
                  (format "~s" result))))

(test-case "借用 payload の latent row を持つ関数では窓を付けない"
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (called const Unit)
              ,(inner-scope-call (window-function-body '(Assign p 7))
                                 '(BorrowMut owner) 'owner-ph
                                 'inner-scope-latent-borrow)
           unit))))
  (check-equal? (window-failure-code core borrowed-row-callables) "E-BOR-025"
                (let-values ([(_ir _filled result)
                              (window-type core borrowed-row-callables)])
                  (format "~s" result))))

(test-case "Handle を含む Scope では窓なしの親停止を保つ"
  (define body
    '(Let (read const Int)
          (Scope ()
            (Let (child let (Borrowed Int ph)) (Reborrow p)
              (Handle (Return boundary Int)
                (captured -> captured)
                (Perform (Return boundary Int) (Read child)))))
       (Assign p 7)))
  (check-equal? (window-failure-code (inner-scope-core body #t))
                "E-BOR-025"))

(test-case "Apply を含む窓の Scope では窓なしの親停止を保つ"
  (define body
    `(Let (read const Int)
          (Scope ()
            (Let (child let (Borrowed Int ph)) (Reborrow p)
              (Let (called const Int)
                   (Apply (PrimVal (Reserved o-add) add) (Read child) 2)
                (Read child))))
       (Assign p 7)))
  (check-equal? (window-failure-code (inner-scope-core body #t))
                "E-BOR-025"))

(test-case "Unsafe を含む Scope は窓なしにして親停止を保つ"
  (define body
    '(Let (read const Int)
          (Scope ()
            (Let (child let (Borrowed Int ph)) (Reborrow p)
              (Unsafe (Read child))))
       (Assign p 7)))
  (check-equal? (window-failure-code (inner-scope-core body #t))
                "E-BOR-025"))

(test-case "子を捕捉する Lam は E-BOR-011 で拒否され、窓外へ逃がさない"
  (define body
    '(Let (callback let (NFn () Int () () () User))
          (Scope ()
            (Let (child let (Borrowed Int ph)) (Reborrow p)
              (Lam User nested () (Read child))))
       (Assign p 7)))
  (check-equal? (window-failure-code (inner-scope-core body #t)) "E-BOR-011"))

(test-case "Owned の capture を許さない Lam は後続借用との順序判定に入らない"
  (define core
    '(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (f let (NFn () Unit () (Mutation) () User))
              (Lam User delayed () (Assign x 7))
           (Let (b let (BorrowedMut Int (RParam %omitted))) (BorrowMut x)
             (Let (ran const Unit) (Apply f) (Read b)))))))
  (define-values (_ir _filled result)
    (type-core core '() '((delayed (NFn () Unit () (Mutation) () User)))))
  ;; function-body-environment は Owned を捕捉環境から除くため、順序判定の前に拒否する。
  (check-true (diagnostic? result))
  (check-equal? (diagnostic-id result) "E-VAR-006"))

(test-case "Handle と Recur をまたぐ point 順は実行順として誤用しない"
  (define handle-core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (handled let (BorrowedMut Int owner-ph))
              (Handle (Return boundary (BorrowedMut Int owner-ph))
                (captured ->
                  (Let (moved let (Owned Int)) (Move owner) captured))
                (Perform (Return boundary (BorrowedMut Int owner-ph))
                         (BorrowMut owner)))
           (Read handled)))))
  (define recur-core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (parent let (BorrowedMut Int owner-ph)) (BorrowMut owner)
           (Recur recur-reader f (p)
             (Assign p 7)
             (Scope ()
               (Let (child let (Borrowed Int (RParam %omitted)))
                    (Reborrow parent)
                 (Let (called const Unit)
                      (Apply (RegionApp f (owner-ph)) parent)
                   (Read child)))))))))
  (define-values (_hir _hfilled handle-result) (type-core handle-core))
  (define-values (_rir _rfilled recur-result)
    (type-core recur-core '() test-callables))
  (check-equal? (diagnostic-id handle-result) "E-BOR-008")
  (check-equal? (diagnostic-id recur-result) "E-BOR-025"))

(test-case "出口の無い署名要約の呼出しは従来どおり lexical loan を残す"
  (define summary
    (signature-forwarding-summary
     (list '(BorrowedMut Int (RParam a))) 'Int 'sink
     (lambda (id node) (error 'signature-forwarding-summary "~a: ~s" id node))))
  (check-equal? (callable-summary-leaf-exits summary) '())
  (check-true (callable-summary-incomplete? summary))
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

(test-case "包んだ呼出しの Scope 後は裸の二つ目の借用を取れる"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (first const Int) ,(scoped-sink-call 'x)
           ,(sink-call '(BorrowMut x))))))
  (define-values (_ir _filled typed) (type-core core))
  (check-true (region-typed? typed) (format "region typing: ~s" typed)))

(test-case "裸の呼出しを先に置くと後の Scope 包みも E-BOR-003"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (first const Int) ,(sink-call '(BorrowMut x))
           ,(scoped-sink-call 'x)))))
  (check-equal? (failure-code core) "E-BOR-003"))

(test-case "包んだ呼出しの後は裸の借用が Move を妨げる"
  (define core
    `(Scope ()
       (Let (x let (Owned Int)) 1
         (Let (first const Int) ,(scoped-sink-call 'x)
           (Let (second const Int) ,(sink-call '(BorrowMut x))
             (Move x))))))
  (check-equal? (failure-code core) "E-BOR-008"))

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

(test-case "Scope で包んだ呼出しの借用結果を返して読める"
  (define callables
    '((borrow-result
       (ForallRegion (a)
         (NFn ((Borrowed Int (RParam a)))
              (Borrowed Int (RParam a)) () () () User)))))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Let (borrowed let (Borrowed Int ph))
              (Scope ()
                (Let (argument let (Borrowed Int ph)) (Borrow owner)
                  (Apply
                   (RegionApp
                    (RegionLam (a) (Lam User borrow-result (p) p))
                    (owner-ph))
                   argument)))
           (Read borrowed)))))
  (define-values (ir filled typed) (type-core core '() callables))
  (check-true (region-typed? typed) (format "typed: ~s" typed))
  (define start (inject-g2m (region-execution-core typed)))
  (define expected (region-typed-type typed))
  (define sidecar (region-typed-sidecar typed))
  (define configs (trace-g2 start))
  (define rows (map (lambda (config) (runtime-row config callables expected))
                    configs))
  (define first-live
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row)
      index))
  (check-not-false first-live "trace に runtime-row がある config がある")
  (for ([config (in-list (drop configs first-live))]
        [row (in-list (drop rows first-live))])
    (check-not-false row)
    (check-true (config-ok? config callables expected row)))
  (check-equal?
   (check-borrow-execution start sidecar ir 300 (make-bcounters))
   'ok))

(test-case "Scope で包んだ呼出しの借用 Return payload が外へ届く形は E-BOR-020"
  (define callables
    '((return-borrow
       (ForallRegion (a)
         (NFn ((BorrowedMut Int (RParam a))) Never ()
              ((Return boundary (Borrowed Int (RParam a)))) () User)))))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Handle (Return boundary (Borrowed Int owner-ph))
           (captured -> (Read captured))
           (Scope ()
             (Let (argument let (BorrowedMut Int ph)) (BorrowMut owner)
               (Apply
                (RegionApp
                 (RegionLam
                  (a)
                  (Lam User return-borrow (p)
                    (Perform (Return boundary (Borrowed Int (RParam a)))
                             (Reborrow p))))
                 (owner-ph))
                argument)))))))
  (define-values (_ir _filled typed) (type-core core '() callables))
  (check-true (diagnostic? typed) (format "typed: ~s" typed))
  (check-equal? (diagnostic-id typed) "E-BOR-020"))

(test-case "Scope で包んだ呼出しの借用 Option Return payload が外へ届く形は E-BOR-020"
  (define callables
    '((return-option-borrow
       (ForallRegion (a)
         (NFn ((BorrowedMut Int (RParam a))) Never ()
              ((Return boundary (Option (Borrowed Int (RParam a))))) () User)))))
  (define core
    `(Scope ()
       (Let (owner let (Owned Int)) 1
         (Handle (Return boundary (Option (Borrowed Int owner-ph)))
           (captured ->
             (Eliminate captured
               ((none () -> 0)
                (some (payload) -> (Read payload)))))
           (Scope ()
             (Let (argument let (BorrowedMut Int ph)) (BorrowMut owner)
               (Apply
                (RegionApp
                 (RegionLam
                  (a)
                  (Lam User return-option-borrow (p)
                    (Perform
                     (Return boundary (Option (Borrowed Int (RParam a))))
                     (Construct (Option (Borrowed Int (RParam a))) some
                                (Reborrow p)))))
                 (owner-ph))
                argument)))))))
  (define-values (_ir _filled typed) (type-core core '() callables))
  (check-true (diagnostic? typed) (format "typed: ~s" typed))
  (check-equal? (diagnostic-id typed) "E-BOR-020"))

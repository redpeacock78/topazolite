#lang racket

(require rackunit
         racket/match
         racket/set
         "../borrow-oracle.rkt"
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../region.rkt"
         "../region-param.rkt"
         "../traits.rkt"
         "../typing.rkt")

(define opt-int '(Option Int))
(define opt-inner '(Option (Record ((h Int mut)))))
(define union-int-string '(Union Int String))
(define borrowed-mut-int '(BorrowedMut Int (RParam %omitted)))
(define eowner-type
  `(Record ((g Int mut) (o ,opt-int mut) (ro ,opt-inner mut)
            (u ,union-int-string mut))))
(define eowner-value
  `(Rec ((g mut 2)
         (o mut (Construct ,opt-int some 1))
         (ro mut (Construct ,opt-inner some (Rec ((h mut 1)))))
         (u mut (UnionInject ,union-int-string Int 1)))))

(define (then e1 e2) `(Let (ignored let Unit) ,e1 ,e2))
(define (then/as type e1 e2) `(Let (ignored let ,type) ,e1 ,e2))

(define (with-eparent body)
  `(Scope ()
     (Let (x let (Owned ,eowner-type)) ,eowner-value
       (Let (p let (BorrowedMut ,eowner-type (RParam %omitted))) (BorrowMut x)
         ,body))))

(define (with-eparent/no-scope body)
  `(Let (x let (Owned ,eowner-type)) ,eowner-value
     (Let (p let (BorrowedMut ,eowner-type (RParam %omitted))) (BorrowMut x)
       ,body)))

(define write-o `(Assign (ProjBorrow p o) (Construct ,opt-int none)))
(define read-o '(Read (ProjBorrow p o)))
(define (elim-u int-body [string-body 'unit])
  `(UnionEliminate (ProjBorrow p u)
     ((Int c -> ,int-body) (String text -> ,string-body))))
(define (elim-ro some-body [none-body 'unit])
  `(Eliminate (ProjBorrow p ro)
     ((some (c) -> ,some-body) (none () -> ,none-body))))
(define (elim-o some-body [none-body 'unit])
  `(Eliminate (ProjBorrow p o)
     ((some (c) -> ,some-body) (none () -> ,none-body))))

(define shared-view-owner-type
  `(Record ((g Int mut) (i ,opt-int imm))))
(define shared-view-owner-value
  `(Rec ((g mut 2) (i imm (Construct ,opt-int some 1)))))
(define shared-parent-write
  `(Assign p (Rec ((g mut 9) (i imm (Construct ,opt-int some 8))))))
(define shared-sibling-write '(Assign (ProjBorrow p g) 9))
(define (with-shared-view-parent body)
  `(Scope ()
     (Let (x let (Owned ,shared-view-owner-type)) ,shared-view-owner-value
       (Let (p let (BorrowedMut ,shared-view-owner-type (RParam %omitted)))
            (BorrowMut x)
         ,body))))
(define (elim-i some-body [none-body 'unit])
  `(Eliminate (ProjBorrow p i)
     ((some (c) -> ,some-body) (none () -> ,none-body))))

(define probe-a-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((ProbeBox () ((box ((Record ((value Int mut))))))))
   #:fail (lambda (reason kind key)
            (error 'probe-a-ledger "~s ~s ~s" reason kind key))))

(define (type-core core [callables '()] [environment '()])
  (define ir (build-region-ir core))
  (define (contains? value marker)
    (or (eq? value marker)
        (and (pair? value)
             (or (contains? (car value) marker)
                 (contains? (cdr value) marker)))))
  (define child-point
    (and (contains? core 'child-ph)
         (find-core-point
          core
          (lambda (node)
            (match node
              [`(Eliminate ,_ ,_) #t]
              [`(UnionEliminate ,_ ,_) #t]
              [_ #f])))))
  (define owner-rho
    (and (contains? core 'owner-ph)
         (region->rho ir (owner-let-body-region ir '(0)))))
  (define child-rho
    (and child-point
         (region->rho ir (region-at/eliminate ir child-point))))
  (define call-point
    (and (contains? core 'call-ph)
         (find-core-point
          core
          (lambda (node)
            (match node
              [`(BorrowMut ,_) #t]
              [_ #f])))))
  (define call-rho
    (and call-point (region->rho ir (region-at ir call-point))))
  (define filled
    (let walk ([value (fill-region-placeholders (erase-core core) ir)])
      (cond [(eq? value 'owner-ph) owner-rho]
            [(eq? value 'child-ph) child-rho]
            [(eq? value 'call-ph) call-rho]
            [(pair? value) (cons (walk (car value)) (walk (cdr value)))]
            [else value])))
  (values ir filled
          (core-type-of/regions filled '() callables environment #:ir ir)))

(define (stage-one-inference core callables)
  (define ir (build-region-ir core))
  (define (contains? value marker)
    (or (eq? value marker)
        (and (pair? value)
             (or (contains? (car value) marker)
                 (contains? (cdr value) marker)))))
  (define child-point
    (and (contains? core 'child-ph)
         (find-core-point
          core
          (lambda (node)
            (match node
              [`(Eliminate ,_ ,_) #t]
              [`(UnionEliminate ,_ ,_) #t]
              [_ #f])))))
  (define owner-rho
    (and (contains? core 'owner-ph)
         (region->rho ir (owner-let-body-region ir '(0)))))
  (define child-rho
    (and child-point
         (region->rho ir (region-at/eliminate ir child-point))))
  (define call-point
    (and (contains? core 'call-ph)
         (find-core-point
          core
          (lambda (node)
            (match node [`(BorrowMut ,_) #t] [_ #f])))))
  (define call-rho
    (and call-point (region->rho ir (region-at ir call-point))))
  (define filled
    (let walk ([value (fill-region-placeholders (erase-core core) ir)])
      (cond [(eq? value 'owner-ph) owner-rho]
            [(eq? value 'child-ph) child-rho]
            [(eq? value 'call-ph) call-rho]
            [(pair? value) (cons (walk (car value)) (walk (cdr value)))]
            [else value])))
  (values
   ir filled
   (typing-inference (annotate-regions filled ir) '() callables '()
                     (region-ctx ir '() (hash) (hash)))))

(define (trace-g2 start [fuel 300])
  (let loop ([current start] [configs (list start)] [fuel fuel])
    (when (zero? fuel) (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-runtime typed ir callables expected label)
  (define start
    (inject-g2m (erase-core (region-execution-core typed))))
  (define configs (trace-g2 start))
  (for ([cfg (in-list configs)] [index (in-naturals)])
    (define row (runtime-row cfg callables expected))
    (check-not-false row
                     (format "~a config ~a の runtime-row: ~s" label index cfg))
    (check-true (config-ok? cfg callables expected row)
                (format "~a config ~a が config-ok? でない: ~s" label index cfg)))
  (check-equal? (check-borrow-execution start (region-typed-sidecar typed) ir
                                         300 (make-bcounters))
                'ok (format "~a: borrow oracle" label)))

(define (config-borrow-mut-refs cfg)
  (define (walk term)
    (match term
      [`(BorrowMutRef ,_place ,_path ,_region) (list term)]
      [(? list? parts) (append-map walk parts)]
      [_ '()]))
  (match cfg
    [`(cfg ,core ,_ ...) (walk core)]
    [_ '()]))

(define (contains-form? term head)
  (or (and (pair? term) (eq? (car term) head))
      (and (pair? term)
           (or (contains-form? (car term) head)
               (contains-form? (cdr term) head)))))

(define (check-parent-rho-trace core label [form 'EliminateAt])
  (define-values (ir _filled typed) (type-core core))
  (check-true (region-typed? typed) (format "~a: 型検査 ~s" label typed))
  (when (region-typed? typed)
    (define annotated-core (region-execution-core typed))
    (check-true (contains-form? annotated-core form)
                (format "~a: annotate-regions が ~a を出す" label form))
    (define annotated-start (inject-g2m annotated-core))
    (define plain-start (inject-g2m (erase-core annotated-core)))
    (define annotated-configs (trace-g2 annotated-start))
    (define annotated-refs
      (append-map config-borrow-mut-refs annotated-configs))
    (define plain-configs (trace-g2 plain-start))
    (define plain-refs
      (append-map config-borrow-mut-refs plain-configs))
    (check-equal? annotated-refs plain-refs
                  (format "~a: %parent 注釈が child BorrowMutRef を変えない" label))
    (check-equal? (last annotated-configs) (last plain-configs)
                  (format "~a: 終端 config は注釈の有無で一致する" label))
    (for ([cfg (in-list annotated-configs)] [index (in-naturals)])
      (define expected (region-typed-type typed))
      (define row (runtime-row cfg '() expected))
      (check-not-false row
                       (format "~a config ~a の runtime-row" label index))
      (check-true (config-ok? cfg '() expected row)
                  (format "~a config ~a の config-ok?" label index)))))

(define (check-accepted core expected [callables '()] [label "fixture"])
  (define-values (ir _filled typed) (type-core core callables))
  (check-true (region-typed? typed) (format "~a: 型検査 ~s" label typed))
  (when (region-typed? typed)
    (check-true (forall-region-types-alpha-equal?
                 (region-typed-type typed) expected)
                (format "~a: 型 ~s が ~s と領域束縛名以外で一致する"
                        label (region-typed-type typed) expected))
    (check-runtime typed ir callables expected label)))

(define (check-accepted-window-points core expected callables label expected-points)
  (define observed-points '())
  (define-values (ir _filled typed)
    (parameterize
        ([current-local-exit-window-probe
          (lambda (_cap _index _alpha _origins _source-alphas window event)
            (when (and window
                       (deferred-leaf-exit? event)
                       (match (deferred-leaf-exit-source event)
                         [`(binder ,_ ...) #t]
                         [_ #f]))
              (set! observed-points (cons window observed-points))))])
      (type-core core callables)))
  (check-true (region-typed? typed) (format "~a: 型検査 ~s" label typed))
  (when (region-typed? typed)
    (check-true (forall-region-types-alpha-equal? (region-typed-type typed) expected)
                (format "~a: 型 ~s が ~s と領域束縛名以外で一致する"
                        label (region-typed-type typed) expected))
    (check-runtime typed ir callables expected label))
  (check-equal? (list->set observed-points) (list->set expected-points)
                (format "~a: 枝ごとの extent window root" label)))

(define (observe-decomposition-extents core callables)
  (define observed '())
  (define reasons (make-hash))
  (define-values (ir _filled typed)
    (parameterize
        ([current-decomposition-extent-probe
          (lambda (point branch root extent events _items)
            (set! observed
                  (cons (list point branch root extent events) observed)))]
         [current-decomposition-extent-reason-probe
          (lambda (point branch root reason)
            (hash-set! reasons (list point branch root) reason))])
      (type-core core callables)))
  (values ir typed
          (for/list ([record (in-list (reverse observed))])
            (append record
                    (list (hash-ref reasons
                                    (list (first record) (second record)
                                          (third record))
                                    #f))))))

(define (observe-local-exit-windows core callables)
  (define observed '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-local-exit-window-probe
          (lambda (_cap _index _alpha _origins _source-alphas window event)
            (when (deferred-leaf-exit? event)
              (set! observed
                    (cons (list event window) observed))))])
      (type-core core callables)))
  (values typed (reverse observed)))

(define (forall-region-types-alpha-equal? actual expected)
  (match* (actual expected)
    [(`(ForallRegion (,actual-rps ...) ,actual-body)
      `(ForallRegion (,expected-rps ...) ,expected-body))
     (and (= (length actual-rps) (length expected-rps))
          (equal?
           (rename-region-params
            actual-body
            (for/hash ([actual-rp (in-list actual-rps)]
                       [expected-rp (in-list expected-rps)])
              (values actual-rp expected-rp)))
           expected-body))]
    [(_ _) (equal? actual expected)]))

(define (check-rejected core expected-id [callables '()] [label "fixture"])
  (define-values (_ir _filled result) (type-core core callables))
  (check-true (diagnostic? result)
              (format "~a: 診断を期待したが ~s" label result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id
                  (format "~a: 診断 id" label))))

(define (check-rejected-conflict-pair core expected-id callables label)
  (define pairs '())
  (define-values (_ir _filled result)
    (parameterize
        ([current-borrow-conflict-probe
          (lambda (left right) (set! pairs (cons (list left right) pairs)))])
      (type-core core callables)))
  (check-true (diagnostic? result)
              (format "~a: 診断を期待したが ~s" label result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id
                  (format "~a: 診断 id" label)))
  (check-not-false (pair? pairs)
                   (format "~a: borrow-conflicting-alias の対を観測する" label))
  (reverse pairs))

(define (requests-with-path typed path)
  (filter (lambda (request)
            (and (borrow-request? request)
                 (equal? (borrow-request-fp request) path)))
          (borrow-sidecar-requests (region-typed-sidecar typed))))

(define (check-binder-alpha core label)
  (define-values (ir _filled typed) (type-core core))
  (check-true (region-typed? typed) (format "~a: 型検査 ~s" label typed))
  (when (region-typed? typed)
    (check-equal? (region-typed-type typed) 'Unit)
    (check-runtime typed ir '() 'Unit label)
    (define binder-requests (requests-with-path typed '(ro 0)))
    (define child-requests (requests-with-path typed '(ro 0 h)))
    (check-equal? (length binder-requests) 1
                  (format "~a: 可変 binder ごとに一つの要求" label))
    (check-equal? (length child-requests) 1
                  (format "~a: binder 内 ProjBorrow が別の要求を持つ" label))
    (when (and (= (length binder-requests) 1)
               (= (length child-requests) 1))
      (define binder-alpha (borrow-request-alpha (first binder-requests)))
      (define child-alpha (borrow-request-alpha (first child-requests)))
      (check-not-equal? binder-alpha child-alpha
                        (format "~a: binder と本体先頭の借用は別 alpha" label))
      (define decomposition
        (find-core-point core
                         (lambda (node)
                           (match node
                             [`(Eliminate (ProjBorrow p ro) ,_) #t]
                             [_ #f]))))
      (check-equal?
       (hash-ref (region-typed-σ typed)
                 (lifetime-var-index binder-alpha))
       (branch-region-of ir decomposition 0)
       (format "~a: binder alpha の下限は枝 region" label)))))

(define (find-core-point core predicate)
  (let walk ([node (erase-core core)] [point '()])
    (if (predicate node)
        point
        (for/or ([child (in-list (core-children node))]
                 [index (in-naturals)])
          (walk child (append point (list index)))))))

(test-case "注釈付き分解を erase-core が素の形へ戻す"
  (check-equal?
   (erase-core
    '(EliminateAt (Move p) ((some (x) (3) -> x))))
   '(Eliminate (Move p) ((some (x) -> x))))
  (check-equal?
   (erase-core
    '(UnionEliminateAt (Move p) ((Int x %parent -> x))))
   '(UnionEliminate (Move p) ((Int x -> x)))))

(test-case "Data の %parent 注釈は child BorrowMutRef の値を変えない"
  (check-parent-rho-trace (with-eparent (elim-o '(Read c) 0)) "eliminate-parent-rho"))

(test-case "Union の %parent 注釈は child BorrowMutRef の値を変えない"
  (check-parent-rho-trace (with-eparent (elim-u '(Read c) 0))
                          "union-parent-rho" 'UnionEliminateAt))

(test-case "分解の退場は部分木の外の後続 point だけ"
  (define ir
    (build-region-ir
     '(Scope ()
        (Let (z let Unit)
             (Eliminate y ((none () -> unit) (some (v) -> unit)))
          unit))))
  (define E '(0 0))
  (check-true (point-after-decomposition? ir E '(0 1)))
  (check-false (point-after-decomposition? ir E '(0 0 1)))
  (check-false (point-after-decomposition? ir E '(0 0 2)))
  (check-false (point-after-decomposition? ir E '(0)))
  (check-false (point-after-decomposition? ir E E)))

(test-case "Handle の handler と本体をまたぐ分解の point は後続としない"
  (define ir
    (build-region-ir
     '(Scope ()
        (Handle (Return b Int)
          (k -> (Eliminate y ((none () -> unit) (some (v) -> unit))))
          unit))))
  (check-false (point-after-decomposition? ir '(0 0) '(0 1))))

(test-case "同じ枝の後続使用は分解の退場として除かれない"
  (define core
    '(Scope (1)
       (Eliminate (Construct Bool true)
         ((true () ->
                 (Let (b let (BorrowedMut Int (RVar 0))) (BorrowMut 1)
                   (Let (written let Unit) (Assign (BorrowMut 1) 2)
                     (Read b))))
          (false () -> 0)))))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw (annotate-regions core ir)
                 (list (list 1 'Int)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (second result) 'borrow-conflicting-alias))

(define flip-reborrow
  `(Scope ()
     (Let (q let (Borrowed ,eowner-type (RParam %omitted))) (Reborrow p)
       (Read (ProjBorrow q o)))))
(define flip-binder-reborrow
  `(Let (d let (Borrowed Int (RParam %omitted))) (Reborrow c)
     (Let (ignored let Int) (Read d) unit)))
(define flip-binder-projection
  `(Let (d let (BorrowedMut Int (RParam %omitted))) (ProjBorrow c h)
     (Assign d 3)))

(test-case "Eliminate 後の同じ欄 Read は Scope と owner-body の両方で受理"
  (for ([wrap (in-list (list with-eparent with-eparent/no-scope))])
    (check-accepted (wrap (then (elim-o 'unit) read-o)) opt-int '()
                    "flip-read")))

(test-case "Eliminate 後の同じ欄 Assign は Scope と owner-body の両方で受理"
  (for ([wrap (in-list (list with-eparent with-eparent/no-scope))])
    (check-accepted (wrap (then (elim-o 'unit) write-o)) 'Unit '()
                    "flip-write")))

(test-case "Eliminate 後の同じ欄 Reborrow は Scope と owner-body の両方で受理"
  (for ([wrap (in-list (list with-eparent with-eparent/no-scope))])
    (check-accepted (wrap (then (elim-o 'unit) flip-reborrow)) opt-int '()
                    "flip-reborrow")))

(test-case "UnionEliminate 後の同じ欄 Assign は Scope と owner-body の両方で受理"
  (for ([wrap (in-list (list with-eparent with-eparent/no-scope))])
    (check-accepted
     (wrap (then (elim-u 'unit)
                 '(Assign (ProjBorrow p u)
                          (UnionInject (Union Int String) String "s"))))
     'Unit '() "flip-union")))

(test-case "Eliminate 後に枝 binder の Reborrow を使い切れば親欄へ書ける"
  (for ([wrap (in-list (list with-eparent with-eparent/no-scope))])
    (check-accepted (wrap (then (elim-o flip-binder-reborrow) write-o))
                    'Unit '() "flip-binder-reborrow")))

(test-case "Eliminate 後に枝 binder の射影を使い切れば親欄へ書ける"
  (for ([wrap (in-list (list with-eparent with-eparent/no-scope))])
    (check-accepted
     (wrap (then (elim-ro flip-binder-projection)
                 '(Assign (ProjBorrow p ro)
                          (Construct (Option (Record ((h Int mut)))) none))))
     'Unit '() "flip-binder-projection")))

(test-case "Eliminate の子を結果へ逃がすと E-BOR-025"
  (check-rejected
   (with-eparent
    `(Let (escaped let (BorrowedMut Int (RParam %omitted)))
          ,(elim-o 'c '(ProjBorrow p g))
       ,(then write-o '(Read escaped))))
   "E-BOR-025" '() "escape-result"))

(test-case "Eliminate の子を結果へ逃がさなければ後で親欄を使える"
  (check-accepted
   (with-eparent
    `(Let (result let Int) ,(elim-o '(Read c) 0)
       ,(then write-o 'result)))
   'Int '() "escape-result/control"))

(test-case "Yield は Eliminate の子を全ての分解の外へ運ぶ"
  (check-rejected
   (with-eparent (then (elim-o '(Yield c unit)) write-o))
   "E-BOR-025" '() "escape-yield"))

(test-case "Yield の観測値を枝内で消費すれば親欄を使える"
  (check-accepted
   (with-eparent (then (elim-o '(Yield (Read c) unit)) write-o))
   'Unit '() "escape-yield/control"))

(define (nested-consumed [scope? #f])
  (define inner
    `(Let (d let (BorrowedMut Int (RParam %omitted)))
          ,(elim-o 'c '(ProjBorrow p g))
       (Assign d 1)))
  (then (elim-ro (if scope? `(Scope () ,inner) inner)) write-o))

(test-case "枝 Scope の無い入れ子分解結果は外側の書込みと競合する"
  (check-rejected (with-eparent (nested-consumed)) "E-BOR-025" '()
                  "nested-consumed/scope-parent/no-branch-scope"))

(test-case "Scope 内の入れ子分解結果を Scope 付き枝内で消費すると受理"
  (check-accepted (with-eparent (nested-consumed #t)) 'Unit '()
                  "nested-consumed/scope-parent/branch-scope"))

(test-case "owner-body でも枝 Scope の無い入れ子結果は書込みと競合する"
  (check-rejected (with-eparent/no-scope (nested-consumed)) "E-BOR-025" '()
                  "nested-consumed/owner-parent/no-branch-scope"))

(test-case "owner-body の入れ子分解結果を Scope 付き枝内で消費すると受理"
  (check-accepted (with-eparent/no-scope (nested-consumed #t)) 'Unit '()
                  "nested-consumed/owner-parent/branch-scope"))

(test-case "枝内 Scope の結果が運ぶ scrutinee 子は Scope の親 region まで生きる"
  (define scope-result
    `(Let (d let (BorrowedMut Int (RParam %omitted)))
       (Scope () ,(elim-o 'c '(ProjBorrow p g)))
       (Assign d 1)))
  (define core
    (with-eparent (then (elim-ro scope-result) write-o)))
  (define-values (ir _filled typed) (type-core core))
  (check-true (region-typed? typed)
              (format "scope-result: 型検査 ~s" typed))
  (when (region-typed? typed)
    (check-equal? (region-typed-type typed) 'Unit)
    (check-runtime typed ir '() 'Unit "scope-result")
    (define child-point
      (find-core-point core (lambda (node) (equal? node '(ProjBorrow p o)))))
    (define scope-point
      (find-core-point
       core
       (lambda (node)
         (match node [`(Scope () (Eliminate (ProjBorrow p o) ,_)) #t] [_ #f]))))
    (define child-request
      (for/first ([request
                   (in-list
                    (borrow-sidecar-requests (region-typed-sidecar typed)))]
                  #:when (equal? (borrow-request-point request) child-point))
        request))
    (check-not-false child-request)
    (when child-request
      (check-equal?
       (hash-ref (region-typed-σ typed)
                 (lifetime-var-index (borrow-request-alpha child-request)))
       (region-parent ir (region-at/branch ir scope-point))))))

(test-case "内側結果を外側の結果へも逃がすと E-BOR-025"
  (check-rejected
   (with-eparent
    `(Let (escaped let (BorrowedMut Int (RParam %omitted)))
          ,(elim-ro (elim-o 'c '(ProjBorrow p g)) '(ProjBorrow p g))
       ,(then write-o '(Read escaped))))
   "E-BOR-025" '() "escape-nested"))

(test-case "兄弟の枝で同じ欄を直接借りても借用期間が重ならない"
  (check-accepted
   (with-eparent
    `(Eliminate (Construct Bool true)
       ((true () ->
          (Let (r let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
            (Assign r 1)))
        (false () ->
          (Let (r2 let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
            (Assign r2 2))))))
   'Unit '() "sibling-borrow"))

(test-case "兄弟の枝で scrutinee binder から Reborrow する形を受理"
  (check-accepted
   (with-eparent
    `(UnionEliminate (ProjBorrow p u)
       ((Int c ->
          (Let (r let (Borrowed Int (RParam %omitted))) (Reborrow c)
            (Let (value let Int) (Read r) unit)))
        (String c ->
          (Let (r let (Borrowed String (RParam %omitted))) (Reborrow c)
            (Let (value let String) (Read r) unit))))))
   'Unit '() "sibling-binder-reborrow"))

(test-case "枝内の別欄借用は枝 region を下限にし、親欄へ書ける"
  (define core
    (with-eparent
     (then
      (elim-o
       `(Let (other let ,borrowed-mut-int) (ProjBorrow p g)
          (Assign other 2)))
      write-o)))
  (check-accepted core 'Unit '() "branch-unrelated-borrow")
  (define-values (ir _filled typed) (type-core core))
  (when (region-typed? typed)
    (define point
      (find-core-point
       core
       (lambda (node) (equal? node '(ProjBorrow p g)))))
    (define request
      (for/first ([request
                   (in-list
                    (borrow-sidecar-requests (region-typed-sidecar typed)))]
                  #:when (equal? point (borrow-request-point request)))
        request))
    (check-not-false request)
    (when request
      (check-equal?
       (hash-ref (region-typed-σ typed)
                 (lifetime-var-index (borrow-request-alpha request)))
       (region-at/branch ir point)
       "枝内の独立した借用の下限は枝 region"))))

(test-case "probe a: 枝内 binder へ書いた後は親全体を再代入できる"
  (define box-type '(Data ProbeBox ()))
  (define box-value
    `(Construct ,box-type box (Rec ((value mut 1)))))
  (define core
    `(Scope ()
       (Let (x let (Owned ,box-type)) ,box-value
         (Let (p let (BorrowedMut ,box-type (RParam %omitted))) (BorrowMut x)
           (Let (ignored let Unit)
               (Eliminate p
                 ((box (c) -> (Assign c (Rec ((value mut 2)))))))
             (Assign p ,box-value))))))
  (call-with-trait-ledger
   probe-a-ledger
   (lambda () (check-accepted core 'Unit '() "probe-a"))))

(test-case "分解の子を Record に格納して外へ出すと E-BOR-025"
  (define record-type `(Record ((payload ,borrowed-mut-int imm))))
  (check-rejected
   (with-eparent
    `(Let (escaped let ,record-type)
          ,(elim-o `(Rec ((payload imm c)))
                   `(Rec ((payload imm (ProjBorrow p g)))))
       ,(then write-o 'unit)))
   "E-BOR-025" '() "escape-construct-record"))

(test-case "分解の子を Option に格納して外へ出すと E-BOR-025"
  (define option-type `(Option (BorrowedMut Int (RVar 0))))
  (check-rejected
   (with-eparent
    `(Let (escaped let ,option-type)
          ,(elim-o `(Construct ,option-type some c)
                   `(Construct ,option-type none))
       ,(then write-o 'unit)))
   "E-BOR-025" '() "escape-construct-option"))

(test-case "分解の子を UnionInject に格納して外へ出すと E-BOR-025"
  (define union-type `(Union ,borrowed-mut-int Unit))
  (check-rejected
   (with-eparent
    `(Let (escaped let ,union-type)
          ,(elim-o `(UnionInject ,union-type ,borrowed-mut-int c)
                   `(UnionInject ,union-type Unit unit))
       ,(then write-o 'unit)))
   "E-BOR-025" '() "escape-construct-union"))

(test-case "分解の枝 binder から Reborrow した子を外へ出すと E-BOR-025"
  (check-rejected
   (with-eparent
    `(Let (escaped let (Borrowed Int (RParam %omitted)))
          ,(elim-o '(Reborrow c) '(Reborrow (ProjBorrow p g)))
       ,(then write-o '(Read escaped))))
   "E-BOR-025" '() "escape-binder-reborrow"))

(test-case "分解の子から AddressOf した raw pointer を外へ出すと E-BOR-025"
  (define rawptr-int '(RawPtr Int Mut NonNull (Align 1)
                              (AddrSpace native) (Prov owned)))
  (check-rejected
   (with-eparent
    `(Let (escaped let ,rawptr-int)
          ,(elim-o '(AddressOf c) '(AddressOf (ProjBorrow p g)))
       ,(then write-o '(Unsafe (RawLoad escaped)))))
   "E-BOR-025" '() "escape-address-of"))

(test-case "分解 binder を捕捉する Lam は既存の E-BOR-011 で拒否"
  (define callable-type '(NFn (Int) Int () () () User))
  (check-rejected
   (with-eparent
    (elim-o
     '(Lam User capture (ignored) (Read c))
     '(Lam User plain (ignored) (Read (ProjBorrow p g)))))
   "E-BOR-011"
   `((capture ,callable-type) (plain ,callable-type))
   "escape-lam"))

(define shared-borrowed-int '(Borrowed Int (RParam %omitted)))
(define shared-return-op `(Return boundary ,shared-borrowed-int))

(test-case "escape-return: 関数結果へ分解の子を Return すると E-BOR-004"
  (define return-type '(Borrowed Int (RParam a)))
  (define return-op `(Return boundary ,return-type))
  (define returner-type
    `(ForallRegion (a) (NFn () ,return-type () () () User)))
  (define callables `((returner ,returner-type)))
  (check-rejected
   `(RegionLam (a)
      (Lam User returner ()
        (Handle ,return-op (returned -> returned)
          ,(with-shared-view-parent
            (elim-i `(Perform ,return-op c)
                    `(Perform ,return-op
                              (Reborrow (ProjBorrow p g))))))))
   "E-BOR-004" callables "escape-return"))

(test-case "分解の枝内で matching Return handler が借用 payload を消費する"
  (check-accepted
   (with-shared-view-parent
    (then/as 'Int
     (elim-i
      `(Handle (Return boundary Int) (answer -> answer)
        (Perform (Return boundary Int) (Read c)))
      0)
     shared-sibling-write))
   'Unit '() "escape-return-control"))

(test-case "escape-handle: 分解の外の Return handler へ子を逃がすと E-BOR-025"
  (check-rejected
   (with-shared-view-parent
    `(Let (returned let ,shared-borrowed-int)
          (Handle ,shared-return-op (answer -> answer)
            ,(elim-i
              `(Perform ,shared-return-op c)
              `(Perform ,shared-return-op (Reborrow (ProjBorrow p g)))))
       ,shared-parent-write))
   "E-BOR-025" '() "escape-handle"))

(test-case "分解の枝の matching Return handler が payload を消費する"
  (check-accepted
   (with-shared-view-parent
    (then/as 'Int
     (elim-i
      `(Read
        (Handle ,shared-return-op (answer -> answer)
          (Perform ,shared-return-op c)))
      0)
     shared-sibling-write))
   'Unit '() "escape-handle-control"))

(test-case "escape-handle-mismatch: 操作の異なる内側 handler を越える"
  (define inner-return-op `(Return inner-boundary ,shared-borrowed-int))
  (check-rejected
   (with-shared-view-parent
    (then
     (elim-i
      `(Handle ,inner-return-op (inner -> inner)
         (Perform ,shared-return-op c)))
     shared-parent-write))
   "E-BOR-025" '() "escape-handle-mismatch"))

(test-case "一致する内側 handler は分解の枝で payload を消費する"
  (check-accepted
   (with-shared-view-parent
    (then/as 'Int
     (elim-i
      `(Read
        (Handle ,shared-return-op (answer -> answer)
          (Perform ,shared-return-op c)))
      0)
     shared-parent-write))
   'Unit '() "escape-handle-matching-control"))

;; 借用を含む mut slot は E-VAR-009 で先に止まり、出口照合まで届かない。
;; E-VAR-009 を回収するときに、子を外側の mut slot へ Reassign して
;; 親へ Assign する形の E-BOR-025 の対を足す。
(test-case "借用型を mutable Let へ Reassign する形は E-VAR-009 で先に拒否"
  (check-rejected
   (with-shared-view-parent
    `(Let (y let (Owned Int)) 3
       (Let (r mut ,shared-borrowed-int) (Borrow y)
         ,(elim-i `(Reassign r ,shared-borrowed-int c) 'unit))))
   "E-VAR-009" '() "escape-assign-reassign-unrepresentable"))

(test-case "Assign の値を Read c にすれば分解の後も受理"
  (check-accepted
   (with-shared-view-parent
    `(Let (y let (Owned Int)) 3
       (Let (r let (BorrowedMut Int (RParam %omitted))) (BorrowMut y)
         ,(elim-i `(Let (updated let Unit) (Assign r (Read c)) 1) 0))))
   'Int '() "escape-assign-read-control"))

(define (borrowed-slot-owner-type-at rho)
  `(Record ((g Int mut)
            (i (Option (Borrowed Int ,rho)) imm)
            (slot (Borrowed Int ,rho) mut))))
(define borrowed-slot-owner-type
  (borrowed-slot-owner-type-at '(RParam a)))
(define (borrowed-slot-parameter-type-at rp)
  `(ForallRegion (,rp)
     (NFn ((BorrowedMut ,(borrowed-slot-owner-type-at `(RParam ,rp))
                        (RParam ,rp)))
          Unit () (Mutation) () User)))
(define borrowed-slot-parameter-type
  (borrowed-slot-parameter-type-at 'a))
(define (borrowed-slot-monotype-at rp)
  `(NFn ((BorrowedMut ,(borrowed-slot-owner-type-at rp) ,rp))
        Unit () (Mutation) () User))
(define borrowed-slot-callables `((slot-writer ,borrowed-slot-parameter-type)))
(define borrowed-slot-writer
  '(RegionLam (a)
     (Lam User slot-writer (p)
       (Let (view let
                  (Record ((g Int mut)
                           (i (Option (Borrowed Int (RParam a))) imm)
                           (slot (Borrowed Int (RParam a)) mut))))
            (Read p)
         unit))))

(define (borrowed-slot-resource-owner-type-at rho)
  `(Record ((g (Option (Owned Res)) mut)
            (slot (Borrowed Res ,rho) mut))))
(define (borrowed-slot-resource-parameter-type-at root-rp slot-rp)
  `(ForallRegion (,root-rp ,slot-rp)
     (NFn ((BorrowedMut ,(borrowed-slot-resource-owner-type-at `(RParam ,slot-rp))
                        (RParam ,root-rp)))
          Unit () (Mutation) () User)))
(define borrowed-slot-resource-parameter-type
  (borrowed-slot-resource-parameter-type-at 'root 'slot))
(define borrowed-slot-resource-writer
  '(RegionLam (root slot)
     (Lam User resource-slot-writer (p)
       (Let (slot-value let (Borrowed Res (RParam slot)))
            (Read (ProjBorrow p slot))
         unit))))
(define borrowed-slot-resource-callables
  `((resource-slot-writer ,borrowed-slot-resource-parameter-type)))

(define borrowed-slot-single-lifetime-parameter-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,(borrowed-slot-resource-owner-type-at '(RParam a))
                        (RParam a)))
          Unit () (Mutation) () User)))
(define borrowed-slot-single-lifetime-writer
  '(RegionLam (a)
     (Lam User single-lifetime-slot-writer (p)
       (Let (slot-value let (Borrowed Res (RParam a)))
            (Read (ProjBorrow p slot))
         unit))))

(define borrowed-slot-curried-parameter-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,(borrowed-slot-resource-owner-type-at '(RParam a))
                        (RParam a))
           Int)
          Unit () (Mutation) () User)))
(define borrowed-slot-curried-writer
  '(RegionLam (a)
     (Lam User borrowed-slot-curried-writer (p n)
       (Let (slot-value let (Borrowed Res (RParam a)))
            (Read (ProjBorrow p slot))
         unit))))

(define (check-pending-owner-boundary-rejected
         core callables boundary position label)
  (define observed '())
  (define-values (_ir _filled result)
    (parameterize
        ([current-callable-summary-boundary-probe
          (lambda (head position _summary)
            (set! observed (cons (list head position) observed)))])
      (type-core core callables)))
  (check-true (diagnostic? result) (format "~a: 診断 ~s" label result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-006"
                  (format "~a: diagnostic details ~s" label result)))
  (check-not-false (member (list boundary position) observed)
                   (format "~a: ~a 境界を観測 ~s" label boundary observed)))

(define single-lifetime-owner-type
  (borrowed-slot-resource-owner-type-at '(RParam %omitted)))
(define single-lifetime-callables
  `((single-lifetime-slot-writer
     ,borrowed-slot-single-lifetime-parameter-type)))

(define (single-lifetime-owner-scope body)
  `(Scope ()
     (Let (y let (Owned Res)) (resource 20)
       (Let (owner let ,single-lifetime-owner-type)
            (Rec ((g mut
                    (Construct (Option (Owned Res)) some
                               (OwnLeaf (resource 21))))
                  (slot mut (Borrow y))))
         ,body))))

(define (check-pending-owner-alias-call wrapper label)
  (define writer-type borrowed-slot-single-lifetime-parameter-type)
  (define external-owner-type
    (borrowed-slot-resource-owner-type-at '(RParam external)))
  (define external-borrow-type
    `(BorrowedMut ,external-owner-type (RParam external)))
  (define monomorphic-type
    `(NFn ((BorrowedMut ,external-owner-type (RParam external)))
          Unit () (Mutation) () User))
  (define core
    (single-lifetime-owner-scope
     `(Let (writer let ,writer-type) ,borrowed-slot-single-lifetime-writer
        (Let (resolved let Unit)
             (Apply (RegionApp writer (call-ph)) (BorrowMut owner))
          (Apply ,(wrapper `(RegionApp writer ((RParam external)))
                            monomorphic-type)
                 q)))))
  (define ir (build-region-ir core))
  (define call-point
    (find-core-point core
                     (lambda (node)
                       (match node [`(BorrowMut ,_) #t] [_ #f]))))
  (define call-rho (region->rho ir (region-at ir call-point)))
  (define filled
    (let walk ([value (fill-region-placeholders (erase-core core) ir)])
      (cond [(eq? value 'call-ph) call-rho]
            [(pair? value) (cons (walk (car value)) (walk (cdr value)))]
            [else value])))
  (define-values (formal-entry _leaves)
    (formal-capability-entry external-borrow-type 'q-root))
  (define Λ
    (region-ctx-add-token
     (region-ctx ir '() (hash) (hash)) 'q
     (capability-entry-keys formal-entry) #f #f
     (capability-entry-fields formal-entry)
     (capability-entry-variants formal-entry)
     #t))
  (define owners '())
  (define result
    (parameterize
        ([current-deferred-owner-check-probe
          (lambda (alpha owner point _node)
            (set! owners (cons (list alpha owner point) owners)))])
      (type-of/raw (annotate-regions filled ir) '()
                   `((single-lifetime-slot-writer ,writer-type))
                   `((q ,external-borrow-type)) Λ)))
  (check-equal? (first result) 'fail (format "~a: 結果 ~s" label result))
  (check-equal? (second result) 'borrow-unknown-owner-region
                (format "~a: owner の無い別名を拒否 ~s" label result))
  (check-equal? (length owners) 1
                (format "~a: 先行する local owner 呼出しだけ解決 ~s"
                        label owners)))

(define (check-single-lifetime-owner-call core label)
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-deferred-owner-check-probe
          (lambda (alpha owner point _node)
            (set! observations (cons (list alpha owner point) observations)))])
      (type-core core single-lifetime-callables)))
  (check-true (region-typed? typed)
              (format "~a: 静的な型検査 ~s" label typed))
  (check-true
   (and (= (length observations) 1)
        (exact-nonnegative-integer? (first (first observations)))
        (exact-nonnegative-integer? (second (first observations)))
        (equal? (first (first observations)) (second (first observations))))
   (format "~a: 呼出しで owner 判定を具体化 ~s" label observations)))

(define (check-owner-call-resolves core callables label)
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-deferred-owner-check-probe
          (lambda (alpha owner point _node)
            (set! observations (cons (list alpha owner point) observations)))])
      (type-core core callables)))
  (check-true (region-typed? typed)
              (format "~a: 静的な型検査 ~s" label typed))
  (check-true
   (and (= (length observations) 1)
        (exact-nonnegative-integer? (first (first observations)))
        (exact-nonnegative-integer? (second (first observations)))
        (equal? (first (first observations)) (second (first observations))))
   (format "~a: RegionApp 後の owner 判定 ~s" label observations)))

(define (resource-slot-owner-call root-rho slot-rho)
  `(Scope ()
     (Let (y let (Owned Res)) (resource 20)
       (Let (owner let ,(borrowed-slot-resource-owner-type-at
                         '(RParam %omitted)))
            (Rec ((g mut
                    (Construct (Option (Owned Res)) some
                               (OwnLeaf (resource 21))))
                  (slot mut (Borrow y))))
         (Apply
          (RegionApp ,borrowed-slot-resource-writer
                     (,root-rho ,slot-rho))
          (BorrowMut owner))))))

(define (outlives-at-point constraints point)
  (filter (lambda (constraint)
            (and (region-constraint? constraint)
                 (eq? (region-constraint-kind constraint) 'outlives)
                 (equal? (region-constraint-point constraint) point)))
          constraints))

(define (apply-outlives-constraints constraints core)
  (filter (lambda (constraint)
            (and (region-constraint? constraint)
                 (eq? (region-constraint-kind constraint) 'outlives)
                 (match (core-node core (region-constraint-point constraint))
                   [`(Apply ,_ ,_ ...) #t]
                   [_ #f])))
          constraints))

(test-case "二寿命の nested slot reader は未呼出し定義を受理する"
  (define-values (_ir _filled typed)
    (type-core borrowed-slot-resource-writer
               borrowed-slot-resource-callables))
  (check-true (region-typed? typed)
              (format "二寿命の callable 定義を保留して受理: ~s" typed))
  (when (region-typed? typed)
    (check-true
     (forall-region-types-alpha-equal?
      (region-typed-type typed) borrowed-slot-resource-parameter-type))))

(test-case "二寿命 outlives は満たす実引数の Apply で具体化する"
  (define core (resource-slot-owner-call 'call-ph 'call-ph))
  (define-values (ir filled inference)
    (stage-one-inference core borrowed-slot-resource-callables))
  (define apply-point
    (find-core-point filled
                     (lambda (node)
                       (match node [`(Apply ,_ ,_) #t] [_ #f]))))
  (define instantiated
    (outlives-at-point (third inference) apply-point))
  (check-equal? (length instantiated) 1
                (format "Apply 位置に outlives を実体化: ~s" instantiated))
  (when (= (length instantiated) 1)
    (check-true (equal? (region-constraint-left (first instantiated))
                        (region-constraint-right (first instantiated)))
                (format "等しい実引数なら outlives を満たす: ~s"
                        (first instantiated))))
  (define-values (_ir _filled typed)
    (type-core core borrowed-slot-resource-callables))
  (check-true (region-typed? typed)
              (format "満たす実引数で静的受理: ~s" typed)))

(test-case "二寿命 outlives の違反は Apply で E-BOR-004 となり owner 判定と分かれる"
  (define core (resource-slot-owner-call 'call-ph 'owner-ph))
  (define-values (ir filled inference)
    (stage-one-inference core borrowed-slot-resource-callables))
  (define apply-point
    (find-core-point filled
                     (lambda (node)
                       (match node [`(Apply ,_ ,_) #t] [_ #f]))))
  (define instantiated
    (outlives-at-point (third inference) apply-point))
  (check-equal? (length instantiated) 1
                (format "違反する outlives を Apply で観測: ~s" instantiated))
  (when (= (length instantiated) 1)
    (define constraint (first instantiated))
    (check-false
     (region-outlives? ir (region-constraint-left constraint)
                       (region-constraint-right constraint))
     (format "Apply の outlives 関係は破れる: ~s" constraint))
    (check-true
     (match (erase-core (region-constraint-node constraint))
       [`(Apply ,_ ,_) #t]
       [_ #f])
     (format "制約の node は Apply: ~s" constraint)))
  (define-values (_ir _filled typed)
    (type-core core borrowed-slot-resource-callables))
  (check-true (diagnostic? typed)
              (format "違反する実引数を拒否: ~s" typed))
  (when (diagnostic? typed)
    (check-equal? (diagnostic-id typed) "E-BOR-004"
                  (format "outlives 項目由来で E-BOR-004: ~s" typed))))

(test-case "outlives だけの保留 summary も Curry 境界で E-BOR-006"
  (define summary
    (callable-summary '()
                      (list (deferred-outlives-check
                             '(RParam long) '(RParam short) '(0 1)))
                      '() (hash) '() #f))
  (define observed '())
  (define failures '())
  (parameterize
      ([current-callable-summary-boundary-probe
        (lambda (boundary position seen-summary)
          (set! observed (cons (list boundary position seen-summary) observed)))])
    (reject-pending-callable-summary!
     '(Curry function 0) 'function summary 'boundary
     (lambda (reason location)
       (set! failures (cons (list reason location) failures)))))
  (check-equal? failures '((borrow-unknown-owner-region boundary)))
  (check-equal? (map (lambda (entry) (take entry 2)) observed)
                '((Curry function))
                "outlives-only item reaches the Curry boundary guard"))

(define two-lifetime-forwarder-type
  `(ForallRegion (outer-root outer-slot)
     (NFn ((BorrowedMut
            ,(borrowed-slot-resource-owner-type-at '(RParam outer-slot))
            (RParam outer-root)))
          Unit () (Mutation) () User)))
(define two-lifetime-forwarder
  `(RegionLam (outer-root outer-slot)
     (Lam User two-lifetime-forwarder (p)
       (Let (writer let ,borrowed-slot-resource-parameter-type)
            ,borrowed-slot-resource-writer
         (Apply
          (RegionApp writer ((RParam outer-root) (RParam outer-slot)))
          p)))))
(define two-lifetime-forwarder-callables
  `((resource-slot-writer ,borrowed-slot-resource-parameter-type)
    (two-lifetime-forwarder ,two-lifetime-forwarder-type)))

(define (outer-generic-resource-slot-call slot-rho)
  `(Scope ()
     (Let (y let (Owned Res)) (resource 20)
       (Let (owner let ,(borrowed-slot-resource-owner-type-at
                         '(RParam %omitted)))
            (Rec ((g mut
                    (Construct (Option (Owned Res)) some
                               (OwnLeaf (resource 21))))
                  (slot mut (Borrow y))))
         (Apply
          (RegionApp ,two-lifetime-forwarder
                     (call-ph ,slot-rho))
          (BorrowMut owner))))))

(define nested-slot-inner-type
  `(ForallRegion (inner-slot)
     (NFn ((BorrowedMut
            ,(borrowed-slot-resource-owner-type-at '(RParam inner-slot))
            (RParam outer-root)))
          Unit () (Mutation) () User)))
(define nested-slot-forwarder-type
  `(ForallRegion (outer-root outer-slot)
     (NFn ((BorrowedMut
            ,(borrowed-slot-resource-owner-type-at '(RParam outer-slot))
            (RParam outer-root)))
          Unit () (Mutation) () User)))
(define nested-slot-forwarder
  `(RegionLam (outer-root outer-slot)
     (Lam User nested-slot-forwarder (p)
       (Let (inner let ,nested-slot-inner-type)
            (RegionLam (inner-slot)
              (Lam User nested-slot-inner (q)
                (Let (writer let ,borrowed-slot-resource-parameter-type)
                     ,borrowed-slot-resource-writer
                  (Apply
                   (RegionApp writer
                              ((RParam outer-root) (RParam inner-slot)))
                   q))))
         (Apply (RegionApp inner ((RParam outer-slot))) p)))))
(define nested-slot-forwarder-callables
  `((resource-slot-writer ,borrowed-slot-resource-parameter-type)
    (nested-slot-inner ,nested-slot-inner-type)
    (nested-slot-forwarder ,nested-slot-forwarder-type)))

(define (nested-slot-forwarder-call slot-rho)
  `(Scope ()
     (Let (y let (Owned Res)) (resource 20)
       (Let (owner let ,(borrowed-slot-resource-owner-type-at
                         '(RParam %omitted)))
            (Rec ((g mut
                    (Construct (Option (Owned Res)) some
                               (OwnLeaf (resource 21))))
                  (slot mut (Borrow y))))
         (Apply
          (RegionApp ,nested-slot-forwarder
                     (call-ph ,slot-rho))
          (BorrowMut owner))))))

(test-case "nested frame の二寿命 outlives は満たす外側 Apply で受理する"
  (define core (nested-slot-forwarder-call 'call-ph))
  (define-values (_ir _filled typed)
    (type-core core nested-slot-forwarder-callables))
  (check-true (region-typed? typed)
              (format "内側 frame から外側 frame へ再保留: ~s" typed)))

(test-case "nested frame の二寿命 outlives 違反は外側 Apply で E-BOR-004"
  (define core (nested-slot-forwarder-call 'owner-ph))
  (define-values (ir filled inference)
    (stage-one-inference core nested-slot-forwarder-callables))
  (define apply-point
    (find-core-point filled
                     (lambda (node)
                       (match node [`(Apply ,_ ,_) #t] [_ #f]))))
  (define instantiated
    (outlives-at-point (third inference) apply-point))
  (check-equal? (length instantiated) 1
                (format "外側 Apply の outlives: ~s" instantiated))
  (when (= (length instantiated) 1)
    (check-false
     (region-outlives? ir (region-constraint-left (first instantiated))
                       (region-constraint-right (first instantiated)))))
  (define-values (_ir _filled typed)
    (type-core core nested-slot-forwarder-callables))
  (check-true (diagnostic? typed)
              (format "入れ子の不適合関係を拒否: ~s" typed))
  (when (diagnostic? typed)
    (check-equal? (diagnostic-id typed) "E-BOR-004")))

(test-case "内側の二寿命 outlives を外側 generic summary へ再保留する"
  (define core (outer-generic-resource-slot-call 'call-ph))
  (define-values (ir filled inference)
    (stage-one-inference core two-lifetime-forwarder-callables))
  (define instantiated
    (apply-outlives-constraints (third inference) filled))
  (check-equal? (length instantiated) 1
                (format "外側 Apply で再保留項目を実体化: ~s" instantiated))
  (when (= (length instantiated) 1)
    (check-true
     (region-outlives? ir (region-constraint-left (first instantiated))
                       (region-constraint-right (first instantiated)))
     (format "外側 Apply の実引数が関係を満たす: ~s" instantiated)))
  (define-values (_ir _filled typed)
    (type-core core two-lifetime-forwarder-callables))
  (check-true (region-typed? typed)
              (format "外側 RParam へ再保留した満足呼出し: ~s" typed)))

(test-case "外側 generic の不適合な再保留 outlives は Apply で E-BOR-004"
  (define core (outer-generic-resource-slot-call 'owner-ph))
  (define-values (ir filled inference)
    (stage-one-inference core two-lifetime-forwarder-callables))
  (define instantiated
    (apply-outlives-constraints (third inference) filled))
  (check-equal? (length instantiated) 1
                (format "外側 Apply の outlives 制約: ~s" instantiated))
  (when (= (length instantiated) 1)
    (check-false
     (region-outlives? ir (region-constraint-left (first instantiated))
                       (region-constraint-right (first instantiated)))
     (format "外側実引数の関係は不成立: ~s" instantiated)))
  (define-values (_ir _filled typed)
    (type-core core two-lifetime-forwarder-callables))
  (check-true (diagnostic? typed)
              (format "外側 summary の不適合を拒否: ~s" typed))
  (when (diagnostic? typed)
    (check-equal? (diagnostic-id typed) "E-BOR-004")))

(test-case "同じ callee の outlives 判定は呼出しごとに独立する"
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,(borrowed-slot-resource-owner-type-at
                           '(RParam %omitted)))
              (Rec ((g mut
                      (Construct (Option (Owned Res)) some
                                 (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Let (writer let ,borrowed-slot-resource-parameter-type)
               ,borrowed-slot-resource-writer
             (Let (satisfied let Unit)
                  (Apply (RegionApp writer (call-ph call-ph))
                         (BorrowMut owner))
               (Apply (RegionApp writer (call-ph owner-ph))
                      (BorrowMut owner))))))))
  (define-values (ir filled inference)
    (stage-one-inference core borrowed-slot-resource-callables))
  (define apply-points
    (for/list ([point (in-list (core-points filled))]
               #:when (match (core-node filled point)
                        [`(Apply ,_ ,_) #t]
                        [_ #f]))
      point))
  (define instantiated
    (for/list ([point (in-list apply-points)])
      (outlives-at-point (third inference) point)))
  (check-equal? (length apply-points) 2)
  (check-equal? (map length instantiated) '(1 1)
                (format "各 Apply に個別の制約を持つ: ~s" instantiated))
  (when (and (= (length instantiated) 2)
             (andmap (lambda (items) (= (length items) 1)) instantiated))
    (define relations
      (for/list ([items (in-list instantiated)])
        (define constraint (first items))
        (region-outlives? ir (region-constraint-left constraint)
                          (region-constraint-right constraint))))
    (check-equal? relations '(#t #f)
                  (format "先の充足結果が後の違反へ漏れない: ~s" relations)))
  (define-values (_ir _filled typed)
    (type-core core borrowed-slot-resource-callables))
  (check-true (diagnostic? typed)
              (format "二度目の不適合 call は拒否: ~s" typed))
  (when (diagnostic? typed)
    (check-equal? (diagnostic-id typed) "E-BOR-004")))

(test-case "Recur fixed point は二寿命 outlives を seed し Apply で判定する"
  (define recur-body
    '(Let (slot-value let (Borrowed Res (RParam slot)))
          (Read (ProjBorrow p slot))
       unit))
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,(borrowed-slot-resource-owner-type-at
                           '(RParam %omitted)))
              (Rec ((g mut
                      (Construct (Option (Owned Res)) some
                                 (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Recur resource-slot-recur loop (p) ,recur-body
             (Apply (RegionApp loop (call-ph call-ph))
                    (BorrowMut owner)))))))
  (define callables `((resource-slot-recur
                       ,borrowed-slot-resource-parameter-type)))
  (define-values (ir filled inference)
    (stage-one-inference core callables))
  (define recur-constraints
    (apply-outlives-constraints (third inference) filled))
  (check-equal? (length recur-constraints) 1
                (format "Recur summary が Apply へ outlives を運ぶ: ~s"
                        recur-constraints))
  (when (= (length recur-constraints) 1)
    (check-true
     (region-outlives? ir (region-constraint-left (first recur-constraints))
                       (region-constraint-right (first recur-constraints)))))
  (define-values (_ir _filled typed) (type-core core callables))
  (check-true (region-typed? typed)
              (format "Recur の固定点を通した outlives: ~s" typed)))

(test-case "RecurVal は二寿命 outlives を summary に運ぶ"
  (define recur-body
    '(Let (slot-value let (Borrowed Res (RParam slot)))
          (Read (ProjBorrow p slot))
       unit))
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,(borrowed-slot-resource-owner-type-at
                           '(RParam %omitted)))
              (Rec ((g mut
                      (Construct (Option (Owned Res)) some
                                 (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Apply
            (RegionApp
             (RecurVal resource-slot-recur loop (p) ,recur-body)
             (call-ph call-ph))
            (BorrowMut owner))))))
  (define callables `((resource-slot-recur
                       ,borrowed-slot-resource-parameter-type)))
  (define-values (ir filled inference)
    (stage-one-inference core callables))
  (define recur-constraints
    (apply-outlives-constraints (third inference) filled))
  (check-equal? (length recur-constraints) 1
                (format "RecurVal summary が Apply へ outlives を運ぶ: ~s"
                        recur-constraints))
  (when (= (length recur-constraints) 1)
    (check-true
     (region-outlives? ir (region-constraint-left (first recur-constraints))
                       (region-constraint-right (first recur-constraints)))))
  (define-values (_ir _filled typed) (type-core core callables))
  (check-true (region-typed? typed)
              (format "RecurVal summary の outlives: ~s" typed)))

(define (resource-slot-writer-with-region-names root-rp slot-rp lambda-name)
  `(RegionLam (,root-rp ,slot-rp)
     (Lam User ,lambda-name (p)
       (Let (slot-value let (Borrowed Res (RParam ,slot-rp)))
            (Read (ProjBorrow p slot))
         unit))))

(define (single-lifetime-slot-writer-with-region-name rp lambda-name)
  `(RegionLam (,rp)
     (Lam User ,lambda-name (p)
       (Let (slot-value let (Borrowed Res (RParam ,rp)))
            (Read (ProjBorrow p slot))
         unit))))

(test-case "escape-assign: Owned root に借用欄を持たせる形は E-OWN-022 で先に拒否"
  (define borrowed-slot-owner-value
    `(Rec ((g mut 2)
           (i imm (Construct ,opt-int some 1))
           (slot mut (Borrow y)))))
  (check-rejected
   `(Scope ()
      (Let (y let (Owned Int)) 3
        (Let (x let (Owned ,borrowed-slot-owner-type))
             ,borrowed-slot-owner-value
          (Let (p let (BorrowedMut ,borrowed-slot-owner-type
                                   (RParam %omitted)))
               (BorrowMut x)
            ,(then/as
              'Int
              `(Eliminate (ProjBorrow p i)
                 ((some (c) -> (Assign (ProjBorrow p slot) c))
                  (none () -> unit)))
              `(Assign p ,borrowed-slot-owner-value))))))
   "E-OWN-022" '() "escape-assign-borrowed-field-precheck"))

(test-case "未呼出しの RegionLam は nested Borrowed slot の所有者を保留する"
  (define-values (_ir _filled typed)
    (type-core borrowed-slot-writer borrowed-slot-callables))
  (check-true (region-typed? typed) (format "未呼出し定義: ~s" typed))
  (when (region-typed? typed)
    (check-true (forall-region-types-alpha-equal?
                 (region-typed-type typed) borrowed-slot-parameter-type))))

(define borrowed-slot-forwarder-type
  `(ForallRegion (b)
     (NFn ((BorrowedMut ,(borrowed-slot-owner-type-at '(RParam b))
                        (RParam b)))
          Unit () (Mutation) () User)))
(define borrowed-slot-forwarder-callables
  `((slot-writer ,borrowed-slot-parameter-type)
    (slot-forwarder ,borrowed-slot-forwarder-type)))
(define borrowed-slot-forwarder
  `(RegionLam (b)
     (Lam User slot-forwarder (q)
       (Apply (RegionApp ,borrowed-slot-writer ((RParam b))) q))))

(test-case "callee の RegionApp は入れ子 owner 要求を外側 summary へ保留する"
  (define-values (_ir _filled typed)
    (type-core borrowed-slot-forwarder borrowed-slot-forwarder-callables))
  (check-true (region-typed? typed)
              (format "nested RegionApp の保留: ~s" typed))
  (when (region-typed? typed)
    (check-true (forall-region-types-alpha-equal?
                 (region-typed-type typed) borrowed-slot-forwarder-type))))

(test-case "単一寿命の nested slot は RegionApp で所有者へ解決する"
  (define callables
    `((single-lifetime-slot-writer
       ,borrowed-slot-single-lifetime-parameter-type)))
  (define owner-type
    (borrowed-slot-resource-owner-type-at '(RParam %omitted)))
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,owner-type)
              (Rec ((g mut
                      (Construct (Option (Owned Res)) some
                                 (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Apply
            (RegionApp ,borrowed-slot-single-lifetime-writer (call-ph))
            (BorrowMut owner))))))
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-deferred-owner-check-probe
          (lambda (alpha owner point _node)
            (set! observations (cons (list alpha owner point) observations)))])
      (type-core core callables)))
  (check-true (region-typed? typed)
              (format "単一寿命の所有者解決: ~s" typed))
  (check-true
   (and (= (length observations) 1)
        (exact-nonnegative-integer? (first (first observations)))
        (exact-nonnegative-integer? (second (first observations)))
        (equal? (first (first observations)) (second (first observations))))
   (format "呼出し側の alpha から BorrowMut owner を解決する: ~s"
           observations)))

(test-case "RecurVal frame は nested owner 判定を呼出しまで運ぶ"
  (define recur-type borrowed-slot-single-lifetime-parameter-type)
  (define callables `((single-lifetime-slot-recur ,recur-type)))
  (define owner-type
    (borrowed-slot-resource-owner-type-at '(RParam %omitted)))
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,owner-type)
              (Rec ((g mut
                      (Construct (Option (Owned Res)) some
                                 (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Apply
            (RegionApp
             (RecurVal single-lifetime-slot-recur loop (p)
               (Let (slot-value let (Borrowed Res (RParam a)))
                    (Read (ProjBorrow p slot))
                 unit))
            (call-ph))
            (BorrowMut owner))))))
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-deferred-owner-check-probe
          (lambda (alpha owner point _node)
            (set! observations (cons (list alpha owner point) observations)))])
      (type-core core callables)))
  (check-true (region-typed? typed)
              (format "RecurVal summary: ~s" typed))
  (check-true
   (and (= (length observations) 1)
        (exact-nonnegative-integer? (first (first observations)))
        (exact-nonnegative-integer? (second (first observations)))
        (equal? (first (first observations)) (second (first observations))))
   (format "RecurVal owner check の具体化: ~s" observations)))

(test-case "RecurVal frame の保留 owner summary は別名を E-BOR-006 にする"
  (define recur-type borrowed-slot-single-lifetime-parameter-type)
  (define callables `((single-lifetime-slot-recur ,recur-type)))
  (define owner-type
    (borrowed-slot-resource-owner-type-at '(RParam external)))
  (define alias-type `(BorrowedMut ,owner-type (RParam external)))
  (define core
    `(Apply
      (RegionApp
       (RecurVal single-lifetime-slot-recur loop (p)
         (Let (slot-value let (Borrowed Res (RParam a)))
              (Read (ProjBorrow p slot))
           unit))
       ((RParam external)))
      q))
  (define ir (build-region-ir core))
  (define-values (formal-entry _leaves)
    (formal-capability-entry alias-type 'q-root))
  (define Λ
    (region-ctx-add-token
     (region-ctx ir '() (hash) (hash)) 'q
     (capability-entry-keys formal-entry) #f #f
     (capability-entry-fields formal-entry)
     (capability-entry-variants formal-entry)
     #t))
  (define result
    (type-of/raw (annotate-regions (fill-region-placeholders
                                    (erase-core core) ir)
                                  ir)
                 '() callables `((q ,alias-type)) Λ))
  (check-equal? (first result) 'fail (format "RecurVal alias: ~s" result))
  (check-equal? (second result) 'borrow-unknown-owner-region
                "RecurVal の保留 summary は呼出しで owner 不明を拒否"))

(test-case "Recur frame は fixed-point の owner 判定を呼出しまで運ぶ"
  (define recur-type borrowed-slot-single-lifetime-parameter-type)
  (define callables `((single-lifetime-slot-recur ,recur-type)))
  (define owner-type
    (borrowed-slot-resource-owner-type-at '(RParam %omitted)))
  (define body
    `(Let (slot-value let (Borrowed Res (RParam a)))
          (Read (ProjBorrow p slot))
       unit))
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,owner-type)
              (Rec ((g mut
                      (Construct (Option (Owned Res)) some
                                 (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Recur single-lifetime-slot-recur loop (p) ,body
             (Apply
              (RegionApp loop (call-ph))
              (BorrowMut owner)))))))
  (define observations '())
  (define-values (_ir _filled typed)
    (parameterize
        ([current-deferred-owner-check-probe
          (lambda (alpha owner point _node)
            (set! observations (cons (list alpha owner point) observations)))])
      (type-core core callables)))
  (check-true (region-typed? typed)
              (format "Recur summary: ~s" typed))
  (check-true
   (and (= (length observations) 1)
        (exact-nonnegative-integer? (first (first observations)))
        (exact-nonnegative-integer? (second (first observations)))
        (equal? (first (first observations)) (second (first observations))))
   (format "Recur owner check の具体化: ~s" observations)))

(test-case "Let-bound RegionLam の RegionApp は保留 summary を引き継ぐ"
  (define writer-type (borrowed-slot-parameter-type-at 'b))
  (define writer
    '(RegionLam (b)
       (Lam User slot-writer (p)
         (Let (view let
                    (Record ((g Int mut)
                             (i (Option (Borrowed Int (RParam b))) imm)
                             (slot (Borrowed Int (RParam b)) mut))))
              (Read p)
           unit))))
  (define callables `((slot-writer ,writer-type)))
  (define core
    `(Let (writer let ,writer-type)
          ,writer
      (RegionApp writer ((RParam a)))))
  (define wrapper-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut ,(borrowed-slot-owner-type-at '(RParam a))
                          (RParam a)))
            Unit () (Mutation) () User)))
  (define-values (_ir _filled typed)
    (type-core `(RegionLam (a) ,core) callables))
  (check-true (region-typed? typed)
              (format "Let-bound RegionApp: ~s" typed))
  (when (region-typed? typed)
    (check-true (forall-region-types-alpha-equal?
                 (region-typed-type typed) wrapper-type))))

(test-case "Let 注釈と RegionLam の ForallRegion 名が異なっても owner を解決する"
  (define writer-type borrowed-slot-single-lifetime-parameter-type)
  (define writer
    (single-lifetime-slot-writer-with-region-name
     'source-region 'renamed-slot-writer))
  (define core
    (single-lifetime-owner-scope
     `(Let (writer let ,writer-type) ,writer
        (Apply (RegionApp writer (call-ph))
               (BorrowMut owner)))))
  (check-owner-call-resolves
   core `((renamed-slot-writer ,writer-type))
   "Let 注釈名と RegionLam binder 名の対応"))

(test-case "注釈名が異なる writer は同じ本体の owner alias だけ E-BOR-006"
  (define writer-type borrowed-slot-single-lifetime-parameter-type)
  (define writer
    (single-lifetime-slot-writer-with-region-name
     'source-region 'renamed-slot-writer))
  (define external-owner-type
    (borrowed-slot-resource-owner-type-at '(RParam external)))
  (define external-borrow-type
    `(BorrowedMut ,external-owner-type (RParam external)))
  ;; 一つの本体で、実所有者のある local borrow は解決し、環境由来の
  ;; external alias は同じ名前対応の writer でも E-BOR-006 にする。
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,single-lifetime-owner-type)
              (Rec ((g mut
                      (Construct (Option (Owned Res)) some
                                 (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Let (writer let ,writer-type) ,writer
             (Let (resolved let Unit)
                  (Apply (RegionApp writer (call-ph))
                         (BorrowMut owner))
               (Apply (RegionApp writer ((RParam external))) q)))))))
  ;; q には capability key と field table を与えるが、RParam external の
  ;; owner 制約は与えない。従って失敗は token 欠落でなく owner 判定である。
  (define ir (build-region-ir core))
  (define call-point
    (find-core-point core
                     (lambda (node)
                       (match node [`(BorrowMut ,_) #t] [_ #f]))))
  (define call-rho (region->rho ir (region-at ir call-point)))
  (define filled
    (let walk ([value (fill-region-placeholders (erase-core core) ir)])
      (cond [(eq? value 'call-ph) call-rho]
            [(pair? value) (cons (walk (car value)) (walk (cdr value)))]
            [else value])))
  (define-values (formal-entry _leaves)
    (formal-capability-entry external-borrow-type 'q-root))
  (define Λ
    (region-ctx-add-token
     (region-ctx ir '() (hash) (hash)) 'q
     (capability-entry-keys formal-entry) #f #f
     (capability-entry-fields formal-entry)
     (capability-entry-variants formal-entry)
     #t))
  (define owners '())
  (define result
    (parameterize
        ([current-deferred-owner-check-probe
          (lambda (alpha owner point _node)
            (set! owners (cons (list alpha owner point) owners)))])
      (type-of/raw (annotate-regions filled ir) '()
                   `((renamed-slot-writer ,writer-type))
                   `((q ,external-borrow-type))
                   Λ)))
  (check-equal? (first result) 'fail (format "外側 alias の owner 判定 ~s" result))
  (check-equal? (second result) 'borrow-unknown-owner-region
                "型引数の name mapping 後も owner のない外側 alias は拒否")
  (check-equal? (length owners) 1
                (format "先行する owner 対照だけ解決: ~s" owners))
  (when (= (length owners) 1)
    (check-equal? (first (first owners)) (second (first owners))
                  "同じ本体の受理側は owner region へ解決する")))

(test-case "内側 ForallRegion の同名 binder は外側 owner RParam を捕獲しない"
  (define inner-type borrowed-slot-single-lifetime-parameter-type)
  (define inner-writer
    (single-lifetime-slot-writer-with-region-name
     'a 'shadowed-inner-writer))
  (define outer-type
    `(ForallRegion (a b)
       (NFn ((BorrowedMut ,(borrowed-slot-resource-owner-type-at '(RParam b))
                          (RParam b)))
            Unit () (Mutation) () User)))
  (define outer-writer
    `(RegionLam (a b)
       (Lam User shadowed-outer-writer (p)
         (Let (inner let ,inner-type) ,inner-writer
           (Apply (RegionApp inner ((RParam b))) p)))))
  (define core
    (single-lifetime-owner-scope
     `(Apply (RegionApp ,outer-writer ((RVar 0) call-ph))
             (BorrowMut owner))))
  (check-owner-call-resolves
   core
   `((shadowed-inner-writer ,inner-type)
     (shadowed-outer-writer ,outer-type))
   "同名 ForallRegion の lexical shadowing"))

(test-case "外側 RParam を RegionApp 実引数にした owner 項目を外側 summary へ合成する"
  (define inner-type borrowed-slot-single-lifetime-parameter-type)
  (define inner-writer
    (single-lifetime-slot-writer-with-region-name
     'source-region 'composed-inner-writer))
  (define outer-type
    `(ForallRegion (outer)
       (NFn ((BorrowedMut ,(borrowed-slot-resource-owner-type-at '(RParam outer))
                          (RParam outer)))
            Unit () (Mutation) () User)))
  (define outer-writer
    `(RegionLam (outer)
       (Lam User composed-outer-writer (p)
         (Let (inner let ,inner-type) ,inner-writer
           (Apply
            (RegionApp inner ((RParam outer)))
            p)))))
  (define core
    (single-lifetime-owner-scope
     `(Apply (RegionApp ,outer-writer (call-ph)) (BorrowMut owner))))
  (check-owner-call-resolves
   core
   `((composed-inner-writer ,inner-type)
     (composed-outer-writer ,outer-type))
   "RegionApp の置換合成で owner を外側へ再保留"))

(test-case "Let の束縛式から callable summary を変数へ引き継ぐ"
  (check-single-lifetime-owner-call
   (single-lifetime-owner-scope
    `(Let (writer let ,borrowed-slot-single-lifetime-parameter-type)
          ,borrowed-slot-single-lifetime-writer
       (Apply (RegionApp writer (call-ph)) (BorrowMut owner))))
   "Let binding summary"))

(test-case "Let の結果位置から callable summary を引き継ぐ"
  (define monomorphic-type
    `(NFn ((BorrowedMut
            ,(borrowed-slot-resource-owner-type-at 'call-ph)
            call-ph))
          Unit () (Mutation) () User))
  (check-single-lifetime-owner-call
   (single-lifetime-owner-scope
    `(Let (writer let ,borrowed-slot-single-lifetime-parameter-type)
          ,borrowed-slot-single-lifetime-writer
       (Let (monomorphic let ,monomorphic-type)
            (RegionApp writer (call-ph))
         (Apply monomorphic (BorrowMut owner)))))
   "Let result summary"))

(test-case "Let の直接結果変数から外側 Apply へ callable summary を引き継ぐ"
  (define monomorphic-type
    `(NFn ((BorrowedMut
            ,(borrowed-slot-resource-owner-type-at 'call-ph)
            call-ph))
          Unit () (Mutation) () User))
  (check-single-lifetime-owner-call
   (single-lifetime-owner-scope
    `(Apply
      (Let (forwarded let ,monomorphic-type)
           (RegionApp ,borrowed-slot-single-lifetime-writer (call-ph))
        forwarded)
      (BorrowMut owner)))
   "Let direct result summary"))

(test-case "Scope の結果位置から callable summary を引き継ぐ"
  (check-single-lifetime-owner-call
   (single-lifetime-owner-scope
    `(Let (writer let ,borrowed-slot-single-lifetime-parameter-type)
          ,borrowed-slot-single-lifetime-writer
       (Apply (Scope () (RegionApp writer (call-ph)))
              (BorrowMut owner))))
   "Scope output summary"))

(test-case "Unsafe の本体から callable summary を引き継ぐ"
  (check-single-lifetime-owner-call
   (single-lifetime-owner-scope
    `(Let (writer let ,borrowed-slot-single-lifetime-parameter-type)
          ,borrowed-slot-single-lifetime-writer
       (Apply (Unsafe (RegionApp writer (call-ph)))
              (BorrowMut owner))))
   "Unsafe output summary"))

(test-case "Move は unowned の保留 callable を E-OWN-012 で先に拒否"
  (define-values (_ir _filled typed)
    (type-core
     `(Let (writer let ,borrowed-slot-single-lifetime-parameter-type)
           ,borrowed-slot-single-lifetime-writer
        (Move writer))
     single-lifetime-callables))
  (check-true (diagnostic? typed) (format "Move の診断 ~s" typed))
  (check-equal? (and (diagnostic? typed) (diagnostic-id typed)) "E-OWN-012"))

(test-case "許可 wrapper は別名を後の Apply で E-BOR-006 にする"
  (define wrappers
    (list
     (cons "RegionApp" (lambda (expression _type) expression))
     (cons "Let binding"
           (lambda (expression type)
             `(Let (forwarded let ,type) ,expression forwarded)))
     (cons "Scope"
           (lambda (expression _type) `(Scope () ,expression)))
     (cons "Unsafe"
           (lambda (expression _type) `(Unsafe ,expression)))))
  (for ([entry (in-list wrappers)])
    (check-pending-owner-alias-call
     (lambda (expression type) ((cdr entry) expression type))
     (format "~a wrapper" (car entry)))))

(test-case "UnionInject は保留 summary の payload を境界で E-BOR-006 にする"
  (define union-type `(Union ,borrowed-slot-parameter-type Unit))
  (define core
    `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
       (UnionInject ,union-type ,borrowed-slot-parameter-type writer)))
  (define boundaries '())
  (define-values (_ir _filled result)
    (parameterize
        ([current-callable-summary-boundary-probe
          (lambda (boundary _position _summary)
            (set! boundaries (cons boundary boundaries)))])
      (type-core core borrowed-slot-callables)))
  (check-true (diagnostic? result)
              (format "UnionInject payload を拒否: ~s" result))
  (check-equal? (and (diagnostic? result) (diagnostic-id result)) "E-BOR-006")
  (check-not-false (member 'UnionInject boundaries)
                   "拒否位置は UnionInject の payload 境界"))

(test-case "Curry は保留 summary を固定引数へ移す前に E-BOR-006"
  (check-pending-owner-boundary-rejected
   `(RegionLam (b)
      (Lam User curry-host ()
        (Let (writer let ,borrowed-slot-parameter-type)
             ,borrowed-slot-writer
          (Curry (RegionApp writer ((RParam b))) 0))))
   `((slot-writer ,borrowed-slot-parameter-type)
     (curry-host (ForallRegion (b) (NFn () Unit () () () User))))
   'Curry 'function "Curry summary boundary"))

(test-case "CurryVal は保留 summary を固定引数へ移す前に E-BOR-006"
  (define curried-type
    `(NFn ((BorrowedMut ,(borrowed-slot-owner-type-at '(RParam b))
                         (RParam b))
           Int)
          Unit () (Mutation) () User))
  (define core
    `(RegionLam (b)
      (Lam User curry-val-host (host-borrow)
        (CurryVal User
          (Lam User local-curried-writer (p n)
            (Let (slot-value let (Borrowed Int (RParam b)))
                 (Read (ProjBorrow p slot))
              unit))
          0))))
  (check-pending-owner-boundary-rejected
   core
   `((local-curried-writer ,curried-type)
     (curry-val-host
      (ForallRegion (b)
        (NFn ((Borrowed Int (RParam b))) Unit () () () User))))
   'CurryVal 'function "CurryVal summary boundary"))

(test-case "Forward は保留 summary を move する前に E-BOR-006"
  (check-pending-owner-boundary-rejected
   `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
      (Forward writer))
   borrowed-slot-callables 'Forward 'target "Forward summary boundary"))

(test-case "Lam capture は保留 summary を閉包へ運ぶ前に E-BOR-006"
  (check-pending-owner-boundary-rejected
   `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
      (Lam User captures-writer () writer))
   `((slot-writer ,borrowed-slot-parameter-type)
     (captures-writer (NFn () Unit () () () User)))
   'Lam 'capture "Lam capture summary boundary"))

(test-case "Apply の実引数に保留 summary を渡すと Apply 境界で E-BOR-006"
  (define consumer-type
    `(ForallRegion (b)
       (NFn (,(borrowed-slot-monotype-at '(RParam b)))
            Unit () () () User)))
  (define core
    `(RegionLam (b)
       (Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
         (Apply
          (RegionApp
           (RegionLam (b)
             (Lam User consumes-writer (callback) unit))
           ((RParam b)))
          (RegionApp writer ((RParam b)))))))
  (check-pending-owner-boundary-rejected
   core
   `((slot-writer ,borrowed-slot-parameter-type)
     (consumes-writer ,consumer-type))
   'Apply 1 "Apply argument summary boundary"))

(test-case "Record 欄へ保留 summary を格納すると Rec 境界で E-BOR-006"
  (define record-type
    `(Record ((callback ,borrowed-slot-parameter-type imm))))
  (check-pending-owner-boundary-rejected
   `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
      (Let (callbacks let ,record-type)
           (Rec ((callback imm writer)))
        unit))
   borrowed-slot-callables 'Rec 0 "record field summary boundary"))

(test-case "Construct 欄へ保留 summary を格納すると Construct 境界で E-BOR-006"
  (define option-type `(Option ,borrowed-slot-parameter-type))
  (check-pending-owner-boundary-rejected
   `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
      (Let (callback let ,option-type)
           (Construct ,option-type some writer)
        unit))
   borrowed-slot-callables 'Construct 0 "constructor field summary boundary"))

(test-case "分解の枝から保留 summary を返すと Eliminate 境界で E-BOR-006"
  (check-pending-owner-boundary-rejected
   `(Let (callback let ,borrowed-slot-parameter-type)
       (Eliminate (Construct (Option Int) some 1)
          ((some (number) -> ,borrowed-slot-writer)
           (none () -> ,borrowed-slot-writer)))
      unit)
   borrowed-slot-callables 'EliminateAt 1 "eliminate branch summary boundary"))

(test-case "Handle の Return payload に保留 summary を渡すと Perform 境界で E-BOR-006"
  (define operation `(Return callback-boundary ,borrowed-slot-parameter-type))
  (check-pending-owner-boundary-rejected
   `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
      (Handle ,operation (returned -> returned)
        (Perform ,operation writer)))
   borrowed-slot-callables 'Perform 0 "Handle Return payload summary boundary"))

(test-case "Yield 値に保留 summary を渡すと Yield 境界で E-BOR-006"
  (check-pending-owner-boundary-rejected
   `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
      (Yield writer unit))
   borrowed-slot-callables 'Yield 0 "yield summary boundary"))

(test-case "未知の親形は保留 summary を Suspend 境界で既定拒否する"
  (check-pending-owner-boundary-rejected
   `(Let (writer let ,borrowed-slot-parameter-type) ,borrowed-slot-writer
      (Suspend (RegionApp writer ((RParam a)))))
   borrowed-slot-callables 'Suspend 0 "unknown summary parent defaults closed"))

(test-case "Lam の結果として保留 summary を返すと result 境界で E-BOR-006"
  (define returned-type
    `(ForallRegion (a)
       (NFn ()
            (NFn ((BorrowedMut
                   ,(borrowed-slot-resource-owner-type-at '(RParam a))
                   (RParam a)))
                 Unit () (Mutation) () User)
            () () () User)))
  (define core
    `(RegionLam (a)
       (Lam User returns-pending-writer ()
         (Let (writer let ,borrowed-slot-single-lifetime-parameter-type)
              ,borrowed-slot-single-lifetime-writer
           (RegionApp writer ((RParam a)))))))
  (check-pending-owner-boundary-rejected
   core
   `((single-lifetime-slot-writer
      ,borrowed-slot-single-lifetime-parameter-type)
     (returns-pending-writer ,returned-type))
   'Let 'result "Lam result summary boundary"))

(test-case "Lam の結果が Int なら result 境界の対照として受理する"
  (define return-type
    '(ForallRegion (a) (NFn () Int () () () User)))
  (define core
    `(RegionLam (a)
       (Lam User returns-int ()
         (Let (writer let ,borrowed-slot-single-lifetime-parameter-type)
              ,borrowed-slot-single-lifetime-writer
           1))))
  (define-values (_ir _filled typed)
    (type-core
     core
     `((single-lifetime-slot-writer
        ,borrowed-slot-single-lifetime-parameter-type)
       (returns-int ,return-type))))
  (check-true (region-typed? typed)
              (format "non-pending Lam result is accepted: ~s" typed)))

(test-case "入れ子借用を使わない callee は同じ owner と call-ph で受理する対照"
  (define owner-type
    (borrowed-slot-resource-owner-type-at '(RParam %omitted)))
  (define writer-type
    (borrowed-slot-resource-parameter-type-at 'root 'slot))
  (define unused-writer
    '(RegionLam (root slot)
       (Lam User resource-slot-writer (p) unit)))
  (define callables `((resource-slot-writer ,writer-type)))
  (define core
    `(Scope ()
       (Let (y let (Owned Res)) (resource 20)
         (Let (owner let ,owner-type)
              (Rec ((g mut (Construct (Option (Owned Res)) some
                                     (OwnLeaf (resource 21))))
                    (slot mut (Borrow y))))
           (Apply
            (RegionApp ,unused-writer (call-ph call-ph))
            (BorrowMut owner))))))
  (define-values (_ir _filled typed) (type-core core callables))
  (check-true (region-typed? typed)
              (format "unused nested owner call: ~s" typed)))

(test-case "escape-curry: borrowed parameter を固定する Curry は E-BOR-020"
  (define curry-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)) Int) Int () () () User)))
  (define callables `((borrowed-curry ,curry-type)))
  (check-rejected
   (with-eparent
    (elim-o
     '(Curry
       (RegionApp
        (RegionLam (a)
          (Lam User borrowed-curry (argument more) 0))
        (child-ph))
       c)
     'unit))
   "E-BOR-020" callables "escape-curry"))

(test-case "Curry の固定値が Read c なら受理"
  (define curry-type '(NFn (Int Int) Int () () () User))
  (define callables `((plain-curry ,curry-type)))
  (check-accepted
   (with-eparent
    (elim-o
     '(Apply (Curry (Lam User plain-curry (argument more) argument)
                    (Read c))
             7)
     0))
   'Int callables "escape-curry-control"))

(define param-parent-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,eowner-type (RParam a)))
          Int () (Mutation) () User)))
(define param-parent-callables `((param-parent ,param-parent-type)))
(define (param-parent-call body)
  `(Apply
    (RegionApp
     (RegionLam (a) (Lam User param-parent (p) ,body))
     (owner-ph))
    p))

(define (check-param-parent-escape core label)
  (define-values (_ir result records)
    (observe-decomposition-extents core param-parent-callables))
  (check-true (diagnostic? result)
              (format "~a: E-BOR-025 を期待したが ~s" label result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-025" label))
  (check-true (pair? records)
              (format "~a: 分解の binder extent を観測する" label))
  (check-true
   (and (pair? records)
        (andmap (lambda (record) (not (fourth record))) records))
   (format "~a: escape を含む分解では extent が付かない: ~s"
           label records))
  (check-true
   (andmap
    (lambda (record)
      (for/and ([event (in-list (fifth record))])
        (and (deferred-leaf-exit? event)
             (not (eq? (deferred-leaf-exit-exit-kind event) 'local)))))
    records)
   (format "~a: binder event がある場合も local の根拠にしない: ~s"
           label records))
  (check-true
   (andmap
    (lambda (record)
      (match (sixth record)
        [(list root? frame-complete? events-nonempty? local-safe? alpha
               alpha-origins result-alphas result-origin-alphas
               forbidden-alphas overlap)
         (and root? frame-complete?
              (eq? events-nonempty? (pair? (fifth record)))
              (boolean? local-safe?)
              (set-member? forbidden-alphas alpha)
              (set-empty?
               (set-subtract alpha-origins forbidden-alphas))
              (equal? overlap
                      (set-intersect result-origin-alphas
                                     forbidden-alphas))
              (set-member? overlap alpha)
              (not (set-empty? overlap)))]
        [_ #f]))
    records)
   (format "~a: 型の寿命と binder 起源の交差で extent を拒否する: ~s"
           label records)))

(test-case "param-parent: 逃げない枝の後の formal parent 書込みは受理"
  (check-accepted
   (with-eparent
     (param-parent-call
     (then/as 'Int (elim-o '(Read c) 0)
              (then `(Assign p ,eowner-value) 1))))
   'Int param-parent-callables "param-parent-nonescape"))

(test-case "param-parent: binder から射影した子を枝内で読み切ると親へ書ける"
  (check-accepted
   (with-eparent
    (param-parent-call
     (then/as 'Int
              (elim-ro '(Read (ProjBorrow c h)) 0)
              (then `(Assign p ,eowner-value) 1))))
   'Int param-parent-callables "param-parent-projected-child-nonescape"))

(test-case "param-parent: formal projection の子を結果へ逃がす形は E-BOR-025"
  (check-rejected
   (with-eparent
    (param-parent-call
     `(Let (escaped let (BorrowedMut Int (RParam a)))
           ,(elim-o 'c '(ProjBorrow p g))
       (Let (written let Unit) (Assign p ,eowner-value)
         (Read escaped)))))
   "E-BOR-025" param-parent-callables "param-parent-escape"))

(test-case "param-parent: 枝 Scope の結果へ子を逃がすと E-BOR-025"
  (check-param-parent-escape
   (with-eparent
    (param-parent-call
     `(Let (escaped let (BorrowedMut Int (RParam a)))
           ,(elim-ro '(Scope () (ProjBorrow c h))
                     '(Scope () (ProjBorrow p g)))
       (Let (written let Unit) (Assign p ,eowner-value)
         (Read escaped)))))
   "param-parent-scope-escape"))

(test-case "param-parent: 分解の子を record に格納して親へ書くと E-BOR-025"
  (define escaped-record
    '(Record ((payload (BorrowedMut Int (RParam %omitted)) imm))))
  (check-param-parent-escape
   (with-eparent
    (param-parent-call
     `(Let (escaped let ,escaped-record)
           ,(elim-ro '(Rec ((payload imm (ProjBorrow c h))))
                     '(Rec ((payload imm (ProjBorrow p g)))))
       (Let (written let Unit) (Assign p ,eowner-value)
         (Read (Proj escaped payload))))))
   "param-parent-record-escape"))

(test-case "escape-apply: identity の結果を分解の外へ出すと E-BOR-025"
  (define identity-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a)))
            (Borrowed Int (RParam a)) () () () User)))
  (define callables `((identity ,identity-type)))
  (define identity-call
    '(Apply
      (RegionApp
       (RegionLam (a) (Lam User identity (argument) argument))
       (child-ph))
      c))
  (for ([write (in-list (list shared-parent-write shared-sibling-write))]
        [label (in-list '("parent" "sibling"))])
    (check-rejected
     (with-shared-view-parent
      `(Let (escaped let (Borrowed Int child-ph))
            ,(elim-i identity-call '(Reborrow (ProjBorrow p g)))
         ,(then write 'unit)))
     "E-BOR-025" callables (format "escape-apply-~a" label))))

(test-case "escape-apply: sink 後の兄弟欄更新は受理し oracle も通る"
  (define sink-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) Int () () () User)))
  (define callables `((sink ,sink-type)))
  (define sink-call
    '(Apply
      (RegionApp
       (RegionLam (a)
         (Lam User sink (argument) 0))
       (child-ph))
      c))
  (check-accepted
   (with-shared-view-parent
    `(Let (result let Int) ,(elim-i sink-call 0)
       ,(then shared-sibling-write 'unit)))
   'Unit callables "escape-apply-sink-sibling"))

(test-case "apply-arg-over-reject: sink 実引数の後の親全体 Assign は E-BOR-025"
  (define sink-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) Int () () () User)))
  (define callables `((sink ,sink-type)))
  (define sink-call
    '(Apply
      (RegionApp
       (RegionLam (a)
         (Lam User sink (argument) 0))
       (child-ph))
      c))
  (check-rejected
   (with-shared-view-parent
    `(Let (result let Int) ,(elim-i sink-call 0)
       ,(then shared-parent-write 'unit)))
   "E-BOR-025" callables "apply-arg-over-reject"))

(test-case "可変の分解 binder の Reborrow を BorrowedMut 仮引数へ渡して読み切る形は受理する"
  (define reader-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))
  (define callables `((reader ,reader-type)))
  (define reader-call
    '(Apply
      (RegionApp
       (RegionLam (a)
         (Lam User reader (argument) (Read argument)))
       (child-ph))
      c))
  (check-accepted
   `(RegionLam (a) ,(with-eparent (elim-o reader-call 0)))
   '(ForallRegion (a) Int) callables "escape-apply-mut-argument"))

(test-case "可変の分解 binder の Reborrow を Borrowed 仮引数へ渡して読み切る形は受理する"
  (define reader-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) Int () () () User)))
  (define callables `((reader ,reader-type)))
  (define reader-call
    '(Apply
      (RegionApp
       (RegionLam (a)
         (Lam User reader (argument) (Read argument)))
       (child-ph))
      (Reborrow c)))
  (check-accepted
   `(RegionLam (a) ,(with-eparent (elim-o reader-call 0)))
   '(ForallRegion (a) Int) callables "escape-apply-reborrow-argument"))

(test-case "Apply の無い局所 owner binder Reborrow を読み切る形は受理する"
  (check-accepted
   `(RegionLam (a)
      ,(with-eparent
        (elim-o
         '(Let (d let (Borrowed Int child-ph)) (Reborrow c)
            (Let (ignored let Int) (Read d) unit))
         'unit)))
   '(ForallRegion (a) Unit) '() "escape-apply-reborrow-without-apply"))

(test-case "RegionLam 本体で親子の借用を作っても子が生きている間の親 Assign は拒否する"
  (check-rejected
   `(RegionLam (a)
      ,(with-eparent
        (elim-o
         '(Let (d let (Borrowed Int child-ph)) (Reborrow c)
            (Let (written let Unit)
                 (Assign (ProjBorrow p o) (Construct (Option Int) none))
              (Read d)))
         'unit)))
   "E-BOR-025" '() "regionlam-parent-write-while-child-live"))

(test-case "RegionLam を局所 Scope の region に具体化して Apply する対照は受理する"
  (check-accepted
   (with-eparent
    (param-parent-call (elim-o '(Read c) 0)))
   'Int param-parent-callables "regionlam-regionapp-local-scope-apply"))

(test-case "分解 binder が BorrowedMut 仮引数の結果へ届き親 Assign 中も生存すると E-BOR-025"
  (define identity-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () () () User)))
  (define call
    '(Apply
      (RegionApp
       (RegionLam (a)
         (Lam User borrow-identity (argument) argument))
       (child-ph))
      c))
  (define core
    `(RegionLam (a)
       ,(with-eparent
         `(EliminateAt (ProjBorrow p o)
            ((some (c) (%parent) ->
               (Let (escaped let (BorrowedMut Int child-ph)) ,call
                 (Let (written let Unit)
                      (Assign (ProjBorrow p o) (Construct (Option Int) none))
                   (Let (observed let (BorrowedMut Int child-ph))
                        (Read escaped)
                     unit))))
             (none () () -> unit))))))
  (check-rejected
   core
   "E-BOR-025"
   `((borrow-identity ,identity-type))
   "escape-apply-mut-argument-result"))

(test-case "RegionLam の RegionApp を局所 Scope で呼び、Apply 前後に親を Read できる"
  (define body (elim-o '(Read c) 0))
  (define (call-with-argument argument)
    `(Apply
      (RegionApp
       (RegionLam (a) (Lam User param-parent (p) ,body))
       (owner-ph))
      ,argument))
  (define before-read
    (with-eparent
     `(Let (called let Int)
        ,(call-with-argument
          '(Let (observed let Int) (Read (ProjBorrow p g)) p))
        (Read (ProjBorrow p g)))))
  (define after-read
    (with-eparent
     `(Let (called let Int)
        ,(call-with-argument 'p)
        (Read (ProjBorrow p g)))))
  (for ([core (in-list (list before-read after-read))]
        [label (in-list '("apply-argument-read" "let-body-read"))])
    (check-accepted core 'Int param-parent-callables label)))

(test-case "formal parent の可変 binder は新しい alpha を作る"
  (define core
    (with-eparent
     (param-parent-call (elim-o '(Read c) 0))))
  (define-values (ir _filled typed) (type-core core param-parent-callables))
  (check-true (region-typed? typed) (format "formal-parent binder: 型検査 ~s" typed))
  (when (region-typed? typed)
    (check-equal? (region-typed-type typed) 'Int)
    (define alphas (hash-values (region-typed-binder-alphas typed)))
    (check-equal? (length alphas) 1
                  "formal parent でも binder alpha を一つ生成する")
    (check-true (pair? alphas)
                "raw RVar の検査が空集合への andmap で通らない")
    (check-true (andmap lifetime-var? alphas)
                "型付け結果には descriptor でなく raw RVar を保持する")
    (match typed
      [(region-typed _ _ _ _ _ _ _ _ _ alpha-table parent-keys)
       (check-equal? parent-keys (list->set (hash-keys alpha-table))
                     "formal-parent の鍵は alpha と分けて保持する")])
    (define (has-parent-binder-region? term)
      (match term
        [`(EliminateAt ,_ (,branches ...))
         (or (for/or ([branch (in-list branches)])
               (match branch
                 [`(some (c) (,region) -> ,_)
                  (equal? region '%parent)]
                 [_ #f]))
             (ormap has-parent-binder-region? branches))]
        [(? pair? parts)
         (or (has-parent-binder-region? (car parts))
             (has-parent-binder-region? (cdr parts)))]
        [_ #f]))
    (check-true (has-parent-binder-region? (region-execution-core typed))
                "materialize 後も formal parent の枝注釈は %parent のまま")
    (check-runtime typed ir param-parent-callables 'Int "formal-parent-binder")))

(test-case "枝内で独立に作った借用は枝の後で同じ欄を書ける"
  (check-accepted
   (with-eparent
    (then
     (elim-o
      `(Let (r let ,borrowed-mut-int) (ProjBorrow p g)
         (Assign r 2))
      'unit)
     '(Assign (ProjBorrow p g) 3)))
   'Unit '() "branch-born-borrow"))

(test-case "infer-eliminate は可変 binder に別 alpha を一度だけ作る"
  (define body
    `(Let (r let ,borrowed-mut-int)
          (ProjBorrow c h)
       (Assign r 3)))
  (check-binder-alpha (with-eparent (elim-ro body 'unit))
   "binder-alpha/infer"))

(test-case "check-eliminate は可変 binder に別 alpha を一度だけ作る"
  (define body
    `(Let (r let ,borrowed-mut-int)
          (ProjBorrow c h)
       (Assign r 3)))
  (check-binder-alpha (with-eparent `(Let (checked Unit)
                                           ,(elim-ro body 'unit)
                                         unit))
   "binder-alpha/check"))

(test-case "可変の分解 binder を Record に包んだ実引数は E-TYP-023"
  (define record-reader-type
    '(ForallRegion (a)
       (NFn ((Record ((payload (BorrowedMut Int (RParam a)) imm))))
            Int () () () User)))
  (define callables `((reader ,record-reader-type)))
  (define reader-call
    '(Apply
      (RegionApp
       (RegionLam (a)
         (Lam User reader (argument) 0))
       (child-ph))
      (Rec ((payload imm c)))))
  (check-rejected
   `(RegionLam (a) ,(with-eparent (elim-o reader-call 0)))
   "E-TYP-023" callables "escape-apply-record-argument"))

(define result-int-string '(Result Int String))
(define data-reader-type
  '(ForallRegion (a)
     (NFn ((BorrowedMut (Result Int String) (RParam a)))
          Unit () () () User)))
(define data-reader-callables `((data-reader ,data-reader-type)))
(define data-sibling-read-apply-core
  `(Scope ()
     (Let (owner let (Owned ,result-int-string))
          (Construct ,result-int-string ok 1)
       (Let (argument let (BorrowedMut ,result-int-string (RParam %omitted)))
            (BorrowMut owner)
         (Let (called const Unit)
              (Apply
               (RegionApp
                (RegionLam (a)
                  (Lam User data-reader (p)
                    (Eliminate p
                      ((ok (payload)
                           -> (Let (read-value const Int) (Read payload) unit))
                       (ng (message)
                           -> (Let (read-message const String)
                                    (Read message)
                                  unit))))))
                (owner-ph))
               argument)
           (Assign argument (Construct ,result-int-string ok 2)))))))

(define union-reader-type
  '(ForallRegion (a)
     (NFn ((BorrowedMut (Union Int String) (RParam a)))
          Unit () () () User)))
(define union-reader-callables `((union-reader ,union-reader-type)))
(define union-sibling-read-apply-core
  '(Scope ()
     (Let (owner let (Owned (Union Int String)))
          (UnionInject (Union Int String) Int 1)
       (Let (argument let (BorrowedMut (Union Int String) (RParam %omitted)))
            (BorrowMut owner)
         (Let (called const Unit)
              (Apply
               (RegionApp
                (RegionLam (a)
                  (Lam User union-reader (p)
                    (UnionEliminate p
                      ((Int payload
                            -> (Let (read-value const Int)
                                    (Read payload)
                                  unit))
                       (String message
                               -> (Let (read-message const String)
                                        (Read message)
                                      unit))))))
                (owner-ph))
               argument)
           (Assign argument
                   (UnionInject (Union Int String) Int 2)))))))

(define child-sibling-record-type '(Record ((h Int mut))))
(define child-sibling-sum-type
  `(Result ,child-sibling-record-type ,child-sibling-record-type))
(define child-sibling-owner-type
  `(Record ((choice ,child-sibling-sum-type mut))))
(define child-sibling-owner-value
  `(Rec ((choice mut
          (Construct ,child-sibling-sum-type ok
                     (Rec ((h mut 1))))))))
(define child-sibling-reader-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,child-sibling-owner-type (RParam a)))
          Unit () (Mutation) () User)))
(define child-sibling-reader-callables
  `((child-sibling-reader ,child-sibling-reader-type)))
(define child-sibling-body
  `(Eliminate (ProjBorrow p choice)
     ((ok (c) ->
       (Let (child let (BorrowedMut Int (RParam %omitted)))
            (ProjBorrow c h)
         (Assign child 2)))
      (ng (c) ->
       (Let (child let (BorrowedMut Int (RParam %omitted)))
            (ProjBorrow c h)
         (Assign child 3))))))
(define child-sibling-apply-core
  `(Scope ()
     (Let (owner let (Owned ,child-sibling-owner-type))
          ,child-sibling-owner-value
       (Let (argument let
                       (BorrowedMut ,child-sibling-owner-type
                                    (RParam %omitted)))
            (BorrowMut owner)
         (Let (called const Unit)
              (Apply
               (RegionApp
                (RegionLam (a)
                  (Lam User child-sibling-reader (p) ,child-sibling-body))
                (owner-ph))
               argument)
           (Assign argument ,child-sibling-owner-value))))))

(define union-int-unit '(Union Int Unit))
(define union-payload-owner-type
  `(Record ((u ,union-int-unit mut))))
(define union-payload-owner-value
  `(Rec ((u mut (UnionInject ,union-int-unit Int 1)))))
(define union-payload-leaker-type
  `(ForallRegion (a)
     (NFn ((Borrowed ,union-int-unit (RParam a)))
          (Borrowed Int (RParam a)) () ((Return dead Int)) () User)))
(define union-payload-leaker-callables
  `((union-payload-leaker ,union-payload-leaker-type)))
(define union-mut-payload-leaker-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,union-int-unit (RParam a)))
          (BorrowedMut Int (RParam a)) () ((Return dead Int)) () User)))
(define union-mut-payload-leaker-callables
  `((union-mut-payload-leaker ,union-mut-payload-leaker-type)))
(define union-payload-leaker-body
  `(Let (escaped let (Borrowed Int (RParam %omitted)))
          (Apply
           (RegionApp
            (RegionLam (a)
              (Lam User union-payload-leaker (argument)
                (UnionEliminate argument
                  ((Int payload -> payload)
                   (Unit ignored -> (Perform (Return dead Int) 0))))))
            (owner-ph))
           (Reborrow (ProjBorrow p u)))
       (Let (written let Unit)
            (Assign (ProjBorrow p u)
                    (UnionInject ,union-int-unit Int 2))
         (Read escaped))))
(define union-payload-leaker-core
  `(Scope ()
     (Let (owner let (Owned ,union-payload-owner-type))
          ,union-payload-owner-value
       (Let (p let (BorrowedMut ,union-payload-owner-type (RParam %omitted)))
            (BorrowMut owner)
         ,union-payload-leaker-body))))
(define union-mut-payload-leaker-core
  `(Scope ()
     (Let (owner let (Owned ,union-payload-owner-type))
          ,union-payload-owner-value
       (Let (p let (BorrowedMut ,union-payload-owner-type (RParam %omitted)))
            (BorrowMut owner)
         (Let (escaped let (BorrowedMut Int (RParam %omitted)))
              (Apply
               (RegionApp
                (RegionLam (a)
                  (Lam User union-mut-payload-leaker (argument)
                    (UnionEliminate argument
                      ((Int payload -> payload)
                       (Unit ignored -> (Perform (Return dead Int) 0))))))
                (owner-ph))
               (ProjBorrow p u))
           (Let (written let Unit)
                (Assign (ProjBorrow p u)
                        (UnionInject ,union-int-unit Int 2))
             (Read escaped)))))))

(define binder-child-result-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,eowner-type (RParam a)))
          (BorrowedMut Int (RParam a)) () () () User)))
(define binder-child-result-callables
  `((binder-child-result ,binder-child-result-type)))
(define binder-child-result-body
  '(Eliminate (ProjBorrow p ro)
     ((some (c) -> (ProjBorrow c h))
      (none () -> (ProjBorrow p g)))))
(define binder-child-result-core
  `(Scope (1)
     (RegionLam (a)
       (Lam User binder-child-result (p) ,binder-child-result-body))))
(define binder-child-result-call
  `(Apply
    (RegionApp
     (RegionLam (a)
       (Lam User binder-child-result (p) ,binder-child-result-body))
     (owner-ph))
    p))
(define binder-child-result-escape-core
  (with-eparent
   `(Let (escaped let (BorrowedMut Int (RParam %omitted)))
         ,binder-child-result-call
     (Let (written let Unit) (Assign p ,eowner-value)
       (Read escaped)))))

(define binder-child-aggregate-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,eowner-type (RParam a)))
          (Record ((field (BorrowedMut Int (RParam a)) imm)))
          () () () User)))
(define binder-child-aggregate-callables
  `((binder-child-aggregate ,binder-child-aggregate-type)))
(define binder-child-aggregate-body
  '(Eliminate (ProjBorrow p ro)
     ((some (c) -> (Rec ((field imm (ProjBorrow c h)))))
      (none () -> (Rec ((field imm (ProjBorrow p g))))))))
(define binder-child-aggregate-core
  (with-eparent
   `(Apply
     (RegionApp
      (RegionLam (a)
        (Lam User binder-child-aggregate (p) ,binder-child-aggregate-body))
      (owner-ph))
     p)))

(define binder-child-capture-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,eowner-type (RParam a)))
          (NFn () (BorrowedMut Int (RParam a)) () () () User)
          () () () User)))
(define binder-child-capture-callables
  `((binder-child-capture ,binder-child-capture-type)
    (captured-child (NFn () (BorrowedMut Int (RParam a)) () () () User))))
(define binder-child-capture-body
  '(Eliminate (ProjBorrow p ro)
     ((some (c) -> (Lam User captured-child () (ProjBorrow c h)))
      (none () -> (Lam User captured-child () (ProjBorrow p g))))))
(define binder-child-capture-core
  (with-eparent
   `(Apply
     (RegionApp
      (RegionLam (a)
        (Lam User binder-child-capture (p) ,binder-child-capture-body))
      (owner-ph))
     p)))

(test-case "Data の局所枝要求は Apply 後に親の使用を許す"
  (check-accepted-window-points data-sibling-read-apply-core 'Unit
                                data-reader-callables "data-sibling-read-apply"
                                '((0 1 1 0 2 1) (0 1 1 0 2 2))))

(test-case "Union の局所枝要求は Apply 後に親の使用を許す"
  (check-accepted-window-points union-sibling-read-apply-core 'Unit
                                union-reader-callables "union-sibling-read-apply"
                                '((0 1 1 0 2 1) (0 1 1 0 2 2))))

(test-case "兄弟枝の binder から射影した子を使い切れば Apply 後に親を書ける"
  (check-accepted-window-points child-sibling-apply-core 'Unit
                                child-sibling-reader-callables
                                "binder-projected-child-apply"
                                '((0 1 1 0 2)
                                  (0 1 1 0 2 1) (0 1 1 0 2 2))))

(test-case "derived scrutinee の binder 無し分解は候補無しでも要約できる"
  (define flag-owner-type '(Record ((flag Bool mut))))
  (define signature
    `(ForallRegion (a)
       (NFn ((BorrowedMut ,flag-owner-type (RParam a)))
            Unit () () () User)))
  (define callables `((nullary-decomposition ,signature)))
  (define core
    '(RegionLam (a)
       (Lam User nullary-decomposition (p)
         (Eliminate (ProjBorrow p flag)
           ((true () -> unit)
            (false () -> unit))))))
  (define-values (_ir _filled result) (type-core core callables))
  (check-true (region-typed? result)
              (format "全枝が binder 無しでも derived scrutinee を処理: ~s"
                      result)))

(test-case "同じ枝の二つの mut 要求は Apply 後も E-BOR-003"
  (define body
    (elim-ro
     `(Let (x let (BorrowedMut Int (RParam %omitted))) (ProjBorrow c h)
        (Let (y let (BorrowedMut Int (RParam %omitted))) (ProjBorrow c h)
          (Let (write-x let Unit) (Assign x 2)
            (Let (write-y let Unit) (Assign y 3) 1))))
     0))
  (define core (with-eparent (param-parent-call body)))
  (define pairs
    (check-rejected-conflict-pair
     core "E-BOR-003" param-parent-callables "same-branch-mut-requests"))
  (check-not-false (pair? pairs))
  (when (pair? pairs)
    (check-equal? (map borrow-request-point (first pairs))
                  '((0 1 1 2 1 0) (0 1 1 2 1 1 0))
                  (format "拒否対は同じ枝で作った x/y の要求である: ~s"
                          (map (lambda (request)
                                 (list (borrow-request-point request)
                                       (borrow-request-node request)
                                       (borrow-request-fp request)
                                       (borrow-request-alpha request)))
                               (first pairs)))))
)

(test-case "Recur 固定点を通って次反復まで生きる枝 loan は E-BOR-003"
  (define recursive-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut ,eowner-type (RParam a)))
            Int () (Mutation) () User)))
  (define callables `((outer-recursive-window ,recursive-type)
                      (inner-recursive-window ,recursive-type)))
  (define recursive-body
    '(Eliminate (ProjBorrow q ro)
       ((some (inner-c) ->
          (Let (inner-child let (BorrowedMut Int (RParam %omitted)))
               (ProjBorrow inner-c h)
            (Let (recursive-step let Int) (Apply f q)
              (Let (write-inner let Unit) (Assign inner-child 2) 1))))
        (none () -> 0))))
  (define core
    (with-eparent
     `(Apply
       (RegionApp
        (RegionLam (a)
          (Lam User outer-recursive-window (p)
            (Eliminate (ProjBorrow p ro)
              ((some (outer-c) ->
                 (Let (outer-child let (BorrowedMut Int (RParam %omitted)))
                      (ProjBorrow outer-c h)
                   (Recur inner-recursive-window f (q)
                     ,recursive-body
                     (Let (inner-result let Int)
                          (Apply (RegionApp f ((RParam a))) p)
                       (Let (write-outer let Unit)
                            (Assign outer-child 1)
                         1)))))
               (none () -> 0)))))
        (owner-ph))
       p)))
  (define observations '())
  (define conflict-pairs '())
  (define-values (_ir _filled result)
    (parameterize
        ([current-local-exit-window-probe
          (lambda (_cap _index _alpha _origins _source-alphas window event)
            (when (and window (deferred-leaf-exit? event)
                       (match (deferred-leaf-exit-source event)
                         [`(binder ,_ ...) #t]
                         [_ #f]))
              (set! observations
                    (cons (list (deferred-leaf-exit-source event) window)
                          observations))))]
         [current-borrow-conflict-probe
          (lambda (left right)
            (set! conflict-pairs (cons (list left right) conflict-pairs)))])
      (type-core core callables)))
  (check-true (diagnostic? result)
              (format "再帰 Apply 中の局所要求が重なる: ~s" result))
  (check-equal? (and (diagnostic? result) (diagnostic-id result)) "E-BOR-003")
  (check-true (>= (set-count (list->set (map second observations))) 2)
              (format "再帰 activation ごとに枝 extent root が異なる: ~s"
                      observations))
  (check-true (pair? conflict-pairs)
              "Recur をまたぐ alias 拒否の対を観測する")
  (when (pair? conflict-pairs)
    (check-equal? (map borrow-request-point (first conflict-pairs))
                  '((0 1 1 2 1) (0 1 1 2 1 1 1 0 2 0))
                  (format "拒否対は現行と次の Recur activation の枝要求である: ~s"
                          (map (lambda (request)
                                 (list (borrow-request-point request)
                                       (borrow-request-node request)
                                       (borrow-request-fp request)
                                       (borrow-request-alpha request)))
                               (first conflict-pairs)))))
)

(test-case "同じ owner への二本の BorrowMut 実引数は作成時に拒否する"
  (define signature
    '(NFn ((BorrowedMut Int (RParam a)) (BorrowedMut Int (RParam b)))
         Unit () () () User))
  (define callables `((two-mut ,signature)))
  (check-rejected
   '(Scope ()
      (Let (owner let (Owned Int)) 1
        (Apply
         (RegionApp
          (RegionLam (a b)
            (Lam User two-mut (left right) unit))
          (owner-ph owner-ph))
         (BorrowMut owner) (BorrowMut owner))))
   "E-BOR-003" callables "same-owner-two-mut-arguments"))

;; caller は既存の p capability を二仮引数へ渡すので、二本の BorrowMut を
;; 引数評価で作らない。拒否対の point が callee 内の左右 ProjBorrowAt と示す。
(test-case "異なる仮引数の同じ枝から同じ欄への mut 要求は拒否する"
  (define signature
    `(ForallRegion (a b)
       (NFn ((BorrowedMut ,eowner-type (RParam a))
             (BorrowedMut ,eowner-type (RParam b)))
            Unit () (Mutation) () User)))
  (define callables `((two-formal-mut ,signature)))
  (define body
    '(Eliminate (ProjBorrow left ro)
       ((some (left-child) ->
          (Eliminate (ProjBorrow right ro)
            ((some (right-child) ->
               (Let (x let (BorrowedMut Int (RParam %omitted)))
                    (ProjBorrow left-child h)
                 (Let (y let (BorrowedMut Int (RParam %omitted)))
                      (ProjBorrow right-child h)
                   (Let (write-x let Unit) (Assign x 1)
                     (Let (write-y let Unit) (Assign y 2) unit)))))
             (none () -> unit))))
        (none () -> unit))))
  (define pairs
    (check-rejected-conflict-pair
     (with-eparent
      `(Apply
        (RegionApp
         (RegionLam (a b)
           (Lam User two-formal-mut (left right) ,body))
         (owner-ph owner-ph))
        p p))
     "E-BOR-003" callables "same-owner-across-formal-indices"))
  (check-equal? (length pairs) 1)
  (when (= (length pairs) 1)
    (define pair (first pairs))
    (check-equal? (map borrow-request-point pair)
                  '((0 1 1 3 1) (0 1 1 3 1 1))
                  "拒否対は caller の引数作成ではなく callee の枝内にある")
    (check-true
     (andmap (lambda (request)
               (and (eq? (borrow-request-mode request) 'mut)
                    (equal? (borrow-request-w request) 'x)
                    (equal? (borrow-request-fp request) '(ro))))
             pair)
     (format "二つの仮引数から来る同じ owner 欄への枝要求: ~s"
             (map (lambda (request)
                    (list (borrow-request-w request)
                          (borrow-request-fp request)
                          (borrow-request-node request)))
                  pair)))
    (check-true
     (match (borrow-request-node (first pair))
       [`(ProjBorrowAt ,_ left ro) #t]
       [_ #f]))
    (check-true
     (match (borrow-request-node (second pair))
       [`(ProjBorrowAt ,_ right ro) #t]
       [_ #f]))))

(test-case "Union payload の子を結果へ逃がすと親 Assign は E-BOR-025"
  (check-rejected union-payload-leaker-core "E-BOR-025"
                  union-payload-leaker-callables "union-payload-escape-result")
  (define-values (_typed windows)
    (observe-local-exit-windows union-payload-leaker-core
                                union-payload-leaker-callables))
  (check-equal? windows '()
                "共有の Union payload には局所 extent の候補が無い"))

(test-case "mut Union payload の結果出口には extent を付けない"
  (define-values (_ir result records)
    (observe-decomposition-extents union-mut-payload-leaker-core
                                   union-mut-payload-leaker-callables))
  (check-true (diagnostic? result)
              "mut payload escape の兄弟要求は現行どおり拒否する")
  (check-not-false (member #f (map fourth records))
                   "結果へ逃げる mut Union payload の extent は #f"))

(test-case "binder から射影した子が結果へ逃げると extent 窓を付けず拒否する"
  (define observations '())
  (define-values (_ir _filled result)
    (parameterize
        ([current-local-exit-window-probe
          (lambda args (set! observations (cons args observations)))])
      (type-core binder-child-result-escape-core
                 binder-child-result-callables)))
  (check-true (diagnostic? result)
              (format "親の更新は E-BOR-025: ~s" result))
  (check-equal? (and (diagnostic? result) (diagnostic-id result))
                "E-BOR-025")
  (check-true
   (for/or ([observation (in-list observations)])
     (define event (list-ref observation 6))
     (and (deferred-leaf-exit? event)
          (eq? (deferred-leaf-exit-exit-kind event) 'result)
          (not (list-ref observation 5))))
   (format "結果へ逃げる binder の子要求に窓を付けない: ~s" observations)))

(test-case "binder の子を集約値へ格納すると extent 窓を付けない"
  (define-values (_ir result records)
    (observe-decomposition-extents binder-child-aggregate-core
                                   binder-child-aggregate-callables))
  (check-true (region-typed? result)
              (format "集約結果に binder alpha の借用が残る: ~s" result))
  (check-true
   (match (region-typed-type result)
     [`(Record ((field (BorrowedMut Int ,_) imm))) #t]
     [_ #f])
   (format "集約の結果型に child borrow が残る: ~s"
           (and (region-typed? result) (region-typed-type result))))
  (check-true (and (pair? records)
                   (andmap (lambda (record) (not (fourth record))) records))
              (format "集約値へ逃げる binder extent: ~s" records)))

(test-case "borrowed function capture は extent の実体化前に拒否する"
  (define-values (_ir result records)
    (observe-decomposition-extents binder-child-capture-core
                                   binder-child-capture-callables))
  (check-true (diagnostic? result) (format "capture の診断: ~s" result))
  (check-equal? (and (diagnostic? result) (diagnostic-id result)) "E-BOR-011")
  (check-equal? records '()
                "check-function-boundary が capture を先に拒否し、extent summary は作らない"))

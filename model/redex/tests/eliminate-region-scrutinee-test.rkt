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
         "../region.rkt"
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

(define (type-core core [callables '()])
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
  (define filled
    (let walk ([value (fill-region-placeholders (erase-core core) ir)])
      (cond [(eq? value 'owner-ph) owner-rho]
            [(eq? value 'child-ph) child-rho]
            [(pair? value) (cons (walk (car value)) (walk (cdr value)))]
            [else value])))
  (values ir filled (core-type-of/regions filled '() callables #:ir ir)))

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

(define (check-accepted core expected [callables '()] [label "fixture"])
  (define-values (ir _filled typed) (type-core core callables))
  (check-true (region-typed? typed) (format "~a: 型検査 ~s" label typed))
  (when (region-typed? typed)
    (check-equal? (region-typed-type typed) expected)
    (check-runtime typed ir callables expected label)))

(define (check-rejected core expected-id [callables '()] [label "fixture"])
  (define-values (_ir _filled result) (type-core core callables))
  (check-true (diagnostic? result)
              (format "~a: 診断を期待したが ~s" label result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id
                  (format "~a: 診断 id" label))))

(define (find-core-point core predicate)
  (let walk ([node (erase-core core)] [point '()])
    (if (predicate node)
        point
        (for/or ([child (in-list (core-children node))]
                 [index (in-naturals)])
          (walk child (append point (list index)))))))

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

(test-case "枝内 Scope の結果が運ぶ scrutinee 子は分解 region まで生きる"
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
    (define outer-point
      (find-core-point
       core
       (lambda (node)
         (match node [`(Eliminate (ProjBorrow p ro) ,_) #t] [_ #f]))))
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
       (region-at/eliminate ir outer-point)))))

(test-case "内側結果を外側の結果へも逃がすと E-BOR-025"
  (check-rejected
   (with-eparent
    `(Let (escaped let (BorrowedMut Int (RParam %omitted)))
          ,(elim-ro (elim-o 'c '(ProjBorrow p g)) '(ProjBorrow p g))
       ,(then write-o '(Read escaped))))
   "E-BOR-025" '() "escape-nested"))

(test-case "兄弟の枝で同じ欄を直接借りる HEAD の E-BOR-003 を維持"
  (check-rejected
   (with-eparent
    `(Eliminate (Construct Bool true)
       ((true () ->
          (Let (r let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
            (Assign r 1)))
        (false () ->
          (Let (r2 let (BorrowedMut Int (RParam %omitted))) (ProjBorrow p g)
            (Assign r2 2))))))
   "E-BOR-003" '() "sibling-borrow"))

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

(test-case "枝の別欄借用は通常の Scope 下限を保ち、親欄へ書ける"
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
       (region-at ir point)
       "非子の借用の下限は分解を含まない通常の region-at"))))

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

(test-case "可変の分解 binder を BorrowedMut の仮引数へ渡すと E-BOR-003"
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
  (check-rejected
   `(RegionLam (a) ,(with-eparent (elim-o reader-call 0)))
   "E-BOR-003" callables "escape-apply-mut-argument"))

(test-case "可変の分解 binder の Reborrow を Borrowed 仮引数へ渡すと E-BOR-003"
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
  (check-rejected
   `(RegionLam (a) ,(with-eparent (elim-o reader-call 0)))
   "E-BOR-003" callables "escape-apply-reborrow-argument"))

(test-case "Apply の無い binder Reborrow を読み出しても E-BOR-003"
  (check-rejected
   `(RegionLam (a)
      ,(with-eparent
        (elim-o
         '(Let (d let (Borrowed Int child-ph)) (Reborrow c)
            (Let (ignored let Int) (Read d) unit))
         'unit)))
   "E-BOR-003" '() "escape-apply-reborrow-without-apply"))

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

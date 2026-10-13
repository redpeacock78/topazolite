#lang racket

(require rackunit
         redex/reduction-semantics
         racket/match
         racket/set
         "../borrow.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../region.rkt"
         "../machine.rkt"
         "../borrow-oracle.rkt"
         "../borrow-gen.rkt"
         "../region-param.rkt"
         "../typing.rkt")

(define int-heap '((0 7 (declared Int))))
(define int-states '((0 Available)))

(define (config-type-result cfg callables)
  (match cfg
    [`(cfg ,core ,heap ,states ,_tokens ,_trace)
     (define places
       (derive-places heap callables #:declared (config-declared-types cfg)))
     (define borrow-types
       (and places (recover-runtime-borrow-types core heap states places)))
     (and borrow-types
          (parameterize ([config-runtime-borrow-types borrow-types])
            (with-config-typing
             (lambda () (type-of/raw core places callables)))))]
    [_ #f]))

(define (config-type-failure-key cfg [callables '()])
  (match (config-type-result cfg callables)
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

(define (raw-failure-key core places)
  (match (type-of/raw core places '())
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

(test-case "構成検査は BorrowAt の注釈を寿命として型へ置く"
  (define core '(Read (BorrowAt 3 (Own 0 ()) 0)))
  (define cfg `(cfg ,core ,int-heap ,int-states () ()))
  (check-true (config-ok? cfg '() 'Int '()))
  (check-equal? (raw-failure-key core '((0 Int))) 'borrow-region-mismatch))

(test-case "構成検査は BorrowMutAt の注釈を寿命として型へ置く"
  (define core '(Read (BorrowMutAt 3 (Own 0 ()) 0)))
  (define cfg `(cfg ,core ,int-heap ,int-states () ()))
  (check-true (config-ok? cfg '() 'Int '()))
  (check-equal? (raw-failure-key core '((0 Int))) 'borrow-region-mismatch))

(test-case "構成検査の BorrowAt は存在しない place を拒否する"
  (define cfg '(cfg (Read (BorrowAt 3 (Own 5 ()) 5))
                    ((0 7 (declared Int))) ((0 Available)) () ()))
  (check-false (config-ok? cfg '() 'Int '())))

(test-case "構成検査は ReborrowAt の注釈を共有借用の寿命として型へ置く"
  (define cfg
    `(cfg (Read (ReborrowAt 4 (Own 0 ()) (BorrowMutRef 0 () 2)))
          ,int-heap ,int-states () ()))
  (check-true (config-ok? cfg '() 'Int '())))

(test-case "構成検査の ReborrowAt は own と capability の不一致を拒否する"
  (define cfg
    '(cfg (Read (ReborrowAt 4 (Own 1 ()) (BorrowMutRef 0 () 2)))
          ((0 7 (declared Int)) (1 8 (declared Int)))
          ((0 Available) (1 Available)) () ()))
  (check-equal? (config-type-failure-key cfg) 'own-designator-mismatch))

(test-case "構成検査も自由な RParam を持つ関数境界を拒否する"
  (define callables
    '((free-borrow
       (NFn ((Borrowed Int (RParam z))) Unit () () () User))))
  (define cfg '(cfg (Lam User free-borrow (p) unit) () () () ()))
  (check-equal? (config-type-failure-key cfg callables)
                'borrowed-function-parameter))

(test-case "Apply の構成検査も具体化済み region を関数境界で許す"
  (define signature '(NFn ((Borrowed Int 3)) Unit () () () User))
  (define cfg
    `(cfg (Apply (Move 1) unit)
          ((1 (Lam User local (p) unit) (declared ,signature)))
          ((1 Available)) () ()))
  (check-equal? (config-type-failure-key cfg) 'type-mismatch))

(test-case "複数 capability の Reborrow は own の入口検査で先に拒否される"
  (define operand
    '(Eliminate (Construct (Option Int) some 1)
       ((none () -> (BorrowMutRef 0 () 0))
        (some (value) -> (BorrowMutRef 1 () 0)))))
  (check-equal? (borrow-token-key (empty-region-ctx) operand)
                (set (cons 0 '()) (cons 1 '())))
  (define cfg
    `(cfg (ReborrowAt 4 (Own 0 ()) ,operand)
          ((0 7 (declared Int)) (1 8 (declared Int)))
          ((0 Available) (1 Available)) () ()))
  (check-equal? (config-type-failure-key cfg) 'own-designator-mismatch))

(test-case "UnionEliminate の別 owner を束ねる Reborrow は source 検査で拒否される"
  (define source
    '(Scope ()
       (Let (x let (Owned Int)) 7
         (Let (y let (Owned Int)) 8
           (Reborrow
            (UnionEliminate
             (UnionInject (Union Int String) Int 0)
             ((Int i -> (BorrowMut x))
              (String s -> (BorrowMut y)))))))))
  (define ir (build-region-ir source))
  (define result
    (type-of/raw*+borrows source '() '() '()
                          (region-ctx ir '() (hash) (hash))))
  (check-equal?
   (match result
     [`(fail ,key ,_node ,_details ...) key]
     [_ #f])
   'unresolved-borrow-owner))

(test-case "構成検査は FromRawPtr の pointer 型検査を保つ"
  (define cfg '(cfg (Unsafe (FromRawPtr 3 7)) () () () ()))
  (check-equal? (config-type-failure-key cfg) 'ptr-non-pointer)
  (check-false (config-ok? cfg '() 'Int '(Unsafe))))

(test-case "構成検査は RegionApp の具体的な region の生存だけを省く"
  (define cfg
    `(cfg (RegionApp (RegionLam (a)
                               (BorrowAt (RParam a) (Own 0 ()) 0))
                    (3))
          ,int-heap ,int-states () ()))
  (check-true (config-ok? cfg '() '(Borrowed Int 3) '()))
  (check-equal?
   (config-type-failure-key
    '(cfg (RegionApp (RegionLam (a) 1) (3 4)) () () () ()))
   'region-app-arity))

(define region-app-callables
  '((useb (ForallRegion (a)
            (NFn ((Borrowed Res (RParam a))) Unit () () () User)))))

(define region-app-function
  '(RegionLam (a) (Lam User useb (p) unit)))

(define (trace-config start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 200])
    (cond
      [(zero? fuel) (error 'trace-config "fuel exhausted: ~s" current)]
      [else
       (match (raw-steps-g2/named current)
         ['() (list configs rules)]
         [(list (list rule next))
          (loop next (append configs (list next))
                (append rules (list rule)) (sub1 fuel))]
         [steps (error 'trace-config "nondeterministic: ~s" steps)])])))

(define (region-app-trace/source source callables)
  (match (prepare-borrow-term* source #:callables callables)
    [(list 'ok start _sidecar _ir expected)
     (define-values (configs rules) (apply values (trace-config start)))
     (list expected configs rules)]
    [other
     (error 'region-app-trace/source
            "source preparation failed: ~s; typing: ~s; ~s"
            other (region-source-typing-result source callables) source)]))

(define (region-source-typing-result source callables)
  (define ir (build-region-ir source))
  (define filled (fill-region-placeholders source ir))
  (with-handlers ([exn:fail? (lambda (error) (list 'annotation-error
                                                   (exn-message error)))])
    (define annotated (annotate-regions filled ir))
    (type-of/raw*+borrows annotated '() callables '()
                          (region-ctx ir '() (hash) (hash)))))

(define (typed-machine-core source callables places)
  (define ir (build-region-ir source))
  (define filled (fill-region-placeholders source ir))
  (define annotated (annotate-regions filled ir))
  (define callable-contexts (box (hash)))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
  (match (type-of/raw*+borrows
          annotated places callables '()
          (region-ctx ir '() owners (hash))
          #:callable-contexts callable-contexts)
    [`(ok (,type ,_row ,table ,sigma ,renamed ,_sidecar))
     (list type
           (annotate-callable-contexts
            (materialize-regions ir renamed table sigma)
            (unbox callable-contexts) 'renamed))]
    [other (error 'typed-machine-core "source 型検査に失敗した: ~s" other)]))

(define (trace-with-initial-int-place source callables)
  (match-define (list expected machine-core)
    (typed-machine-core source callables '((1 Int))))
  (define start
    (match (inject-g2m machine-core)
      [`(cfg ,core ,_heap ,_states ,tokens ,events)
       `(cfg ,core ((1 0 (declared Int))) ((1 Available)) ,tokens ,events)]))
  (define-values (configs rules) (apply values (trace-config start)))
  (list expected configs rules))

(define (check-config-trace configs callables expected)
  (define row (runtime-row (first configs) callables expected))
  (check-not-false row "起点の runtime-row")
  (for ([cfg (in-list configs)] [index (in-naturals)])
    (check-true (config-ok? cfg callables expected row)
                (format "構成 ~a の config-ok?" index))
    (check-equal? (runtime-row cfg callables expected) row
                  (format "構成 ~a の runtime-row" index))))

(define (collect-inst-cids term)
  (match term
    [`(Inst ,_ ,_ ,_) (list term)]
    [(? list?) (append-map collect-inst-cids term)]
    [_ '()]))

(define (config-core cfg)
  (match cfg [`(cfg ,core ,_ ,_ ,_ ,_) core]))

(define (inst-cids-after rules configs target)
  (for/list ([rule (in-list rules)]
             [next (in-list (rest configs))]
             #:when (eq? rule target))
    (collect-inst-cids (config-core next))))

(define (wrap-region-app-scopes count term)
  (if (zero? count) term
      `(Scope () ,(wrap-region-app-scopes (sub1 count) term))))

(define (make-region-app-core depth borrow-rho owner-rho)
  `(Scope ()
     (Let (x let (Owned Res)) (resource 7)
       ,(wrap-region-app-scopes
         depth
         `(Let (b let (Borrowed Res ,borrow-rho)) (Borrow x)
            (Apply (RegionApp ,region-app-function (,owner-rho)) b))))))

(define (find-core-path term predicate [path '()])
  (cond
    [(predicate term) path]
    [(list? term)
     (for/first ([child (in-list (core-children term))]
                 [index (in-naturals)]
                 #:do [(define found
                         (find-core-path child predicate
                                         (append path (list index))))]
                 #:when found)
       found)]
    [else #f]))

(define (region-app-trace depth)
  (define skeleton (make-region-app-core depth 0 0))
  (define ir (build-region-ir skeleton))
  (define owner-rho (region->rho ir (region-at ir '(0))))
  (define borrow-path
    (find-core-path skeleton (lambda (node) (equal? node '(Borrow x)))))
  (define borrow-rho (region->rho ir (region-at ir borrow-path)))
  (define source (make-region-app-core depth borrow-rho owner-rho))
  (define annotated (annotate-regions source ir))
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (match (type-of/raw*+borrows annotated '() region-app-callables '()
                               (region-ctx ir '() (hash) (hash))
                               #:mut-types mut-types
                               #:callable-contexts callable-contexts)
    [`(ok (,type ,_row ,table ,sigma ,renamed ,_sidecar))
     (define materialized
       (annotate-mut-binding-types
        (materialize-regions ir renamed table sigma)
        (unbox mut-types)))
     (define start
       (inject-g2m
        (annotate-callable-contexts materialized
                                    (unbox callable-contexts) 'renamed)))
     (define-values (configs rules) (apply values (trace-config start)))
     (list type configs rules)]
    [other (error 'region-app-trace "source typing failed: ~s" other)]))

(test-case "R-RegionApp 後も callable の署名を出現位置の文脈で解く"
  (for ([depth (in-list '(1 2 3))])
    (match-define (list expected configs rules) (region-app-trace depth))
    (check-not-false (index-of rules 'R-RegionApp))
    (for ([cfg (in-list configs)] [index (in-naturals)])
      (check-true (config-ok? cfg region-app-callables expected '())
                  (format "深さ ~a の構成 ~a の config-ok? key=~s expected=~s inferred=~s cfg=~s"
                          depth index (config-type-failure-key cfg region-app-callables)
                          expected
                          (config-type-result cfg region-app-callables)
                          cfg))
      (check-not-false (runtime-row cfg region-app-callables expected)
                       (format "深さ ~a の構成 ~a の runtime-row" depth index)))))

(define phantom-callables
  '((phantom (ForallRegion (a b) (NFn () Unit () () () User)))))

(define (make-phantom-source)
  `(Scope ()
     (Let (owner let (Owned Res)) (resource 1)
       (Scope ()
         (Scope ()
            (Apply
            (RegionApp (RegionLam (x y) (Lam User phantom () unit))
                       (ph ph))))))))

(test-case "phantom binder を含む RegionApp の構成を検査する"
  (match-define (list expected configs rules)
    (region-app-trace/source (make-phantom-source) phantom-callables))
  (check-not-false (index-of rules 'R-RegionApp))
  (check-config-trace configs phantom-callables expected)
  (define region-app-index (index-of rules 'R-RegionApp))
  (define after (list-ref configs (add1 region-app-index)))
  (define cids (collect-inst-cids (second after)))
  (check-equal? (length cids) 1)
  (check-equal? (map first (cid-pairs (first cids))) '(a b))
  (check-eq? (cid-poly (first cids)) 'Mono)
  (check-true (andmap exact-nonnegative-integer?
                      (map second (cid-pairs (first cids))))))

(define record-callables
  '((record-useb (ForallRegion (a)
                   (NFn () Unit () () () User)))))

(test-case "Rec の欄から RegionApp 後に Lam を取り出して適用する"
  (define source
    '(Scope ()
       (Apply
        (Proj
         (RegionApp
          (RegionLam (a)
            (Rec ((f imm (Lam User record-useb () unit)))))
          (ph))
         f))))
  (match-define (list expected configs rules)
    (region-app-trace/source source record-callables))
  (check-not-false (index-of rules 'R-RegionApp))
  (check-not-false (index-of rules 'R-Proj))
  (check-not-false (index-of rules 'R-Beta))
  (check-config-trace configs record-callables expected))

(define repeated-callable
  '((polyuse (ForallRegion (a) (NFn () Unit () () () User)))))

(test-case "同じ RegionLam を異なる region で二度適用する"
  (define source
    '(Scope ()
       (Let (f const
               (ForallRegion (a) (NFn () Unit () () () User)))
            (RegionLam (a) (Lam User polyuse () unit))
         (Scope ()
           (Let (first const Unit) (Apply (RegionApp f (ph)))
             (Scope ()
               (Apply (RegionApp f (ph)))))))))
  (match-define (list expected configs rules)
    (region-app-trace/source source repeated-callable))
  (check-config-trace configs repeated-callable expected)
  (define events (inst-cids-after rules configs 'R-RegionApp))
  (check-equal? (length events) 2)
  (define concrete-cids
    (for/list ([event (in-list events)])
      (findf (lambda (cid)
               (exact-nonnegative-integer?
                (second (first (cid-pairs cid)))))
             event)))
  (check-equal? (map (lambda (cid) (and cid #t)) concrete-cids) '(#t #t))
  (define first-rho
    (second (first (cid-pairs (first concrete-cids)))))
  (define second-rho
    (second (first (cid-pairs (second concrete-cids)))))
  (check-not-equal? first-rho second-rho))

(test-case "同じ cid の Lam は出現位置ごとに別の文脈を記録する"
  (define callables
    '((shared (ForallRegion (a) (NFn () Unit () () () User)))))
  (define source
    '(Scope ()
       (Let (first const
                   (ForallRegion (a) (NFn () Unit () () () User)))
            (RegionLam (a) (Lam User shared () unit))
         (Scope ()
           (Let (second const
                        (ForallRegion (a) (NFn () Unit () () () User)))
                (RegionLam (b) (Lam User shared () unit))
             (Let (discarded const Unit) (Apply (RegionApp first (ph)))
               (Apply (RegionApp second (ph)))))))))
  (match-define (list expected configs rules)
    (region-app-trace/source source callables))
  (check-config-trace configs callables expected)
  (define initial-cids (collect-inst-cids (config-core (first configs))))
  (check-equal? (length initial-cids) 2)
  (check-not-equal? (second (first (cid-pairs (first initial-cids))))
                    (second (first (cid-pairs (second initial-cids)))))
  (check-equal? (length (inst-cids-after rules configs 'R-RegionApp)) 2))

(define deep-callables
  '((outer (ForallRegion (a)
             (NFn ((Borrowed Res (RParam a))) Unit () () () User)))
    (deep (NFn ((Borrowed Res (RParam a))) Unit () () () User))))

(test-case "RegionLam の Let の奥にある Lam の署名文脈を記録する"
  (define source
    '(Scope ()
       (Let (owner let (Owned Res)) (resource 3)
         (Let (argument let (Borrowed Res ph)) (Borrow owner)
           (Apply
            (RegionApp
             (RegionLam (a)
               (Lam User outer (x)
                 (Let (f const
                         (NFn ((Borrowed Res (RParam a))) Unit () () () User))
                      (Lam User deep (p) unit)
                   (Apply f x))))
             (ph))
            argument)))))
  (match-define (list expected configs rules)
    (region-app-trace/source source deep-callables))
  (check-not-false (index-of rules 'R-RegionApp))
  (check-config-trace configs deep-callables expected)
  (define region-app-index (index-of rules 'R-RegionApp))
  (define after (list-ref configs (add1 region-app-index)))
  (define cids (collect-inst-cids (config-core after)))
  (check-equal? (map cid-base cids) '(outer deep))
  (check-equal? (length cids) 2)
  (check-equal? (map first (cid-pairs (first cids))) '(a))
  (check-true (andmap exact-nonnegative-integer?
                      (map (lambda (cid)
                             (second (first (cid-pairs cid))))
                           cids))))

(define recur-forall-callables
  '((recf (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))))

(define recur-forall-source
  '(Scope (1)
     (Recur recf f (x)
       (Apply f x)
       (Let (g let (NFn ((BorrowedMut Int (RVar 0))) Int () () () User))
            (RegionApp f ((RVar 0)))
         0))))

(test-case "RecurBind 後の region 多相な RecurVal が Inst を保つ"
  (match-define (list expected configs rules)
    (trace-with-initial-int-place recur-forall-source recur-forall-callables))
  (check-not-false (index-of rules 'R-RecurBind))
  (check-config-trace configs recur-forall-callables expected)
  (define region-app-index (index-of rules 'R-RegionAppRecur))
  (check-not-false region-app-index)
  (define before-cids
    (collect-inst-cids
     (config-core (list-ref configs region-app-index))))
  (check-equal? (cid-poly (first before-cids)) '(Poly (a)))
  (check-equal? (raw-steps-g2/named (last configs)) '())
  (check-true (redex-match? G2m v (config-core (last configs))))
  (define cids (first (inst-cids-after rules configs 'R-RegionAppRecur)))
  (check-equal? (length cids) 1)
  (check-equal? (cid-base (first cids)) 'recf)
  (check-eq? (cid-poly (first cids)) 'Mono))

(define recur-forall0-callables
  '((recf0 (ForallRegion () (NFn () Unit () () () User)))))

(define recur-forall0-source
  '(Scope ()
     (Recur recf0 f () unit
       (Apply (RegionApp f ())))))

(test-case "空の ForallRegion を持つ RecurBind 後も Poly を区別する"
  (match-define (list expected configs rules)
    (region-app-trace/source recur-forall0-source recur-forall0-callables))
  (check-not-false (index-of rules 'R-RecurBind))
  (check-config-trace configs recur-forall0-callables expected)
  (define region-app-index (index-of rules 'R-RegionAppRecur))
  (check-not-false region-app-index)
  (define before-cids
    (collect-inst-cids
     (config-core (list-ref configs region-app-index))))
  (check-equal? (cid-poly (first before-cids)) '(Poly ()))
  (check-equal? (raw-steps-g2/named (last configs)) '())
  (check-true (redex-match? G2m v (config-core (last configs))))
  (define cids (first (inst-cids-after rules configs 'R-RegionAppRecur)))
  (check-equal? (length cids) 1)
  (check-eq? (cid-poly (first cids)) 'Mono))

(define recur-outer-region-callables
  '((recouter (ForallRegion (b)
                 (NFn ((BorrowedMut Int (RParam a))
                      (BorrowedMut Int (RParam b)))
                      Int () () () User)))))

(define recur-outer-region-source
  '(Scope ()
     (RegionApp
      (RegionLam (a)
        (Recur recouter f (x y)
          (Apply f x y)
          (Let (g const
                  (NFn ((BorrowedMut Int (RParam a))
                        (BorrowedMut Int (RVar 0)))
                       Int () () () User))
               (RegionApp f ((RVar 0)))
            0)))
      (ph))))

(test-case "RegionApp 後の RecurVal は具体化済み region と Poly を併せ持つ"
  (match-define (list expected configs rules)
    (region-app-trace/source recur-outer-region-source
                             recur-outer-region-callables))
  (check-not-false (index-of rules 'R-RegionApp))
  (check-not-false (index-of rules 'R-RecurBind))
  (check-config-trace configs recur-outer-region-callables expected)
  (define region-app-index (index-of rules 'R-RegionAppRecur))
  (check-not-false region-app-index)
  (define before-cids
    (collect-inst-cids
     (config-core (list-ref configs region-app-index))))
  (check-equal? (length before-cids) 1)
  (check-equal? (cid-poly (first before-cids)) '(Poly (b)))
  (check-equal? (map first (cid-pairs (first before-cids))) '(a))
  (check-equal? (raw-steps-g2/named (last configs)) '())
  (check-true (redex-match? G2m v (config-core (last configs))))
  (define cids (first (inst-cids-after rules configs 'R-RegionAppRecur)))
  (check-equal? (length cids) 1)
  (check-eq? (cid-poly (first cids)) 'Mono)
  (check-equal? (map first (cid-pairs (first cids))) '(a b))
  (check-true (andmap exact-nonnegative-integer?
                      (map second (cid-pairs (first cids))))))

(test-case "Poly の内側の Recur 本体は外側の RegionApp で置き換わらない"
  (define callables
    '((outer (ForallRegion (a)
               (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))
      (inner (ForallRegion (a)
               (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))))
  (define source
    '(Scope (1)
       (Recur outer outerf (outer-x)
         (Let (outer-y let (BorrowedMut Int (RParam a))) outer-x
           (Recur inner innerf (inner-x)
             (Let (inner-y let (BorrowedMut Int (RParam a))) inner-x 0)
             0))
         (Apply (RegionApp outerf ((RVar 0))) (BorrowMut 1)))))
  (match-define (list expected configs rules)
    (trace-with-initial-int-place source callables))
  (check-not-false (index-of rules 'R-RegionAppRecur))
  (check-config-trace configs callables expected)
  (define region-app-index (index-of rules 'R-RegionAppRecur))
  (define before-cids
    (collect-inst-cids (config-core (list-ref configs region-app-index))))
  (check-equal? (map cid-base before-cids) '(outer inner))
  (check-equal? (map cid-poly before-cids)
                '((Poly (a)) (Poly (a))))
  (define after (list-ref configs (add1 region-app-index)))
  (define after-cids (collect-inst-cids (config-core after)))
  (define outer-cid (findf (lambda (cid) (eq? (cid-base cid) 'outer)) after-cids))
  (define inner-cid (findf (lambda (cid) (eq? (cid-base cid) 'inner)) after-cids))
  (check-eq? (cid-poly outer-cid) 'Mono)
  (define outer-rho (second (first (cid-pairs outer-cid))))
  (check-true (exact-nonnegative-integer? outer-rho))
  (check-equal? (cid-poly inner-cid) '(Poly (a)))
  (define (contains? term needle)
    (or (equal? term needle)
        (and (list? term) (ormap (lambda (part) (contains? part needle)) term))))
  (check-true (contains? (config-core after) `(BorrowedMut Int ,outer-rho)))
  (check-true (contains? (config-core after) '(BorrowedMut Int (RParam a))))
  (check-equal? (raw-steps-g2/named (last configs)) '())
  (check-true (redex-match? G2m v (config-core (last configs)))))

(test-case "R-RegionAppRecur は arity 不一致と Inst 無しでは発火しない"
  (for ([core
         (in-list
          '((RegionApp (RecurVal (Inst recf () (Poly (a))) f () 0) ())
            (RegionApp (RecurVal recf f () 0) ((RVar 0)))))])
    (define steps (raw-steps-g2/named `(cfg ,core () () () ())))
    (check-false (memq 'R-RegionAppRecur (map first steps)))))

(test-case "具体化した RecurVal の再帰呼出しは二度 unfold する"
  (define callables
    '((recf (ForallRegion (a)
             (NFn ((Option Int)) Int () () () User)))))
  (define source
    '(Scope (1)
       (Recur recf f (state)
         (Eliminate state
           ((none () -> 0)
            (some (item) ->
              (Apply f (Construct (Option Int) none)))))
         (Apply (RegionApp f (ph))
                (Construct (Option Int) some 1)))))
  (match-define (list expected configs rules)
    (trace-with-initial-int-place source callables))
  (check-config-trace configs callables expected)
  (check-equal?
   (check-borrow-execution (first configs) #f #f 200 (make-bcounters))
   'ok)
  (check-not-false (index-of rules 'R-RegionAppRecur))
  (check-true (>= (count (lambda (rule) (eq? rule 'R-RecurUnfold)) rules) 2))
  (check-equal? (raw-steps-g2/named (last configs)) '())
  (check-true (redex-match? G2m v (config-core (last configs)))))

(define nested-poly-callables
  '((outer (ForallRegion (a) (NFn () Int () () () User)))
    (inner (ForallRegion (a)
             (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))))

(define nested-poly-source
  '(Scope (1)
     (Recur outer outerf ()
       (Recur inner innerf (z)
         (Let (y let (BorrowedMut Int (RParam a))) z 0)
         0)
       0)))

(test-case "入れ子の region 多相 Recur の両 cid が Poly binder を持つ"
  (define machine-core
    (second (typed-machine-core nested-poly-source nested-poly-callables
                                '((1 Int)))))
  (define cids (collect-inst-cids machine-core))
  (check-equal? (map cid-base cids) '(outer inner))
  (check-equal? (map cid-poly cids) '((Poly (a)) (Poly (a)))))

(test-case "Inst cid は source 型付けで unknown-callable になる"
  (check-equal?
   (match (type-of/raw '(Lam User (Inst useb ((a 0)) Mono) (p) (Read p))
                       '()
                       '((useb (ForallRegion (a)
                                  (NFn ((Borrowed Int (RParam a)))
                                       Int () () () User))))
                       '())
     [`(fail ,key ,_node ,_details ...) key]
     [_ #f])
   'unknown-callable))

(test-case "callable-signature は Poly の形と Mono の binder 対応を検証する"
  (define callables
    '((poly (ForallRegion (a) (NFn () Unit () () () User)))))
  (check-equal?
   (with-config-typing
    (lambda ()
      (callable-signature callables '(Inst poly ((a 4)) Mono))))
   '(NFn () Unit () () () User))
  (check-false
   (with-config-typing
    (lambda ()
      (callable-signature callables '(Inst poly () Mono)))))
  (check-false
   (with-config-typing
    (lambda ()
      (callable-signature callables '(Inst poly ((a 4)) (Poly (b))))))))

(test-case "core-type-of/materialized も callable context を cid に付ける"
  (define source
    '(Scope () (RegionLam (a) (Lam User polyuse () unit))))
  (match-define `(ok ,_type ,machine-core)
    (core-type-of/materialized source '() repeated-callable))
  (define cids (collect-inst-cids machine-core))
  (check-equal? (length cids) 1)
  (check-equal? (cid-pairs (first cids)) '((a (RParam a.0))))
  (check-eq? (cid-poly (first cids)) 'Mono))

(test-case "execution-core の同名 RegionLam shadow は出現位置へ追随する"
  (define callables
    '((shadow (NFn ((Borrowed Int (RParam a))) Unit () () () User))))
  (define source
    '(Scope ()
       (RegionLam (a)
         (RegionLam (a)
           (RegionApp
            (RegionLam (b) (Lam User shadow (x) unit))
            ((RParam a)))))))
  (define machine-core (execution-core source callables))
  (define cids (collect-inst-cids machine-core))
  (check-equal? (length cids) 1)
  (check-equal? (cid-pairs (first cids)) '((a (RParam a))))
  (define-values (configs _rules)
    (apply values (trace-config (inject-g2m machine-core))))
  (define expected
    (match (type-of/raw source '() callables '())
      [`(ok (,type ,_row)) type]
      [other (error 'execution-core-shadow "source 型検査: ~s" other)]))
  (check-config-trace configs callables expected))

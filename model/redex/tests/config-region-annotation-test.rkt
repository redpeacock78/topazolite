#lang racket

(require rackunit
         racket/match
         racket/set
         "../borrow.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../region.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define int-heap '((0 7 (declared Int))))
(define int-states '((0 Available)))

(define (config-type-failure-key cfg [callables '()])
  (match cfg
    [`(cfg ,core ,heap ,states ,_tokens ,_trace)
     (define places
       (derive-places heap callables #:declared (config-declared-types cfg)))
     (define borrow-types
       (and places (recover-runtime-borrow-types core heap states places)))
     (and borrow-types
          (parameterize ([config-runtime-borrow-types borrow-types])
            (with-config-typing
             (lambda ()
               (match (type-of/raw core places callables)
                 [`(fail ,key ,_node ,_details ...) key]
                 [_ #f])))))]
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
            (NFn ((Borrowed Res (RParam a))) Res () () () User)))))

(define region-app-function
  '(RegionLam (a) (Lam User useb (p) (Read p))))

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
  (match (type-of/raw*+borrows annotated '() region-app-callables '()
                               (region-ctx ir '() (hash) (hash))
                               #:mut-types mut-types)
    [`(ok (,type ,_row ,table ,sigma ,renamed ,_sidecar))
     (define materialized
       (annotate-mut-binding-types
        (materialize-regions ir renamed table sigma)
        (unbox mut-types)))
     (define start (inject-g2m materialized))
     (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
       (cond
         [(zero? fuel) (error 'region-app-trace "fuel exhausted")]
         [else
          (match (raw-steps-g2/named current)
            ['() (list type configs rules)]
            [(list (list rule next))
             (loop next (append configs (list next))
                   (append rules (list rule)) (sub1 fuel))]
            [steps (error 'region-app-trace "nondeterministic: ~s" steps)])]))]
    [other (error 'region-app-trace "source typing failed: ~s" other)]))

(test-case "R-RegionApp 後の callable 型回復境界を Task 1b へ渡す"
  (for ([depth (in-list '(1 2 3))])
    (match-define (list expected configs rules) (region-app-trace depth))
    (define region-app-index
      (index-of rules 'R-RegionApp))
    (check-not-false region-app-index)
    (for ([cfg (in-list (take configs (add1 region-app-index)))])
      (check-true (config-ok? cfg region-app-callables expected '()))
      (check-not-false (runtime-row cfg region-app-callables expected)))
    (define after-region-app (list-ref configs (add1 region-app-index)))
    ;; Task 1b は RegionApp 後に失われた callable の具体型を回復する。
    (check-equal? (config-type-failure-key after-region-app
                                           region-app-callables)
                  'unknown-callable)
    (check-false (config-ok? after-region-app region-app-callables expected '()))
    (check-false (runtime-row after-region-app region-app-callables expected))))

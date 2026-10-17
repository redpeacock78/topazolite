#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define borrowed-type '(Borrowed Res ph))
(define wide-type
  '(Record ((hidden (Borrowed Res ph) imm) (name String imm))))
(define narrow-type '(Record ((name String imm))))
(define proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,wide-type ,narrow-type)))
(define (replace-symbol term target replacement)
  (cond
    [(eq? term target) replacement]
    [(pair? term)
     (cons (replace-symbol (car term) target replacement)
           (replace-symbol (cdr term) target replacement))]
    [else term]))

(define (find-core-point core predicate)
  (let walk ([term core] [point '()])
    (cond
      [(predicate term) point]
      [else
       (for/or ([child (in-list (core-children term))]
                [index (in-naturals)])
         (walk child (append point (list index))))])))

(define (prepare core [callables '()])
  (define region-ir (build-region-ir core))
  (define filled (fill-region-placeholders core region-ir))
  (define borrow-point
    (find-core-point core (lambda (node) (match node [`(Borrow ,_) #t] [_ #f]))))
  (check-not-false borrow-point "Borrow の region point がある")
  (define rho (region->rho region-ir (region-at region-ir borrow-point)))
  ;; Use one IR: concretizing Proof regions before rebuilding it changes region numbering.
  (define filled-proof (replace-symbol filled 'ph rho))
  (define filled-callables (replace-symbol callables 'ph rho))
  (define annotated (annotate-regions filled-proof region-ir))
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (match (type-of/raw*+borrows annotated '() filled-callables '()
                                (region-ctx region-ir '() (hash) (hash))
                                #:mut-types mut-types
                                #:callable-contexts callable-contexts)
    [(list 'ok (list type _row table sigma renamed sidecar))
     (define materialized (materialize-regions region-ir renamed table sigma))
     (define machine-core
       (annotate-callable-contexts
        (annotate-mut-binding-types materialized (unbox mut-types))
        (unbox callable-contexts) 'renamed))
     (values (inject-g2m machine-core) sidecar region-ir type)]
    [other
     (fail (format "Core が型検査されなかった: ~s; typed=~s"
                   other annotated))]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 300])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (cfg-core cfg)
  (match cfg [`(cfg ,core ,_ ,_ ,_ ,_) core]))

(define (cfg-fields cfg)
  (match cfg [`(cfg ,core ,heap ,states ,tokens ,events)
              (values core heap states tokens events)]))

(define (borrow-refs term)
  (cond
    [(match term
       [(or `(BorrowRef ,_ ,_ ,_) `(BorrowMutRef ,_ ,_ ,_)) #t]
       [_ #f])
     (list term)]
    [(pair? term)
     (append (borrow-refs (car term)) (borrow-refs (cdr term)))]
    [else '()]))

(define (check-live-trace configs rules expected callables
                          #:token-preserved? [token-preserved? #t])
  (define rows
    (for/list ([config (in-list configs)])
      (runtime-row config callables expected)))
  (define start-index
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
  (define scope-exit-index
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (eq? rule 'R-ScopeValue))
      index))
  (check-not-false start-index "trace に runtime-row がある config がある")
  (check-not-false scope-exit-index "trace に Scope 終端がある")
  (check-true (< start-index scope-exit-index)
              "runtime-row の検査開始は Scope 終端より前")
  (for ([config (in-list (drop configs start-index))]
        [row (in-list (drop rows start-index))]
        [index (in-naturals start-index)])
    (check-not-false row (format "config ~a の runtime-row: ~s" index config))
    (check-true (config-ok? config callables expected row)
                (format "config ~a の config-ok?" index)))
  (check-true (redex-match? G2m v (cfg-core (last configs)))
              "trace の終端が値")
  (check-false (pair? (borrow-refs (cfg-core (last configs))))
               "Scope を抜けた最終値に BorrowRef がない")
  (for ([rule (in-list rules)] [index (in-naturals)]
        #:when (eq? rule 'R-DischargeRemainder))
    (define-values (_before-core before-heap before-states before-tokens before-events)
      (cfg-fields (list-ref configs index)))
    (define-values (_after-core after-heap after-states after-tokens after-events)
      (cfg-fields (list-ref configs (add1 index))))
    (check-equal? after-heap before-heap "RSD は H を変えない")
    (check-equal? after-states before-states "RSD は Ω を変えない")
    (when token-preserved?
      (check-equal? after-tokens before-tokens "借用のみの RSD は Λtok を変えない"))
    (check-equal? after-events before-events "RSD は θ を変えない")))

(define (borrow-scope body)
  `(Scope ()
     (Let (owner let (Owned Res)) (resource 501)
       (Scope ()
         (Let (borrow let ,borrowed-type) (Borrow owner)
           ,body)))))

(define (wide-record borrow)
  `(Rec ((hidden imm ,borrow) (name imm "A"))))

(test-case "Scope の結果から RSD が BorrowRef を除き、終端後も config を保つ"
  (define core (borrow-scope `(Discharge ,proof ,(wide-record 'borrow))))
  (define-values (start sidecar ir expected) (prepare core))
  (define-values (configs rules) (trace-g2 start))
  (check-live-trace configs rules expected '())
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (check-borrow-execution start sidecar ir 300 (make-bcounters))
                'ok))

(test-case "閉包の捕捉で RSD 後に Scope を抜けても BorrowRef を残さない"
  (define fn-type '(NFn () String () () () User))
  (define core
    `(Scope ()
       (Let (owner let (Owned Res)) (resource 502)
         (Let (captured let ,fn-type)
           (Scope ()
             (Let (borrow let ,borrowed-type) (Borrow owner)
               (Let (value let ,narrow-type)
                    (Discharge ,proof ,(wide-record 'borrow))
                 (Lam User captured () (Proj value name)))))
           (Apply captured)))))
  (define callables `((captured ,fn-type)))
  (define-values (start _sidecar _ir expected) (prepare core callables))
  (define-values (configs rules) (trace-g2 start))
  (check-live-trace configs rules expected callables)
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (cfg-core (last configs)) "A"))

(test-case "Recur の back-edge で RSD し BorrowRef なしの引数を反復する"
  (define core
    `(Recur loop-id loop (again value)
       (Eliminate again
         ((true () -> (Proj value name))
          (false () ->
           (Scope ()
             (Let (owner let (Owned Res)) (resource 505)
               (Scope ()
                 (Let (borrow let ,borrowed-type) (Borrow owner)
                   (Let (next let ,narrow-type)
                        (Discharge ,proof ,(wide-record 'borrow))
                     (Apply loop (Construct Bool true) next)))))))))
       (Apply loop (Construct Bool false)
              (Rec ((name imm "A"))))))
  (define loop-type
    `(NFn (Bool ,narrow-type) String () (Partial) () User))
  (define-values (start sidecar _ir expected)
    (prepare core `((loop-id ,loop-type))))
  (define-values (configs rules) (trace-g2 start))
  (check-live-trace configs rules expected '())
  (check-equal? (count (lambda (rule) (eq? rule 'R-DischargeRemainder)) rules) 1)
  (check-equal? (check-borrow-execution start sidecar _ir 300 (make-bcounters))
                'ok)
  (check-equal? (cfg-core (last configs)) "A"))

(test-case "const の直接と Let 包みの RSD は Scope 後も config を保つ"
  (for ([bound (in-list
                (list `(Discharge ,proof ,(wide-record 'borrow))
                      `(Let (tmp let ,wide-type)
                         (Discharge
                          (ProofRep (Reserved o-narrow)
                                    (RemainderSafelyDropped ,wide-type ,wide-type))
                          ,(wide-record 'borrow))
                         (Discharge ,proof tmp))))])
    (define core
      (borrow-scope
       `(Let (kept const ,narrow-type) ,bound kept)))
    (define-values (start sidecar ir expected) (prepare core))
    (define-values (configs rules) (trace-g2 start))
    (check-live-trace configs rules expected '())
    (check-not-false (member 'R-DischargeRemainder rules))
    (check-equal? (check-borrow-execution start sidecar ir 300
                                          (make-bcounters))
                  'ok)))

(test-case "UnionInject の payload 内の RSD を全 trace で検査する"
  (define union-type `(Union Bool ,narrow-type))
  (define core
    (borrow-scope
     `(UnionInject ,union-type ,narrow-type
                   (Discharge ,proof ,(wide-record 'borrow)))))
  (define-values (start sidecar ir expected) (prepare core))
  (define-values (configs rules) (trace-g2 start))
  (check-live-trace configs rules expected '())
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (check-borrow-execution start sidecar ir 300 (make-bcounters))
                'ok))

(test-case "RSD の別 alias は追跡され、同じ値の可変借用競合は拒否される"
  (define core
    (borrow-scope
     `(Let (alias let ,borrowed-type) borrow
        (Let (kept let ,narrow-type)
             (Discharge ,proof ,(wide-record 'borrow))
          (Let (again let ,borrowed-type) (Suspend alias) unit)))))
  (define-values (start sidecar _ir expected) (prepare core))
  (define-values (configs rules) (trace-g2 start))
  (check-live-trace configs rules expected '())
  (define rsd-index
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (eq? rule 'R-DischargeRemainder)) index))
  (check-not-false rsd-index)
  (define before-refs (borrow-refs (cfg-core (list-ref configs rsd-index))))
  (define after-refs (borrow-refs (cfg-core (list-ref configs (add1 rsd-index)))))
  (check-equal? (length before-refs) 2 "RSD 前は alias と残余の二参照")
  (check-equal? (length after-refs) 1 "RSD 後も alias 一参照は生存")
  (check-equal? (first after-refs) (first before-refs)
                "残った alias の BorrowRef と region は不変")
  (define counters (make-bcounters))
  (check-equal? (check-borrow-execution start sidecar _ir 300 counters) 'ok)
  (check-true (positive? (bcounters-shared counters))
              "alias の共有借用 event が照合される")

  (define conflicting
    (borrow-scope
     `(Let (alias let ,borrowed-type) borrow
        (Let (kept let ,narrow-type)
             (Discharge ,proof ,(wide-record 'borrow))
          (Yield (BorrowMut owner) (Read alias))))))
  (define ir (build-region-ir conflicting))
  (define point
    (find-core-point conflicting
                     (lambda (node) (match node [`(Borrow ,_) #t] [_ #f]))))
  (define rho (region->rho ir (region-at ir point)))
  (define filled (replace-symbol conflicting 'ph rho))
  (match (type-of/raw filled '() '() '() (region-ctx ir '() (hash) (hash)))
    [(list 'fail key _node _details ...) (check-equal? key 'borrow-conflicting-alias)]
    [other (fail (format "mutable-borrow conflict unexpectedly accepted: ~s" other))]))

(test-case "RSD は同じ残余の Owned token だけを Dropped にする"
  (define option-owned '(Option (Owned Res)))
  (define actual
    `(Record ((hidden ,borrowed-type imm)
              (name String imm)
              (owned ,option-owned imm))))
  (define expected-type '(Record ((name String imm))))
  (define mixed-proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,actual ,expected-type)))
  (define core
    (borrow-scope
     `(Let (owned-value let ,option-owned)
           (Construct ,option-owned some (OwnLeaf (resource 503)))
        (Discharge ,mixed-proof
                   (Rec ((hidden imm borrow)
                         (name imm "A")
                         (owned imm (Move owned-value))))))))
  (define-values (start sidecar _ir expected) (prepare core))
  (define-values (configs rules) (trace-g2 start))
  (check-live-trace configs rules expected '() #:token-preserved? #f)
  (define rsd-index
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (eq? rule 'R-DischargeRemainder)) index))
  (check-not-false rsd-index)
  (define-values (_before-core before-heap before-states before-tokens before-events)
    (cfg-fields (list-ref configs rsd-index)))
  (define-values (_after-core after-heap after-states after-tokens after-events)
    (cfg-fields (list-ref configs (add1 rsd-index))))
  (check-equal? after-heap before-heap "RSD は H を変えない")
  (check-equal? after-states before-states "RSD は Ω を変えない")
  (check-equal? after-events before-events "RSD は θ を変えない")
  (define newly-dropped
    (for/list ([entry (in-list after-tokens)]
               #:when (and (eq? (second entry) 'Dropped)
                           (match (assoc (first entry) before-tokens)
                             [(list _ old-state) (not (eq? old-state 'Dropped))]
                             [_ #f])))
      (first entry)))
  (check-equal? (length newly-dropped) 1 "Owned leaf token だけを drop")
  (check-equal? (length (borrow-refs (cfg-core (list-ref configs rsd-index)))) 1)
  (check-equal? (length (borrow-refs (cfg-core (list-ref configs (add1 rsd-index))))) 0)
  (check-equal? (check-borrow-execution start sidecar _ir 300 (make-bcounters)) 'ok))

(test-case "Surface 借用注釈は SUR-004 前なので E-SYN-003 のまま"
  (define result
    (elab '(Fn ((xs (Borrowed (List Int) 0))) Int ()
             (Eliminate xs
               ((nil () -> 0)
                (cons (head tail) -> 0))))))
  (match result
    [`(err ,diagnostic) (check-equal? (diagnostic-id diagnostic) "E-SYN-003")]
    [other (fail (format "Surface borrow unexpectedly accepted: ~s" other))]))

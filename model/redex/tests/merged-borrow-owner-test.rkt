#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow-gen.rkt"
         "../borrow.rkt"
         "../borrow-oracle.rkt"
         "../diagnostic.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define (replace-symbol term target replacement)
  (cond
    [(eq? term target) replacement]
    [(pair? term)
     (cons (replace-symbol (car term) target replacement)
           (replace-symbol (cdr term) target replacement))]
    [else term]))

(define (find-borrow-point core)
  (let walk ([term core] [point '()])
    (cond
      [(match term
         [(or `(Borrow ,_) `(BorrowMut ,_)) #t]
         [_ #f])
       point]
      [else
       (for/or ([child (in-list (core-children term))]
                [index (in-naturals)])
         (walk child (append point (list index))))])))

(define (prepare core)
  (define ir (build-region-ir core))
  (define filled (fill-region-placeholders core ir))
  (define point (find-borrow-point core))
  (check-not-false point "借用 point がある")
  (define rho (region->rho ir (region-at ir point)))
  (prepare-annotated
   (annotate-regions (replace-symbol filled 'ph rho) ir)
   ir))

(define (prepare-all-regions core)
  (define ir (build-region-ir core))
  (prepare-annotated (annotate-regions (fill-region-placeholders core ir) ir) ir))

(define (prepare-annotated annotated ir)
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (match (type-of/raw*+borrows annotated '() '() '()
                                (region-ctx ir '() (hash) (hash))
                                #:mut-types mut-types
                                #:callable-contexts callable-contexts)
    [(list 'ok (list type _row table sigma renamed sidecar))
     (define materialized (materialize-regions ir renamed table sigma))
     (define machine-core
       (annotate-callable-contexts
        (annotate-mut-binding-types materialized (unbox mut-types))
        (unbox callable-contexts) 'renamed))
     (values (inject-g2m machine-core) sidecar ir type)]
    [other (fail (format "Core が型検査されなかった: ~s; typed=~s"
                         other annotated))]))

(define (failure-key core)
  (define ir (build-region-ir core))
  (define annotated (annotate-regions (fill-region-placeholders core ir) ir))
  (match (type-of/raw*+borrows annotated '() '() '()
                              (region-ctx ir '() (hash) (hash)))
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

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
  (match cfg [`(cfg ,core ,_ ...) core]))

(define (cfg-fields cfg)
  (match cfg
    [`(cfg ,core ,heap ,states ,tokens ,events)
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

(define (check-live-trace configs rules expected)
  (define rows
    (for/list ([config (in-list configs)])
      (runtime-row config '() expected)))
  (define start-index
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
  (define scope-exit-index
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (eq? rule 'R-ScopeValue))
      index))
  (check-not-false start-index "trace に runtime-row がある config がある")
  (check-not-false scope-exit-index "trace に Scope 終端がある")
  (for ([config (in-list (drop configs start-index))]
        [row (in-list (drop rows start-index))]
        [index (in-naturals start-index)])
    (check-not-false row (format "config ~a の runtime-row: ~s" index config))
    (check-true (config-ok? config '() expected row)
                (format "config ~a の config-ok?" index)))
  (check-true (redex-match? G2m v (cfg-core (last configs)))
              "trace の終端が値")
  (check-false (pair? (borrow-refs (cfg-core (last configs))))
               "終端値に BorrowRef が残らない"))

(define (config-after configs rules rule-name)
  (define index (index-of rules rule-name))
  (check-not-false index)
  (list-ref configs (add1 index)))

(define (heap-field heap root label)
  (match (assoc root heap)
    [`(,_ (Rec ,fields) (declared ,_))
     (match (assoc label fields)
       [`(,_ ,_ ,value) value]
       [_ (fail (format "heap に欄 ~a がない: ~s" label heap))])]
    [_ (fail (format "heap に place ~a の record がない: ~s" root heap))]))

(define (merged-shared-core branch left right)
  `(Scope ()
     (Let (x let (Owned (Record ((n Int imm))))) (Rec ((n imm 1)))
       (Let (y let (Owned (Record ((n Int imm))))) (Rec ((n imm 2)))
         (Let (b let (Borrowed (Record ((n Int imm))) ph))
              (Eliminate (Construct Bool ,branch)
                ((true () -> (Borrow ,left)) (false () -> (Borrow ,right))))
              (Read (ProjBorrow b n)))))))

(test-case "合流した共有借用からの射影は走った枝の root と path を保つ"
  (for ([branch '(true false)]
        [expected-root '(0 1)]
        [expected-value '(1 2)])
    (define-values (start _sidecar _ir type)
      (prepare (merged-shared-core branch 'x 'y)))
    (check-equal? type 'Int)
    (define-values (configs rules) (trace-g2 start))
    (check-live-trace configs rules 'Int)
    (define-values (core heap _states _tokens _events)
      (cfg-fields (config-after configs rules 'R-ProjBorrow)))
    (match (borrow-refs core)
      [(list `(BorrowRef ,root ,path ,_))
       (check-equal? root expected-root)
       (check-equal? path '(n))
       (check-equal? (heap-field heap root 'n) expected-value)]
      [refs (fail (format "BorrowRef 一つを期待した: ~s" refs))])))

(define (merged-mut-core branch)
  `(Scope ()
     (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
       (Let (y let (Owned (Record ((n Int mut))))) (Rec ((n mut 2)))
         (Scope ()
           (Let (b let (BorrowedMut (Record ((n Int mut))) ph))
                (Eliminate (Construct Bool ,branch)
                  ((true () -> (BorrowMut x)) (false () -> (BorrowMut y))))
                (Let (ignored const Unit) (Assign (ProjBorrow b n) 5)
                     (Read (ProjBorrow b n)))))))))

(define (merged-reborrow-core branch child-body)
  `(Scope ()
     (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
       (Let (y let (Owned (Record ((n Int mut))))) (Rec ((n mut 2)))
         (Let (b let (BorrowedMut (Record ((n Int mut))) ph))
              (Eliminate (Construct Bool ,branch)
                ((true () -> (BorrowMut x)) (false () -> (BorrowMut y))))
           (Let (before const Int)
                (Scope ()
                  (Let (c let (Borrowed (Record ((n Int mut))) ph))
                       (Reborrow b)
                       ,child-body))
                (Assign (ProjBorrow b n) 5)))))))

(define (merged-reborrow-read)
  '(Read (ProjBorrow c n)))

(define (merged-reborrow-move owner)
  `(Let (m let (Owned (Record ((n Int mut))))) (Move ,owner)
        (Read (ProjBorrow c n))))

(define (merged-reborrow-parent-write)
  '(Let (ignored const Unit) (Assign (ProjBorrow b n) 5)
        (Read (ProjBorrow c n))))

(define (stale-reborrow-core branch child-body)
  (define current-borrow
    (if branch
        `(Eliminate (Construct Bool ,branch)
           ((true () -> (BorrowMut x)) (false () -> (BorrowMut y))))
        '(BorrowMut x)))
  `(Scope ()
     (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
       (Let (y let (Owned (Record ((n Int mut))))) (Rec ((n mut 2)))
         (Let (old-scope const Int)
              (Scope ()
                (Let (old let (BorrowedMut (Record ((n Int mut))) ph))
                     (BorrowMut x)
                     0))
           (Let (current-scope const Unit)
                (Scope ()
                  (Let (b let (BorrowedMut (Record ((n Int mut))) ph))
                       ,current-borrow
                    (Let (child-scope const Int)
                         (Scope ()
                           (Let (c let (Borrowed (Record ((n Int mut))) ph))
                                (Reborrow b)
                                ,child-body))
                      (Assign (ProjBorrow b n) 5))))
             0))))))

(define forwarding-callables
  '((forward-id
     (ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () () () User)))
    (choose
     (ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))
             (BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () () () User)))
    (choose-reborrow
     (ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))
             (BorrowedMut Int (RParam a)))
            (Borrowed Int (RParam a)) () () () User)))
    (recursive-forward
     (ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))
             (BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () () () User)))
    (left-of
     (ForallRegion (a b)
       (NFn ((BorrowedMut Int (RParam a))
             (BorrowedMut Int (RParam b)))
            (BorrowedMut Int (RParam a)) () () () User)))
    (outer
     (ForallRegion (q)
       (NFn ((BorrowedMut Int (RParam q))
             (BorrowedMut Int (RParam q)))
            Unit () (Mutation) () User)))))

(define (formal-forwarding-callable kind)
  (match kind
    ['forward-id
     '(RegionLam (a) (Lam User forward-id (x) x))]
    ['choose
     '(RegionLam (a)
        (Lam User choose (left right)
          (Eliminate (Construct Bool true)
            ((true () -> left) (false () -> right)))))]
    ['choose-reborrow
     '(RegionLam (a)
        (Lam User choose-reborrow (left right)
          (Reborrow
           (Eliminate (Construct Bool true)
             ((true () -> left) (false () -> right))))))]
    ['left-of
     '(RegionLam (a b) (Lam User left-of (left right) left))]))

(define (formal-forwarding-body kind use)
  (define single-argument? (eq? kind 'forward-id))
  (define result-is-mut?
    (memq kind '(forward-id choose left-of)))
  (define arg-names (if single-argument? '(p) '(p s)))
  (define region-args (if (eq? kind 'left-of)
                          '((RParam q) (RParam q))
                          '((RParam q))))
  (define call
    `(Apply (RegionApp ,(formal-forwarding-callable kind) ,region-args)
            ,@arg-names))
  (define borrowed-type
    (if result-is-mut?
        '(BorrowedMut Int (RParam q))
        '(Borrowed Int (RParam q))))
  (define observed-name (if result-is-mut? 'c 'r))
  (define read-observed `(Read ,observed-name))
  (define (observe body)
    (if result-is-mut?
        `(Let (c let (Borrowed Int (RVar 0))) (Reborrow r) ,body)
        body))
  (match use
    ['discard
     `(Let (r let ,borrowed-type) ,call unit)]
    ['consume
     `(Scope ()
        (Let (r let ,borrowed-type) ,call
          ,(observe `(Let (read const Int) ,read-observed unit))))]
    ['live-left
     `(Let (r let ,borrowed-type) ,call
        (Let (read const Int)
             (Scope ()
               ,(observe `(Let (written const Unit) (Assign p 7)
                            ,read-observed)))
          unit))]
    ['live-right
     `(Let (r let ,borrowed-type) ,call
        (Let (read const Int)
             (Scope ()
               ,(observe `(Let (written const Unit) (Assign s 7)
                            ,read-observed)))
          unit))]
    ['after-left
     `(Let (r let ,borrowed-type) ,call
        (Let (read const Int)
             (Scope () ,(observe read-observed))
          (Assign p 7)))]
    ['after-right
     `(Let (r let ,borrowed-type) ,call
        (Let (read const Int)
             (Scope () ,(observe read-observed))
          (Assign s 7)))]))

(define (formal-forwarding-result kind use)
  (define skeleton
    `(Scope (1 2)
       (Apply
        (RegionApp
         (RegionLam (q)
           (Lam User outer (p s)
             ,(formal-forwarding-body kind use)))
         (ph))
        (BorrowMut 1) (BorrowMut 2))))
  (define ir (build-region-ir skeleton))
  (define ρ (region->rho ir (region-at ir '(0))))
  (type-of/raw*+borrows
   (annotate-regions (replace-symbol skeleton 'ph ρ) ir)
   '((1 Int) (2 Int)) forwarding-callables '()
   (region-ctx ir '() (hash 1 (region-at ir '()) 2 (region-at ir '())) (hash))))

(define (formal-forwarding-direct-result kind)
  (define single-argument? (eq? kind 'forward-id))
  (define result-is-mut? (memq kind '(forward-id choose left-of)))
  (define region-args (if (eq? kind 'left-of) '(ph ph) '(ph)))
  (define arguments (if single-argument? '(1) '(1 2)))
  (define result-type
    (if result-is-mut? '(BorrowedMut Int ph) '(Borrowed Int ph)))
  (define observed-result
    (if result-is-mut?
        '(Let (c let (Borrowed Int ph)) (Reborrow r) (Read c))
        '(Read r)))
  (define skeleton
    `(Scope (1 2)
       (Let (r let ,result-type)
            (Apply (RegionApp ,(formal-forwarding-callable kind) ,region-args)
                   ,@(for/list ([place (in-list arguments)]) `(BorrowMut ,place)))
            ,observed-result)))
  (define ir (build-region-ir skeleton))
  (define ρ (region->rho ir (region-at ir '(0))))
  (type-of/raw*+borrows
   (annotate-regions (replace-symbol skeleton 'ph ρ) ir)
   '((1 Int) (2 Int)) forwarding-callables '()
   (region-ctx ir '() (hash 1 (region-at ir '()) 2 (region-at ir '())) (hash))))

(define (formal-forwarding-definition-result kind)
  (type-of/raw
   `(RegionLam (q)
      (Lam User outer (p s)
        ,(formal-forwarding-body kind 'discard)))
   '() forwarding-callables))

(define (formal-forwarding-result-positions kind)
  (define inference
    (typing-inference (formal-forwarding-callable kind) '() forwarding-callables))
  (append-map callable-summary-result-index (sixth inference)))

(define (formal-forwarding-borrow-keys kind)
  (match (formal-forwarding-direct-result kind)
    [(list 'ok (list _type _row _table _sigma _renamed sidecar))
     (for/set ([request (in-list (borrow-sidecar-requests sidecar))]
               #:when (eq? (borrow-request-mode request) 'shared))
       (cons (borrow-request-w request) (borrow-request-fp request)))]
    [_ (set)]))

(define (formal-forwarding-borrow-positions kind)
  (for/set ([key (in-set (formal-forwarding-borrow-keys kind))])
    (match key
      [(cons (? exact-nonnegative-integer? place) fp) (cons place fp)]
      [(cons (list 'formal _point _node index) fp) (cons index fp)]
      [_ key])))

(define (formal-forwarding-key kind use)
  (match (formal-forwarding-result kind use)
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

(define (recursive-forwarding-result use [recursive-args '(a b)])
  (define core
    `(Scope (1 2)
       (Apply
        (RegionApp
         (RegionLam (q)
           (Lam User outer (p s)
             (Recur recursive-forward rec (a b)
               (Eliminate (Construct Bool true)
                 ((true () -> a) (false () -> (Apply rec ,@recursive-args))))
               (Let (r let (BorrowedMut Int (RParam q)))
                    (Apply (RegionApp rec ((RParam q))) p s)
                 (Let (c let (Borrowed Int (RParam q))) (Reborrow r)
                   ,(match use
                      ['consume '(Let (read const Int) (Read c) unit)]
                      ['live-left
                       '(Let (written const Unit) (Assign p 7)
                          (Let (read const Int) (Read c) unit))]
                      ['live-right
                       '(Let (written const Unit) (Assign s 7)
                          (Let (read const Int) (Read c) unit))]))))))
         (ph))
        (BorrowMut 1) (BorrowMut 2))))
  (define ir (build-region-ir core))
  (define ρ (region->rho ir (region-at ir '(0))))
  (type-of/raw*+borrows
   (annotate-regions (replace-symbol core 'ph ρ) ir)
   '((1 Int) (2 Int)) forwarding-callables '()
   (region-ctx ir '() (hash 1 (region-at ir '()) 2 (region-at ir '())) (hash))))

(define (recursive-forwarding-key use [recursive-args '(a b)])
  (match (recursive-forwarding-result use recursive-args)
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

(test-case "合流した可変借用の再借用を両枝で実行でき、退場後は親から書ける"
  (for ([branch '(true false)]
        [expected-root '(0 1)]
        [expected-other '(1 0)])
    (define-values (start _sidecar _ir type)
      (prepare-all-regions (merged-reborrow-core branch (merged-reborrow-read))))
    (check-equal? type 'Unit)
    (define-values (configs rules) (trace-g2 start))
    (check-live-trace configs rules 'Unit)
    (define-values (_core heap _states _tokens _events)
      (cfg-fields (last configs)))
    (check-equal? (heap-field heap expected-root 'n) 5)
    (check-equal? (heap-field heap expected-other 'n)
                  (if (zero? expected-other) 1 2))))

(test-case "再借用の停止窓は両所有者の Move と親経由の書込みを拒む"
  (for ([owner '(x y)])
    (check-equal?
     (failure-key (merged-reborrow-core 'true (merged-reborrow-move owner)))
     'move-borrowed
     (format "~a は子が生きている間 Move できない" owner)))
  (check-equal?
   (failure-key (merged-reborrow-core 'true (merged-reborrow-parent-write)))
   'borrow-conflicting-use))

(test-case "期限切れの同一 capability を先に借りても通常の再借用を選べる"
  (define-values (start _sidecar _ir type)
    (prepare-all-regions (stale-reborrow-core #f (merged-reborrow-read))))
  (check-equal? type 'Int)
  (define-values (configs rules) (trace-g2 start))
  (check-live-trace configs rules 'Int)
  (define-values (_core heap _states _tokens _events) (cfg-fields (last configs)))
  (check-equal? (heap-field heap 0 'n) 5))

(test-case "合流の片枝に期限切れの同一 capability があってもその枝の alpha を選ぶ"
  (for ([branch '(true false)] [root '(0 1)] [other '(1 0)])
    (define-values (start _sidecar _ir type)
      (prepare-all-regions (stale-reborrow-core branch (merged-reborrow-read))))
    (check-equal? type 'Int)
    (define-values (configs rules) (trace-g2 start))
    (check-live-trace configs rules 'Int)
    (define-values (_core heap _states _tokens _events) (cfg-fields (last configs)))
    (check-equal? (heap-field heap root 'n) 5)
    (check-equal? (heap-field heap other 'n) (if (zero? other) 1 2))))

(test-case "期限切れの同一 capability が先にあっても再借用中の親書込みは拒む"
  (check-equal?
   (failure-key (stale-reborrow-core #f (merged-reborrow-parent-write)))
   'borrow-conflicting-use))

(test-case "生存中の左右と退場後の観測で候補位置を保つ"
  (check-true
   (match (formal-forwarding-definition-result 'forward-id)
     [`(ok (,type ,_row))
      (match type [`(ForallRegion ,_ ,_) #t] [_ #f])]
     [_ #f]))
  (check-equal? (formal-forwarding-result-positions 'forward-id) '(0))
  (check-equal? (formal-forwarding-result-positions 'choose) '(0 1))
  (check-equal? (formal-forwarding-result-positions 'left-of) '(0))
  (check-false (formal-forwarding-key 'forward-id 'live-right))
  (check-equal? (formal-forwarding-key 'forward-id 'live-left)
                'borrow-conflicting-use)
  (check-equal? (formal-forwarding-key 'choose 'live-left)
                'borrow-conflicting-use)
  (check-equal? (formal-forwarding-key 'choose 'live-right)
                'borrow-conflicting-use)
  (check-equal? (formal-forwarding-key 'choose-reborrow 'live-left)
                'borrow-conflicting-use)
  (check-equal? (formal-forwarding-key 'choose-reborrow 'live-right)
                'borrow-conflicting-use)
  (check-equal? (formal-forwarding-key 'left-of 'live-left)
                'borrow-conflicting-use)
  (check-false (formal-forwarding-key 'left-of 'live-right))
  ;; 外側の r は RParam q の lexical loan のまま残るため、対象位置への
  ;; 退場後の書込みは現状 E-BOR-025。非候補位置は受理する。
  (for ([case (in-list
               '((forward-id after-left borrow-conflicting-use)
                 (forward-id after-right #f)
                 (choose after-left borrow-conflicting-use)
                 (choose after-right borrow-conflicting-use)
                 (choose-reborrow after-left borrow-conflicting-use)
                 (choose-reborrow after-right borrow-conflicting-use)
                 (left-of after-left borrow-conflicting-use)
                 (left-of after-right #f)))])
    (match-define (list kind use expected) case)
    (check-equal? (formal-forwarding-key kind use) expected
                  (format "~a / ~a" kind use)))
  (check-equal? (formal-forwarding-borrow-positions 'choose)
                (set (cons 1 '()) (cons 2 '())))
  (check-equal? (formal-forwarding-borrow-positions 'left-of)
                (set (cons 1 '()))))

(test-case "仮の再帰呼出しは frame の候補位置を転送し根の制約を保つ"
  (check-false (recursive-forwarding-key 'consume))
  (check-equal? (recursive-forwarding-key 'live-left) 'borrow-conflicting-use)
  (check-equal? (recursive-forwarding-key 'live-right) 'borrow-conflicting-use)
  (check-equal? (recursive-forwarding-key 'consume '(b a))
                'unresolved-borrow-owner))

(test-case "合流した可変借用からの射影は選んだ field だけを書き換える"
  (for ([branch '(true false)]
        [expected-root '(0 1)]
        [expected-before '(1 2)]
        [expected-final '((5 2) (1 5))])
    (define-values (start _sidecar _ir type) (prepare (merged-mut-core branch)))
    (define-values (configs rules) (trace-g2 start))
    (check-live-trace configs rules type)
    (define-values (core heap _states _tokens _events)
      (cfg-fields (config-after configs rules 'R-ProjBorrowMut)))
    (match (borrow-refs core)
      [(list `(BorrowMutRef ,root (n) ,token)
             `(BorrowMutRef ,same-root () ,same-token))
       (check-equal? root expected-root)
       (check-equal? same-root root)
       (check-equal? same-token token)
       (check-equal? (heap-field heap root 'n) expected-before)]
      [refs (fail (format "射影先と元の BorrowMutRef を期待した: ~s" refs))])
    (define-values (_final-core final-heap _final-states _final-tokens _final-events)
      (cfg-fields (last configs)))
    (check-equal? (list (heap-field final-heap 0 'n)
                        (heap-field final-heap 1 'n))
                  expected-final)))

(test-case "同じ owner の合流後の射影も実行できる"
  (define-values (start _sidecar _ir type)
    (prepare (merged-shared-core 'true 'x 'x)))
  (define-values (configs rules) (trace-g2 start))
  (check-equal? type 'Int)
  (check-live-trace configs rules 'Int)
  (check-equal? (cfg-core (last configs)) 1))

(test-case "再借用と射影の machine rule は入力借用値から capability を作る"
  (check-equal?
   (apply-reduction-relation
    -->g2
    '(cfg (ReborrowAt 0 (BorrowMutRef 7 () 1)) () () () ()))
   '((cfg (BorrowRef 7 () 0) () () () ())))
  (check-equal?
   (apply-reduction-relation
    -->g2
    '(cfg (ProjBorrowAt 0 (BorrowRef 7 () 1) n) () () () ()))
   '((cfg (BorrowRef 7 (n) 1) () () () ())))
  (check-equal?
   (apply-reduction-relation
    -->g2
    '(cfg (ProjBorrowAt 0 (BorrowMutRef 7 () 1) n)
          ((7 (Rec ((n mut 1))) (declared (Owned (Record ((n Int mut)))))))
          ((7 Available)) () ()))
   '((cfg (BorrowMutRef 7 (n) 1)
          ((7 (Rec ((n mut 1))) (declared (Owned (Record ((n Int mut)))))))
          ((7 Available)) () ()))))

(test-case "直接の BorrowAt と BorrowMutAt の own 不一致は E-BOR-023 のまま拒否する"
  (for ([form '(BorrowAt BorrowMutAt)])
    (define core `(Scope (1) (,form 0 (Own 7 ()) 1)))
    (define result
      (type-of/raw core '((1 Int)) '() '() (empty-region-ctx)))
    (check-equal? (first result) 'fail)
    (check-equal? (second result) 'own-designator-mismatch))
  (for ([form '(BorrowAt BorrowMutAt)])
    (define cfg
      `(cfg (Read (,form 4 (Own 1 ()) 0))
            ((0 7 (declared Int)) (1 8 (declared Int)))
            ((0 Available) (1 Available)) () ()))
    (check-false (config-ok? cfg '() 'Int '()))))

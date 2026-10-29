#lang racket

(require rackunit
         racket/list
         racket/match
         racket/set
         "../backend-matrix.rkt"
         "../borrow.rkt"
         "../region-param.rkt"
         "../region.rkt"
         "../typing.rkt")

(define g2-only-heads
  (set 'Absent 'RecRewriteOpen 'Borrow 'BorrowMut 'Reborrow 'ProjBorrow
       'Read 'Assign 'Reassign 'RegionLam 'RegionApp 'AddressOf 'PtrOffset
       'RawLoad 'RawStore 'FromRawPtr 'Unsafe 'MutSlot 'BorrowAt 'BorrowMutAt
       'ReborrowAt 'ProjBorrowAt 'BorrowRef 'BorrowMutRef 'PtrVal))

(define leaf-exit-sites-expected
  (set (list 'Apply '(from 1) 'formal)
       (list 'Assign 0 'local)
       (list 'Assign 1 'storage)
       (list 'AddressOf 0 'yield)
       (list 'Curry 1 'capture)
       (list 'Curry 0 'transit)
       (list 'Construct '(from 0) 'transit)
       (list 'Drop 0 'local)
       (list 'Discharge 0 'transit)
       (list 'Eliminate 0 'transit)
       (list 'Eliminate '(from 1) 'transit)
       (list 'EliminateAt 0 'transit)
       (list 'EliminateAt '(from 1) 'transit)
       (list 'Handle 0 'transit)
       (list 'Handle 1 'transit)
       (list 'Lam 0 'transit)
       (list 'Let 0 'transit)
       (list 'Let 1 'transit)
       (list 'OwnLeaf 0 'transit)
       (list 'OwnedLeaf 0 'transit)
       (list 'OwnedTransit 0 'transit)
       (list 'Perform 0 'handle)
       (list 'Proj 0 'transit)
       (list 'ProjBorrow 0 'transit)
       (list 'ProjBorrowAt 0 'transit)
       (list 'ProjOpt 0 'transit)
       (list 'RVal 0 'transit)
       (list 'Reborrow 0 'transit)
       (list 'ReborrowAt 0 'transit)
       (list 'Rec '(from 0) 'transit)
       (list 'RecRewrite 0 'transit)
       (list 'RecRewrite '(from 1) 'transit)
       (list 'RecRewriteOpen '(from 0) 'transit)
       (list 'Recur 0 'transit)
       (list 'Recur 1 'transit)
       (list 'RecurVal 0 'transit)
       (list 'RegionApp 0 'transit)
       (list 'RegionLam 0 'transit)
       (list 'Read 0 'local)
       (list 'Reassign 0 'storage)
       (list 'Scope 0 'transit)
       (list 'Suspend 0 'transit)
       (list 'UVal 0 'transit)
       (list 'UnionEliminate 0 'transit)
       (list 'UnionEliminate '(from 1) 'transit)
       (list 'UnionEliminateAt 0 'transit)
       (list 'UnionEliminateAt '(from 1) 'transit)
       (list 'UnionInject 0 'transit)
       (list 'UnionVal 0 'transit)
       (list 'Unsafe 0 'transit)
       (list 'Yield 0 'yield)
       (list 'Yield 1 'transit)
       (list 'CurryVal 0 'transit)
       (list 'CurryVal 1 'capture)))

(define leaf-exit-heads-expected
  (set-union (list->set (map first core-form-features)) g2-only-heads))

(define (flatten-sites table)
  (for*/set ([(head sites) (in-hash table)]
             [site (in-list sites)])
    (list head (car site) (cdr site))))

(define (descriptor-samples descriptor)
  (match descriptor
    [(? exact-nonnegative-integer? k) (list (list k) (list k 0))]
    [`(from ,(? exact-nonnegative-integer? k))
     (list (list k) (list (add1 k)))]
    [(list segments ...)
     (define samples
       (for/fold ([prefixes (list '())]) ([segment (in-list segments)])
         (for*/list ([prefix (in-list prefixes)]
                     [suffix (in-list (descriptor-samples segment))])
           (append prefix suffix))))
     (take samples (min 2 (length samples)))]))

(define (sample-points-for _head sites)
  (append-map
   (lambda (site)
     (descriptor-samples (car site)))
   sites))

(test-case "出口の位置の一覧は Core の全 head を覆う"
  (check-false (set-empty? g2-only-heads) "G2 の head が空")
  (check-equal? (list->set (hash-keys leaf-exit-sites))
                leaf-exit-heads-expected))

(test-case "出口の位置の一覧は期待の表と子の位置まで一致する"
  (check-false (set-empty? leaf-exit-sites-expected) "期待の表が空")
  (define actual (flatten-sites leaf-exit-sites))
  (check-equal? (set-subtract leaf-exit-sites-expected actual) (set)
                "本体の表から漏れた位置")
  (check-equal? (set-subtract actual leaf-exit-sites-expected) (set)
                "期待の表に無い位置"))

(test-case "出口の位置の一覧は七つの出口と transit だけを使い unclassified を含まない"
  (for* ([(head sites) (in-hash leaf-exit-sites)]
         [site (in-list sites)])
    (check-not-false (memq (cdr site)
                           '(local result formal handle yield capture storage transit))
                     (format "~a の位置 ~a" head site))))

(test-case "Apply の callee 位置は transit にせず unclassified にする"
  (check-false
   (for/or ([site (in-list (hash-ref leaf-exit-sites 'Apply))])
     (site-position-matches? (car site) '(0)))))

(test-case "一つの head の中で一つの実際の位置に当てはまる記述子は高々一つである"
  (for ([(head sites) (in-hash leaf-exit-sites)])
    (define samples (sample-points-for head sites))
    (check-true
     (for/and ([site (in-list sites)])
       (>= (length (descriptor-samples (car site))) 2))
     (format "~a の各記述子に二つ以上の位置を試す" head))
    (for ([point (in-list samples)])
      (check-true
       (<= (count (lambda (site) (site-position-matches? (car site) point)) sites)
           1)
       (format "~a の位置 ~a" head point)))))

(test-case "入れ子の位置記述子は各 level の実 index と照合する"
  (check-true (site-position-matches? '((from 1) 0) '(2 0 4)))
  (check-false (site-position-matches? '((from 1) 0) '(2 1 4))))

(test-case "出口イベントの挿入順が違っても summary は等しい"
  (define a (deferred-leaf-exit '(formal 0 ()) 0 '() '() 'shared
                                '(RParam a) '() 'local #f))
  (define b (deferred-leaf-exit '(formal 0 ()) 0 '() '() 'shared
                                '(RParam b) '() 'local #f))
  (check-equal? (normalize-leaf-exits (list a b))
                (normalize-leaf-exits (list b a))))

(define borrowed-int '(Borrowed Int (RParam a)))
(define reader-type
  '(ForallRegion (a)
     (NFn ((Borrowed Int (RParam a))) Int () () () User)))
(define outer-type reader-type)
(define returner-type
  '(ForallRegion (a)
     (NFn ((Borrowed Int (RParam a))) (Borrowed Int (RParam a)) () () () User)))

(define binder-owner-type
  '(Record ((g Int mut) (o (Option Int) mut))))
(define binder-reader-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,binder-owner-type (RParam a)))
          Int () (Mutation) () User)))
(define binder-returner-type
  `(ForallRegion (a)
     (NFn ((BorrowedMut ,binder-owner-type (RParam a)))
          (BorrowedMut Int (RParam a)) () (Mutation) () User)))
(define binder-owner-value
  '(Rec ((g mut 1) (o mut (Construct (Option Int) some 2)))))
(define (binder-reader-core some-body [none-body 0])
  `(Scope (1)
     (RegionLam (a)
       (Lam User binder-reader (p)
         (Eliminate (ProjBorrow p o)
           ((some (c) -> ,some-body)
            (none () -> ,none-body)))))))
(define (binder-source? exit)
  (match (deferred-leaf-exit-source exit)
    [`(binder ,_ ...) #t]
    [_ #f]))
(define (binder-events summary)
  (filter binder-source? (callable-summary-leaf-exits summary)))

(define (binder-reader-body some-body [none-body 0])
  `(Eliminate (ProjBorrow p o)
     ((some (c) -> ,some-body)
      (none () -> ,none-body))))

(define (summaries core callables)
  (define ir (build-region-ir core))
  (sixth
   (typing-inference (annotate-regions core ir)
                     '((1 Int)) callables '()
                     (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))))

(define (exit-shape exit)
  (match exit
    [(deferred-leaf-exit source formal-index parent-path binder-path mode _alpha
                         body-point exit-kind destination)
     (list source formal-index parent-path binder-path mode body-point
           exit-kind destination)]))

(test-case "一覧にない出口位置へ流れる formal の葉を unclassified として記録する"
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User reader (x) (Read x)))))
  (for ([sites (in-list (list (hash-set leaf-exit-sites 'Read '())
                              (hash-remove leaf-exit-sites 'Read)))])
    (define all-summaries
      (parameterize ([current-leaf-exit-sites sites])
        (summaries core `((reader ,reader-type)))))
    (define event
      (for*/first ([summary (in-list all-summaries)]
                   [exit (in-list (callable-summary-leaf-exits summary))]
                   #:when (eq? (deferred-leaf-exit-exit-kind exit) 'unclassified))
        exit))
    (check-not-false event)
    (check-false (deferred-leaf-exit-destination event))))

(test-case "RecurVal の枠の往復で formal の出口イベントを落とさない"
  (define recur-reader-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) Int () () () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (RecurVal recur-reader f (x) (Read x)))))
  (define all-summaries
    (summaries core `((recur-reader ,recur-reader-type))))
  (check-true (pair? all-summaries) (format "summaries: ~s" all-summaries))
  (define summary (first all-summaries))
  (define direct-summary
    (first
     (summaries '(Scope (1)
                   (RegionLam (a) (Lam User recur-reader (x) (Read x))))
                `((recur-reader ,recur-reader-type)))))
  (check-equal?
   (map exit-shape (callable-summary-leaf-exits summary))
   (map exit-shape (callable-summary-leaf-exits direct-summary))))

(test-case "Recur の枠の往復で formal の出口イベントを落とさない"
  (define recur-reader-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))) Int () () () User)))
  (define continuation-type
    '(NFn ((BorrowedMut Int (RParam a))) Int () () () User))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Recur recur-reader f (x)
                (Let (t let Int) (Read x) (Apply f x))
                (Lam User continuation (y)
                  (Apply (RegionApp f ((RParam a))) y))))))
  (define all-summaries
    (summaries core `((recur-reader ,recur-reader-type)
                      (continuation ,continuation-type))))
  (define recur-summary
    (for/first ([summary (in-list all-summaries)]
                #:when (for/or ([exit (in-list (callable-summary-leaf-exits summary))])
                         (eq? (deferred-leaf-exit-exit-kind exit) 'local)))
      summary))
  (define direct-summary
    (first (summaries '(Scope (1)
                         (RegionLam
                          (a)
                          (RecurVal recur-reader f (x)
                            (Let (t let Int) (Read x) (Apply f x)))))
                      `((recur-reader ,recur-reader-type)))))
  (check-not-false recur-summary
                   (format "summaries: ~s" (map callable-summary-leaf-exits all-summaries)))
  (check-equal? (map exit-shape (callable-summary-leaf-exits recur-summary))
                (map exit-shape (callable-summary-leaf-exits direct-summary))))

(test-case "Let の束縛式と body は formal の葉を通過させる"
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User reader (x)
           (Let (read-result let Int) (Read x) x)))))
  (define summary (first (summaries core `((reader ,returner-type)))))
  (check-equal?
   (for/set ([event (in-list (callable-summary-leaf-exits summary))])
     (deferred-leaf-exit-exit-kind event))
   (set 'local 'result)))

(test-case "分解の枝は formal の葉を通過させ、結果出口を本体の根だけに記録する"
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User identity (x)
           (Eliminate (Construct Bool true)
             ((true () -> x)
              (false () -> x)))))))
  (define summary (first (summaries core `((identity ,returner-type)))))
  (define results
    (filter (lambda (event) (eq? (deferred-leaf-exit-exit-kind event) 'result))
            (callable-summary-leaf-exits summary)))
  (check-equal? (length results) 1)
  (check-equal? (deferred-leaf-exit-source (first results)) '(formal 0 ())))

(test-case "入れ子 Lam は自由な仮引数を capture として一度だけ記録する"
  (define inner-type
    '(NFn () (Borrowed Int (RParam a)) () () () User))
  (define capturing-outer-type
    `(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) ,inner-type () () () User)))
  (define inner-lam '(Lam User inner () x))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User outer (x)
           (Lam User inner () x)))))
  (define outer-summary
    (for/first ([summary (in-list
                          (summaries core
                                     `((outer ,capturing-outer-type)
                                       (inner ,inner-type))))]
                #:when (= (length (callable-summary-formals summary)) 1))
      summary))
  (define captures
    (filter (lambda (event)
              (and (equal? (deferred-leaf-exit-source event) '(formal 0 ()))
                   (eq? (deferred-leaf-exit-exit-kind event) 'capture)))
            (callable-summary-leaf-exits outer-summary)))
  (check-not-false outer-summary)
  (check-equal? (length captures) 1)
  (check-equal? (deferred-leaf-exit-destination (first captures)) inner-lam))

(test-case "行き先の表が空のときは unclassified の印を残す"
  ;; well-typed な値は引数・結果の宣言型と整合するため、空対応は helper で固定する。
  (define choices (list (list 'result '())
                        (list 'formal '())
                        (list 'handle '())))
  (for ([choice (in-list choices)])
    (check-equal? (leaf-exit-destinations (first choice) (second choice))
                  (list (list 'unclassified #f)))))

(test-case "署名だけの要約は記録漏れの印を持つ"
  (define summary
    (signature-forwarding-summary
     (list '(BorrowedMut Int (RParam a)))
     '(BorrowedMut Int (RParam a))
     'apply-unknown-summary
     (lambda (key node) (error 'unexpected-failure "~a at ~a" key node))))
  (check-true (callable-summary-incomplete? summary)))

(test-case "capability の取得例外は callable summary に記録漏れを残す"
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User reader (x) (Read x)))))
  (define all-summaries
    (parameterize ([current-leaf-exit-capability-reader
                    (lambda (_Λ _expression)
                      (error 'probe "強制した capability 取得失敗"))])
      (summaries core `((reader ,reader-type)))))
  (check-true (pair? all-summaries))
  (check-true (callable-summary-incomplete? (first all-summaries)))
  (define recur-summaries
    (parameterize ([current-leaf-exit-capability-reader
                    (lambda (_Λ _expression)
                      (error 'probe "強制した capability 取得失敗"))])
      (summaries '(Scope (1)
                   (RegionLam (a)
                     (RecurVal reader f (x) (Read x))))
                 `((reader ,reader-type)))))
  (check-true (pair? recur-summaries))
  (check-true (callable-summary-incomplete? (first recur-summaries))))

(test-case "Recur で読み切る枝と再帰結果を返す枝の formal 出口を併せて記録する"
  (define recurrent-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () () () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Recur recur-reader f (x)
           (Eliminate (Construct Bool true)
             ((true () -> (Let (read-result let Int) (Read x) x))
              (false () -> (Apply f x))))
           (Lam User continuation (y)
             (Apply (RegionApp f ((RParam a))) y))))))
  (define all-summaries
    (summaries core `((recur-reader ,recurrent-type)
                      (continuation ,recurrent-type))))
  (define summary
    (for/first ([candidate (in-list all-summaries)]
                #:when
                (let ([events (callable-summary-leaf-exits candidate)])
                  (for/or ([local (in-list events)]
                           #:when (eq? (deferred-leaf-exit-exit-kind local) 'local))
                    (for/or ([result (in-list events)]
                             #:when (eq? (deferred-leaf-exit-exit-kind result) 'result))
                      (equal? (deferred-leaf-exit-source local)
                              (deferred-leaf-exit-source result))))))
      candidate))
  (check-not-false summary
                   (format "summaries: ~s"
                           (map callable-summary-leaf-exits all-summaries))))

(test-case "出口イベントを持つ summary を呼出し側で読み飛ばせる"
  (define inner-type
    '(ForallRegion (b)
       (NFn ((Borrowed Int (RParam b))) Int () () () User)))
  (define outer-type
    '(ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) Int () () () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User outer (p)
           (Apply
            (RegionApp
             (RegionLam (b) (Lam User inner (x) (Read x)))
             ((RParam a)))
            p)))))
  (define all-summaries
    (summaries core `((outer ,outer-type) (inner ,inner-type))))
  (check-true (pair? all-summaries))
  (check-true
   (for/or ([summary (in-list all-summaries)])
     (for/or ([exit (in-list (callable-summary-leaf-exits summary))])
       (eq? (deferred-leaf-exit-exit-kind exit) 'local)))))

(test-case "RegionApp 後も Union member を通る formal の葉を解決できる"
  (define (union-of a b)
    `(Union (Borrowed Int (RParam ,a)) (Borrowed Bool (RParam ,b))))
  (define reader-type
    `(ForallRegion (x y)
       (NFn (,(union-of 'x 'y)) Int () () () User)))
  (define core
    '(Scope (1)
       (RegionLam (a b)
         (RegionApp
          (RegionLam (x y)
            (Lam User union-reader (u)
              (UnionEliminate u
                (((Borrowed Int (RParam x)) left ->
                  (Let (discard let Int) (Read left) 0))
                 ((Borrowed Bool (RParam y)) right ->
                  (Let (discard let Bool) (Read right) 0))))))
          ((RParam a) (RParam b))))))
  (define all-summaries
    (summaries core `((union-reader ,reader-type))))
  (define summary
    (for/first ([candidate (in-list all-summaries)]
                #:when (positive? (hash-count
                                   (callable-summary-region-subst candidate)))
                #:when (pair? (callable-summary-leaf-exits candidate)))
      candidate))
  (check-not-false summary (format "summaries: ~s" all-summaries))
  (define event (first (callable-summary-leaf-exits summary)))
  (define path (deferred-leaf-exit-parent-path event))
  (check-equal? (deferred-leaf-exit-source event) (list 'formal 0 path))
  (define formal-entry
    (hash-ref (first (callable-summary-formal-fields summary)) path))
  (check-equal? (deferred-leaf-exit-alpha event)
                (capability-entry-declared-lifetime formal-entry))
  (define formal-paths
    (hash-keys (first (callable-summary-formal-fields summary))))
  (define actual-members
    (map (lambda (member-type)
           (subst-region-params member-type
                                (callable-summary-region-subst summary)))
         (map first formal-paths)))
  (define actual-type `(Union ,(first actual-members) ,(second actual-members)))
  (define actual-path
    (instantiate-capability-path actual-type path
                                 (callable-summary-region-subst summary)))
  (check-not-false actual-path)
  (define-values (_actual-root actual-leaves)
    (formal-capability-entry actual-type 'actual))
  (define actual-entry
    (struct-copy capability-entry (hash-ref actual-leaves actual-path)
                 [source-alphas (set '(RVar 7))]))
  (define-values (declared-alpha source-alphas)
    (formal-leaf-info summary 0 path actual-entry))
  (check-equal? declared-alpha (deferred-leaf-exit-alpha event))
  (check-equal? source-alphas (set '(RVar 7))))

(test-case "仮引数の葉を読み切る Lam は formal 起点の local の出口を一つ記録する"
  (define core
    '(Scope (1) (RegionLam (a) (Lam User reader (x) (Read x)))))
  (define summary (first (summaries core `((reader ,reader-type)))))
  (define exits (callable-summary-leaf-exits summary))
  (define formal-entry
    (hash-ref (first (callable-summary-formal-fields summary)) '()))
  (check-equal? (length exits) 1)
  (check-equal? (deferred-leaf-exit-source (first exits)) '(formal 0 ()))
  (check-equal? (deferred-leaf-exit-exit-kind (first exits)) 'local)
  (check-equal? (deferred-leaf-exit-alpha (first exits))
                (capability-entry-declared-lifetime formal-entry)))

(test-case "仮引数を親に持つ分解 binder は binder 起点の local 出口を一つ記録する"
  (define summary (first (summaries (binder-reader-core '(Read c))
                                    `((binder-reader ,binder-reader-type)))))
  (define exits (binder-events summary))
  (check-equal? (length exits) 1)
  (check-equal? (deferred-leaf-exit-formal-index (first exits)) 0)
  (check-eq? (deferred-leaf-exit-exit-kind (first exits)) 'local)
  (check-true (lifetime-var? (deferred-leaf-exit-alpha (first exits)))))

(test-case "仮引数を親に持つ分解 binder を結果へ返すと binder 起点の result 出口を記録する"
  (define summary
    (first (summaries (binder-reader-core 'c '(ProjBorrow p g))
                      `((binder-reader ,binder-returner-type)))))
  (define exits
    (filter (lambda (exit)
              (eq? (deferred-leaf-exit-exit-kind exit) 'result))
            (binder-events summary)))
  (check-equal? (length exits) 1)
  (check-equal? (deferred-leaf-exit-formal-index (first exits)) 0)
  (check-equal? (deferred-leaf-exit-destination (first exits)) '()))

(test-case "Recur の枠の往復で binder 起点の出口イベントを落とさない"
  (define body (binder-reader-body '(Read c)))
  (define recur-summary
    (for/first ([summary
                 (in-list
                  (summaries
                   `(Scope (1)
                      (RegionLam (a)
                        (RecurVal binder-reader f (p) ,body)))
                   `((binder-reader ,binder-reader-type))))]
                #:when (pair? (binder-events summary)))
      summary))
  (define direct-summary
    (for/first ([summary
                 (in-list
                  (summaries
                   `(Scope (1)
                      (RegionLam (a)
                        (Lam User binder-reader (p) ,body)))
                   `((binder-reader ,binder-reader-type))))]
                #:when (pair? (binder-events summary)))
      summary))
  (check-not-false recur-summary)
  (check-not-false direct-summary)
  (when (and recur-summary direct-summary)
    (check-equal? (map exit-shape (binder-events recur-summary))
                  (map exit-shape (binder-events direct-summary)))))

(test-case "Recur で読み切る枝と再帰結果を返す枝の binder 出口を併せて記録する"
  (define recursive-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut (Option Int) (RParam a))
             (BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () (Mutation) () User)))
  (define body
    '(Eliminate parent
        ((some (child) ->
          (Let (read-result let Int) (Read child) child))
        (none () -> (Apply f parent fallback)))))
  (define core
    `(Scope (1)
       (RegionLam (a)
         (Recur binder-reader f (parent fallback)
           ,body
           (Lam User continuation (next-parent next-fallback)
             (Apply (RegionApp f ((RParam a))) next-parent next-fallback))))))
  (define all-summaries
    (summaries core `((binder-reader ,recursive-type)
                      (continuation ,recursive-type))))
  (define summary
    (for/first ([candidate (in-list all-summaries)]
                #:when
                (let ([events (binder-events candidate)])
                  (and (for/or ([event (in-list events)])
                         (eq? (deferred-leaf-exit-exit-kind event) 'local))
                       (for/or ([event (in-list events)])
                         (eq? (deferred-leaf-exit-exit-kind event) 'result)))))
      candidate))
  (check-not-false summary
                   (format "summary events: ~s"
                           (map callable-summary-leaf-exits all-summaries))))

(test-case "局所 owner を親に持つ分解 binder は binder 起点の local 出口を記録する"
  (define local-reader-type '(NFn (Unit) Int () () () User))
  (define core
    `(Scope (1)
       (Lam User local-reader (ignored)
         (Let (owner let (Owned ,binder-owner-type)) ,binder-owner-value
           (Let (p let (BorrowedMut ,binder-owner-type (RParam %omitted)))
             (BorrowMut owner)
             ,(binder-reader-body '(Read c)))))))
  (define all-summaries
    (summaries core `((local-reader ,local-reader-type))))
  (define exits
    (append-map binder-events all-summaries))
  (check-equal? (length exits) 1)
  (check-eq? (deferred-leaf-exit-exit-kind (first exits)) 'local))

(test-case "Lam 本体の根に置いた自身の仮引数は capture にせず result として記録する"
  (define inner-type
    '(NFn ((BorrowedMut Int (RParam a)))
          (BorrowedMut Int (RParam a)) () () () User))
  (define outer-type
    `(ForallRegion (a) (NFn () ,inner-type () () () User)))
  (define all-summaries
    (summaries
     '(Scope (1)
        (RegionLam (a)
          (Lam User outer ()
            (Lam User inner (y) y))))
     `((outer ,outer-type) (inner ,inner-type))))
  (define inner-summary
    (for/first ([summary (in-list all-summaries)]
                #:when
                (for/or ([exit (in-list (callable-summary-leaf-exits summary))])
                  (and (equal? (deferred-leaf-exit-source exit) '(formal 0 ()))
                       (eq? (deferred-leaf-exit-exit-kind exit) 'result))))
      summary))
  (check-not-false inner-summary)
  (when inner-summary
    (check-false
     (for/or ([exit (in-list (callable-summary-leaf-exits inner-summary))])
       (eq? (deferred-leaf-exit-exit-kind exit) 'capture)))
    (check-true
     (for/or ([exit (in-list (callable-summary-leaf-exits inner-summary))])
       (and (equal? (deferred-leaf-exit-source exit) '(formal 0 ()))
            (eq? (deferred-leaf-exit-exit-kind exit) 'result))))))

(test-case "仮引数の葉を Return payload にする Lam は handle の出口を記録する"
  (define return-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a))) Never ()
            ((Return boundary (Borrowed Int (RParam a)))) () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User return-borrow (p)
           (Perform (Return boundary (Borrowed Int (RParam a)))
                    (Reborrow p))))))
  (define summary
    (first (summaries core `((return-borrow ,return-type)))))
  (define handle-exits
    (filter (lambda (exit) (eq? (deferred-leaf-exit-exit-kind exit) 'handle))
            (callable-summary-leaf-exits summary)))
  (check-equal? (length handle-exits) 1)
  (check-equal? (deferred-leaf-exit-source (first handle-exits)) '(formal 0 ()))
  (check-equal? (deferred-leaf-exit-destination (first handle-exits))
                '(Return ())))

(test-case "仮引数の葉を結果へ返す Lam は formal 起点の result の出口を記録する"
  (define core '(Scope (1) (RegionLam (a) (Lam User id (x) x))))
  (define summary (first (summaries core `((id ,returner-type)))))
  (define exits (callable-summary-leaf-exits summary))
  (check-true
   (for/or ([exit (in-list exits)])
     (and (equal? (deferred-leaf-exit-source exit) '(formal 0 ()))
          (eq? (deferred-leaf-exit-exit-kind exit) 'result)
          (equal? (deferred-leaf-exit-destination exit) '())))))

(test-case "Apply の第二の実引数に置いた仮引数の葉も formal の出口として記録する"
  ;; 二つ目の引数の point は関数を 0 番として数え、index 2 になる。
  (define pair-type
    '(ForallRegion (a)
       (NFn (Int (Borrowed Int (RParam a))) Int () () () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User outer (x)
           (Apply (RegionApp
                   (RegionLam (a) (Lam User sink (p q) 0))
                   ((RParam a)))
                  0 x)))))
  (define all-summaries
    (summaries core `((outer ,outer-type) (sink ,pair-type))))
  (define events
    (for*/list ([summary (in-list all-summaries)]
                [exit (in-list (callable-summary-leaf-exits summary))]
                #:when (equal? (deferred-leaf-exit-source exit) '(formal 0 ())))
      exit))
  (check-equal? (length events) 1
              (format "summaries: ~s"
                      (map callable-summary-leaf-exits all-summaries)))
  (check-eq? (deferred-leaf-exit-exit-kind (first events)) 'formal)
  (check-equal? (deferred-leaf-exit-destination (first events)) '(1 ())))

(test-case "異なる仮引数を親に持つ binder は unclassified にして閉じる"
  (define two-parent-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut (Option Int) (RParam a))
             (BorrowedMut (Option Int) (RParam a)))
            Int () (Mutation) () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User two-parent (left right)
           (Eliminate
            (Eliminate (Construct Bool true)
              ((true () -> left)
               (false () -> right)))
            ((some (child) -> (Read child))
             (none () -> 0)))))))
  (define all-summaries
    (summaries core `((two-parent ,two-parent-type))))
  (define exits (append-map binder-events all-summaries))
  (check-equal? (length exits) 1)
  (check-eq? (deferred-leaf-exit-exit-kind (first exits)) 'unclassified)
  (check-false (deferred-leaf-exit-destination (first exits))))

(test-case "Let を挟んだ分解 binder の合流結果も result 出口として記録する"
  (define merge-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut (Result (Option Int) (Option Int)) (RParam a)))
            (BorrowedMut (Option Int) (RParam a)) () (Mutation) () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User merge-result (parent)
           (Let (merged let (BorrowedMut (Option Int) (RParam %omitted)))
             (Eliminate parent
               ((ok (left) -> left)
                (ng (right) -> right)))
             merged)))))
  (define ir (build-region-ir core))
  (define analysis
    (typing-inference (annotate-regions core ir)
                      '((1 Int)) `((merge-result ,merge-type)) '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (define all-summaries (sixth analysis))
  (define typed (core-type-of/regions core '() `((merge-result ,merge-type))))
  (define events (append-map binder-events all-summaries))
  (check-true (pair? events)
              (format "type: ~s, summaries: ~s, binder alphas: ~s"
                      (first analysis)
                      (map callable-summary-leaf-exits all-summaries)
                      (and (region-typed? typed)
                           (region-typed-binder-alphas typed))))
  (check-true
   (for/or ([event (in-list events)])
     (eq? (deferred-leaf-exit-exit-kind event) 'result))))

(test-case "分解 binder の合流結果を Apply に渡す形は owner 未解決で閉じる"
  (define observer-type
    '(NFn ((BorrowedMut (Option Int) (RParam a))) Int () () () User))
  (define parent-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut (Result (Option Int) (Option Int)) (RParam a))
             ,observer-type)
            Int () (Mutation) () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User merge-argument (parent observer)
           (Let (merged let (BorrowedMut (Option Int) (RParam %omitted)))
             (Eliminate parent
               ((ok (left) ->
                 (Scope ()
                   (Let (left-view let
                                   (BorrowedMut (Option Int) (RParam a)))
                     left left-view)))
                (ng (right) ->
                 (Scope ()
                    (Let (right-view let
                                    (BorrowedMut (Option Int) (RParam a)))
                     right right-view)))))
             (Apply observer merged))))))
  (check-exn #rx"unresolved-borrow-owner"
             (lambda ()
               (summaries core `((merge-argument ,parent-type))))))

(test-case "分解 binder の合流結果を閉包が捕捉する形は境界で拒否する"
  (define inner-type
    '(NFn () (BorrowedMut (Option Int) (RParam a)) () () () User))
  (define outer-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut (Result (Option Int) (Option Int)) (RParam a)))
            ,inner-type () (Mutation) () User)))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User merge-capture (parent)
           (Let (merged let (BorrowedMut (Option Int) (RParam %omitted)))
             (Eliminate parent
               ((ok (left) -> left)
                (ng (right) -> right)))
             (Lam User capture-merged () merged))))))
  (check-exn #rx"borrowed-function-capture"
             (lambda ()
               (summaries core
                          `((merge-capture ,outer-type)
                            (capture-merged ,inner-type))))))

(test-case "分解 binder を Curry の固定引数にする形は owner 未解決で閉じる"
  (define parent-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut (Result (Option Int) (Option Int)) (RParam a)))
            Unit () (Mutation) () User)))
  (define curry-target-type
    '(NFn ((BorrowedMut (Option Int) (RParam a))) Unit () () () User))
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User curry-merged (parent)
           (Let (merged let (BorrowedMut (Option Int) (RParam %omitted)))
             (Eliminate parent
               ((ok (left) -> left)
                (ng (right) -> right)))
             (Curry (Lam User curry-target (value) unit) merged))))))
  (check-exn #rx"unresolved-borrow-owner"
             (lambda ()
               (summaries core `((curry-merged ,parent-type)
                                 (curry-target ,curry-target-type))))))

(test-case "RParam と合流した借用が生存中の親への書込みを拒否する"
  (define parent-type
    '(ForallRegion (a)
       (NFn ((BorrowedMut (Result (Option Int) (Option Int)) (RParam a)))
            (Option Int) () (Mutation) () User)))
  (define result-type '(Result (Option Int) (Option Int)))
  (define core
    `(Scope (1)
       (RegionLam (a)
         (Lam User rparam-merge-write (parent)
           (Let (merged let (BorrowedMut (Option Int) (RParam %omitted)))
             (Eliminate parent
               ((ok (left) -> left)
                (ng (right) -> right)))
             (Let (written let Unit)
               (Assign parent
                       (Construct ,result-type ok
                                  (Construct (Option Int) none)))
               (Read merged)))))))
  (check-exn #rx"borrow-conflicting-use"
             (lambda ()
               (summaries core `((rparam-merge-write ,parent-type))))))

(test-case "分解 binder の再借用と子射影は binder 起点の出口として追跡する"
  (define reborrow-parent
    '(Record ((o (Option Int) mut))))
  (define reborrow-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut ,reborrow-parent (RParam a))) Unit ()
            ((Yield Int) Mutation) () User)))
  (define reborrow-core
    '(Scope (1)
       (RegionLam (a)
         (Lam User reborrow-derived (parent)
           (Eliminate (ProjBorrow parent o)
             ((some (child) -> (Yield (Read (Reborrow child)) unit))
              (none () -> unit)))))))
  (define reborrow-events
    (append-map binder-events
                (summaries reborrow-core `((reborrow-derived ,reborrow-type)))))
  (check-true (pair? reborrow-events)
              (format "reborrow events: ~s" reborrow-events))
  (check-true
   (for/or ([event (in-list reborrow-events)])
     (eq? (deferred-leaf-exit-exit-kind event) 'local)))
  (define projection-parent
    '(Record ((o (Option (Record ((inner Int mut)))) mut))))
  (define projection-type
    `(ForallRegion (a)
       (NFn ((BorrowedMut ,projection-parent (RParam a))) Unit ()
            ((Yield Int) Mutation) () User)))
  (define projection-core
    '(Scope (1)
       (RegionLam (a)
         (Lam User projected-derived (parent)
           (Eliminate (ProjBorrow parent o)
             ((some (record-ref) ->
               (Yield (Read (ProjBorrow record-ref inner)) unit))
              (none () -> unit)))))))
  (define projection-events
    (append-map binder-events
                (summaries projection-core `((projected-derived ,projection-type)))))
  (check-true (pair? projection-events)
              (format "projection events: ~s" projection-events))
  (check-true
   (for/or ([event (in-list projection-events)])
     (eq? (deferred-leaf-exit-exit-kind event) 'local))))

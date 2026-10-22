#lang racket

(require rackunit
         racket/match
         racket/string
         "../gen.rkt"
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../typing.rkt")

(define limits (read-bounds))

(define borrow-shapes
  '(shared mut reborrow projection mut-projection
    eliminate-shared eliminate-mut assign
    merged-projection merged-reborrow))
(define merged-borrow-shapes '(merged-projection merged-reborrow))

(define (contains-core-node? tree pred?)
  (or (pred? tree)
      (and (list? tree)
           (ormap (lambda (part) (contains-core-node? part pred?)) tree))))

(define (find-core-node tree pred?)
  (cond
    [(pred? tree) tree]
    [(list? tree)
     (for/or ([part (in-list tree)]) (find-core-node part pred?))]
    [else #f]))

(define (merged-choice term)
  (define merged-node
    (find-core-node
     term
     (lambda (node)
       (match node
         [`(Let (,x let (Borrowed ,_ ,_))
             (Eliminate (Borrow ,d)
               ((none () -> (Borrow ,left))
                (some ,_ -> (Borrow ,right))))
             (Let (,q let (Borrowed Int ,_))
               (ProjBorrow ,x ,_) (Read ,q)))
          (not (equal? left right))]
         [`(Let (,x let (BorrowedMut ,_ ,_))
             (Eliminate (BorrowMut ,d)
               ((none () -> (BorrowMut ,left))
                (some ,_ -> (BorrowMut ,right))))
             (Let (,_ let (Borrowed ,_ ,_)) (Reborrow ,x) ,_))
          (not (equal? left right))]
         [_ #f]))))
  (and merged-node
       (let* ([discriminator
               (match merged-node
                 [`(Let (,_ let ,_) (Eliminate ,scrutinee ,_) ,_)
                  (second scrutinee)])]
              [value
               (let find-value ([tree term])
                 (match tree
                   [`(Let (,name let ,_) ,bound ,body)
                    (if (equal? name discriminator)
                        bound
                        (or (find-value bound) (find-value body)))]
                   [(? list?)
                    (for/or ([part (in-list tree)]) (find-value part))]
                   [_ #f]))])
         (match value
           [`(Construct ,_ none) 'none]
           [`(Construct ,_ some ,_) 'some]
           [_ #f]))))

(define (root-merged-owner-term? term)
  (match term
    [`(Scope () (Let (,name let ,_) ,_ ,_))
     (string-prefix? (symbol->string name) "merge-left")]
    [_ #f]))

(define (borrow-shape? shape term)
  (define (node? pattern)
    (contains-core-node? term (lambda (node) (pattern node))))
  (case shape
    [(shared) (node? (match-lambda [`(Borrow ,_) #t] [_ #f]))]
    [(mut) (node? (match-lambda [`(BorrowMut ,_) #t] [_ #f]))]
    [(reborrow) (node? (match-lambda [`(Reborrow ,_) #t] [_ #f]))]
    [(projection)
     (or (node? (match-lambda [`(ProjBorrow (Borrow ,_) ,_) #t] [_ #f]))
         (node? (match-lambda [`(ProjBorrow (BorrowMut ,_) ,_) #t] [_ #f])))]
    [(mut-projection)
     (node? (match-lambda [`(ProjBorrow (BorrowMut ,_) ,_) #t] [_ #f]))]
    [(eliminate-shared)
     (node? (match-lambda [`(Eliminate (Borrow ,_) ,_) #t] [_ #f]))]
    [(eliminate-mut)
     (node? (match-lambda [`(Eliminate (BorrowMut ,_) ,_) #t] [_ #f]))]
    [(assign) (node? (match-lambda [`(Assign ,_ ,_) #t] [_ #f]))]
    [(merged-projection)
     (node? (match-lambda [`(Let (,x let (Borrowed ,_ ,_))
                               (Eliminate ,_ ((none () -> (Borrow ,left))
                                              (some ,_ -> (Borrow ,right))))
                               (Let (,q let (Borrowed Int ,_))
                                 (ProjBorrow ,x ,_) (Read ,q)))
                             (not (equal? left right))]
                            [_ #f]))]
    [(merged-reborrow)
     (node? (match-lambda [`(Let (,x let (BorrowedMut ,_ ,_))
                               (Eliminate ,_ ((none () -> (BorrowMut ,left))
                                              (some ,_ -> (BorrowMut ,right))))
                               (Let (,y let (Borrowed ,_ ,_)) (Reborrow ,x) ,_))
                             (not (equal? left right))]
                            [_ #f]))]
    [else #f]))

(test-case "R-Yield が continuation 内の借用を新規生成と誤認しない"
  (check-equal?
   (borrow-form-candidates
    '(Yield 100 (Read (BorrowRef 0 () 0)))
    '(Read (BorrowRef 0 () 0)))
   '()))

(test-case "Redex が freshen した束縛名を静的 designator へ戻す"
  (define fresh (string->symbol "x«0»"))
  (define pre
    `(cfg (Scope (0)
                 (Let (,fresh let (Borrowed Res 0))
                      (BorrowRef 0 () 0)
                      (Read ,fresh)))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 () 0)))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define prov (provenance-extend (empty-provenance) 'R-LetB pre post))
  (check-equal? (resolve-designator prov 'x) '(0)))

;; 性質 8。生成した G2 項の到達可能な実行の上で、借用の生存が
;; 三条件を満たし、根の発生が静的側の借用要求と対応する。
(define (union-borrow-eliminate-reached? configs)
  (for/or ([before (in-list configs)]
           [after (in-list (cdr configs))])
    (and (contains-ready-borrowed-union-eliminate? (config-core before))
         (not (contains-ready-borrowed-union-eliminate? (config-core after))))))

(define (contains-ready-borrowed-union-eliminate? tree)
  (match tree
    [(or `(UnionEliminate (BorrowRef ,_ ,_ ,_) ,_)
         `(UnionEliminate (BorrowMutRef ,_ ,_ ,_) ,_)) #t]
    [(? list?) (ormap contains-ready-borrowed-union-eliminate? tree)]
    [_ #f]))

(define (run-borrow-search)
  (define limits (read-bounds))
  (define counters (make-bcounters))
  (define failures '())
  (define discarded 0)
  (define accepted 0)
  (define union-attempted 0)
  (define union-reached 0)
  (define shape-counts
    (make-hash (append (for/list ([shape (in-list borrow-shapes)])
                         (cons (list shape 'generated) 0))
                       (for/list ([shape (in-list borrow-shapes)])
                         (cons (list shape 'accepted) 0))
                       (for*/list ([shape (in-list merged-borrow-shapes)]
                                   [branch (in-list '(none some))]
                                   [field (in-list '(generated accepted))])
                         (cons (list shape branch field) 0))
                       (list (cons '(gen-core-merged accepted) 0)))))
  (define (bump-shape! shape field)
    (define key (list shape field))
    (hash-set! shape-counts key (add1 (hash-ref shape-counts key))))
  (define (bump-branch! shape branch field)
    (define key (list shape branch field))
    (hash-set! shape-counts key (add1 (hash-ref shape-counts key))))
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range (bounds-attempts limits))])
       (define union? (zero? (random 10)))
       (define term (gen-borrow-term (bounds-term-depth limits)
                                     #:include-union? union?))
       (define present-merged-shapes
         (filter (lambda (shape) (borrow-shape? shape term))
                 merged-borrow-shapes))
       (define present-shapes
         (if (pair? present-merged-shapes)
             present-merged-shapes
             (filter (lambda (shape) (borrow-shape? shape term))
                     (filter (lambda (shape)
                               (not (memq shape merged-borrow-shapes)))
                             borrow-shapes))))
       (define merged-branch
         (and (pair? present-merged-shapes)
              (merged-choice term)))
       (for ([shape (in-list present-shapes)])
         (bump-shape! shape 'generated))
       (when merged-branch
         (for ([shape (in-list present-merged-shapes)])
           (bump-branch! shape merged-branch 'generated)))
       (when union? (set! union-attempted (add1 union-attempted)))
       (match (prepare-borrow-term term)
         [(list 'ok config sidecar ir)
          (for ([shape (in-list present-shapes)])
            (bump-shape! shape 'accepted))
          (when merged-branch
            (for ([shape (in-list present-merged-shapes)])
              (bump-branch! shape merged-branch 'accepted))
            (unless (root-merged-owner-term? term)
              (bump-shape! 'gen-core-merged 'accepted)))
          (define outcome
            (check-borrow-execution config sidecar ir
                                    (bounds-fuel limits) counters))
          (when (and union?
                     (union-borrow-eliminate-reached?
                      (execution-configs
                       (bounded-trace-g2 config (bounds-fuel limits)))))
            (set! union-reached (add1 union-reached)))
          (match outcome
            ['ok (set! accepted (add1 accepted))]
            ['discard (set! discarded (add1 discarded))]
            [(list 'fail reason detail)
             (set! failures (cons (list reason detail term) failures))])]
         ['discard (set! discarded (add1 discarded))]))))
  (list accepted discarded failures counters union-attempted union-reached
        shape-counts))

(define search-result (run-borrow-search))

(define (matched-borrow-events counters)
  (+ (bcounters-shared counters)
     (bcounters-mut counters)
     (bcounters-reborrow counters)
     (bcounters-proj counters)
     (bcounters-use counters)))

(printf "P2m2a property 8: matched-events=~a failures=~a\n"
        (matched-borrow-events (fourth search-result))
        (length (third search-result)))

(define (check-property8-fixture source expected-counter)
  (match-define (list 'ok config sidecar ir _type)
    (prepare-borrow-term* source))
  (define counters (make-bcounters))
  (check-equal? (check-borrow-execution config sidecar ir
                                        (bounds-fuel limits) counters)
                'ok)
  (check-true (positive? (expected-counter counters)))
  counters)

(test-case "性質 8 の単純な Borrow は解決済み寿命で照合する"
  (define counters
    (check-property8-fixture
     '(Scope ()
        (Let (x let (Owned Int)) 1
          (Let (b let (Borrowed Int ph))
               (Scope () (Borrow x))
               (Read b))))
      bcounters-shared))
  (check-equal? (bcounters-shared counters) 1))

(test-case "性質 8 の ProjBorrowAt は親の解決済み寿命で照合する"
  (define counters
    (check-property8-fixture
     '(Scope ()
        (Let (c let (Owned (Record ((a Int mut) (b Int imm)))))
             (Rec ((a mut 1) (b imm 2)))
          (Let (q let (Borrowed Int ph))
               (ProjBorrow (Borrow c) a)
               (Read q))))
      bcounters-proj))
  (check-equal? (bcounters-shared counters) 1)
  (check-equal? (bcounters-proj counters) 1))

(test-case "性質 8 の反例が無い"
  (check-equal? (third search-result) '()))

(test-case "受理した実行がある"
  (check-true (positive? (first search-result))))

(test-case "discard が上限を超えない"
  (check-true (< (second search-result)
                 (bounds-discard-limit (read-bounds)))))

(test-case "6 つのカウンタがすべて非零"
  (check-equal? (bcounters-zeros (fourth search-result)) '()))

(test-case "借用探索の Union 項が分解規則へ到達する"
  (check-true (positive? (fifth search-result)))
  (check-true (positive? (sixth search-result)))
  (printf "Borrow search: Union attempted=~a UnionEliminate=~a\n"
          (fifth search-result) (sixth search-result)))

(define shape-counts (seventh search-result))
(define accepted-minima
  '((shared . 140) (mut . 99) (reborrow . 1) (projection . 47)
    (mut-projection . 22) (eliminate-shared . 34)
    (eliminate-mut . 35) (assign . 7)))

(test-case "生成器は既存8形の受理下限を保つ"
  (for ([shape (in-list (filter (lambda (shape)
                                 (not (memq shape merged-borrow-shapes)))
                               borrow-shapes))])
    (define generated (hash-ref shape-counts (list shape 'generated)))
    (define accepted (hash-ref shape-counts (list shape 'accepted)))
    (check-true (positive? generated) (format "~a was generated" shape))
    (check-true (>= accepted (cdr (assq shape accepted-minima)))
                (format "~a accepted >= ~a (actual ~a)"
                        shape (cdr (assq shape accepted-minima)) accepted))
    (printf "Borrow generator ~a: generated=~a accepted=~a\n"
            shape generated accepted)))

(test-case "異なる owner の借用を合流した後の射影を生成して型検査する"
  (define generated (hash-ref shape-counts '(merged-projection generated)))
  (define accepted (hash-ref shape-counts '(merged-projection accepted)))
  (check-true (positive? generated))
  (check-true (positive? accepted))
  (printf "Borrow generator merged-projection: generated=~a accepted=~a\n"
          generated accepted)
  (for ([branch (in-list '(none some))])
    (define branch-generated
      (hash-ref shape-counts (list 'merged-projection branch 'generated)))
    (define branch-accepted
      (hash-ref shape-counts (list 'merged-projection branch 'accepted)))
    (check-true (positive? branch-accepted)
                (format "merged-projection ~a accepted" branch))
    (printf "Borrow generator merged-projection/~a: generated=~a accepted=~a\n"
            branch branch-generated branch-accepted)))

(test-case "異なる owner の可変借用を合流した後の再借用を生成して型検査する"
  (define generated (hash-ref shape-counts '(merged-reborrow generated)))
  (define accepted (hash-ref shape-counts '(merged-reborrow accepted)))
  (check-true (positive? generated))
  (check-true (positive? accepted))
  (printf "Borrow generator merged-reborrow: generated=~a accepted=~a\n"
          generated accepted)
  (for ([branch (in-list '(none some))])
    (define branch-generated
      (hash-ref shape-counts (list 'merged-reborrow branch 'generated)))
    (define branch-accepted
      (hash-ref shape-counts (list 'merged-reborrow branch 'accepted)))
    (check-true (positive? branch-accepted)
                (format "merged-reborrow ~a accepted" branch))
    (printf "Borrow generator merged-reborrow/~a: generated=~a accepted=~a\n"
            branch branch-generated branch-accepted))
  (printf "Borrow generator gen-core merged accepted=~a\n"
          (hash-ref shape-counts '(gen-core-merged accepted))))

(define (contains-form? tree form)
  (or (and (pair? tree) (eq? (first tree) form))
      (and (list? tree) (ormap (lambda (part) (contains-form? part form)) tree))))

(define (check-union-borrow-configs configs)
  (check-true (andmap (lambda (configuration)
                        (config-ok? configuration '() 'Int '()))
                      configs)
              "every config in the trace must be valid")
  (length configs))

(test-case "borrowed Union programme は全 config と borrow oracle を通る"
  (define started (current-inexact-milliseconds))
  (define generated 0)
  (define typed 0)
  (define discarded 0)
  (define reached 0)
  (define checked-configs 0)
  (define oracle-failures '())
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_attempt (in-range 100)])
         (define source (gen-borrow-term (bounds-term-depth limits)
                                         #:include-union? #t))
         (set! generated (add1 generated))
         (match (prepare-borrow-term source)
           [(list 'ok config sidecar ir)
            (set! typed (add1 typed))
            (let* ([run (bounded-trace-g2 config (bounds-fuel limits))]
                   [configs (execution-configs run)])
              (unless (eq? (execution-outcome run) 'terminal)
                (set! oracle-failures
                      (cons (list 'nonterminal source) oracle-failures)))
              (set! checked-configs
                    (+ checked-configs (check-union-borrow-configs configs)))
              (unless (eq? (check-borrow-execution
                            config sidecar ir (bounds-fuel limits)
                            (make-bcounters))
                           'ok)
                (set! oracle-failures (cons source oracle-failures)))
              (when (union-borrow-eliminate-reached? configs)
                (set! reached (add1 reached))))]
           ['discard (set! discarded (add1 discarded))]
           [other
            (set! discarded (add1 discarded))
            (set! oracle-failures
                  (cons (list 'unexpected-prepare-result other source)
                        oracle-failures))]))))
  (check-equal? generated 100)
  (check-equal? discarded 0 "ill-typed Union borrow programmes are not discarded")
  (check-equal? typed generated)
  (check-true (positive? checked-configs)
              "generated borrowed unions exercise configuration checking")
  (check-equal? oracle-failures '())
  (check-true (positive? typed))
  (check-true (positive? reached))
  (printf "P2m2a borrowed Union: generated=~a typed=~a discarded=~a checked-configs=~a UnionEliminate=~a elapsed-ms=~a\n"
          generated typed discarded checked-configs reached
          (inexact->exact
           (round (- (current-inexact-milliseconds) started)))))

;; ここから負例。oracle が三条件を実際に見ていることを、
;; 条件ごとに違反する config を手で組んで確かめる。
;; 負例の config は型検査を通らない。prepare-borrow-term を通さず
;; check-borrow-execution へ直接渡すので、型は問題にならない。確かめるべきは
;; 各負例が意図した条件で落ちたか、その手前の discard や別の理由で終わったかで
;; ある。実装時に返り値の reason を見て確かめ、結果をコメントへ書き残す。
;; Move と BorrowAt の負例は簡約が実際に発火する必要があるので、place は Ω に
;; ある番号を書く。記号の変数を置くと規則の where が解けず、歩数 0 の
;; 'ok で終わって条件を検査しない。

(define empty-sidecar (borrow-sidecar '() (hash)))

(define (fails-with config reason)
  (match (check-borrow-execution config empty-sidecar #f 200
                                 (make-bcounters))
    [(list 'fail actual _detail) (equal? actual reason)]
    [_ #f]))

(test-case "生きている借用の place を move すると落ちる"
  ;; 借用値を本体に残したまま Move が発火する config。
  (check-true
   (fails-with
    '(cfg (Scope (0) (Let (y let Int) (Move 0) (Read (BorrowRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ())
    'move-of-live-borrow)))

(test-case "同じ place の可変借用が 2 つ生きると落ちる"
  (check-true
   (fails-with
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 0)
                             (Read (BorrowMutRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ())
    'mut-not-exclusive)))

(test-case "可変借用と共有借用が重なって生きると落ちる"
  (check-true
   (fails-with
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 0)
                             (Read (BorrowRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ())
    'mut-not-exclusive)))

(test-case "静的側に無い根の借用は落ちる"
  (check-true
   (fails-with
    '(cfg (Scope (0) (BorrowAt (RVar 0) (Own 0 ()) 0))
          ((0 (resource 1000))) ((0 Available)) () ())
    'unmatched-root)))

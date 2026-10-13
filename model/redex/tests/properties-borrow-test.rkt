#lang racket

(require rackunit
         racket/match
         "../gen.rkt"
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../typing.rkt")

(define limits (read-bounds))

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
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range (bounds-attempts limits))])
       (define union? (zero? (random 10)))
       (define term (gen-borrow-term (bounds-term-depth limits)
                                     #:include-union? union?))
       (when union? (set! union-attempted (add1 union-attempted)))
       (match (prepare-borrow-term term)
         [(list 'ok config sidecar ir)
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
  (list accepted discarded failures counters union-attempted union-reached))

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

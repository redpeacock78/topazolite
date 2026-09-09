#lang racket

(require rackunit
         racket/match
         "../gen.rkt"
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt")

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
(define (run-borrow-search)
  (define limits (read-bounds))
  (define counters (make-bcounters))
  (define failures '())
  (define discarded 0)
  (define accepted 0)
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range (bounds-attempts limits))])
       (define term (gen-borrow-term (bounds-term-depth limits)))
       (match (prepare-borrow-term term)
         [(list 'ok config sidecar ir)
          (define outcome
            (check-borrow-execution config sidecar ir
                                    (bounds-fuel limits) counters))
          (match outcome
            ['ok (set! accepted (add1 accepted))]
            ['discard (set! discarded (add1 discarded))]
            [(list 'fail reason detail)
             (set! failures (cons (list reason detail term) failures))])]
         ['discard (set! discarded (add1 discarded))]))))
  (list accepted discarded failures counters))

(define search-result (run-borrow-search))

(test-case "性質 8 の反例が無い"
  (check-equal? (third search-result) '()))

(test-case "受理した実行がある"
  (check-true (positive? (first search-result))))

(test-case "discard が上限を超えない"
  (check-true (< (second search-result)
                 (bounds-discard-limit (read-bounds)))))

(test-case "6 つのカウンタがすべて非零"
  (check-equal? (bcounters-zeros (fourth search-result)) '()))

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

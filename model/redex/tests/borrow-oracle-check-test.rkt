#lang racket

(require rackunit
         racket/match
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt")

(define shared-skeleton
  '(Scope ()
     (Let (x let (Owned Res)) (resource 1000)
       (Scope ()
         (Let (y let (Borrowed Res ph)) (Borrow x) 1000)))))

;; 可変借用へ書き込む値は payload 型と互換でなければならない
;; （`infer-assign` の union 成分検査）。`Res` payload へ整数は代入できないので、
;; 代入を含む骨格は `Int` payload にする。
(define mut-skeleton
  '(Scope ()
     (Let (x let (Owned Int)) 1000
       (Scope ()
         (Let (y let (BorrowedMut Int ph)) (BorrowMut x)
           (Assign y 1001))))))

(define (run skeleton)
  (define counters (make-bcounters))
  (match (prepare-borrow-term skeleton)
    [(list 'ok config sidecar ir)
     (list (check-borrow-execution config sidecar ir 200 counters) counters)]
    [other (list other #f)]))

(test-case "共有借用の実行は ok になる"
  (check-equal? (first (run shared-skeleton)) 'ok))

(test-case "共有借用の実行は shared カウンタを進める"
  (check-true (positive? (bcounters-shared (second (run shared-skeleton))))))

(test-case "可変借用と代入の実行は ok になり use カウンタが進む"
  (match-define (list outcome counters) (run mut-skeleton))
  (check-equal? outcome 'ok)
  (check-true (positive? (bcounters-mut counters)))
  (check-true (positive? (bcounters-use counters))))

(test-case "静的側の借用集合は mode と fp と ρ を持つ"
  (match-define (list 'ok _config sidecar ir)
    (prepare-borrow-term shared-skeleton))
  (define entries (static-borrow-set sidecar ir))
  (check-equal? (length entries) 1)
  (check-equal? (first (first entries)) 'shared))

(test-case "初期 config に借用値がある実行は入口で discard になる"
  ;; prepare-borrow-term が弾くので、oracle へは届かない。
  (check-equal? (prepare-borrow-term
                 '(Scope () (Read (BorrowRef 0 () 0))))
                'discard))

(test-case "未追跡の親からの reborrow は fail になる"
  ;; 親の可変借用を静的側の要求に持たない config を手で組み、
  ;; R-Reborrow が根として発火したときに静的側と照合できないことを見る。
  (define config
    '(cfg (Scope (0) (ReborrowAt 0 (Own 0 ()) (BorrowMutRef 0 () 0)))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (define empty-sidecar (borrow-sidecar '() (hash)))
  (match (check-borrow-execution config empty-sidecar #f 200
                                 (make-bcounters))
    [(list 'fail reason _detail) (check-equal? reason 'unmatched-root)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "カウンタが 0 の欄を列挙できる"
  (define counters (make-bcounters))
  (check-equal? (sort (map symbol->string (bcounters-zeros counters))
                      string<?)
                '("mut" "proj" "reborrow" "scope-exit" "shared" "use")))

(test-case "raw pointer 規則は借用の置換規則へ分類されない"
  (for ([name (in-list '(R-AddressOf R-PtrOffset R-RawLoad R-RawStore
                         R-FromRawPtrConst R-FromRawPtrMut R-UnsafeExit))])
    (check-equal? (rule-bucket name) 'non-substituting)))

(test-case "生きている借用の place を move する遷移は fail になる"
  ;; 条件 1。Ω が Available から Moved へ変わる前後の config を手で組む。
  ;; place 0 を指す共有借用が制御項に生きているので落ちる。
  (define pre
    '(cfg (Scope (0) (Read (BorrowRef 0 () 0)))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 () 0)))
          ((0 (resource 1000))) ((0 Moved)) () ()))
  (match (check-no-move-of-live pre post)
    [(list 'fail reason place)
     (check-equal? reason 'move-of-live-borrow)
     (check-equal? place 0)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "重なる可変借用が同時に生きている config は fail になる"
  ;; 条件 2。同じ place と欄 path を指す可変借用が 2 箇所に現れる制御項。
  ;; normalize-borrow が出現ごとに新しい 4 つ組を作るので、
  ;; for*/or の eq? による自己対の除外には掛からない。
  (define config
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 0)
                             (Read (BorrowMutRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (match (check-mut-exclusive config)
    [(list 'fail reason _detail) (check-equal? reason 'mut-not-exclusive)]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "reborrow の子が生きている間に親が現れると fail になる"
  ;; 条件 3。update-parents が積む (子 親) の対をそのまま渡す。
  ;; 子は共有で ρ が 0、親は可変で ρ が 1 であり、place と欄 path は同じ。
  (define config
    '(cfg (Scope (0) (Assign (BorrowMutRef 0 () 1)
                             (Read (BorrowRef 0 () 0))))
          ((0 (resource 1000))) ((0 Available)) () ()))
  (define parents (list (list '(shared 0 () 0) '(mut 0 () 1))))
  (match (check-reborrow-parents config parents)
    [(list 'fail reason _pair) (check-equal? reason 'reborrow-parent-live)]
    [other (fail (format "unexpected: ~e" other))]))

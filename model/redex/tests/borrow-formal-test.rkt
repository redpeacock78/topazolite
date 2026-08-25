#lang racket

;; [REQ: BOR-005] 借用の仮引数の formal 鍵と、本体で出た要求の雛形の収集。

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (inference core ir τ_place callables)
  (typing-inference (annotate-regions core ir)
                    (list (list 1 τ_place)) callables '()
                    (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

(define (status core ir τ_place callables)
  (first (type-of/raw (annotate-regions core ir)
                      (list (list 1 τ_place)) callables '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))))

;; 借用の仮引数を 1 つ取り、それを読み書きするだけの署名。
(define use-callables
  '((useb (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a)))
                 Unit
                 () ())))))

;; 借用の仮引数を 2 つ取る署名。片方を再借用し、もう片方を使う本体に使う。
(define pair-callables
  '((pairb (ForallRegion (a)
             (NFn ((BorrowedMut Int (RParam a)) (BorrowedMut Int (RParam a)))
                  Unit
                  () ())))))

;; 借用の仮引数を持つ Recur の署名。
(define rec-callables
  '((recb (NFn ((BorrowedMut Int 0)) Int () ()))))

;; 1。借用の仮引数を読み書きする本体が型検査を通る。
;; 今日は borrow-token-key が親を引けず E-BOR-020 で落ちる。
(test-case
 "借用の仮引数の読み書きが本体で通る"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Lam User useb (x)
                           (Let (t let Int) (Read x) (Assign x 7))))))
 (define ir (build-region-ir core))
 (check-equal? (status core ir 'Int use-callables) 'ok))

;; 2。本体の要求が外へ漏れない。
;; formal 鍵を普通の借用として要求へ入れる実装は、ここで要求が 0 件にならない。
(test-case
 "本体の要求が外へ漏れない"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Lam User useb (x)
                           (Let (t let Int) (Read x) (Assign x 7))))))
 (define ir (build-region-ir core))
 (define requests (fourth (inference core ir 'Int use-callables)))
 (check-equal? requests '()))

;; 3。雛形が実際に集まっている。
;; 2 だけでは、要求を作らずに捨てる実装が通ってしまう。
;; 再借用と使用の両方が雛形として残ることを見る。
(test-case
 "本体の再借用と使用が雛形として残る"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Lam User pairb (x y)
                           (Let (t let Int)
                                (Read (Reborrow x))
                                (Assign y 7))))))
 (define ir (build-region-ir core))
 (define summaries (sixth (inference core ir 'Int pair-callables)))
 (check-equal? (length summaries) 1)
 (define summary (first summaries))
 (define deferred (callable-summary-deferred summary))
 (define formals (list->set (filter values (callable-summary-formals summary))))
 (check-equal? (set-count formals) 2)
 (check-true (> (length (filter borrow-request? deferred)) 0))
 (check-true (> (length (filter use-request? deferred)) 0))
 ;; 雛形の鍵はこの要約自身の formal 鍵であり、実引数の designator でも
 ;; 別の要約の formal 鍵でもない。記号かどうかを見るだけでは、
 ;; 実引数の名前がそのまま残った実装を通してしまう。
 (check-true
  (for/and ([r (in-list deferred)] #:when (use-request? r))
    (set-member? formals (use-request-w r))))
 (check-true
  (for/and ([r (in-list deferred)] #:when (borrow-request? r))
    (set-member? formals (borrow-request-w r)))))

;; 4。借用の仮引数を持つ Recur を落とす。
;; 再帰の呼出しごとに実引数が変わり、formal 鍵の実体化が出現をまたぐ。
(test-case
 "借用の仮引数を持つ Recur を落とす"
 (define core '(Scope (1) (Recur recb g (x) (Read x) 0)))
 (define ir (build-region-ir core))
 (check-equal? (status core ir 'Int rec-callables)
               'fail))

;; 5。外側の仮引数の借用を捕捉する入れ子の Lam を落とす。
;; check-function-boundary の捕捉の判定は borrowed-type? のままであり、
;; 束縛の有無を見ないので、formal も捕捉として落とす。
(test-case
 "外側の仮引数を捕捉する入れ子の Lam を落とす"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Lam User useb (x)
                           (Lam User useb (y) (Read x))))))
 (define ir (build-region-ir core))
 (check-equal? (status core ir 'Int use-callables) 'fail))

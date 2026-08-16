#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (rho-at ir point) (region->rho ir (region-at ir point)))
(define (status core ir [callables '()])
  (first (type-of/raw (annotate-regions core ir)
                      (list (list 1 'Res)) callables '()
                      (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))))
(define (status/no-ir core)
  (first (type-of/raw core
                      (list (list 1 'Res)) '() '()
                      (empty-region-ctx))))

;; 宣言型が借用を含むときも Error は期待した型を問わずに通る。
;; G5b の受理をそのまま保つ（spec §6.3 の 段 1 の key を変えない）。
(let ()
  (define (make ρ) `(Let (b let (Borrowed Res ,ρ)) (Error 1) 0))
  ;; Error は G2m の実行時形であり、region IR の意味的子ではない。
  ;; 借用も注釈も無いこの枝は IR を作らずに検査する。
  (check-equal? (status/no-ir (make 0)) 'ok))

;; 分岐ごとに別の α を持つ借用でも、検査の位置なら合流は起きない。
;; 各分岐が期待した型と照合されるだけなので、Task 12 を待たずに通る。
;; ただしこの枝は束縛の型へ期待した型をそのまま返すため、(RVar k) を保たない。
;; 束縛名を使う位置が spec §5.1 の下限を立てられない状態は Task 12 Step 7b が回収する。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ))
                     (Eliminate (Construct Bool true)
                                ((true () -> (Borrow 1))
                                 (false () -> (Borrow 1))))
                     0)))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0))) ir) 'ok))

;; Scope 枝。借用は内側の Scope で作るが、束縛は外側の宣言型で受ける。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Scope () (Borrow 1)) 0)))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0 0))) ir) 'ok))

;; Let 枝（2 要素の形）。内側の Let を通っても寿命が上がる。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ))
                     (Let (r Int) 0 (Borrow 1))
                     0)))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0 1))) ir) 'ok))

;; Suspend 枝。row へ (Suspend) が乗ったまま借用が通る。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Suspend (Borrow 1)) 0)))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0 0))) ir) 'ok))

;; Yield 枝。next の側の借用が束縛の型になる。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Yield 0 (Borrow 1)) 0)))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0 1))) ir) 'ok))

;; Construct 枝。宣言型が借用を含まない形は Task 8 の前と同じに通る。
(let ()
  (define core '(Scope () (Let (b let Bool) (Construct Bool true) 0)))
  (define ir (build-region-ir core))
  (check-equal? (status core ir) 'ok))

;; Recur 枝。関数本体は Int を返し、継続側の借用が Recur の結果になる。
(let ()
  (define (make ρ)
    `(Scope (1)
            (Let (b let (Borrowed Res ,ρ))
                 (Recur loop-id loop (x) 0 (Borrow 1))
                 0)))
  (define ir (build-region-ir (make 0)))
  (define callables (list (list 'loop-id '(NFn (Int) Int () ()))))
  (check-equal? (status (make (rho-at ir '(0 0))) ir callables) 'ok))

;; 最後の枝を通ったとき、推論した型が binding-context まで戻る。
;; 戻らなければ束縛の型が (RVar k) を失い、この Move が素通りする。
;; borrow-check-stage-test.rkt の同型の fixture が cond の側を押さえていたので、
;; 迂回を消したあとの経路をここで別に押さえる。
(let ()
  (define (make ρ) `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Borrow 1) (Move 1))))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0))) ir) 'fail))

;; 入れ子の内側で落ちる type-mismatch は内側の項を節点にする。
;; 段 1 が渡した key と節点を保つ（spec §6.3）。
(let ()
  (define (make ρ) `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Scope () 0) 0)))
  (define ir (build-region-ir (make 0)))
  (define result
    (type-of/raw (annotate-regions (make (rho-at ir '(0 0))) ir)
                 (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (second result) 'type-mismatch)
  ;; 節点は Scope そのものではなく、その中の 0 である。
  (check-equal? (peel-node (third result)) 0))

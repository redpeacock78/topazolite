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
;; この fixture が押さえるのは既存の borrow-request による使用判定であり、
;; Step 7b の合流した寿命を判別するものではない。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ))
                     (Eliminate (Construct Bool true)
                                ((true () -> (Borrow 1))
                                 (false () -> (Borrow 1))))
                     0)))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0))) ir) 'ok))

;; 検査の位置の Eliminate でも、分岐の借用が生きている間の Move を捕まえる。
;; Task 8b では束縛の型が (RVar k) を失い、この Move が素通りしていた。
(let ()
  (define (make body)
    `(Scope (1) (Let (b let (Borrowed Res 0))
                     (Eliminate (Construct Bool true)
                                ((true () -> (Borrow 1))
                                 (false () -> (Borrow 1))))
                     ,body)))
  (define ir (build-region-ir (make '(Move 1))))
  (check-equal? (status (make '(Move 1)) ir) 'fail)
  ;; 借用の使用が無ければ、合流が使用の判定を広げすぎず通る。
  (check-equal? (status (make 0) ir) 'ok))

;; Scope 枝。借用は内側の Scope で作るが、束縛は外側の宣言型で受ける。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Scope () (Borrow 1)) 0)))
  (define ir (build-region-ir (make 0)))
  (check-equal? (status (make (rho-at ir '(0 0 0))) ir) 'ok))

;; 検査位置の Eliminate を内側 Scope へ置き、束縛名を外側で観測する。
;; check-as/full が合流した型を binding-context へ返さないと宣言型の内側 ρ が
;; そのまま結果へ残る。合流した (RVar k) を返す経路では、外側の Yield が下限を
;; 足し、結果の借用は外側 ρ へ広がる。
(let ()
  (define skeleton
    `(Scope (1)
            (Let (b let (Borrowed Res 0))
                 (Scope ()
                        (Eliminate (Construct Bool true)
                                   ((true () -> (Borrow 1))
                                    (false () -> (Borrow 1)))))
                 (Yield b 0))))
  (define ir (build-region-ir skeleton))
  (define inner-rho (rho-at ir '(0 0)))
  (define outer-rho (rho-at ir '()))
  (define core
    `(Scope (1)
            (Let (b let (Borrowed Res ,inner-rho))
                 (Scope ()
                        (Eliminate (Construct Bool true)
                                   ((true () -> (Borrow 1))
                                    (false () -> (Borrow 1)))))
                 (Yield b 0))))
  (check-equal?
   (type-of/raw (annotate-regions core ir)
                (list (list 1 'Res)) '() '()
                (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))
   `(ok (Int ((Yield (Borrowed Res ,outer-rho)))))))

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

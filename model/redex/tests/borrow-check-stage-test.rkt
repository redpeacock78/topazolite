#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; Let の宣言型の ρ を IR から引く。
;; region の構造は型注釈に依存しないので、仮の 0 で IR を作り、
;; 引いた ρ で core を組み直してから annotate-regions を 1 度だけ通す。
;; 借用の region は、その節点を囲む Scope の region である。
;; borrow-test.rkt の ok-ρ が (region-at ok-ir '(0 1)) を引いているのと同じ数え方である。
(define (rho-at ir point) (region->rho ir (region-at ir point)))

;; 内側 Scope の中の Move を拒む。借用が生きている位置である。
(let ()
  (define (make ρ) `(Scope (1) (Let (b let (Borrowed Res ,ρ)) (Borrow 1)
                                    (Move 1))))
  (define ir (build-region-ir (make 0)))
  ;; Borrow は Scope の子 0 の Let の子 0 に居る。
  (define annotated (annotate-regions (make (rho-at ir '(0 0))) ir))
  (check-equal?
   (key-of (type-of/raw annotated (list (list 1 'Res)) '() '()
                        (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'move-borrowed))

;; 兄弟の Scope に置いた 2 つの可変借用は偽の衝突を起こさない。
;; 兄弟を作る形は Yield である。G2 に Seq は無い。
;; borrow-test.rkt の shared-twice と mut-twice が同じ形で対を作っている。
;; 借用は 2 つとも Yield の observed 側へ置き、next は Int で閉じる。
;; Yield の結果型は next の型なので、借用を next へ置くと、その α が
;; 外側の Scope の出口でも収集され、下限が外側の region まで広がる。
;; そうなると兄弟どうしが regions-overlap? で真になり、偽の衝突が出る。
(let ()
  (define core
    '(Scope (1) (Yield (Scope () (BorrowMut 1))
                       (Yield (Scope () (BorrowMut 1)) 0))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (check-equal?
   (first (type-of/raw annotated (list (list 1 'Res)) '() '()
                       (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'ok))

;; 内側 Scope で尽きた借用は、その Scope を出た後の Move を妨げない。
;; 使用の判定は region-outlives? であり、重なりでは判定しない。§7.4。
(let ()
  (define (make ρ)
    `(Scope (1) (Let (r let Int)
                     (Scope () (Let (b let (Borrowed Res ,ρ)) (Borrow 1) 0))
                     (Move 1))))
  (define ir (build-region-ir (make 0)))
  ;; Borrow は Let(r) の子 0 の Scope の子 0 の Let(b) の子 0 に居る。
  (define annotated (annotate-regions (make (rho-at ir '(0 0 0 0))) ir))
  (check-equal?
   (first (type-of/raw annotated (list (list 1 'Res)) '() '()
                       (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
   'ok))

;; 段 3 は row からも RVar を落とす。
;; Yield は観測値の型を (Yield τ) として row へ入れるので、
;; 借用を Yield で返すと row が α を運ぶ経路になる。
(let ()
  (define core '(Scope (1) (Yield (Borrow 1) 0)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (match-define (list 'ok (list _type row))
    (type-of/raw annotated (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-false (contains-lifetime-var? row)))

;; 段 1 の棄却と制約の破れが同時に起きる形。
;; 宣言型 Int と借用の型が食い違うので段 1 が type-mismatch で棄却する。
;; 同じ項で BOR-001 も破れるように、owner を借用より短い Scope へ置く。
;; infer-borrow は借用の位置で contains α (外側の region) を立てるので、
;; σ(α) は外側になる。owner の region は内側なので outlives が破れる。
;; 破れた制約を診断へ昇格させると、型不一致が borrow-escapes-owner へ化ける。
;; 段 1 の key を保ち、解けない details を捨てることを固定する。
(let ()
  ;; Borrow は Let の子 0 で point は (0 0)、内側 Scope は Let の子 1 で (0 1)。
  ;; build-region-ir は Scope の節点そのものの point を at-table の鍵にするので、
  ;; (region-at ir '(0 1)) は内側 Scope の region を返す。
  (define core '(Scope (1) (Let (b let Int) (Borrow 1) (Scope () 0))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (match-define (list 'fail key _node details)
    (type-of/raw annotated (list (list 1 'Res)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '(0 1))) (hash))))
  (check-equal? key 'type-mismatch)
  ;; 段 2 が解けない以上、推論の途中の型を読み手へ見せる根拠が無い。
  ;; expected と found を捨て、key と span だけを残す。
  (check-equal? details '()))

;; spec §7.5。裸の名前の Drop は借用の生死で key が変わる。
;; 借用が生きている位置では段 3 が drop-borrowed を出す。
;; 既存の borrow-test.rkt と borrow-regression-test.rkt が凍結している形と同じである。
(let ()
  (define core
    `(Scope ()
       (Let (x let (Owned Res)) (resource 1) (Yield (Borrow x) (Drop x)))))
  (define ir (build-region-ir core))
  (match-define (list 'fail key _node _details)
    (type-of/raw core '() '() '() (region-ctx ir '() (hash) (hash))))
  (check-equal? key 'drop-borrowed))

;; 借用が生きていない位置では段 3 が otherwise の key を出す。
;; G5b はこれを段 1 の裸の名前の枝で出していた。key を変えない。
(let ()
  (define core
    `(Scope () (Let (x let (Owned Res)) (resource 1) (Drop x))))
  (define ir (build-region-ir core))
  (match-define (list 'fail key _node _details)
    (type-of/raw core '() '() '() (region-ctx ir '() (hash) (hash))))
  (check-equal? key 'owned-variable-requires-move))

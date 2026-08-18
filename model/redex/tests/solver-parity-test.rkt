#lang racket

;; [REQ: BOR-003] 型付けは region の内部構造を読まない。
;; solver を差し替えても判定の結果が変わらないことを、この枠で確かめる。

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; 判定の結果だけを返す。region 識別子は返さない。spec §6.4。
(define (judgment-of ir core places callables environment)
  (match (type-of/raw core places callables environment
                      (region-ctx ir '() (owners-of ir places) (hash)))
    [(list 'ok _) 'ok]
    [(list 'fail key _ _) key]))

;; places の所有者を根の region に置く。parity の対象は借用の判定である。
(define (owners-of ir places)
  (for/hash ([p (in-list places)]) (values (first p) (region-at ir '()))))

;; fixture は注釈前の形で書き、annotate-regions を 1 度だけ通す。
;; Let の宣言型の ρ は IR から引くので、各 case は core そのものではなく、
;; ρ を引く手続きを受けて core を返す手続きを持つ。
(define (zero point) 0)

(define (solver-parity-cases)
  (list
   (list "共有借用"
         (lambda (rho) '(Scope (1) (Borrow 1)))
         (list (list 1 'Res))
         'ok)
   (list "可変借用"
         (lambda (rho) '(Scope (1) (BorrowMut 1)))
         (list (list 1 'Res))
         'ok)
   (list "衝突する別名"
         ;; Borrow は Scope の子 0 の Let の子 0 で '(0 0) に居る。
         (lambda (rho)
           `(Scope (1) (Let (a let (Borrowed Res ,(rho '(0 0)))) (Borrow 1)
                            (BorrowMut 1))))
         (list (list 1 'Res))
         'borrow-conflicting-alias)
   (list "兄弟の可変借用"
         ;; 兄弟を作る形は Yield である。G2 に Seq は無い。
         ;; 借用は 2 つとも observed 側へ置き、next は Int で閉じる。
         ;; 寿命が兄弟の region に留まるため regions-overlap? は偽であり、
         ;; 同じ所有者の可変借用でも衝突しない。
         (lambda (rho)
           '(Scope (1) (Yield (Scope () (BorrowMut 1))
                              (Yield (Scope () (BorrowMut 1)) 0))))
         (list (list 1 'Res))
         'ok)))

;; region の構造は型注釈に依存しないので、仮の 0 で IR を作り、
;; 引いた ρ で core を組み直してから annotate-regions を 1 度だけ通す。
(define (prepare make)
  (define ir (build-region-ir (make zero)))
  (define annotated
    (annotate-regions (make (lambda (point) (region->rho ir (region-at ir point))))
                      ir))
  (values ir annotated))

;; §7 条件 6 の第 1 文。lexical が受理した形は同じ solver でも受理する。
;; §7 条件 6 の第 2 文。上限制約の検査が真だった対で真である。
;; §7 条件 6 の第 3 文。衝突の判定が偽だった対で偽である。
;; NLL solver が入るまで、右辺も lexical である。
(for ([c (in-list (solver-parity-cases))])
  (match-define (list name make places expected) c)
  ;; 注釈は ir ごとに別々に作る。region 識別子は ir を作るたびに新しく振られるので、
  ;; ir-a で注釈した core を ir-b の側へ渡すと、起点との一致を見る
  ;; check-region-annotation が borrow-region-mismatch を出す。
  ;; 比べるのは判定の結果だけであり、識別子は比べない。spec §6.4。
  (define-values (ir-a annotated-a) (prepare make))
  (define-values (ir-b annotated-b) (prepare make))
  (define judgment (judgment-of ir-a annotated-a places '() '()))
  ;; parity の等式だけでは、両辺が同じ solver なので必ず成り立つ。
  ;; fixture が壊れてどの case も同じ key を返す状態でも通ってしまう。
  ;; case ごとに期待した判定を先に押さえ、枠が意図した経路を通ることを固定する。
  (check-equal? judgment expected name)
  (check-equal? judgment (judgment-of ir-b annotated-b places '() '()) name))

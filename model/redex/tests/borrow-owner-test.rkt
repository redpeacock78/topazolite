#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../erase.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt")

;; 手組みの ir。region.md §5 のとおり、手組みの ir は実装誤りを示す
;; fixture のためのものである。
(define ρa (region 100))
(define ρb (region 101))
(define ρroot (region 102))

;; region-owning は gen:region-solver の method であるため、素の region-ir では
;; 呼べない。手組みの fixture も lexical adapter として組む。
;; parents は 2 つの子を root へ結び、at-table は空、points は根だけである。
;; region-at と regions-exiting-at をこの fixture で呼ばないため、この 2 つで足りる。
(define (hand-ir owners)
  (lexical-region-ir (list->set (list ρroot ρa ρb))
                     (list->set (list (list ρroot ρa) (list ρroot ρb)))
                     owners
                     (hash ρa ρroot ρb ρroot)
                     (hash)
                     (set '())))

;; 一意に定まるとき、その region を返す。
(check-equal? (region-owning (hand-ir (hash ρroot '() ρa '(0 1) ρb '(2)))
                             0)
              ρa)

;; 所有者が無いときは error。root region へ落とさない。
;; root は最も長生きするため、黙って root にすると BOR-001 の判定が
;; すべて通ってしまう。
(check-exn exn:fail?
           (lambda ()
             (region-owning (hand-ir (hash ρroot '() ρa '(0) ρb '(1))) 9)))

;; 所有者が 2 つ以上ある IR は不正であり error。
(check-exn exn:fail?
           (lambda ()
             (region-owning (hand-ir (hash ρroot '() ρa '(0) ρb '(0))) 0)))

;; spec §7.3。入れ子の Scope と代入を含む fixture を置く。
;; 外側 Scope の中に内側 Scope を置き、双方で owned の Let を行う。
;; 内側から外側の所有者を指す形が、この補題の眼目である。
(define nested
  '(Scope ()
     (Let (x let (Owned Int)) 1
       (Scope ()
         (Let (y let (Owned Int)) 2
           (Apply (PrimVal User add) (Move x) (Move y)))))))

;; 静的側: x を束縛する Let の節点の region。
;; point は region.md §3 の子の並びに従う。
;; (Scope () c) の c は添字 0、(Let (x bmode τ) c1 c2) の c2 は添字 1。
(define ir-static (build-region-ir nested))
(define ρ-x-static (region-at ir-static '(0)))
(define ρ-y-static (region-at ir-static '(0 1 0)))

;; 外側の Let と内側の Let は別の Scope に属する。
(check-not-equal? ρ-x-static ρ-y-static)

;; 静的側の構造: 外側の region が内側の region を包み、逆は成り立たない。
;; この 2 本の真偽が、下の実行時側と突き合わせる相手である。
(define static-x-contains-y (region-contains? ir-static ρ-x-static ρ-y-static))
(define static-y-contains-x (region-contains? ir-static ρ-y-static ρ-x-static))
(check-true static-x-contains-y)
(check-false static-y-contains-x)

;; 実行時側: R-LetOwned が p を割り当てた後の config を見る。
;; config から作った ir と静的な core から作った ir は別の実行結果であるため、
;; region 識別子そのものは一致しない（段 2 の fresh 採番）。
;; 突き合わせるのは識別子ではなく、上の 2 本が述べた包含の真偽である。

;; 両方の Let を通過した config を取る。
(define (all-configs config0 [fuel 200])
  (let loop ([todo (list config0)] [seen '()] [fuel fuel])
    (cond
      [(or (null? todo) (zero? fuel)) (reverse seen)]
      [else
       (define next (append-map raw-steps-g2 todo))
       (loop next (append (reverse todo) seen) (sub1 fuel))])))

(define (config-heap config)
  (match config [`(cfg ,_ ,H ,_ ,_tokens ,_) H]))

(define (config-core config)
  (match config [`(cfg ,c ,_ ,_ ,_tokens ,_) c]))

(define reached
  (for/first ([cfg (in-list (all-configs (inject-g2 nested)))]
              #:when (= 2 (length (config-heap cfg))))
    cfg))
(check-true (and reached #t))

;; 実行時の place を静的な x と y へ結び付ける。
;; H の並びから拾うと、どちらの place がどちらの Let のものか分からない。
;; 誤った owners 割当でも 2 region の包含は同じ形になるため、それでは補題に
;; ならない。R-LetOwned は束縛子を place で置換するため、本体の中の位置が
;; 対応を与える。fixture の本体は (Apply (PrimVal User add) (Move x) (Move y))
;; であり、置換後は第 1 引数が x の place、第 2 引数が y の place である。
(define (applied-places core)
  (let search ([t core])
    (match t
      [`(Apply (PrimVal User add) (Move ,p_x) (Move ,p_y)) (list p_x p_y)]
      [(? list?) (for/or ([e (in-list t)]) (search e))]
      [_ #f])))

(match-define (list p-x p-y) (applied-places (config-core reached)))

;; 置換が済んでいることを確かめる。まだ変数のままなら対応が付いていない。
(check-true (redex-match? G2m p p-x))
(check-true (redex-match? G2m p p-y))
(check-not-equal? p-x p-y)

;; 拾った 2 つの place が H の 2 項目とちょうど対応する。
;; 本体に現れない place が heap にあるなら、fixture の読み方が誤っている。
(check-equal? (list->set (list p-x p-y))
              (list->set (for/list ([entry (in-list (config-heap reached))])
                           (first entry))))

;; ir は 1 度だけ作る。region 識別子は ir ごとに別であるため、
;; 別々に作った ir から引いた region を比べても意味がない。
(define reached-ir (build-region-ir (config-core reached)))
(define ρ-x-run (region-owning reached-ir p-x))
(define ρ-y-run (region-owning reached-ir p-y))

;; 2 つの place は別の region に属する。
(check-not-equal? ρ-x-run ρ-y-run)

;; 補題の本体。region 識別子どうしは比べず、包含の真偽が静的側と一致する
;; ことだけを見る。x と y を取り違えた owners では、この 2 本のどちらかが
;; 反転して落ちる。
(check-equal? (region-contains? reached-ir ρ-x-run ρ-y-run)
              static-x-contains-y)
(check-equal? (region-contains? reached-ir ρ-y-run ρ-x-run)
              static-y-contains-x)

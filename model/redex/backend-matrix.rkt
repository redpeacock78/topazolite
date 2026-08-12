#lang racket

(require "diagnostic.rkt")

(provide (struct-out capability-diagnostic)
         arithmetic-shim-features
         backend-features
         core-form-features
         core-form-feature
         diagnostic-ids
         feature-primitives
         feature-support
         feature-support/matrix
         primitive-feature
         primitive-features
         check-tables!
         check-tables!/matrix)

;; 非対応 feature に当たったときに lower が返す値。近似的な写しは出さない。
;; spec §22: node は棄却した節点そのものであり span ではない。span の算出は
;; lower と lower-value の側へ寄せる。
(struct capability-diagnostic (feature-id backend node reason) #:transparent)

;; feature 正典表。列は
;;   (feature-id racket-cs racketscript shim semantic-test note)
;; racket-cs と racketscript は native / shim / unsupported の 3 値。
;; shim 列は shim 名か #f。semantic-test 列はテスト名、(deferred "..."),
;; または unsupported 行の #f。
(define backend-features
  '((literal          native native #f (deferred "Phase 3 以降") "")
    (variable-binding native native #f (deferred "Phase 3 以降") "")
    (closure          native native #f (deferred "Phase 3 以降") "")
    (tagged-adt       native native #f (deferred "Phase 3 以降") "")
    (immutable-record native native #f (deferred "Phase 3 以降") "")
    (effect-dispatch  native native #f (deferred "Phase 3 以降") "")
    (scope-exit       native native #f (deferred "Phase 3 以降") "")
    (runtime-call     native native #f (deferred "Phase 3 以降") "")
    (resource-runtime native native #f (deferred "Phase 3 以降") "")
    (static-erasure   native native #f (deferred "Phase 3 以降") "")
    ;; primitive 値そのものの写し。η 展開した closure を作るだけなので両 backend
    ;; で native である。どの名前を写せるかは下の 7 行が決める
    ;; （backend-matrix.md §7）。
    (primitive-value  native native #f (deferred "Phase 3 以降") "")
    ;; Γ0 の 7 件は名前ごとに 1 行を持つ。shim 列は名前 1 つであり、リストを置か
    ;; ない（backend-matrix.md §10）。算術と比較の 6 件は G3c の表の検査が native を
    ;; 禁じる対象になる（backend-matrix.md §10）。
    (primitive-add    shim shim tz:add (deferred "Phase 3 以降")
                      "算術は Host の演算を直接指さない")
    (primitive-sub    shim shim tz:sub (deferred "Phase 3 以降")
                      "算術は Host の演算を直接指さない")
    (primitive-mul    shim shim tz:mul (deferred "Phase 3 以降")
                      "算術は Host の演算を直接指さない")
    (primitive-lt     shim shim tz:lt (deferred "Phase 3 以降")
                      "比較は Host の演算を直接指さない")
    (primitive-le     shim shim tz:le (deferred "Phase 3 以降")
                      "比較は Host の演算を直接指さない")
    (primitive-eq     shim shim tz:eq (deferred "Phase 3 以降")
                      "比較は Host の演算を直接指さない")
    (primitive-acquire shim shim tz:acquire (deferred "Phase 3 以降")
                      "資源取得は Host の演算を直接指さない")
    ;; 予約行。Typed Core に対応する型が無いので形の対応表には現れない。両
    ;; backend の support を shim とするのは、Racket の任意精度整数でも
    ;; RacketScript の倍精度数でも固定幅の切り詰めを native に持たないためで
    ;; ある。native を宣言すると backend-matrix.md §10 と矛盾する。
    (fixed-width-int   shim shim tz:wrap (deferred "Phase 2 以降")
                       "固定幅の切り詰めは Phase 2 以降の型追加を待つ")
    (bits-n            shim shim tz:bits (deferred "Phase 2 以降")
                       "Bits<N> に対応する Typed Core の型が無い")
    (kernel-primitive unsupported unsupported #f #f
                      "Phase 0 の Typed Core は kernel primitive を持たない")
    (trait-primitive  unsupported unsupported #f #f
                      "trait primitive の写しは Phase 2 以降の emitter を待つ")))

;; 診断 ID 一覧。feature に対応する ID と、対応しない ID の 2 種類がある。
;; unknown-core-form は対応表に無い形、unknown-core-type は op-code が τ でない
;; 入力を受けたときの fallback である（backend-matrix.md §8）。
;; どちらも backend の能力の話ではないので support 値を持たない。
;;
;; 表そのものは diagnostic.rkt の registry が持ち、ここはその射影である。
;; 同じ 4 件を 2 箇所に置くと二重管理になるため、整合を test で検出するのでは
;; なく、食い違いうる状態を無くしている。並びは registry の lowering 行の
;; 並びであり、従来の列と同じである。
(define diagnostic-ids
  (for/list ([row (in-list diagnostic-registry)]
             #:when (eq? (diagnostic-code-phase row) 'lowering))
    (list (diagnostic-code-key row)
          (diagnostic-code-title row))))

;; c と v の頭シンボルから feature-id への形の対応表であり、
;; backend-matrix.md §7 の feature 対応を形へ割り当てる。
;; 表の突合は、この左辺の集合と lang.rkt の c と v の形の集合を比べ、
;; backend-matrix.md §7 が求める表の完全性を確かめる。
;; 集合をここへ書くのは、Redex の language-nts が非終端名しか返さず、生成規則の右辺を
;; 取る公開 API が無いためである。lang.rkt に形が増えたとき、この表を更新しなければ
;; 検査が落ちる。
;;
;; 変数と literal は頭シンボルを持たないので、% を冠した擬似的な頭で表す。% は
;; G2m にも PR にも現れないので、源の形の名前と衝突しない。
(define core-form-features
  '((%literal   literal)
    (%variable  variable-binding)
    (Let        variable-binding)
    (Recur      variable-binding)
    (RecurVal   variable-binding)
    (Apply      closure)
    (Lam        closure)
    (CurryVal   closure)
    (Construct  tagged-adt)
    (Eliminate  tagged-adt)
    (UVal       tagged-adt)
    (RVal       tagged-adt)
    (Rec        immutable-record)
    (Proj       immutable-record)
    (Perform    effect-dispatch)
    (Handle     effect-dispatch)
    (Scope      scope-exit)
    (Yield      runtime-call)
    (Suspend    runtime-call)
    (Move       runtime-call)
    (Drop       runtime-call)
    (Curry      runtime-call)
    (Error      resource-runtime)
    (resource   resource-runtime)
    (Discharge  static-erasure)
    (TypeRep    static-erasure)
    (ProofRep   static-erasure)
    (PrimVal    primitive-value)))

;; 対応表に無い頭シンボルで例外を投げない。lower が全域であるための土台であり、
;; 呼び出し側が #f を unknown-core-form の診断へ変える（backend-matrix.md §8）。
(define (core-form-feature head)
  (define row (assq head core-form-features))
  (and row (second row)))

;; Γ0 の primitive の名前から feature-id への写像である。`PrimVal` の頭が指す
;; `primitive-value` とは別の層であり、名前の feature を lower が別々に引く
;;（backend-matrix.md §7）。名前と feature を 1 対 1 にしてあるのは、
;; shim 列が名前 1 つを持つ backend-matrix.md §10 の約束を守るためであり、
;; 1 件を unsupported にしたときに他の名前まで閉じないためでもある。
(define primitive-features
  '((add . primitive-add)
    (sub . primitive-sub)
    (mul . primitive-mul)
    (lt  . primitive-lt)
    (le  . primitive-le)
    (eq  . primitive-eq)
    (acquire . primitive-acquire)))

;; 算術と比較の 6 件。backend-matrix.md §10 の「native を禁じる検査」は
;; この 6 件だけを対象にする。acquire は資源取得であり、算術の禁則とは別の理由で shim
;; である。
(define arithmetic-shim-features
  '(primitive-add primitive-sub primitive-mul
    primitive-lt primitive-le primitive-eq))

;; 表に無い名前で例外を投げない。呼び出し側が #f を unknown-core-form の診断へ変
;; える（backend-matrix.md §8）。
(define (primitive-feature nm)
  (define row (assq nm primitive-features))
  (and row (cdr row)))

;; feature-id からその feature が覆う名前を引く。名前の束を lowering.rkt が二重に
;; 持たないための逆写像である。
(define (feature-primitives feature-id)
  (for/list ([row (in-list primitive-features)]
             #:when (eq? (cdr row) feature-id))
    (car row)))

(define (feature-row matrix feature-id)
  (or (assq feature-id matrix)
      (error 'feature-support "unknown feature id: ~a" feature-id)))

(define (feature-support/matrix matrix feature-id backend)
  (define row (feature-row matrix feature-id))
  (case backend
    [(racket-cs) (second row)]
    [(racketscript) (third row)]
    [else (error 'feature-support "unknown backend: ~a" backend)]))

(define (feature-support feature-id backend)
  (feature-support/matrix backend-features feature-id backend))

(define (row-unsupported? row)
  (or (eq? (second row) 'unsupported)
      (eq? (third row) 'unsupported)))

;; 表と診断 ID 一覧の整合検査。正典表以外の表も検査できるよう matrix を取る。
(define (check-tables!/matrix matrix)
  (define ids (map first matrix))
  (unless (= (length ids) (set-count (list->set ids)))
    (error 'check-tables! "duplicate feature id"))
  (for ([row (in-list matrix)])
    (define id (first row))
    (for ([support (in-list (list (second row) (third row)))])
      (unless (memq support '(native shim unsupported))
        (error 'check-tables! "~a: invalid support value: ~a" id support)))
    (when (and (or (eq? (second row) 'shim) (eq? (third row) 'shim))
               (not (fourth row)))
      (error 'check-tables! "~a: shim row names no shim" id))
    (when (and (eq? (second row) 'native)
               (eq? (third row) 'native)
               (fourth row))
      (error 'check-tables! "~a: native row names a shim" id))
    (cond
      [(row-unsupported? row)
       (when (fifth row)
         (error 'check-tables! "~a: unsupported row carries a semantic test" id))
       (when (or (not (string? (sixth row))) (string=? (sixth row) ""))
         (error 'check-tables! "~a: unsupported row states no reason" id))
       (unless (assq id diagnostic-ids)
         (error 'check-tables! "~a: unsupported row is absent from the roster"
                id))]
      [else
       (unless (fifth row)
         (error 'check-tables! "~a: row carries no semantic test" id))]))
  (define feature-ids (list->set ids))
  (define orphans
    (for/list ([entry (in-list diagnostic-ids)]
               #:unless (set-member? feature-ids (first entry)))
      (first entry)))
  (unless (equal? orphans '(unknown-core-form unknown-core-type))
    (error 'check-tables! "unexpected non-feature diagnostic ids: ~a" orphans))
  (for ([entry (in-list diagnostic-ids)])
    (when (or (not (string? (second entry))) (string=? (second entry) ""))
      (error 'check-tables! "~a: roster entry states no reason" (first entry))))
  ;; 形の対応表の右辺は正典表の行でなければならない。形を足したときに feature を
  ;; 宣言し忘れると load 時に落ちる。
  (define form-heads (map first core-form-features))
  (unless (= (length form-heads) (set-count (list->set form-heads)))
    (error 'check-tables! "duplicate core form head"))
  (for ([row (in-list core-form-features)])
    (unless (set-member? feature-ids (second row))
      (error 'check-tables! "~a: undeclared feature ~a"
             (first row) (second row))))
  ;; 名前の対応表も同じ規律に従う。名前を足して feature を書き忘れると load 時に
  ;; 落ちる。Γ0 との突合は表の検査では行わず、lowering 側の primitive-arity が
  ;; Γ0 を引き、shim-primitives が feature-primitives 経由で担保する
  ;; （backend-matrix.md §10）。
  (for ([row (in-list primitive-features)])
    (unless (set-member? feature-ids (cdr row))
      (error 'check-tables! "~a: undeclared feature ~a"
             (car row) (cdr row))))
  ;; backend-matrix.md §10。算術と比較の shim feature は両 backend で shim を
  ;; 要求し、
  ;; native を許さない。backend を差し替えても結果が変わらないことの Phase 0 に
  ;; おける形である。
  (for* ([feature-id (in-list arithmetic-shim-features)]
         [backend (in-list '(racket-cs racketscript))])
    (unless (eq? (feature-support/matrix matrix feature-id backend) 'shim)
      (error 'check-tables! "~a: arithmetic feature is not shim on ~a"
             feature-id backend)))
  (void))

(define (check-tables!) (check-tables!/matrix backend-features))

(check-tables!)

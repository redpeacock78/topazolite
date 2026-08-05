#lang racket

(provide (struct-out capability-diagnostic)
         backend-features
         diagnostic-ids
         feature-support
         check-tables!)

;; 非対応 feature に当たったときに lower が返す値。近似的な写しは出さない。
(struct capability-diagnostic (feature-id backend reason) #:transparent)

;; feature 正典表。列は
;;   (feature-id racket-cs racketscript shim semantic-test note)
;; racket-cs と racketscript は native / shim / unsupported の 3 値。
;; shim 列は shim 名か #f。semantic-test 列はテスト名、(deferred "..."),
;; または unsupported 行の #f。
(define backend-features
  '((closure          native native #f (deferred "Phase 3 以降") "")
    (tagged-adt       native native #f (deferred "Phase 3 以降") "")
    (immutable-record native native #f (deferred "Phase 3 以降") "")
    (effect-dispatch  native native #f (deferred "Phase 3 以降") "")
    (scope-exit       native native #f (deferred "Phase 3 以降") "")
    (kernel-primitive unsupported unsupported #f #f
                      "Phase 0 の Typed Core は kernel primitive を持たない")
    (trait-primitive  unsupported unsupported #f #f
                      "trait primitive の写しは Phase 2 以降の emitter を待つ")))

;; 診断 ID 一覧。feature に対応する ID と、対応しない ID の 2 種類がある。
;; unknown-core-form は対応表に無い形、unknown-core-type は op-code が τ でない
;; 入力を受けたときの fallback である（spec §6.4）。どちらも backend の能力の話
;; ではないので support 値を持たない。
(define diagnostic-ids
  '((kernel-primitive "Typed Core の kernel primitive は写し先を持たない")
    (trait-primitive  "trait primitive は Phase 2 以降の emitter を待つ")
    (unknown-core-form "対応表に無い Typed Core の形")
    (unknown-core-type "op-code の入力が Typed Core の τ でない")))

(define (feature-row feature-id)
  (or (assq feature-id backend-features)
      (error 'feature-support "unknown feature id: ~a" feature-id)))

(define (feature-support feature-id backend)
  (define row (feature-row feature-id))
  (case backend
    [(racket-cs) (second row)]
    [(racketscript) (third row)]
    [else (error 'feature-support "unknown backend: ~a" backend)]))

(define (row-unsupported? row)
  (or (eq? (second row) 'unsupported)
      (eq? (third row) 'unsupported)))

;; 表と診断 ID 一覧の整合検査。load 時に走らせ、表を書き換えたときに気付ける
;; ようにする。
(define (check-tables!)
  (define ids (map first backend-features))
  (unless (= (length ids) (set-count (list->set ids)))
    (error 'check-tables! "duplicate feature id"))
  (for ([row (in-list backend-features)])
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
  (define feature-ids (list->set (map first backend-features)))
  (define orphans
    (for/list ([entry (in-list diagnostic-ids)]
               #:unless (set-member? feature-ids (first entry)))
      (first entry)))
  (unless (equal? orphans '(unknown-core-form unknown-core-type))
    (error 'check-tables! "unexpected non-feature diagnostic ids: ~a" orphans))
  (for ([entry (in-list diagnostic-ids)])
    (when (or (not (string? (second entry))) (string=? (second entry) ""))
      (error 'check-tables! "~a: roster entry states no reason" (first entry))))
  (void))

(check-tables!)

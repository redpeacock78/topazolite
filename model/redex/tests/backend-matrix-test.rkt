#lang racket

(require racket/set
         rackunit
         "../backend-matrix.rkt")

;; [REQ: BAK-003]
;; [REQ: BIT-002] 算術 shim の宣言を表の検査で固定する。

(define (row-feature-id row) (first row))
(define (row-racket-cs row) (second row))
(define (row-racketscript row) (third row))
(define (row-shim row) (fourth row))
(define (row-semantic-test row) (fifth row))
(define (row-note row) (sixth row))

(define (row-unsupported? row)
  (or (eq? (row-racket-cs row) 'unsupported)
      (eq? (row-racketscript row) 'unsupported)))

(test-case
 "support values are limited to the three declared symbols"
 ;; memq は真のとき非空リストを返す。check-true は #t そのものを要求するので
 ;; ここでは使えない。
 (for ([row (in-list backend-features)])
   (check-not-false (memq (row-racket-cs row) '(native shim unsupported))
                    (format "racket-cs of ~a" (row-feature-id row)))
   (check-not-false (memq (row-racketscript row) '(native shim unsupported))
                    (format "racketscript of ~a" (row-feature-id row)))))

(test-case
 "a row declaring shim names the shim"
 (for ([row (in-list backend-features)]
       #:when (or (eq? (row-racket-cs row) 'shim)
                  (eq? (row-racketscript row) 'shim)))
   (check-not-false (row-shim row)
                    (format "shim column of ~a" (row-feature-id row)))))

(test-case
 "a row native on both backends names no shim"
 (for ([row (in-list backend-features)]
       #:when (and (eq? (row-racket-cs row) 'native)
                   (eq? (row-racketscript row) 'native)))
   (check-false (row-shim row)
                (format "shim column of ~a" (row-feature-id row)))))

(test-case
 "a row without unsupported carries a semantic test"
 (for ([row (in-list backend-features)]
       #:unless (row-unsupported? row))
   (check-not-false (row-semantic-test row)
                    (format "semantic-test of ~a" (row-feature-id row)))))

(test-case
 "feature ids do not repeat"
 (define ids (map row-feature-id backend-features))
 (check-equal? (length ids) (set-count (list->set ids))))

;; unsupported 行の 4 つの義務。semantic-test を免除するだけだと、support 値を
;; unsupported に書き換えれば検査を免れる。

(test-case
 "an unsupported row carries no semantic test"
 (for ([row (in-list backend-features)]
       #:when (row-unsupported? row))
   (check-false (row-semantic-test row)
                (format "semantic-test of ~a" (row-feature-id row)))))

(test-case
 "an unsupported row states a reason in the note column"
 (for ([row (in-list backend-features)]
       #:when (row-unsupported? row))
   (check-true (and (string? (row-note row))
                    (not (string=? (row-note row) "")))
               (format "note of ~a" (row-feature-id row)))))

(test-case
 "an unsupported feature id is declared in the diagnostic roster"
 (define roster (list->set (map first diagnostic-ids)))
 (for ([row (in-list backend-features)]
       #:when (row-unsupported? row))
   (check-true (set-member? roster (row-feature-id row))
               (format "roster entry for ~a" (row-feature-id row)))))

(test-case
 "the roster ids absent from the feature table are exactly the two fallbacks"
 ;; backend-matrix.md §8。feature に対応しない診断 ID は unknown-core-form
 ;; （対応表に無い
 ;; 形）と unknown-core-type（τ でない op-code の入力）の 2 件だけである。
 (define feature-ids (list->set (map row-feature-id backend-features)))
 (define orphans
   (for/list ([entry (in-list diagnostic-ids)]
              #:unless (set-member? feature-ids (first entry)))
     (first entry)))
 (check-equal? orphans '(unknown-core-form unknown-core-type)))

(test-case
 "every roster entry states a reason"
 (for ([entry (in-list diagnostic-ids)])
   (check-true (and (string? (second entry))
                    (not (string=? (second entry) "")))
               (format "reason of ~a" (first entry)))))

(test-case
 "check-tables! accepts the canonical tables"
 (check-not-exn (lambda () (check-tables!))))

(test-case
 "feature-support reads the declared value"
 (check-eq? (feature-support 'kernel-primitive 'racket-cs) 'unsupported)
 (check-eq? (feature-support 'kernel-primitive 'racketscript) 'unsupported))

(test-case
 "capability-diagnostic carries the feature id, backend, and reason"
 (define diagnostic
   (capability-diagnostic 'kernel-primitive 'racket-cs "test"))
 (check-eq? (capability-diagnostic-feature-id diagnostic) 'kernel-primitive)
 (check-eq? (capability-diagnostic-backend diagnostic) 'racket-cs)
 (check-equal? (capability-diagnostic-reason diagnostic) "test"))

(test-case
 "every core form names a feature declared in the canonical table"
 (define feature-ids (list->set (map row-feature-id backend-features)))
 (for ([row (in-list core-form-features)])
   (check-true (set-member? feature-ids (second row))
               (format "feature of ~a" (first row)))))

(test-case
 "core form heads do not repeat"
 (define heads (map first core-form-features))
 (check-equal? (length heads) (set-count (list->set heads))))

(test-case
 "core-form-feature reads the table and fails closed"
 (check-eq? (core-form-feature 'Apply) 'closure)
 (check-eq? (core-form-feature '%literal) 'literal)
 (check-eq? (core-form-feature 'PrimVal) 'primitive-value)
 ;; 対応表に無い頭シンボルは例外ではなく #f を返す。lower はこれを
 ;; unknown-core-form の診断へ変える（backend-matrix.md §8）。
 (check-false (core-form-feature 'Frobnicate)))

(test-case
 "every primitive name has its own shim feature"
 ;; backend-matrix.md §10。shim 列は名前 1 つであり、リストを置かない。
 ;; 名前と feature が
 ;; 1 対 1 なので、1 件を unsupported にしても他の 6 件は閉じない。
 (check-equal? (sort (map car primitive-features) symbol<?)
               '(acquire add eq le lt mul sub))
 (define feature-ids (map cdr primitive-features))
 (check-equal? (length feature-ids) (set-count (list->set feature-ids)))
 (check-eq? (primitive-feature 'add) 'primitive-add)
 (check-eq? (primitive-feature 'acquire) 'primitive-acquire)
 ;; Γ0 に無い名前は例外ではなく #f を返す。lower はこれを unknown-core-form の
 ;; 診断へ変える（backend-matrix.md §8）。
 (check-false (primitive-feature 'frobnicate))
 (check-equal? (feature-primitives 'primitive-add) '(add))
 (check-equal? (feature-primitives 'primitive-value) '()))

(test-case
 "the primitive features are shim on both backends"
 ;; backend-matrix.md §10。native を許さない検査そのものは Task 15 で足す。
 ;; ここでは表の値だけ
 ;; を固定する。
 (for* ([feature-id (in-list (map cdr primitive-features))]
        [backend (in-list '(racket-cs racketscript))])
   (check-eq? (feature-support feature-id backend) 'shim
              (format "~a on ~a" feature-id backend)))
 ;; PrimVal の頭に付く feature は別である。η 展開した closure を作るだけなので、
 ;; 両 backend で native であり、算術を閉じても閉じない（backend-matrix.md §7）。
 (check-eq? (feature-support 'primitive-value 'racket-cs) 'native)
 (check-eq? (feature-support 'primitive-value 'racketscript) 'native)
 ;; 算術と比較の 6 件だけを G3c の検査の対象にする。
 (check-equal? (sort arithmetic-shim-features symbol<?)
               '(primitive-add primitive-eq primitive-le primitive-lt
                 primitive-mul primitive-sub)))

(test-case
 "feature-support/matrix reads the injected table"
 ;; test seam。正典表と同じ形の別の表を読む（backend-matrix.md §5）。
 (define injected
   (for/list ([row (in-list backend-features)])
     (if (eq? (row-feature-id row) 'closure)
         '(closure unsupported unsupported #f #f "test seam")
         row)))
 (check-eq? (feature-support/matrix injected 'closure 'racket-cs) 'unsupported)
 (check-eq? (feature-support 'closure 'racket-cs) 'native))

(test-case
 "check-tables! rejects an arithmetic feature declared native"
 ;; 検査そのものが効いていることを、壊した写しで確かめる。native / native は
 ;; shim 列が #f なので既存の 4 本は通り、算術の検査だけが落ちる。
 (for ([feature-id (in-list arithmetic-shim-features)])
   (define broken
     (for/list ([row (in-list backend-features)])
       (if (eq? (row-feature-id row) feature-id)
           (list feature-id 'native 'native #f '(deferred "Phase 3 以降") "")
           row)))
   (check-exn exn:fail? (lambda () (check-tables!/matrix broken))
              (format "native ~a" feature-id)))
 (check-not-exn (lambda () (check-tables!/matrix backend-features))))

(test-case
 "the arithmetic roster is exactly the primitives minus resource acquisition"
 ;; 名前を足して名簿へ入れ忘れると、その名前だけ native を宣言できてしまう。
 ;; 名前の表の像と名簿を突き合わせて閉じる（backend-matrix.md §10）。
 (check-equal? (sort arithmetic-shim-features symbol<?)
               (sort (for/list ([row (in-list primitive-features)]
                                #:unless (eq? (car row) 'acquire))
                       (cdr row))
                     symbol<?))
 ;; 資源取得も shim だが、native を禁じる検査の対象ではない。
 (check-false (memq 'primitive-acquire arithmetic-shim-features))
 (check-eq? (feature-support 'primitive-acquire 'racket-cs) 'shim)
 (check-eq? (feature-support 'primitive-acquire 'racketscript) 'shim))

(test-case
 "check-tables! rejects a primitive naming an undeclared feature"
 ;; 名前の表の右辺が正典表に無い場合も落ちる。名前を足して行を書き忘れる経路
 ;; である（backend-matrix.md §10）。
 (define broken
   (for/list ([row (in-list backend-features)]
              #:unless (eq? (row-feature-id row) 'primitive-eq))
     row))
 (check-exn exn:fail? (lambda () (check-tables!/matrix broken))))

(test-case
 "fixed width integers and Bits<N> are reserved rows"
 ;; backend-matrix.md §10。Typed Core に対応する型が無いので、
 ;; 形の対応表の値域には現れない。
 (for ([feature-id (in-list '(fixed-width-int bits-n))])
   (define row (assq feature-id backend-features))
   (check-not-false row (format "reserved row ~a" feature-id))
   (check-eq? (row-racket-cs row) 'shim)
   (check-eq? (row-racketscript row) 'shim)
   (check-equal? (row-semantic-test row) '(deferred "Phase 2 以降"))
   ;; shim 列は名前 1 つである（backend-matrix.md §10）。
   (check-true (symbol? (row-shim row)))
   (check-true (and (string? (row-note row))
                    (not (string=? (row-note row) "")))))
 (define assigned (list->set (map second core-form-features)))
 (check-false (set-member? assigned 'fixed-width-int))
 (check-false (set-member? assigned 'bits-n))
 ;; 予約行は名前の表にも現れない。Γ0 に対応する primitive が無いためである。
 (define named (list->set (map cdr primitive-features)))
 (check-false (set-member? named 'fixed-width-int))
 (check-false (set-member? named 'bits-n)))

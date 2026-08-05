#lang racket

(require racket/set
         rackunit
         "../backend-matrix.rkt")

;; [REQ: BAK-003]

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
 ;; spec §8.1。feature に対応しない診断 ID は unknown-core-form（対応表に無い
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

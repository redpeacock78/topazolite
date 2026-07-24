#lang racket

(require racket/file
         racket/set
         racket/string
         rackunit
         "../../../tools/req-coverage.rkt")

(define (write-text path content)
  (call-with-output-file path
    (lambda (output) (display content output))
    #:exists 'truncate))

(define (registry-entry id [state "G1"])
  (format "### ~a\n\n- **状態**：~a\n" id state))

(define (with-fixture registry spec test procedure)
  (define root (make-temporary-file "req-coverage~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (define registry-path (build-path root "requirements.md"))
      (define spec-path (build-path root "spec.md"))
      (define test-path (build-path root "test.rkt"))
      (write-text registry-path registry)
      (write-text spec-path spec)
      (write-text test-path test)
      (procedure registry-path (list spec-path) (list test-path)))
    (lambda () (delete-directory/files root))))

;; This file is scanned as a test input, so fixture IDs must not be literal
;; requirement references that could make the real coverage check pass.
(define known-id (string-append "NAR" "-001"))
(define typ-003 (string-append "TYP" "-003"))
(define row-001 (string-append "ROW" "-001"))
(define row-002 (string-append "ROW" "-002"))
(define row-003 (string-append "ROW" "-003"))
(define row-004 (string-append "ROW" "-004"))
(define psr-001 (string-append "PSR" "-001"))
(define psr-002 (string-append "PSR" "-002"))
(define psr-003 (string-append "PSR" "-003"))
(define trt-001 (string-append "TRT" "-001"))

(define expected-g2a-ids
  (set typ-003 row-001 row-002 row-003 row-004))
(define expected-g2b-ids
  (set psr-001 psr-002 psr-003))

(define (registry-entries ids state)
  (apply string-append
         (for/list ([id (in-list ids)])
           (registry-entry id state))))

(define (spec-references ids)
  (string-join
   (for/list ([id (in-list ids)])
     (format "[REQ: ~a]" id))
   "\n"))

(define (test-references ids)
  (string-join
   (for/list ([id (in-list ids)])
     (format "(test-case ~s (void))" id))
   "\n"))

(define g2a-ids (sort (set->list expected-g2a-ids) string<?))
(define g2a-ids-missing (remove row-004 g2a-ids))
(define g2a-ids-replaced (sort (cons trt-001 g2a-ids-missing) string<?))

(define g2a-registry (registry-entries g2a-ids "G2"))
(define g2a-spec (spec-references g2a-ids))
(define g2a-test (test-references g2a-ids))
(define g2a-registry-missing (registry-entries g2a-ids-missing "G2"))
(define g2a-spec-missing (spec-references g2a-ids-missing))
(define g2a-test-missing (test-references g2a-ids-missing))
(define g2a-registry-replaced (registry-entries g2a-ids-replaced "G2"))
(define g2a-spec-replaced (spec-references g2a-ids-replaced))
(define g2a-test-replaced (test-references g2a-ids-replaced))

(define g2b-ids (sort (set->list expected-g2b-ids) string<?))
(define g2b-ids-missing (remove psr-003 g2b-ids))
(define g2b-ids-replaced (sort (cons trt-001 g2b-ids-missing) string<?))

(define (fixture-errors registry spec test
                        #:expected-g1-count [expected-g1-count #f]
                        #:expected-g2a-ids [expected-g2a-ids #f])
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (if expected-g2a-ids
         (coverage-errors registry-path '() '()
                          #:g2a-spec-paths spec-paths
                          #:g2a-test-paths test-paths
                          #:expected-g2a-ids expected-g2a-ids)
         (coverage-errors registry-path spec-paths test-paths
                          #:expected-g1-count expected-g1-count)))))

(define (fixture-errors-g2b registry spec test)
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (coverage-errors registry-path '() '()
                      #:g2b-spec-paths spec-paths
                      #:g2b-test-paths test-paths
                      #:expected-g2b-ids expected-g2b-ids))))

(test-case "G2a coverage requires the exact ID set"
  (check-equal?
   (fixture-errors g2a-registry g2a-spec g2a-test
                   #:expected-g2a-ids expected-g2a-ids)
   '())
  (check-not-false
   (member
    (format "G2a spec ID set missing expected ID: ~a" row-004)
    (fixture-errors g2a-registry-missing
                    g2a-spec-missing
                    g2a-test-missing
                    #:expected-g2a-ids expected-g2a-ids)))
  ;; A five-for-five replacement must report both halves of the symmetric
  ;; difference instead of passing on count alone.
  (define replaced-errors
    (fixture-errors g2a-registry-replaced
                    g2a-spec-replaced
                    g2a-test-replaced
                    #:expected-g2a-ids expected-g2a-ids))
  (check-not-false
   (member (format "G2a spec ID set missing expected ID: ~a" row-004)
           replaced-errors))
  (check-not-false
   (member (format "G2a spec ID set contains unexpected ID: ~a" trt-001)
           replaced-errors))
  (check-not-false
   (member (format "G2a test ID set missing expected ID: ~a" row-004)
           replaced-errors))
  (check-not-false
   (member (format "G2a test ID set contains unexpected ID: ~a" trt-001)
           replaced-errors)))

(test-case "G2b coverage requires the exact ID set"
  (check-equal?
   (fixture-errors-g2b
    (registry-entries g2b-ids "G2")
    (spec-references g2b-ids)
    (test-references g2b-ids))
   '())
  (check-not-false
   (member
    (format "G2b spec ID set missing expected ID: ~a" psr-003)
    (fixture-errors-g2b
     (registry-entries g2b-ids-missing "G2")
     (spec-references g2b-ids-missing)
     (test-references g2b-ids-missing))))
  (define replaced-errors
    (fixture-errors-g2b
     (registry-entries g2b-ids-replaced "G2")
     (spec-references g2b-ids-replaced)
     (test-references g2b-ids-replaced)))
  (check-not-false
   (member (format "G2b spec ID set contains unexpected ID: ~a" trt-001)
           replaced-errors))
  (check-not-false
   (member (format "G2b test ID set contains unexpected ID: ~a" trt-001)
           replaced-errors)))

(test-case "normal coverage passes"
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    (format "[REQ: ~a]\n" known-id)
    (format "(test-case ~s (void))\n" known-id))
   '()))

(test-case "heading titles are accepted"
  (check-equal?
   (fixture-errors
    (format "### ~a title\n\n- **状態**：G1\n" known-id)
    (format "[REQ: ~a]\n" known-id)
    (format "(test-case ~s (void))\n" known-id))
   '()))

(test-case "spec and test reference gaps remain distinct"
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    (format "[REQ: ~a]\n" known-id)
    "")
   (list (format "G1 requirement lacks test reference: ~a" known-id)))
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    ""
    (format "(test-case ~s (void))\n" known-id))
   (list (format "G1 requirement lacks spec annotation: ~a" known-id))))

(test-case "unknown references fail"
  (define unknown-id (string-append "ZZZ" "-999"))
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    (format "[REQ: ~a] [REQ: ~a]\n" known-id unknown-id)
    (format "(test-case ~s (void))\n" known-id))
   (list (format "unknown requirement ID: ~a" unknown-id))))

(test-case "test IDs require token boundaries"
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    (format "[REQ: ~a]\n" known-id)
    "XNAR-001 SMART-001\n")
   (list (format "G1 requirement lacks test reference: ~a" known-id))))

(test-case "invalid states and unexpected G1 counts fail closed"
  (check-equal?
   (fixture-errors
    (format "### ~a\n\n- **状態**: G1\n" known-id)
    (format "[REQ: ~a]\n" known-id)
    (format "(test-case ~s (void))\n" known-id))
   (list (format "invalid or missing requirement state: ~a" known-id)))
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    (format "[REQ: ~a]\n" known-id)
    (format "(test-case ~s (void))\n" known-id)
    #:expected-g1-count 2)
   (list "expected 2 G1 requirements, found 1")))

(test-case "duplicate registry definitions fail"
  (check-equal?
   (fixture-errors
    (string-append (registry-entry known-id)
                   (registry-entry known-id))
    (format "[REQ: ~a]\n" known-id)
    (format "(test-case ~s (void))\n" known-id))
   (list (format "duplicate requirement ID: ~a" known-id))))

(test-case "run-coverage returns failure and writes diagnostics"
  (with-fixture
   (registry-entry known-id)
   (format "[REQ: ~a]\n" known-id)
   ""
   (lambda (registry-path spec-paths test-paths)
     (define output (open-output-string))
     (define errors (open-output-string))
     (check-equal?
      (run-coverage registry-path spec-paths test-paths output errors)
      1)
     (check-equal? (get-output-string output) "")
     (check-true
      (regexp-match? #rx"lacks test reference"
                     (get-output-string errors))))))

(test-case "main resolves repository paths and reports the expected count"
  (define output (open-output-string))
  (define errors (open-output-string))
  (check-equal? (main output errors) 0)
  (check-equal? (get-output-string output)
                "Requirement coverage OK: 18 G1 IDs, 5 G2a IDs, 3 G2b IDs\n")
  (check-equal? (get-output-string errors) ""))

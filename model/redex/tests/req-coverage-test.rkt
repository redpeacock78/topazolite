#lang racket

(require racket/file
         rackunit
         "../../../tools/req-coverage.rkt")

(define (write-text path content)
  (call-with-output-file path
    (lambda (output) (display content output))
    #:exists 'truncate))

(define (registry-entry id)
  (format "### ~a\n\n- **状態**：G1\n" id))

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

(define (fixture-errors registry spec test
                        #:expected-g1-count [expected-g1-count #f])
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (coverage-errors registry-path spec-paths test-paths
                      #:expected-g1-count expected-g1-count))))

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
                "Requirement coverage OK: 18 G1 IDs\n")
  (check-equal? (get-output-string errors) ""))

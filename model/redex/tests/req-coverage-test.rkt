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

(define (fixture-errors registry spec test)
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
      (coverage-errors registry-path (list spec-path) (list test-path)))
    (lambda () (delete-directory/files root))))

(define known-id (string-append "NAR" "-001"))

(test-case "normal coverage passes"
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    (format "[REQ: ~a]\n" known-id)
    (format "(test-case ~s (void))\n" known-id))
   '()))

(test-case "missing G1 references fail"
  (check-equal?
   (fixture-errors (registry-entry known-id) "" "")
   (list (format "G1 requirement lacks spec annotation: ~a" known-id)
         (format "G1 requirement lacks test reference: ~a" known-id))))

(test-case "unknown references fail"
  (define unknown-id (string-append "ZZZ" "-999"))
  (check-equal?
   (fixture-errors
    (registry-entry known-id)
    (format "[REQ: ~a] [REQ: ~a]\n" known-id unknown-id)
    (format "(test-case ~s (void))\n" known-id))
   (list (format "unknown requirement ID: ~a" unknown-id))))

(test-case "duplicate registry definitions fail"
  (check-equal?
   (fixture-errors
    (string-append (registry-entry known-id)
                   (registry-entry known-id))
    (format "[REQ: ~a]\n" known-id)
    (format "(test-case ~s (void))\n" known-id))
   (list (format "duplicate requirement ID: ~a" known-id))))

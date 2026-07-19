#lang racket

(require racket/file
         racket/runtime-path)

(provide coverage-errors
         main
         run-coverage)

(define heading-rx #px"^### ([A-Z]{3}-[0-9]{3})(?: +.*)?$")
(define state-rx #px"^- \\*\\*状態\\*\\*： *(.+?) *$")
(define spec-id-rx #px"\\[REQ: ([A-Z]{3}-[0-9]{3})\\]")
(define test-id-rx
  #px"(?<![A-Za-z0-9])[A-Z]{3}-[0-9]{3}(?![A-Za-z0-9])")
(define valid-states
  (set "G1" "G2" "G3" "G4" "G5"
       "Phase 1 以降" "Phase 2 以降" "Phase 3 以降"))

(define (registry-definitions path)
  (define definitions '())
  (define current-id #f)
  (for ([line (in-list (file->lines path))])
    (match (regexp-match heading-rx line)
      [(list _ id)
       (set! current-id id)
       (set! definitions (cons (cons id #f) definitions))]
      [_
       (when current-id
         (match (regexp-match state-rx line)
           [(list _ state)
            (set! definitions
                  (cons (cons current-id (string-trim state))
                        (cdr definitions)))]
           [_ (void)]))]))
  (reverse definitions))

(define (spec-ids paths)
  (append-map
   (lambda (path)
     (regexp-match* spec-id-rx (file->string path)
                    #:match-select cadr))
   paths))

(define (test-ids paths)
  (append-map
   (lambda (path)
     (regexp-match* test-id-rx (file->string path)))
   paths))

(define (sorted-ids ids)
  (sort (set->list ids) string<?))

(define (coverage-analysis registry-path spec-paths test-paths
                           expected-g1-count)
  (define definitions (registry-definitions registry-path))
  (define counts (make-hash))
  (for ([definition (in-list definitions)])
    (hash-update! counts (car definition) add1 0))
  (define known (list->set (map car definitions)))
  (define g1
    (list->set
     (for/list ([definition (in-list definitions)]
                #:when (equal? (cdr definition) "G1"))
       (car definition))))
  (define specs (list->set (spec-ids spec-paths)))
  (define tests (list->set (test-ids test-paths)))
  (define g1-count (set-count g1))
  (define duplicates
    (sort
     (for/list ([(id count) (in-hash counts)] #:when (> count 1)) id)
     string<?))
  (define invalid-states
    (list->set
     (for/list ([definition (in-list definitions)]
                #:unless (set-member? valid-states (cdr definition)))
       (car definition))))
  (values
   g1-count
   (append
    (for/list ([id (in-list duplicates)])
      (format "duplicate requirement ID: ~a" id))
    (for/list ([id (in-list (sorted-ids invalid-states))])
      (format "invalid or missing requirement state: ~a" id))
    (if (and expected-g1-count
             (not (= expected-g1-count g1-count)))
        (list (format "expected ~a G1 requirements, found ~a"
                      expected-g1-count g1-count))
        '())
    (for/list ([id (in-list
                    (sorted-ids
                     (set-subtract (set-union specs tests) known)))])
      (format "unknown requirement ID: ~a" id))
    (for/list ([id (in-list (sorted-ids (set-subtract g1 specs)))])
      (format "G1 requirement lacks spec annotation: ~a" id))
    (for/list ([id (in-list (sorted-ids (set-subtract g1 tests)))])
      (format "G1 requirement lacks test reference: ~a" id)))))

(define (coverage-errors registry-path spec-paths test-paths
                         #:expected-g1-count [expected-g1-count #f])
  (define-values (_ errors)
    (coverage-analysis registry-path spec-paths test-paths expected-g1-count))
  errors)

(define (run-coverage registry-path spec-paths test-paths
                      [output (current-output-port)]
                      [error-output (current-error-port)]
                      #:expected-g1-count [expected-g1-count #f])
  (define-values (g1-count errors)
    (coverage-analysis registry-path spec-paths test-paths expected-g1-count))
  (cond
    [(null? errors)
     (fprintf output "Requirement coverage OK: ~a G1 IDs\n" g1-count)
     0]
    [else
     (for ([message (in-list errors)])
       (fprintf error-output "~a\n" message))
     1]))

(define-runtime-path tools-directory ".")

(define (matching-files directory extension-rx)
  (sort
   (for/list ([path (in-directory directory)]
              #:when (and (file-exists? path)
                          (regexp-match? extension-rx
                                         (path->string path))))
     path)
   string<?
   #:key path->string))

;; Update this when the registry intentionally gains or removes a G1 ID.
(define expected-g1-count 18)

(define (main [output (current-output-port)]
              [error-output (current-error-port)])
  (define root (simplify-path (build-path tools-directory 'up)))
  (define registry (build-path root "docs/specification/requirements.md"))
  (define specs (list (build-path root "docs/specification/core-calculus.md")))
  (define tests
    (matching-files (build-path root "model/redex/tests") #rx"[.]rkt$"))
  (run-coverage registry specs tests output error-output
                #:expected-g1-count expected-g1-count))

(module+ main
  (exit (main)))

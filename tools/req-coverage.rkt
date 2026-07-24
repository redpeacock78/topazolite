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

(define (coverage-analysis registry-path g1-spec-paths g1-test-paths
                           expected-g1-count
                           g2a-spec-paths g2a-test-paths
                           expected-g2a-ids
                           g2b-spec-paths g2b-test-paths
                           expected-g2b-ids)
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
  (define g2
    (list->set
     (for/list ([definition (in-list definitions)]
                #:when (equal? (cdr definition) "G2"))
       (car definition))))
  (define g1-specs (list->set (spec-ids g1-spec-paths)))
  (define g1-tests (list->set (test-ids g1-test-paths)))
  (define g2a-spec-references (list->set (spec-ids g2a-spec-paths)))
  (define g2a-test-references (list->set (test-ids g2a-test-paths)))
  (define g2b-spec-references (list->set (spec-ids g2b-spec-paths)))
  (define g2b-test-references (list->set (test-ids g2b-test-paths)))
  ;; G2a property tests may restate G1 invariants, so G1 references are
  ;; allowed in the mapped files.  Every other reference must be in the
  ;; explicit G2a set; this also rejects accidental G3/Phase IDs.
  (define g2a-specs (set-subtract g2a-spec-references g1))
  (define g2a-tests (set-subtract g2a-test-references g1))
  (define earlier-cycle-ids
    (set-union g1 (or expected-g2a-ids (set))))
  (define g2b-specs
    (set-subtract g2b-spec-references earlier-cycle-ids))
  (define g2b-tests
    (set-subtract g2b-test-references earlier-cycle-ids))
  (define all-references
    (set-union g1-specs g1-tests
               g2a-spec-references g2a-test-references
               g2b-spec-references g2b-test-references))
  (define g1-count (set-count g1))
  (define g2a-count
    (if expected-g2a-ids (set-count expected-g2a-ids) 0))
  (define g2b-count
    (if expected-g2b-ids (set-count expected-g2b-ids) 0))
  (define duplicates
    (sort
     (for/list ([(id count) (in-hash counts)] #:when (> count 1)) id)
     string<?))
  (define invalid-states
    (list->set
     (for/list ([definition (in-list definitions)]
                #:unless (set-member? valid-states (cdr definition)))
       (car definition))))
  (define (set-difference-errors actual expected source)
    (append
     (for/list ([id (in-list
                     (sorted-ids (set-subtract expected actual)))])
       (format "~a ID set missing expected ID: ~a" source id))
     (for/list ([id (in-list
                     (sorted-ids (set-subtract actual expected)))])
       (format "~a ID set contains unexpected ID: ~a" source id))))
  (values
   g1-count
   g2a-count
   g2b-count
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
                    (sorted-ids (set-subtract all-references known)))])
      (format "unknown requirement ID: ~a" id))
    (for/list ([id (in-list (sorted-ids (set-subtract g1 g1-specs)))])
      (format "G1 requirement lacks spec annotation: ~a" id))
    (for/list ([id (in-list (sorted-ids (set-subtract g1 g1-tests)))])
      (format "G1 requirement lacks test reference: ~a" id))
    (if expected-g2a-ids
        (append
         (for/list ([id (in-list
                         (sorted-ids
                          (set-subtract expected-g2a-ids g2)))])
           (format "G2a expected ID is absent or not state G2: ~a" id))
         (set-difference-errors g2a-specs expected-g2a-ids
                                "G2a spec")
         (set-difference-errors g2a-tests expected-g2a-ids
                                "G2a test"))
        '())
    (if expected-g2b-ids
        (append
         (for/list ([id (in-list
                         (sorted-ids
                          (set-subtract expected-g2b-ids g2)))])
           (format "G2b expected ID is absent or not state G2: ~a" id))
         (set-difference-errors g2b-specs expected-g2b-ids
                                "G2b spec")
         (set-difference-errors g2b-tests expected-g2b-ids
                                "G2b test"))
        '()))))

(define (coverage-errors registry-path g1-spec-paths g1-test-paths
                         #:expected-g1-count [expected-g1-count #f]
                         #:g2a-spec-paths [g2a-spec-paths '()]
                         #:g2a-test-paths [g2a-test-paths '()]
                         #:expected-g2a-ids [expected-g2a-ids #f]
                         #:g2b-spec-paths [g2b-spec-paths '()]
                         #:g2b-test-paths [g2b-test-paths '()]
                         #:expected-g2b-ids [expected-g2b-ids #f])
  (define-values (_g1-count _g2a-count _g2b-count errors)
    (coverage-analysis registry-path g1-spec-paths g1-test-paths
                       expected-g1-count
                       g2a-spec-paths g2a-test-paths
                       expected-g2a-ids
                       g2b-spec-paths g2b-test-paths
                       expected-g2b-ids))
  errors)

(define (run-coverage registry-path g1-spec-paths g1-test-paths
                      [output (current-output-port)]
                      [error-output (current-error-port)]
                      #:expected-g1-count [expected-g1-count #f]
                      #:g2a-spec-paths [g2a-spec-paths '()]
                      #:g2a-test-paths [g2a-test-paths '()]
                      #:expected-g2a-ids [expected-g2a-ids #f]
                      #:g2b-spec-paths [g2b-spec-paths '()]
                      #:g2b-test-paths [g2b-test-paths '()]
                      #:expected-g2b-ids [expected-g2b-ids #f])
  (define-values (g1-count g2a-count g2b-count errors)
    (coverage-analysis registry-path g1-spec-paths g1-test-paths
                       expected-g1-count
                       g2a-spec-paths g2a-test-paths
                       expected-g2a-ids
                       g2b-spec-paths g2b-test-paths
                       expected-g2b-ids))
  (cond
    [(null? errors)
     (fprintf output "Requirement coverage OK: ~a G1 IDs" g1-count)
     (when expected-g2a-ids
       (fprintf output ", ~a G2a IDs" g2a-count))
     (when expected-g2b-ids
       (fprintf output ", ~a G2b IDs" g2b-count))
     (newline output)
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

;; Update this only when the G2a scope intentionally gains or removes an ID.
(define expected-g2a-ids
  (set "TYP-003" "ROW-001" "ROW-002" "ROW-003" "ROW-004"))

;; Update this only when the G2b scope intentionally gains or removes an ID.
(define expected-g2b-ids
  (set "PSR-001" "PSR-002" "PSR-003"))

(define (main [output (current-output-port)]
              [error-output (current-error-port)])
  (define root (simplify-path (build-path tools-directory 'up)))
  (define registry (build-path root "docs/specification/requirements.md"))
  (define g1-specs
    (list (build-path root "docs/specification/core-calculus.md")))
  (define g1-tests
    (matching-files (build-path root "model/redex/tests") #rx"[.]rkt$"))
  (define g2a-specs
    (list (build-path root "docs/specification/structural-row.md")))
  (define g2a-tests
    (for/list ([name (in-list '("properties-record-test.rkt"
                                "properties-test.rkt"
                                "typing-binding-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (define g2b-specs
    (list (build-path root "docs/specification/proof-search.md")))
  (define g2b-tests
    (for/list ([name (in-list '("search-test.rkt"
                                "search-admissible-test.rkt"
                                "search-discharge-test.rkt"
                                "properties-search-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (run-coverage registry g1-specs g1-tests output error-output
                #:expected-g1-count expected-g1-count
                #:g2a-spec-paths g2a-specs
                #:g2a-test-paths g2a-tests
                #:expected-g2a-ids expected-g2a-ids
                #:g2b-spec-paths g2b-specs
                #:g2b-test-paths g2b-tests
                #:expected-g2b-ids expected-g2b-ids))

(module+ main
  (exit (main)))

#lang racket

(require racket/file
         racket/runtime-path)

(provide (struct-out cycle-descriptor)
         coverage-errors
         default-cycle-descriptors
         main
         run-coverage)

;; サブサイクル 1 件分の入力と期待値。
;; expected-count と expected-ids は、使わない側へ #f を入れる。
(struct cycle-descriptor
  (name spec-paths test-paths expected-count expected-ids)
  #:transparent)

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

(define (coverage-analysis registry-path cycles)
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

  (define (expected-id-set cycle)
    (and (cycle-descriptor-expected-ids cycle)
         (list->set
          (for/list ([id (in-list (cycle-descriptor-expected-ids cycle))])
            (if (symbol? id) (symbol->string id) id)))))
  (define expected-sets (map expected-id-set cycles))
  (define owned-sets
    (for/list ([cycle (in-list cycles)]
               [expected (in-list expected-sets)])
      (cond
        [expected expected]
        [(eq? (cycle-descriptor-name cycle) 'G1) g1]
        [else (set)])))
  (define spec-reference-sets
    (for/list ([cycle (in-list cycles)])
      (list->set (spec-ids (cycle-descriptor-spec-paths cycle)))))
  (define test-reference-sets
    (for/list ([cycle (in-list cycles)])
      (list->set (test-ids (cycle-descriptor-test-paths cycle)))))

  ;; サイクルの正典やテストは、先行要件を回帰として再掲したり、同じ文書に後続
  ;; サイクルの要件を置いたりできる。宣言順から自身以外の既知サイクル ID を
  ;; 引き、そのサイクル固有の参照だけを残す。
  (define (cycle-local-references references index)
    (for/fold ([local references])
              ([ids (in-list owned-sets)]
               [other-index (in-naturals)]
               #:unless (= index other-index))
      (set-subtract local ids)))
  (define cycle-specs
    (for/list ([references (in-list spec-reference-sets)]
               [index (in-naturals)])
      (cycle-local-references references index)))
  (define cycle-tests
    (for/list ([references (in-list test-reference-sets)]
               [index (in-naturals)])
      (cycle-local-references references index)))

  (define all-references
    (for/fold ([references (set)])
              ([cycle-references
                (in-list (append spec-reference-sets test-reference-sets))])
      (set-union references cycle-references)))
  (define cycle-counts (map set-count owned-sets))
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
  (define g1-index
    (for/first ([cycle (in-list cycles)]
                [index (in-naturals)]
                #:when (eq? (cycle-descriptor-name cycle) 'G1))
      index))
  (define g1-specs
    (if g1-index (list-ref spec-reference-sets g1-index) (set)))
  (define g1-tests
    (if g1-index (list-ref test-reference-sets g1-index) (set)))
  (define count-errors
    (append-map
     (lambda (cycle count)
       (define expected (cycle-descriptor-expected-count cycle))
       (if (and expected (not (= expected count)))
           (list
            (format "expected ~a ~a requirements, found ~a"
                    expected (cycle-descriptor-name cycle) count))
           '()))
     cycles cycle-counts))
  (define exact-set-errors
    (append-map
     (lambda (cycle expected actual-specs actual-tests)
       (if expected
           (let ([name (cycle-descriptor-name cycle)])
             (append
              (for/list ([id (in-list
                              (sorted-ids
                               (set-subtract expected g2)))])
                (format "~a expected ID is absent or not state G2: ~a"
                        name id))
              (set-difference-errors actual-specs expected
                                     (format "~a spec" name))
              (set-difference-errors actual-tests expected
                                     (format "~a test" name))))
           '()))
     cycles expected-sets cycle-specs cycle-tests))
  (values
   cycle-counts
   (append
    (for/list ([id (in-list duplicates)])
      (format "duplicate requirement ID: ~a" id))
    (for/list ([id (in-list (sorted-ids invalid-states))])
      (format "invalid or missing requirement state: ~a" id))
    count-errors
    (for/list ([id (in-list
                    (sorted-ids (set-subtract all-references known)))])
      (format "unknown requirement ID: ~a" id))
    (for/list ([id (in-list (sorted-ids (set-subtract g1 g1-specs)))])
      (format "G1 requirement lacks spec annotation: ~a" id))
    (for/list ([id (in-list (sorted-ids (set-subtract g1 g1-tests)))])
      (format "G1 requirement lacks test reference: ~a" id))
    exact-set-errors)))

(define (coverage-errors registry-path
                         #:cycles [cycles (default-cycle-descriptors)])
  (define-values (_counts errors)
    (coverage-analysis registry-path cycles))
  errors)

(define (run-coverage registry-path
                      [output (current-output-port)]
                      [error-output (current-error-port)]
                      #:cycles [cycles (default-cycle-descriptors)])
  (define-values (counts errors)
    (coverage-analysis registry-path cycles))
  (cond
    [(null? errors)
     (display "Requirement coverage OK: " output)
     (for ([cycle (in-list cycles)]
           [count (in-list counts)]
           [index (in-naturals)])
       (unless (zero? index) (display ", " output))
       (fprintf output "~a ~a IDs" count (cycle-descriptor-name cycle)))
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
  '(TYP-003 ROW-001 ROW-002 ROW-003 ROW-004))

;; Update this only when the G2b scope intentionally gains or removes an ID.
(define expected-g2b-ids
  '(PSR-001 PSR-002 PSR-003))

;; Update this only when the G2c scope intentionally gains or removes an ID.
(define expected-g2c-ids
  '(VAR-001 VAR-002 VAR-003))

;; Update this only when the G2d scope intentionally gains or removes an ID.
(define expected-g2d-ids
  '(RFN-001 RFN-002 RFN-003))

;; Update this only when the G2e scope intentionally gains or removes an ID.
(define expected-g2e-ids
  '(TRT-001 TRT-002 TRT-003 CMP-001 CMP-002))

;; Update this only when the G2f scope intentionally gains or removes an ID.
(define expected-g2f-ids
  '(POL-001 POL-002 TRT-004 TRT-005))

(define (default-cycle-descriptors)
  (define root (simplify-path (build-path tools-directory 'up)))
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
  (define g2c-specs
    (list (build-path root "docs/specification/structural-row.md")))
  (define g2c-tests
    (for/list ([name (in-list '("variance-test.rkt"
                                "properties-variance-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (define g2d-specs
    (list (build-path root "docs/specification/proof-value.md")))
  (define g2d-tests
    (for/list ([name (in-list '("refine-lang-test.rkt"
                                "validators-test.rkt"
                                "machine-refine-test.rkt"
                                "typing-refine-test.rkt"
                                "origins-refine-test.rkt"
                                "elaborate-refine-test.rkt"
                                "search-goal-test.rkt"
                                "typing-witness-test.rkt"
                                "compat-discharge-test.rkt"
                                "properties-refine-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (define g2e-specs
    (list (build-path root "docs/specification/trait.md")))
  (define g2e-tests
    ;; Task 16 と Task 17 の統合・性質検査に、CMP-002 の直接回帰を加える。
    (for/list ([name (in-list '("search-trait-integration-test.rkt"
                                "search-coherence-test.rkt"
                                "properties-trait-test.rkt"
                                "type-normalize-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (define g2f-specs
    (for/list ([name (in-list '("policy-narrative.md"
                                "trait.md"))])
      (build-path root "docs/specification" name)))
  (define g2f-tests
    (for/list ([name (in-list '("policy-test.rkt"
                                "search-compose-test.rkt"
                                "properties-policy-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (list
   (cycle-descriptor 'G1 g1-specs g1-tests expected-g1-count #f)
   (cycle-descriptor 'G2a g2a-specs g2a-tests #f expected-g2a-ids)
   (cycle-descriptor 'G2b g2b-specs g2b-tests #f expected-g2b-ids)
   (cycle-descriptor 'G2c g2c-specs g2c-tests #f expected-g2c-ids)
   (cycle-descriptor 'G2d g2d-specs g2d-tests #f expected-g2d-ids)
   (cycle-descriptor 'G2e g2e-specs g2e-tests #f expected-g2e-ids)
   (cycle-descriptor 'G2f g2f-specs g2f-tests #f expected-g2f-ids)))

(define (main [output (current-output-port)]
              [error-output (current-error-port)])
  (define root (simplify-path (build-path tools-directory 'up)))
  (define registry (build-path root "docs/specification/requirements.md"))
  (run-coverage registry output error-output))

(module+ main
  (exit (main)))

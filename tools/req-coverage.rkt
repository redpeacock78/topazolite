#lang racket

(require racket/file
         racket/runtime-path)

(provide (struct-out cycle-descriptor)
         coverage-errors
         deferred-test-counts
         default-cycle-descriptors
         main
         run-coverage)

;; サブサイクル 1 件分の入力と期待値。
;; expected-count と expected-ids は、使わない側へ #f を入れる。
;; state は要件の状態文字列で、期待 ID 集合の照合対象を選ぶ。
(struct cycle-descriptor
  (name state spec-paths test-paths expected-count expected-ids)
  #:transparent)

(define heading-rx #px"^### ([A-Z]{3}-[0-9]{3})(?: +.*)?$")
(define state-rx #px"^- \\*\\*状態\\*\\*： *(.+?) *$")
(define verify-rx #px"^- \\*\\*検証\\*\\*： *(.+?) *$")
(define spec-id-rx #px"\\[REQ: ([A-Z]{3}-[0-9]{3})\\]")
;; 後読みへハイフンを含める。含めないと error code の E-TYP-014 から
;; TYP-014 を取り出し、テストが要件 ID を参照したものと誤って数える。
(define test-id-rx
  #px"(?<![-A-Za-z0-9])[A-Z]{3}-[0-9]{3}(?![A-Za-z0-9])")
(define valid-states
  (set "G1" "G2" "G3" "G4" "G5"
       "Phase 1 以降" "Phase 2 以降" "Phase 3 以降"))

;; descriptor が名乗れる状態は G サイクルに限る。valid-states は Phase 送りの
;; 状態も含むため、後続 Phase の状態を descriptor に書けないよう別に制限する。
(define descriptor-states (set "G1" "G2" "G3" "G4" "G5"))

(define (state-set definitions state)
  (list->set
   (for/list ([definition (in-list definitions)]
              #:when (equal? (cdr definition) state))
     (car definition))))

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

;; 検証欄を持つ ID の集合。この ID はテスト参照の要求から免除される。
(define (registry-deferred path)
  (define deferred (set))
  (define current-id #f)
  (for ([line (in-list (file->lines path))])
    (match (regexp-match heading-rx line)
      [(list _ id) (set! current-id id)]
      [_
       (when (and current-id (regexp-match? verify-rx line))
         (set! deferred (set-add deferred current-id)))]))
  deferred)

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
  (define deferred (registry-deferred registry-path))
  (define counts (make-hash))
  (for ([definition (in-list definitions)])
    (hash-update! counts (car definition) add1 0))
  (define known (list->set (map car definitions)))
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
        [(eq? (cycle-descriptor-name cycle) 'G1) (state-set definitions "G1")]
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

  ;; 免除された ID ごとに、所有サイクルのテストファイルのうち ID を参照して
  ;; いるファイル数を数える。同一ファイル内の出現回数は書き方で揺れるため、
  ;; ファイル単位で数える。
  (define deferred-counts
    (sort
     (append*
      (for/list ([cycle (in-list cycles)]
                 [owned (in-list owned-sets)])
        (for/list ([id (in-list (sorted-ids (set-intersect owned deferred)))])
          (cons id
                (for/sum ([path (in-list (cycle-descriptor-test-paths cycle))]
                          #:when (member id
                                         (regexp-match* test-id-rx
                                                        (file->string path))))
                  1)))))
     string<?
     #:key car))

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
  (define invalid-descriptor-states
    (for/list ([cycle (in-list cycles)]
               #:unless (set-member? descriptor-states
                                     (cycle-descriptor-state cycle)))
      (format "descriptor ~a declares invalid state: ~a"
              (cycle-descriptor-name cycle)
              (cycle-descriptor-state cycle))))
  (define (set-difference-errors actual expected source [exempt (set)])
    (append
     (for/list ([id (in-list
                     (sorted-ids
                      (set-subtract (set-subtract expected exempt)
                                    actual)))])
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
       ;; descriptor の状態が無効なら owned が空集合になり、expected ID 全件が
       ;; 偽の欠落として並ぶ。宣言そのものの誤りなので、ここでは何も出さず
       ;; invalid-descriptor-states だけを返す。
       (if (and expected
                (set-member? descriptor-states
                             (cycle-descriptor-state cycle)))
           (let* ([name (cycle-descriptor-name cycle)]
                  [state (cycle-descriptor-state cycle)]
                  [owned (state-set definitions state)])
             (append
              (for/list ([id (in-list
                              (sorted-ids
                               (set-subtract expected owned)))])
                (format "~a expected ID is absent or not state ~a: ~a"
                        name state id))
              (set-difference-errors actual-specs expected
                                     (format "~a spec" name))
              (set-difference-errors actual-tests expected
                                     (format "~a test" name)
                                     deferred)))
           '()))
     cycles expected-sets cycle-specs cycle-tests))
  (values
   cycle-counts
   deferred-counts
   (append
    (for/list ([id (in-list duplicates)])
      (format "duplicate requirement ID: ~a" id))
    (for/list ([id (in-list (sorted-ids invalid-states))])
      (format "invalid or missing requirement state: ~a" id))
    invalid-descriptor-states
    count-errors
    (for/list ([id (in-list
                    (sorted-ids (set-subtract all-references known)))])
      (format "unknown requirement ID: ~a" id))
    (for/list ([id (in-list
                    (sorted-ids
                     (set-subtract (state-set definitions "G1")
                                   g1-specs)))])
      (format "G1 requirement lacks spec annotation: ~a" id))
    (for/list ([id (in-list
                    (sorted-ids
                     (set-subtract
                      (set-subtract (state-set definitions "G1") deferred)
                      g1-tests)))])
      (format "G1 requirement lacks test reference: ~a" id))
    exact-set-errors)))

(define (coverage-errors registry-path
                         #:cycles [cycles (default-cycle-descriptors)])
  (define-values (_counts _deferred errors)
    (coverage-analysis registry-path cycles))
  errors)

;; car は ID の記号、cdr は ID を参照するテストファイルの数である。
(define (deferred-test-counts registry-path
                              #:cycles [cycles (default-cycle-descriptors)])
  (define-values (_counts deferred-counts _errors)
    (coverage-analysis registry-path cycles))
  (for/list ([entry (in-list deferred-counts)])
    (cons (string->symbol (car entry)) (cdr entry))))

(define (run-coverage registry-path
                      [output (current-output-port)]
                      [error-output (current-error-port)]
                      #:cycles [cycles (default-cycle-descriptors)])
  (define-values (counts deferred-counts errors)
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
     (unless (null? deferred-counts)
       (display "deferred-tests: " output)
       (for ([entry (in-list deferred-counts)]
             [index (in-naturals)])
         (unless (zero? index) (display ", " output))
         (fprintf output "~a:~a" (car entry) (cdr entry)))
       (newline output))
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

;; Update this only when the G2g scope intentionally gains or removes an ID.
(define expected-g2g-ids
  '(COH-001 PRF-004 ROW-005 TRT-006 TRT-007))

;; Update this only when the G3a scope intentionally gains or removes an ID.
(define expected-g3a-ids '(BAK-003))

;; Update this only when the G3b scope intentionally gains or removes an ID.
(define expected-g3b-ids '(BAK-001))

;; Update this only when the G3c scope intentionally gains or removes an ID.
(define expected-g3c-ids '(BIT-002))

;; Update this only when the G3d scope intentionally gains or removes an ID.
(define expected-g3d-ids '(BAK-002))

;; Update this only when the G4 scope intentionally gains or removes an ID.
;; G4 はサブサイクル（G4c、G4d1 から G4d3、G4e、G4f）に分かれるが descriptor は
;; 1 件である。cycle-local-references が自身以外の owned 集合を差し引くため、
;; サブサイクルごとに立てると DIA-001 と DIA-002 の置き先が無くなる。
;; サブサイクルが要件を回収するたび、この列へ ID を足す。
(define expected-g4-ids '(DIA-001 DIA-002 DIA-003 DIA-004 DIA-005))

;; Update this only when the G5 scope intentionally gains or removes an ID.
;; G5 はサブサイクル（G5a から G5e）に分かれるが descriptor は 1 件である。
;; cycle-local-references が自身以外の owned 集合を差し引くため、
;; サブサイクルごとに立てると BOR-001 と BOR-002 の置き先が無くなる。
;; サブサイクルが要件を回収するたび、この列へ ID を足す。
(define expected-g5-ids '(BOR-001 BOR-002 BOR-003 BOR-004 BOR-005 BOR-006 BOR-007))

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
  (define g2g-specs
    (for/list ([name (in-list '("structural-row.md"
                                "trait.md"
                                "proof-value.md"))])
      (build-path root "docs/specification" name)))
  (define g2g-tests
    (for/list ([name (in-list '("trait-scope-test.rkt"
                                "trait-tables-test.rkt"
                                "typing-join-test.rkt"
                                "search-discharge-proof-test.rkt"
                                "discharge-term-test.rkt"
                                "elaborate-discharge-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (define g3-specs
    (list (build-path root "docs/specification/backend-matrix.md")))
  (define g3a-tests
    (list (build-path root "model/redex/tests/backend-matrix-test.rkt")))
  (define g3b-tests
    (list (build-path root "model/redex/tests/rule-crosscheck-test.rkt")
          (build-path root "model/redex/tests/pr-lang-test.rkt")
          (build-path root "model/redex/tests/pr-machine-test.rkt")
          (build-path root "model/redex/tests/pr-obs-test.rkt")
          (build-path root "model/redex/tests/lowering-test.rkt")
          (build-path root "model/redex/tests/properties-lowering-test.rkt")))
  (define g3c-tests
    (list (build-path root "model/redex/tests/backend-matrix-test.rkt")
          (build-path root "model/redex/tests/lowering-arith-test.rkt")))
  (define g4-specs
    (for/list ([name (in-list '("diagnostic.md"
                                "span.md"))])
      (build-path root "docs/specification" name)))
  (define g4-tests
    (for/list ([name (in-list '("diagnostic-test.rkt"
                                "elaborate-diagnostic-test.rkt"
                                "typing-diagnostic-test.rkt"
                                "origins-diagnostic-test.rkt"
                                "lowering-test.rkt"
                                "source-map-test.rkt"
                                "diagnostic-render-test.rkt"))])
      (build-path root "model/redex/tests" name)))
  (define g5-specs
    (list (build-path root "docs/specification/region.md")
          (build-path root "docs/specification/borrow.md")))
  (define g5-tests
    (list (build-path root "model/redex/tests/region-test.rkt")
          (build-path root "model/redex/tests/borrow-test.rkt")
          (build-path root "model/redex/tests/borrow-reborrow-test.rkt")
          (build-path root "model/redex/tests/borrow-boundary-test.rkt")
          (build-path root "model/redex/tests/borrow-fnbound-test.rkt")
          (build-path root "model/redex/tests/borrow-regression-test.rkt")
          (build-path root "model/redex/tests/borrow-escape-test.rkt")
          (build-path root "model/redex/tests/borrow-merge-test.rkt")
          (build-path root "model/redex/tests/borrow-path-test.rkt")
          (build-path root "model/redex/tests/borrow-own-annot-test.rkt")
          (build-path root "model/redex/tests/borrow-proj-test.rkt")
          (build-path root "model/redex/tests/borrow-read-test.rkt")
          (build-path root "model/redex/tests/borrow-assign-test.rkt")
          (build-path root "model/redex/tests/borrow-use-test.rkt")
          (build-path root "model/redex/tests/borrow-mut-join-test.rkt")
          (build-path root "model/redex/tests/solver-parity-test.rkt")))
  (list
   (cycle-descriptor 'G1 "G1" g1-specs g1-tests expected-g1-count #f)
   (cycle-descriptor 'G2a "G2" g2a-specs g2a-tests #f expected-g2a-ids)
   (cycle-descriptor 'G2b "G2" g2b-specs g2b-tests #f expected-g2b-ids)
   (cycle-descriptor 'G2c "G2" g2c-specs g2c-tests #f expected-g2c-ids)
   (cycle-descriptor 'G2d "G2" g2d-specs g2d-tests #f expected-g2d-ids)
   (cycle-descriptor 'G2e "G2" g2e-specs g2e-tests #f expected-g2e-ids)
   (cycle-descriptor 'G2f "G2" g2f-specs g2f-tests #f expected-g2f-ids)
   (cycle-descriptor 'G2g "G2" g2g-specs g2g-tests #f expected-g2g-ids)
   (cycle-descriptor 'G3a "G3" g3-specs g3a-tests #f expected-g3a-ids)
   (cycle-descriptor 'G3b "G3" g3-specs g3b-tests #f expected-g3b-ids)
   (cycle-descriptor 'G3c "G3" g3-specs g3c-tests #f expected-g3c-ids)
   (cycle-descriptor 'G3d "G3" g3-specs '() #f expected-g3d-ids)
   (cycle-descriptor 'G4 "G4" g4-specs g4-tests #f expected-g4-ids)
   (cycle-descriptor 'G5 "G5" g5-specs g5-tests #f expected-g5-ids)))

(define (main [output (current-output-port)]
              [error-output (current-error-port)])
  (define root (simplify-path (build-path tools-directory 'up)))
  (define registry (build-path root "docs/specification/requirements.md"))
  (run-coverage registry output error-output))

(module+ main
  (exit (main)))

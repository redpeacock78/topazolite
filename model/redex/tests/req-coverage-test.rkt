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

(define (fixture-output registry spec test cycles-of)
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (define output (open-output-string))
     (define code
       (run-coverage registry-path output (open-output-string)
                     #:cycles (cycles-of spec-paths test-paths)))
     (list code (get-output-string output)))))

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
(define var-001 (string-append "VAR" "-001"))
(define var-002 (string-append "VAR" "-002"))
(define var-003 (string-append "VAR" "-003"))
(define trt-001 (string-append "TRT" "-001"))
(define rfn-001 (string-append "RFN" "-001"))
(define rfn-002 (string-append "RFN" "-002"))
(define rfn-003 (string-append "RFN" "-003"))

;; 状態フィールドのテスト用 ID は実データの参照集合へ混入させない。
(define bak-003 (string-append "BAK" "-003"))
(define bak-001 (string-append "BAK" "-001"))
(define bak-002 (string-append "BAK" "-002"))

(define (registry-entry/verify id state verification)
  (format "### ~a\n\n- **状態**：~a\n- **検証**：~a\n"
          id state verification))

(define expected-g2a-ids
  (set typ-003 row-001 row-002 row-003 row-004))
(define expected-g2b-ids
  (set psr-001 psr-002 psr-003))
(define expected-g2c-ids
  (set var-001 var-002 var-003))
(define expected-g2d-ids
  (set rfn-001 rfn-002 rfn-003))

(define (descriptor-ids ids)
  (map string->symbol (sort (set->list ids) string<?)))

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

(define g2c-ids (sort (set->list expected-g2c-ids) string<?))
(define g2c-ids-missing (remove var-003 g2c-ids))
(define g2c-ids-replaced (sort (cons trt-001 g2c-ids-missing) string<?))

(define g2d-ids (sort (set->list expected-g2d-ids) string<?))
(define g2d-ids-missing (remove rfn-003 g2d-ids))
(define g2d-ids-replaced (sort (cons trt-001 g2d-ids-missing) string<?))

(define (fixture-errors registry spec test
                        #:expected-g1-count [expected-g1-count #f]
                        #:expected-g2a-ids [expected-g2a-ids #f])
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (if expected-g2a-ids
         (coverage-errors
          registry-path
          #:cycles
          (list
           (cycle-descriptor 'G2a "G2" spec-paths test-paths #f
                             (descriptor-ids expected-g2a-ids))))
         (coverage-errors
          registry-path
          #:cycles
          (list
           (cycle-descriptor 'G1 "G1" spec-paths test-paths
                             expected-g1-count #f)))))))

(define (fixture-errors-g2b registry spec test)
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (coverage-errors
      registry-path
      #:cycles
      (list
       (cycle-descriptor 'G2b "G2" spec-paths test-paths #f
                         (descriptor-ids expected-g2b-ids)))))))

(define (fixture-errors-g2c registry spec test)
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (coverage-errors
      registry-path
      #:cycles
      (list
       (cycle-descriptor 'G2c "G2" spec-paths test-paths #f
                         (descriptor-ids expected-g2c-ids)))))))

(define (fixture-errors-g2d registry spec test)
  (with-fixture
   registry spec test
   (lambda (registry-path spec-paths test-paths)
     (coverage-errors
      registry-path
      #:cycles
      (list
       (cycle-descriptor 'G2d "G2" spec-paths test-paths #f
                         (descriptor-ids expected-g2d-ids)))))))

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

(test-case "G2c coverage requires the exact ID set"
  (check-equal?
   (fixture-errors-g2c
    (registry-entries g2c-ids "G2")
    (spec-references g2c-ids)
    (test-references g2c-ids))
   '())
  (check-not-false
   (member
    (format "G2c spec ID set missing expected ID: ~a" var-003)
    (fixture-errors-g2c
     (registry-entries g2c-ids-missing "G2")
     (spec-references g2c-ids-missing)
     (test-references g2c-ids-missing))))
  (define replaced-errors
    (fixture-errors-g2c
     (registry-entries g2c-ids-replaced "G2")
     (spec-references g2c-ids-replaced)
     (test-references g2c-ids-replaced)))
  (check-not-false
   (member (format "G2c spec ID set contains unexpected ID: ~a" trt-001)
           replaced-errors))
  (check-not-false
   (member (format "G2c test ID set contains unexpected ID: ~a" trt-001)
           replaced-errors)))

(test-case "G2d coverage requires the exact ID set"
  (check-equal?
   (fixture-errors-g2d (registry-entries g2d-ids "G2")
                       (spec-references g2d-ids)
                       (test-references g2d-ids))
   '())
  ;; 状態が G2 でない ID は、明示集合に置いても G2d の対象にならない。
  (check-not-false
   (member
    (format "G2d expected ID is absent or not state G2: ~a" rfn-003)
    (fixture-errors-g2d
     (string-append (registry-entries g2d-ids-missing "G2")
                    (registry-entry rfn-003 "G3"))
     (spec-references g2d-ids)
     (test-references g2d-ids))))
  ;; 正典に [REQ: ...] が無い ID を検出する。
  (check-not-false
   (member
    (format "G2d spec ID set missing expected ID: ~a" rfn-003)
    (fixture-errors-g2d (registry-entries g2d-ids-missing "G2")
                        (spec-references g2d-ids-missing)
                        (test-references g2d-ids-missing))))
  ;; テストが参照しない ID を検出する。
  (check-not-false
   (member
    (format "G2d test ID set missing expected ID: ~a" rfn-003)
    (fixture-errors-g2d (registry-entries g2d-ids "G2")
                        (spec-references g2d-ids)
                        (test-references g2d-ids-missing))))
  ;; 三対三の入れ替えは、件数だけで通らず対称差の両側を報告する。
  (define replaced-errors
    (fixture-errors-g2d (registry-entries g2d-ids-replaced "G2")
                        (spec-references g2d-ids-replaced)
                        (test-references g2d-ids-replaced)))
  (check-not-false
   (member (format "G2d spec ID set contains unexpected ID: ~a" trt-001)
           replaced-errors))
  (check-not-false
   (member (format "G2d test ID set contains unexpected ID: ~a" trt-001)
           replaced-errors)))

;; structural-row.md は G2a と G2c の正典を兼ねる。同一ファイルを両 gate の
;; spec/test に渡しても、G2a 側が G2c の明示集合を除外して green になること。
(test-case "G2a canon file may also carry G2c references"
  (with-fixture
   (string-append (registry-entries g2a-ids "G2")
                  (registry-entries g2c-ids "G2"))
   (string-append (spec-references g2a-ids) "\n" (spec-references g2c-ids))
   (string-append (test-references g2a-ids) "\n" (test-references g2c-ids))
   (lambda (registry-path spec-paths test-paths)
     (check-equal?
      (coverage-errors
       registry-path
       #:cycles
       (list
        (cycle-descriptor 'G2a "G2" spec-paths test-paths #f
                          (descriptor-ids expected-g2a-ids))
        (cycle-descriptor 'G2c "G2" spec-paths test-paths #f
                          (descriptor-ids expected-g2c-ids))))
      '()))))

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
      (run-coverage
       registry-path output errors
       #:cycles
       (list (cycle-descriptor 'G1 "G1" spec-paths test-paths #f #f)))
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
                (string-append
                 "Requirement coverage OK: 18 G1 IDs, 5 G2a IDs, "
                 "3 G2b IDs, 3 G2c IDs, 3 G2d IDs, 5 G2e IDs, 4 G2f IDs, "
                 "5 G2g IDs\n"))
  (check-equal? (get-output-string errors) ""))

(test-case "cycle-descriptors covers every declared sub-cycle"
  (define ds (default-cycle-descriptors))
  (check-equal? (map cycle-descriptor-name ds)
                '(G1 G2a G2b G2c G2d G2e G2f G2g))
  (define (by-name n)
    (findf (lambda (d) (eq? (cycle-descriptor-name d) n)) ds))
  (check-equal? (cycle-descriptor-expected-count (by-name 'G1)) 18)
  (check-false (cycle-descriptor-expected-ids (by-name 'G1)))
  (check-equal? (cycle-descriptor-expected-ids (by-name 'G2d))
                '(RFN-001 RFN-002 RFN-003))
  (check-false (cycle-descriptor-expected-count (by-name 'G2d))))

(test-case "G2e descriptor covers the trait and composite requirements"
  (define descriptor
    (findf (lambda (d) (eq? (cycle-descriptor-name d) 'G2e))
           (default-cycle-descriptors)))
  (check-not-false descriptor)
  (check-equal? (cycle-descriptor-expected-ids descriptor)
                '(TRT-001 TRT-002 TRT-003 CMP-001 CMP-002))
  (check-true
   (for/or ([path (in-list (cycle-descriptor-spec-paths descriptor))])
     (regexp-match? #rx"docs/specification/trait[.]md$"
                    (path->string path)))
   "G2e descriptor must point at trait.md"))

(test-case "every descriptor carries its own spec and test paths"
  (for ([d (in-list (default-cycle-descriptors))])
    (check-true (list? (cycle-descriptor-spec-paths d))
                (format "~s" (cycle-descriptor-name d)))
    (check-true (list? (cycle-descriptor-test-paths d))
                (format "~s" (cycle-descriptor-name d)))))

(test-case
 "verification field exempts an ID from the test reference requirement"
 (define errors
   (with-fixture
    (registry-entry/verify bak-002 "G3" "Phase 3 以降（runtime の実装）")
    (format "[REQ: ~a]" bak-002)
    ""
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3d "G3" spec-paths test-paths #f
                               (list (string->symbol bak-002))))))))
 (check-equal? errors '()))

(test-case
 "the exemption is permissive: an exempt ID may still be referenced"
 (define errors
   (with-fixture
    (registry-entry/verify bak-001 "G3" "Phase 2 以降（emitter の実装）")
    (format "[REQ: ~a]" bak-001)
    (format "(test-case ~s (void))" bak-001)
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3b "G3" spec-paths test-paths #f
                               (list (string->symbol bak-001))))))))
 (check-equal? errors '()))

(test-case
 "an ID without a verification field still requires a test reference"
 (define errors
   (with-fixture
    (registry-entry bak-002 "G3")
    (format "[REQ: ~a]" bak-002)
    ""
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3d "G3" spec-paths test-paths #f
                               (list (string->symbol bak-002))))))))
 (check-equal?
  errors
  (list (format "G3d test ID set missing expected ID: ~a" bak-002))))

(test-case
 "the spec annotation side is not exempted"
 ;; 免除は test 参照の側にしか効かない。spec 注釈の側は検証欄の有無によらず
 ;; 要求し続ける。test 側を満たした fixture にしてあるのは、観測したいのが
 ;; spec 側の 1 行だけだからである。test 側を空にすると、免除が入る前は test
 ;; 側の欠落も並び、このテストが名前と違う理由で落ちる。
 (define errors
   (with-fixture
    (registry-entry/verify bak-002 "G3" "Phase 3 以降（runtime の実装）")
    ""
    (format "(test-case ~s (void))" bak-002)
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3d "G3" spec-paths test-paths #f
                               (list (string->symbol bak-002))))))))
 (check-equal?
  errors
  (list (format "G3d spec ID set missing expected ID: ~a" bak-002))))

(test-case
 "the verification regexp does not match a state line"
 (define errors
   (with-fixture
    (registry-entry bak-002 "G3")
    (format "[REQ: ~a]" bak-002)
    ""
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3d "G3" spec-paths test-paths #f
                               (list (string->symbol bak-002))))))))
 (check-equal?
  errors
  (list (format "G3d test ID set missing expected ID: ~a" bak-002))))

(test-case
 "deferred-tests line reports the measured reference count"
 (define result
   (fixture-output
    (registry-entry/verify bak-001 "G3" "Phase 2 以降（emitter の実装）")
    (format "[REQ: ~a]" bak-001)
    (format "(test-case ~s (void))" bak-001)
    (lambda (spec-paths test-paths)
      (list (cycle-descriptor 'G3b "G3" spec-paths test-paths #f
                              (list (string->symbol bak-001)))))))
 (check-equal? (first result) 0)
 (check-equal?
  (second result)
  (format "Requirement coverage OK: 1 G3b IDs\ndeferred-tests: ~a:1\n"
          bak-001)))

(test-case
 "deferred-tests keeps a zero count visible"
 (define result
   (fixture-output
    (registry-entry/verify bak-002 "G3" "Phase 3 以降（runtime の実装）")
    (format "[REQ: ~a]" bak-002)
    ""
    (lambda (spec-paths test-paths)
      (list (cycle-descriptor 'G3d "G3" spec-paths test-paths #f
                              (list (string->symbol bak-002)))))))
 (check-equal? (first result) 0)
 (check-equal?
  (second result)
  (format "Requirement coverage OK: 1 G3d IDs\ndeferred-tests: ~a:0\n"
          bak-002)))

;; 出力の行だけでなく、後続タスクが使う関数の側も固定する。ID を記号へ写す
;; ところが壊れても、Task 14 まで気付けないままになる。
(test-case
 "deferred-test-counts exposes the same measurement as symbols"
 (define counts
   (with-fixture
    (registry-entry/verify bak-001 "G3" "Phase 2 以降（emitter の実装）")
    (format "[REQ: ~a]" bak-001)
    (format "(test-case ~s (void))" bak-001)
    (lambda (registry-path spec-paths test-paths)
      (deferred-test-counts
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3b "G3" spec-paths test-paths #f
                               (list (string->symbol bak-001))))))))
 (check-equal? counts (list (cons (string->symbol bak-001) 1))))

(test-case
 "no deferred-tests line when nothing is exempt"
 (define result
   (fixture-output
    (registry-entry bak-002 "G3")
    (format "[REQ: ~a]" bak-002)
    (format "(test-case ~s (void))" bak-002)
    (lambda (spec-paths test-paths)
      (list (cycle-descriptor 'G3d "G3" spec-paths test-paths #f
                              (list (string->symbol bak-002)))))))
 (check-equal? (first result) 0)
 (check-equal?
  (second result)
  "Requirement coverage OK: 1 G3d IDs\n"))

;; 状態フィールドが descriptor ごとに効くこと。G3 の ID を G2 の descriptor で
;; 期待すると「absent or not state G2」が出る。
(test-case
 "descriptor state selects the requirement state set"
 (define errors
   (with-fixture
    (registry-entry bak-003 "G3")
    (format "[REQ: ~a]" bak-003)
    (format "(test-case ~s (void))" bak-003)
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3a "G3" spec-paths test-paths #f
                               (list (string->symbol bak-003))))))))
 (check-equal? errors '()))

(test-case
 "descriptor state mismatch is reported with the declared state"
 (define errors
   (with-fixture
    (registry-entry bak-003 "G3")
    (format "[REQ: ~a]" bak-003)
    (format "(test-case ~s (void))" bak-003)
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3a "G2" spec-paths test-paths #f
                               (list (string->symbol bak-003))))))))
 (check-equal?
  errors
  (list (format "G3a expected ID is absent or not state G2: ~a" bak-003))))

(test-case
 "descriptor state outside G1..G5 is rejected"
 (define errors
   (with-fixture
    (registry-entry bak-003 "G3")
    (format "[REQ: ~a]" bak-003)
    (format "(test-case ~s (void))" bak-003)
    (lambda (registry-path spec-paths test-paths)
      (coverage-errors
       registry-path
       #:cycles
       (list (cycle-descriptor 'G3a "Phase 2 以降" spec-paths test-paths #f
                               (list (string->symbol bak-003))))))))
 (check-equal?
  errors
  (list "descriptor G3a declares invalid state: Phase 2 以降")))

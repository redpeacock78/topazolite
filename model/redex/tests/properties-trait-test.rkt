#lang racket/base

(require racket/list
         racket/match
         rackunit
         redex/reduction-semantics
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define limits (read-bounds))
(define attempts (bounds-attempts limits))
(define field-types '(Int String Bool Unit))

(struct impl-fixture (row record type callables) #:transparent)

(define (verify core)
  (term (verify-origins ,R0 ,core)))

(define (verify-initial core)
  (term (verify-initial-origins ,R0 ,core)))

(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) (bounds-fuel limits))
    [`(cfg ,result () () () ()) result]
    [other (fail-check (format "unexpected run-g2 result: ~s" other))]))

(define (impl-proposition row)
  `(Implements ,(impl-target-type row) ,(impl-trait-name row)))

(define (sample-value type)
  (case type
    [(Int) 0]
    [(String) "fixture"]
    [(Unit) 'unit]
    [else (error 'properties-trait-test
                 "no fixture value for return type: ~s"
                 type)]))

;; 性質1と2が共有する、requirement と同じ shape を持つ record。
(define impl-fixtures
  (for/list ([row (in-list impl-table)])
    (define trait-row (trait-row-by-name (impl-trait-name row)))
    (define requirements
      (instantiate-requirements (trait-template trait-row)
                                (impl-target-type row)))
    (define source-fields
      (for/list ([field (in-list requirements)])
        (match field
          [`(,label (NFn (,parameters ...) ,return-type () ()) ,mutability)
           (define names
             (for/list ([_parameter (in-list parameters)]
                        [index (in-naturals)])
               (string->symbol (format "argument-~a" index))))
           `(,label ,mutability
                    (Fn ,(map list names parameters)
                        ,return-type
                        ()
                        ,(sample-value return-type)))]
          [other
           (error 'properties-trait-test
                  "unsupported requirement fixture: ~s"
                  other)])))
    (match (elab `(Rec ,source-fields))
      [(list record type '() callables)
       (impl-fixture row (erase-core record) type callables)]
      [other
       (error 'properties-trait-test
              "record fixture no longer elaborates: ~s"
              other)])))

(test-case "TRT-001: 性質1 shape 一致だけでは Proof を偽造できない"
  (call-with-search-seed
   limits
   (lambda ()
     (define forged-count (box 0))
     ;; 正しい表由来の oid と φ の再表明は新しい事実を作らないため、初期層でも
     ;; 許可される。下の拒否が ProofRep 一般の禁止ではないことを固定する。
     (define authorized
       '(ProofRep (Reserved o-impl-printable-int)
                  (Implements Int Printable)))
     (check-equal? (verify-initial authorized) 'ok)
     (check-equal? (verify authorized) 'ok)
     (for ([_i (in-range attempts)])
       (define fixture (pick-one impl-fixtures))
       (define row (impl-fixture-row fixture))
       ;; 同じ record が requirement shape を満たすことを先に確認する。
       (check-equal?
        (core-type-of (impl-fixture-record fixture)
                      '()
                      (impl-fixture-callables fixture))
        (list (impl-fixture-type fixture) '()))
       ;; o-add は既知の予約 origin だが、この Implements 命題の発行者ではない。
       (define forged
         `(ProofRep (Reserved o-add) ,(impl-proposition row)))
       (define initial-result (verify-initial forged))
       (define reached-result (verify forged))
       (check-equal? initial-result `(forged ,forged))
       (check-equal? reached-result `(forged ,forged))
       (when (and (equal? initial-result `(forged ,forged))
                  (equal? reached-result `(forged ,forged)))
         (set-box! forged-count (add1 (unbox forged-count)))))
     (check-true (positive? (unbox forged-count)))
     (printf "性質1: attempts=~a forged=~a seed=~a\n"
             attempts (unbox forged-count) (bounds-seed limits)))))

(test-case "TRT-002: 性質2 impl と derive の Proof は成果物検証を通る"
  (call-with-search-seed
   limits
   (lambda ()
     (define impl-count (box 0))
     (define derive-count (box 0))
     (for ([_i (in-range attempts)])
       (define fixture (pick-one impl-fixtures))
       (define row (impl-fixture-row fixture))
       (define result
         (run-g2-core
          `(Apply (PrimVal (Reserved ,(impl-oid row)) ,(impl-name row))
                  ,(impl-fixture-record fixture))))
       (define expected
         `(ProofRep (Reserved ,(impl-oid row))
                    ,(impl-proposition row)))
       (define verification (verify result))
       (check-equal? result expected)
       (check-equal? verification 'ok)
       (when (and (equal? result expected) (eq? verification 'ok))
         (case (impl-kind row)
           [(impl) (set-box! impl-count (add1 (unbox impl-count)))]
           [(derive) (set-box! derive-count (add1 (unbox derive-count)))])))
     (check-true (positive? (unbox impl-count)))
     (check-true (positive? (unbox derive-count)))
     (printf "性質2: attempts=~a impl=~a derive=~a seed=~a\n"
             attempts (unbox impl-count) (unbox derive-count)
             (bounds-seed limits)))))

(test-case "TRT-003: 性質3 一意候補は Resolved、重複候補は Ambiguous"
  (call-with-search-seed
   limits
   (lambda ()
     (define resolved-count (box 0))
     (define ambiguous-count (box 0))
     (for ([_i (in-range attempts)])
       ;; Int は1行、String は同じ (型, trait) の2行を持つ fixture である。
       (define target (pick-one '(Int String)))
       (define goal (make-goal `(Implements ,target Printable)))
       (define candidates (project-goal Γ-pc0 '(root) goal))
       (define result (resolve-candidates goal candidates))
       (cond
         [(resolved? result)
          (set-box! resolved-count (add1 (unbox resolved-count)))]
         [(ambiguous? result)
          (set-box! ambiguous-count (add1 (unbox ambiguous-count)))])
       (case target
         [(Int)
          (check-equal? (length candidates) 1)
          (check-true (resolved? result))]
         [(String)
          (check-equal? (length candidates) 2)
          (check-true (ambiguous? result))]))
     (check-true (positive? (unbox resolved-count)))
     (check-true (positive? (unbox ambiguous-count)))
     (printf "性質3: attempts=~a resolved=~a ambiguous=~a seed=~a\n"
             attempts (unbox resolved-count) (unbox ambiguous-count)
             (bounds-seed limits)))))

(test-case "TRT-003: 性質4 coherence は候補を scope で採否する"
  ;; search-coherence-test.rkt の決定的 fixture を、seed 付き標本化で補う。
  (call-with-search-seed
   limits
   (lambda ()
     (define kept-count (box 0))
     (define dropped-count (box 0))
     (define goal (make-goal '(Implements Bool Taggable)))
     (for ([_i (in-range attempts)])
       (define visible? (zero? (random 2)))
       (define candidates
         (project-goal Γ-pc0
                       (if visible? '(root s-user) '(root))
                       goal))
       (if (null? candidates)
           (set-box! dropped-count (add1 (unbox dropped-count)))
           (set-box! kept-count (add1 (unbox kept-count))))
       (if visible?
           (check-equal? (length candidates) 1)
           (check-equal? candidates '())))
     (check-true (positive? (unbox kept-count)))
     (check-true (positive? (unbox dropped-count)))
     (printf "性質4: attempts=~a kept=~a dropped=~a seed=~a\n"
             attempts (unbox kept-count) (unbox dropped-count)
             (bounds-seed limits)))))

(test-case "CMP-001: 性質5 join 型は branch 順序に依らない"
  (call-with-search-seed
   limits
   (lambda ()
     (define nontrivial-count (box 0))
     (define multi-branch-count (box 0))
     (for ([_i (in-range attempts)])
       (define branches (random-branch-rows))
       (define types
         (for/list ([row (in-list branches)]) `(Record ,row)))
       (define-values (merged witnesses) (merge-record-types types))
       (when (>= (length types) 2)
         (set-box! multi-branch-count
                   (add1 (unbox multi-branch-count))))
       (for ([permutation (in-list (permutations types))])
         (define-values (permuted-merged permuted-witnesses)
           (merge-record-types permutation))
         (check-equal? permuted-merged merged)
         (check-equal? permuted-witnesses witnesses))
       (match merged
         [`(Record ,row)
          (when
              (for/or ([field (in-list row)])
                (>= (length (union-members (second field))) 2))
            (set-box! nontrivial-count
                      (add1 (unbox nontrivial-count))))]))
     (check-true (positive? (unbox nontrivial-count)))
     (check-true (positive? (unbox multi-branch-count)))
     (printf "性質5: attempts=~a multi-branch=~a nontrivial-joins=~a seed=~a\n"
             attempts (unbox multi-branch-count) (unbox nontrivial-count)
             (bounds-seed limits)))))

(test-case "CMP-001: 性質6 join は全枝が mut のときだけ mut を保つ"
  (call-with-search-seed
   limits
   (lambda ()
     (define imm-joined-count (box 0))
     (define mut-joined-count (box 0))
     (for ([_i (in-range attempts)])
       ;; properties-refine-test.rkt の dropped は欠落を含む。ここでは同じ label
       ;; と異なる型を必ず置き、可変性によらず join する経路を分離する。
       (define left (pick-one field-types))
       (define right (pick-one (remove left field-types)))
       (define mutability (pick-one '(imm mut)))
       (define-values (merged witnesses)
         (merge-record-types
          (list `(Record ((a ,left ,mutability)))
                `(Record ((a ,right ,mutability))))))
       (case mutability
         [(imm)
          (define expected
            `(Record ((a ,(normalize-type `(Union ,left ,right)) imm))))
          (check-equal?
           merged
           expected)
          (check-true (pair? witnesses))
          (when (equal? merged expected)
            (set-box! imm-joined-count
                      (add1 (unbox imm-joined-count))))]
         [(mut)
          (define expected
            `(Record ((a ,(normalize-type `(Union ,left ,right)) mut))))
          (check-equal? merged expected)
          (check-true (pair? witnesses))
          (when (equal? merged expected)
            (set-box! mut-joined-count
                      (add1 (unbox mut-joined-count))))])
       (define-values (mismatched mismatch-witnesses)
         (merge-record-types
          (list `(Record ((a ,left imm)))
                `(Record ((a ,right mut))))))
       (define expected-mismatch
         `(Record ((a ,(normalize-type `(Union ,left ,right)) imm))))
       (check-equal? mismatched expected-mismatch)
       (check-true (pair? mismatch-witnesses)))
     (check-true (positive? (unbox imm-joined-count)))
     (check-true (positive? (unbox mut-joined-count)))
     (printf "性質6: attempts=~a imm-joined=~a mut-joined=~a seed=~a\n"
             attempts (unbox imm-joined-count) (unbox mut-joined-count)
             (bounds-seed limits)))))

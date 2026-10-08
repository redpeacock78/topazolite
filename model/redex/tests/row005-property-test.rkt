#lang racket

(require rackunit
         racket/match
         "../compat.rkt"
         "../ownership.rkt"
         "row005-property-support.rkt")

(test-case "ROW-005 convert の有限な Record 対"
  (check-equal? (length R) 40)
  (define counts (convert-pair-group convert-record-cases 1600))
  (check-equal? (sorted-counts counts)
                '((accepted . 121) (drop-obligation . 11) (not-compatible . 1468)))
  (displayln `(convert-record ,(hash->list counts))))

(test-case "ROW-005 convert の有限な Union 対"
  (check-equal? (length R_a) 8)
  (define counts (convert-pair-group convert-union-cases 1120))
  (check-equal? (sorted-counts counts)
                '((accepted . 4) (not-compatible . 1116)))
  (displayln `(convert-union ,(hash->list counts))))

(test-case "Task 8 の二成分 decompose 例は convert の有限な受理群に含まれる"
  ;; この programme は convert-union 群の一件として再実行される。
  (check-not-false (member task8-two-way-case convert-union-cases equal?))
  (match (run-conversion (first task8-two-way-case) (second task8-two-way-case))
    [`(accepted ,result-type ,_core ,_callables)
     (check-equal? result-type task8-a-bool-or-int)]
    [other
     (fail-check (format "Task 8 の 2 成分 decompose が受理されない: ~s" other))]))

(test-case "drop-obligation の有限な Record 対は全て runtime shape を持つ"
  (define obligation-pairs
    (for*/list ([actual (in-list R)]
                [expected (in-list R)]
                #:when (eq? (case-class actual expected) 'drop-obligation))
      (list actual expected)))
  (check-equal? (length obligation-pairs) 11)
  (for ([pair (in-list obligation-pairs)])
    (define actual (first pair))
    (define expected (second pair))
    (define shape (remainder-removal-shape actual expected))
    (check-true (and shape (pair? shape))
                (format "drop-obligation に対応する runtime removal shape が無い: ~s => ~s"
                        actual expected))))

(test-case "2 段 Record の有限対で nested drop の shape を網羅する"
  (define (field label type mode optional?)
    (if optional?
        (list label type mode 'opt)
        (list label type mode)))
  (define cases
    (for*/list ([inner-optional? (in-list '(#f #t))]
                [outer-optional? (in-list '(#f #t))]
                [owned-mode (in-list '(imm mut))])
      (define actual-inner
        `(Record ((kept Int imm)
                  ,(field 'x '(Option (Owned Res)) owned-mode
                          inner-optional?))))
      (define expected-inner '(Record ((kept Int imm))))
      (define actual
        `(Record (,(field 'a actual-inner 'imm outer-optional?))))
      ;; Expected の外側欄は opt。required actual でも値の存在は保証される。
      (define expected
        `(Record (,(field 'a expected-inner 'imm #t))))
      (list actual expected)))
  (check-equal? (length cases) 8)
  (define drop-count 0)
  (for ([pair (in-list cases)])
    (match-define (list actual expected) pair)
    (check-true (compat? actual expected)
                (format "有限対が互換でない: ~s => ~s" actual expected))
    (define kind (narrowing-kind actual expected))
    (define shape (remainder-removal-shape actual expected))
    (check-not-false shape
                     (format "有限対に runtime shape が無い: ~s => ~s"
                             actual expected))
    (when (match kind [`(drop-obligation ,_ ,_) #t] [_ #f])
      (set! drop-count (add1 drop-count))
      (check-true (pair? shape)
                  (format "drop-obligation の shape が空: ~s => ~s"
                          actual expected))))
  (check-equal? drop-count 8))

#lang racket

(require rackunit
         racket/match
         "../elaborate.rkt"
         "row005-property-support.rkt")

(test-case "ROW-005 join の有限な順序なし Record 二組"
  (check-equal? (length join-record-cases) 820)
  (define counts (join-group join-record-cases 820))
  (check-equal? (sorted-counts counts)
                '((accepted . 365)
                  (accepted-with-rsd . 30)
                  (one-owned-one-unowned . 375)
                  (owned-owned-without-upper-bound . 50)))
  (define convert-counts (join-record-convert-group join-record-cases))
  (check-equal? (sorted-counts convert-counts)
                '((convert-accepted . 365)
                  (convert-drop-rejected . 30)
                  (no-row005-upper . 425)))
  (displayln `(join-record-convert ,(hash->list convert-counts)))
  (displayln `(join-record ,(hash->list counts))))

(test-case "ROW-005 join の有限な異なる Record 三組"
  (check-equal? (length join-three-cases) 56)
  (define counts (join-group join-three-cases 56))
  (check-equal? (sorted-counts counts)
                '((accepted . 10)
                  (one-owned-one-unowned . 35)
                  (owned-owned-without-upper-bound . 11)))
  (displayln `(join-three ,(hash->list counts))))

(test-case "Task 8 の三型合流は join の有限な受理群に含まれる"
  ;; この programme は join-three 群の一件として再実行される。
  (check-equal? (length task8-three-way-types) 3)
  (check-not-false (member task8-three-way-types join-three-cases equal?))
  (check-equal? (row005-join task8-three-way-types) task8-a-bool-or-int)
  (match (run-join-conversion task8-three-way-types task8-a-bool-or-int)
    [`(accepted ,result-type ,_core ,_callables)
     (check-equal? result-type task8-a-bool-or-int)]
    [other
     (fail-check (format "Task 8 の 3 型合流が受理されない: ~s" other))]))

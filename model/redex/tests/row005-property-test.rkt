#lang racket

(require rackunit
         racket/match
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
    [`(accepted ,result-type ,_core)
     (check-equal? result-type task8-a-bool-or-int)]
    [other
     (fail-check (format "Task 8 の 2 成分 decompose が受理されない: ~s" other))]))

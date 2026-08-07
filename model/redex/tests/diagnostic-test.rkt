#lang racket

(require racket/set
         rackunit
         "../diagnostic.rkt")

;; [REQ: DIA-005] error code の安定識別子と versioning（diagnostic.md）

;; test 1
(test-case
 "registry の全 code が書式に合う"
 (for ([row (in-list diagnostic-registry)])
   (check-regexp-match diagnostic-code-rx (diagnostic-code-code row))))

;; test 2
(test-case
 "code が重複しない"
 (define codes (map diagnostic-code-code diagnostic-registry))
 (check-equal? (length codes) (set-count (list->set codes))))

;; test 3
(test-case
 "(phase . key) の組が重複しない"
 (define pairs
   (for/list ([row (in-list diagnostic-registry)])
     (cons (diagnostic-code-phase row) (diagnostic-code-key row))))
 (check-equal? (length pairs) (set-count (list->set pairs))))

;; test 4
(test-case
 "since と deprecated-in が registry version の範囲に収まる"
 (for ([row (in-list diagnostic-registry)])
   (define since (diagnostic-code-since row))
   (define deprecated (diagnostic-code-deprecated-in row))
   (check-pred exact-positive-integer? since)
   (check-true (<= since diagnostic-registry-version))
   (when deprecated
     (check-pred exact-positive-integer? deprecated)
     (check-true (> deprecated since))
     (check-true (<= deprecated diagnostic-registry-version)))))

;; test 5
(test-case
 "G4c の registry は 59 行であり内訳が一致する"
 (check-equal? (length diagnostic-registry) 59)
 (define (count-of phase)
   (for/sum ([row (in-list diagnostic-registry)]
             #:when (eq? (diagnostic-code-phase row) phase))
     1))
 (check-equal? (count-of 'elaborate) 53)
 (check-equal? (count-of 'typing) 1)
 (check-equal? (count-of 'origins) 1)
 (check-equal? (count-of 'lowering) 4)
 (for ([row (in-list diagnostic-registry)])
   (check-equal? (diagnostic-code-since row) 1)
   (check-false (diagnostic-code-deprecated-in row))))

;; test 8
(test-case
 "diagnostic-code-of と diagnostic-code-row が引き当てる"
 (check-equal? (diagnostic-code-of 'elaborate 'type-mismatch) "E-TYP-012")
 (check-equal? (diagnostic-code-of 'typing 'ill-typed) "E-TYP-001")
 (check-equal? (diagnostic-code-of 'origins 'forged) "E-ORG-001")
 (check-equal? (diagnostic-code-of 'lowering 'kernel-primitive) "E-LOW-001")
 (check-false (diagnostic-code-of 'elaborate 'no-such-reason))
 (check-false (diagnostic-code-of 'no-such-phase 'type-mismatch))
 (check-equal? (diagnostic-code-key (diagnostic-code-row "E-TYP-012"))
               'type-mismatch)
 (check-false (diagnostic-code-row "E-ZZZ-999")))

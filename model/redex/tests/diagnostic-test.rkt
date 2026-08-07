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

;; 検証器の test で使う最小の材料。
(define ok-span '(#:span src 3 7))
(define other-span '(#:span src 11 15))

(define (base-diagnostic)
  (make-diagnostic #:id "E-TYP-012"
                   #:title "型が期待と一致しない"
                   #:message "Bool を期待したが Int である"
                   #:primary-span ok-span))

;; test 9
(test-case
 "既定値で作った Diagnostic が検証を通る"
 (define d (base-diagnostic))
 (check-true (diagnostic-valid? d))
 (check-equal? (diagnostic-schema-errors d) '())
 (check-eq? (diagnostic-severity d) 'error)
 (check-equal? (diagnostic-secondary-labels d) '())
 (check-equal? (diagnostic-notes d) '())
 (check-equal? (diagnostic-help d) '())
 (check-false (diagnostic-expected d))
 (check-false (diagnostic-found d))
 (check-false (diagnostic-effect-context d))
 (check-false (diagnostic-proof-context d))
 (check-equal? (diagnostic-origin-chain d) '())
 (check-equal? (diagnostic-expansion-trace d) '())
 (check-equal? (diagnostic-related d) '())
 (check-equal? (diagnostic-fixes d) '()))

;; test 10
(test-case
 "category は id から導出した記号である"
 (define d (base-diagnostic))
 (check-pred symbol? (diagnostic-category d))
 (check-eq? (diagnostic-category d) 'TYP)
 ;; id と食い違う記号を直に入れた場合。
 (check-false
  (diagnostic-valid?
   (struct-copy diagnostic d [category 'OWN])))
 ;; 記号の代わりに文字列を入れた場合。
 (check-false
  (diagnostic-valid?
   (struct-copy diagnostic d [category "TYP"]))))

;; test 11
(test-case
 "必須欄が欠けた Diagnostic は検証を通らず理由が返る"
 (define d (base-diagnostic))
 (for ([broken (in-list
                (list (struct-copy diagnostic d [id "E-ZZZ-999"])
                      (struct-copy diagnostic d [severity 'fatal])
                      (struct-copy diagnostic d [title ""])
                      (struct-copy diagnostic d [message 'not-a-string])
                      (struct-copy diagnostic d [primary-span #f])
                      (struct-copy diagnostic d
                                   [primary-span '(#:span src 9 2)])))])
   (check-false (diagnostic-valid? broken))
   (check-true (pair? (diagnostic-schema-errors broken)))
   (for ([reason (in-list (diagnostic-schema-errors broken))])
     (check-pred string? reason))))

;; test 12
(test-case
 "2 つの版がどちらも 1 である"
 (check-equal? diagnostic-schema-version 1)
 (check-equal? diagnostic-registry-version 1))

;; test 14
(test-case
 "list の要素まで検査する"
 (define d (base-diagnostic))
 (for ([broken (in-list
                (list
                 ;; secondary-labels の第 1 要素が span でない。
                 (struct-copy diagnostic d
                              [secondary-labels (list (list 'nope "ここ"))])
                 ;; secondary-labels の要素が 2 要素でない。
                 (struct-copy diagnostic d
                              [secondary-labels (list (list other-span))])
                 ;; secondary-labels のラベルが空文字列である。
                 (struct-copy diagnostic d
                              [secondary-labels (list (list other-span ""))])
                 ;; notes の要素が文字列でない。
                 (struct-copy diagnostic d [notes (list 'note)])
                 ;; help の要素が空文字列である。
                 (struct-copy diagnostic d [help (list "")])))])
   (check-false (diagnostic-valid? broken)))
 ;; 正しい要素なら通る。
 (check-true
  (diagnostic-valid?
   (struct-copy diagnostic d
                [secondary-labels (list (list other-span "ここで束縛した"))]
                [notes (list "Int と Bool は別の型である")]
                [help (list "注釈を Bool へ変える")]))))

;; test 15
(test-case
 "schema version 1 は 4 欄へ空を要求する"
 (define d (base-diagnostic))
 (for ([broken (in-list
                (list (struct-copy diagnostic d [origin-chain (list 'o)])
                      (struct-copy diagnostic d [expansion-trace (list 'e)])
                      (struct-copy diagnostic d [related (list d)])
                      (struct-copy diagnostic d [fixes (list 'f)])))])
   (check-false (diagnostic-valid? broken))))

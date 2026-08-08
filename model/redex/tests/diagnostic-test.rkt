#lang racket

(require racket/runtime-path
         racket/set
         rackunit
         "../backend-matrix.rkt"
         "../diagnostic.rkt"
         "diagnostic-fixture-v1.rkt")

;; [REQ: DIA-005] error code の安定識別子と versioning（diagnostic.md）
;; [REQ: DIA-001] Diagnostic IR の生成（diagnostic.md §7）

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
 "registry の行数と内訳と since が一致する"
 ;; 件数は registry へ行を足すたびにこの test も動かす。下限にすると、
 ;; 足し忘れや二重登録が通ってしまう。
 (check-equal? (length diagnostic-registry) 65)
 (define (count-of phase)
   (for/sum ([row (in-list diagnostic-registry)]
             #:when (eq? (diagnostic-code-phase row) phase))
     1))
 (check-equal? (count-of 'elaborate) 53)
 (check-equal? (count-of 'typing) 7)
 (check-equal? (count-of 'origins) 1)
 (check-equal? (count-of 'lowering) 4)
 (define (since-count v)
   (for/sum ([row (in-list diagnostic-registry)]
             #:when (= (diagnostic-code-since row) v))
     1))
 ;; version 1 の 59 行は動かない。増えるのは version 2 の typing だけである。
 (check-equal? (since-count 1) 59)
 (check-equal? (since-count 2) 6)
 (for ([row (in-list diagnostic-registry)])
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
 "schema version は 1、registry version は 2 である"
 (check-equal? diagnostic-schema-version 1)
 (check-equal? diagnostic-registry-version 2))

(test-case
 "typing の registry version 2 と入口 key"
 (check-equal? diagnostic-registry-version 2)
 (check-equal? (diagnostic-code-of 'typing 'ill-typed) "E-TYP-001")
 (check-equal? (diagnostic-code-of 'typing 'not-core-term) "E-SYN-004"))

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

;; test 6
(test-case
 "凍結 fixture v1 の全 (code phase key) が現在の registry にある"
 (check-equal? (length diagnostic-entries-v1) 59)
 (define current
   (list->set
    (for/list ([row (in-list diagnostic-registry)])
      (list (diagnostic-code-code row)
            (diagnostic-code-phase row)
            (diagnostic-code-key row)))))
 ;; 契約は包含のみである。追加は fixture に触れない。削除、改名、番号の
 ;; 再利用、意味の付け替えがあると落ちる。
 (for ([entry (in-list diagnostic-entries-v1)])
   (check-true (set-member? current entry)
               (format "registry から消えたか意味が変わった: ~a" entry))))

(define-runtime-path elaborate-source "../elaborate.rkt")

;; test 7
(test-case
 "elaborate の reject reason が全て registry にある"
 (define source (file->string elaborate-source))
 (define production-source
   (car (string-split source "\n(module+ test")))
 (define reasons
   (sort
    (remove-duplicates
     (for/list ([m (in-list
                    (regexp-match*
                     #px"\\(reject\\s+(?:[a-z-]+|\\([^)]*\\))\\s+'([a-z][a-z0-9-]*)"
                                   production-source
                                   #:match-select values))])
       (string->symbol (second m))))
    symbol<?))
 ;; 件数を固定する。下限にすると、正規表現が壊れて一部しか拾わなくなっても
 ;; 通ってしまう。reason を足したらこの数と registry の両方を更新する。
 (check-equal? (length reasons) 51)
 (for ([reason (in-list reasons)])
   (check-not-false (diagnostic-code-of 'elaborate reason)
                    (format "registry に無い reason: ~a" reason)))
 ;; resolve-proposition の第 3 引数として渡る reason は (reject '...) の
 ;; 字面で現れない。走査の対象外なので明示の許容表で確かめる。
 (for ([reason (in-list '(invalid-obligation invalid-proposition))])
   (check-false (memq reason reasons))
   (check-not-false (diagnostic-code-of 'elaborate reason))))

;; test 13
(test-case
 "lowering の registry 行が diagnostic-ids と一致する"
 (define lowering-rows
   (for/list ([row (in-list diagnostic-registry)]
              #:when (eq? (diagnostic-code-phase row) 'lowering))
     row))
 (define registry-keys (map diagnostic-code-key lowering-rows))
 (define registry-titles (map diagnostic-code-title lowering-rows))
 ;; key は feature-id であり、capability-diagnostic の reason 文字列ではない。
 ;; 文字列が紛れ込むとここで落ちる。
 (for ([key (in-list registry-keys)])
   (check-pred symbol? key))
 (check-equal? registry-keys (map first diagnostic-ids))
 (check-equal? registry-titles (map second diagnostic-ids)))

(test-case "diagnostic-of は registry から id と title を引き当てる"
  (define d (diagnostic-of 'typing 'ill-typed #:primary-span '(#:span src 0 4)))
  (check-equal? (diagnostic-id d) (diagnostic-code-of 'typing 'ill-typed))
  (check-equal? (diagnostic-primary-span d) '(#:span src 0 4))
  ;; message が title と同じなのは Phase 0 の暫定である（spec §13）。
  (check-equal? (diagnostic-message d) (diagnostic-title d))
  (check-true (diagnostic-valid? d))
  ;; expected と found の既定は #f である。
  (check-false (diagnostic-expected d))
  (check-false (diagnostic-found d)))

(test-case "diagnostic-of は registry に無い key を error にする"
  ;; 既定の code へ落とすと、registry へ行を足し忘れたまま診断が出てしまう。
  (check-exn exn:fail?
             (lambda ()
               (diagnostic-of 'typing 'no-such-key #:primary-span '(#:span src 0 4))))
  ;; phase が違えば同じ key でも引き当たらない。
  (check-exn exn:fail?
             (lambda ()
               (diagnostic-of 'origins 'ill-typed #:primary-span '(#:span src 0 4)))))

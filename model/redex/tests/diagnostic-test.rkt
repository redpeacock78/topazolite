#lang racket

(require racket/runtime-path
         racket/set
         rackunit
         "../backend-matrix.rkt"
         "../diagnostic.rkt"
         "diagnostic-fixture-v1.rkt"
         "diagnostic-fixture-v2.rkt"
         "diagnostic-fixture-v3.rkt"
         "diagnostic-fixture-v4.rkt"
         "diagnostic-fixture-v5.rkt"
         "diagnostic-fixture-v6.rkt"
         "diagnostic-fixture-v7.rkt"
         "diagnostic-fixture-v8.rkt"
         "diagnostic-fixture-v9.rkt")

;; [REQ: DIA-005] error code の安定識別子と versioning（diagnostic.md）
;; [REQ: DIA-001] Diagnostic IR の生成（diagnostic.md §8）

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
 (check-equal? (length diagnostic-registry) 141)
 (define (count-of phase)
   (for/sum ([row (in-list diagnostic-registry)]
             #:when (eq? (diagnostic-code-phase row) phase))
     1))
 (check-equal? (count-of 'elaborate) 53)
 (check-equal? (count-of 'typing) 83)
 (check-equal? (count-of 'origins) 1)
 (check-equal? (count-of 'lowering) 4)
 (define (since-count v)
   (for/sum ([row (in-list diagnostic-registry)]
             #:when (= (diagnostic-code-since row) v))
     1))
 ;; version 1 の 59 行は動かない。増えるのは version 2、version 3、version 5 の typing である。
 (check-equal? (since-count 1) 59)
 (check-equal? (since-count 2) 48)
 (check-equal? (since-count 3) 13)
 (check-equal? (since-count 4) 12)
 (check-equal? (since-count 5) 4)
 (check-equal? (since-count 7) 2)
 (check-equal? (since-count 8) 1)
 (check-equal? (since-count 9) 2)
 ;; version 6 で E-BOR-024 を、version 7 と 8 で E-OWN の行を廃止した。
 (define deprecated-map
   '(("E-BOR-024" . 6) ("E-OWN-004" . 8) ("E-OWN-005" . 8)
     ("E-OWN-006" . 7)
     ("E-OWN-009" . 7) ("E-OWN-014" . 8) ("E-OWN-015" . 7)))
 (for ([row (in-list diagnostic-registry)])
   (define expected (assoc (diagnostic-code-code row) deprecated-map))
   (if expected
       (check-equal? (diagnostic-code-deprecated-in row) (cdr expected))
       (check-false (diagnostic-code-deprecated-in row)))))

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
                   #:primary-span ok-span
                   #:source-chain (list (list 'surface 'verbatim ok-span))))

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
 (check-equal? (diagnostic-source-chain d)
               (list (list 'surface 'verbatim ok-span)))
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
 "schema version は 3、registry version は 9 である"
 (check-equal? diagnostic-schema-version 3)
 (check-equal? diagnostic-registry-version 9))

(test-case
 "typing の registry version 9 と入口 key"
 (check-equal? diagnostic-registry-version 9)
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
 "schema version 3 は expansion-trace と fixes へ空を要求する"
 (define d (base-diagnostic))
 (for ([broken (in-list
                (list (struct-copy diagnostic d [expansion-trace (list 'e)])
                      (struct-copy diagnostic d [fixes (list 'f)])))])
   (check-false (diagnostic-valid? broken))))

(test-case
 "related は (relation span description) の 3 要素の list を受ける"
 (define d (base-diagnostic))
 (check-true
  (diagnostic-valid?
   (struct-copy diagnostic d
                [related (list (list 'defined-here other-span "ここで束縛した"))])))
 (check-true
  (diagnostic-valid?
   (struct-copy diagnostic d
                [related (list (list 'defined-here other-span "ここで束縛した")
                               (list 'used-here ok-span "ここで使った"))])))
 (check-true (diagnostic-valid? (struct-copy diagnostic d [related '()]))))

(test-case
 "related の要素が形を外れたら落ちる"
 (define d (base-diagnostic))
 (for ([broken (in-list
                (list
                 (list (list 'defined-here other-span))
                 (list (list 'defined-here other-span "説明" "余り"))
                 (list (list "defined-here" other-span "説明"))
                 (list (list 'defined-here '(#:span src 9 2) "説明"))
                 (list (list 'defined-here other-span ""))
                 (list (list 'defined-here other-span '説明))
                 (list 'defined-here)))])
   (check-false
    (diagnostic-valid? (struct-copy diagnostic d [related broken]))
    (format "~s は落ちなければならない" broken))))

(test-case
 "relation の語彙は固定しない"
 (define d (base-diagnostic))
 (check-true
  (diagnostic-valid?
   (struct-copy diagnostic d
                [related (list (list 'no-such-relation-name other-span "説明"))]))))

;; test 15b
(test-case
 "検証器は妥当な source-chain を通す"
 (define d (base-diagnostic))
 (for ([chain (in-list
               (list (list (list 'surface 'verbatim ok-span))
                     (list (list 'surface 'synthetic-span ok-span))
                     (list (list 'surface 'synthesized ok-span))
                     (list (list 'surface 'verbatim ok-span)
                           (list 'elaborate 'synthesized other-span))))])
   (define good (struct-copy diagnostic d [source-chain chain]))
   (check-equal? (diagnostic-schema-errors good) '()
                 (format "通るはずの chain である: ~s" chain))))

;; test 15c
(test-case
 "検証器は不正な source-chain を棄却する"
 (define d (base-diagnostic))
 (for ([chain (in-list
               (list '()
                     (list (list 'elaborate 'synthesized ok-span))
                     (list (list 'surface 'verbatim ok-span)
                           (list 'surface 'verbatim other-span))
                     (list (list 'surface 'verbatim ok-span)
                           (list 'elaborate 'synthesized other-span)
                           (list 'surface 'verbatim ok-span))
                     (list (list 'surface 'verbatim))
                     (list (list 'surface 'bogus ok-span))
                     (list (list 'surface 'verbatim '(#:span src 7 3)))
                     'not-a-list))])
   (define broken (struct-copy diagnostic d [source-chain chain]))
   (check-false (diagnostic-valid? broken)
                (format "棄却するはずの chain である: ~s" chain))))

;; test 15d
(test-case
 "検証器は backend の値域を検査する"
 (define d (base-diagnostic))
 (check-false (diagnostic-backend d))
 (for ([good (in-list '(racket-cs racketscript #f))])
   (check-equal? (diagnostic-schema-errors (struct-copy diagnostic d [backend good]))
                 '()
                 (format "通るはずの backend である: ~s" good)))
 (for ([bad (in-list '(node "racket-cs" chez))])
   (check-false (diagnostic-valid? (struct-copy diagnostic d [backend bad]))
                (format "棄却するはずの backend である: ~s" bad))))

;; test 15e
(test-case
 "diagnostic-of は phase と backend の対応に反する呼出しを error にする"
 (check-exn exn:fail?
            (lambda ()
              (diagnostic-of 'lowering 'unknown-core-form
                             #:primary-span '(#:span src 0 4))))
 (check-exn exn:fail?
            (lambda ()
              (diagnostic-of 'typing 'ill-typed
                             #:primary-span '(#:span src 0 4)
                             #:backend 'racket-cs))))

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

(test-case
 "凍結 fixture v2 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v2) 107)
 (for ([entry (in-list diagnostic-entries-v2)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

(test-case
 "凍結 fixture v3 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v3) 120)
 (for ([entry (in-list diagnostic-entries-v3)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

(test-case
 "凍結 fixture v4 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v4) 132)
 (for ([entry (in-list diagnostic-entries-v4)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

(test-case
 "凍結 fixture v5 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v5) 136)
 (for ([entry (in-list diagnostic-entries-v5)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

(test-case
 "凍結 fixture v6 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v6) 136)
 (for ([entry (in-list diagnostic-entries-v6)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

(test-case
 "凍結 fixture v7 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v7) 138)
 (for ([entry (in-list diagnostic-entries-v7)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

(test-case
 "凍結 fixture v8 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v8) 139)
 (for ([entry (in-list diagnostic-entries-v8)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

(test-case
 "凍結 fixture v9 の全 (code phase key) が現在の registry に同じ組である"
 (check-equal? (length diagnostic-entries-v9) 141)
 (for ([entry (in-list diagnostic-entries-v9)])
   (match-define (list code phase key) entry)
   (define row (diagnostic-code-row code))
   (check-true (and row
                    (eq? (diagnostic-code-phase row) phase)
                    (eq? (diagnostic-code-key row) key))
               (format "~a が registry に同じ組で存在する" code))))

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
 ;; 通ってしまう。G5c5b3b で elaborate 側の owned-constructor-field は OwnLeaf
 ;; gate へ移り到達しなくなったため、ここでは registry を据え置いたまま 1 件減る。
 (check-equal? (length reasons) 46)
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

;; [REQ: DIA-001] 1 行として出す欄への改行の禁止（spec §4）
;; 6 欄それぞれについて #\newline と #\return の 2 文字を個別に検査する。
;; 文字列の 5 欄はこの表で回し、記号である relation は次の test-case で扱う。
;; 合わせて 12 通りになる。1 欄だけへ検査を足した実装は、どれかで落ちる。
(define newline-injection-table
  (list
   (list 'title
         (lambda (d s) (struct-copy diagnostic d [title s])))
   (list 'notes
         (lambda (d s) (struct-copy diagnostic d [notes (list s)])))
   (list 'help
         (lambda (d s) (struct-copy diagnostic d [help (list s)])))
   (list 'secondary-label
         (lambda (d s)
           (struct-copy diagnostic d [secondary-labels (list (list other-span s))])))
   (list 'related-description
         (lambda (d s)
           (struct-copy diagnostic d
                        [related (list (list 'defined-here other-span s))])))))

(test-case
 "1 行として出す 5 つの文字列の欄は改行を含めない"
 (define d (base-diagnostic))
 (for* ([entry (in-list newline-injection-table)]
        [ch (in-list (list "\n" "\r"))])
   (match-define (list name inject) entry)
   (define broken (inject d (string-append "前" ch "後")))
   (check-false (diagnostic-valid? broken)
                (format "~a へ ~s を入れたら落ちなければならない" name ch))))

(test-case
 "related の relation の記号名も改行を含めない"
 (define d (base-diagnostic))
 (for ([ch (in-list (list "\n" "\r"))])
   (define relation (string->symbol (string-append "前" ch "後")))
   (define broken
     (struct-copy diagnostic d
                  [related (list (list relation other-span "説明"))]))
   (check-false (diagnostic-valid? broken)
                (format "relation へ ~s を入れたら落ちなければならない" ch))))

(test-case
 "改行を含まない値は 6 欄とも通る"
 (define d (base-diagnostic))
 (check-true
  (diagnostic-valid?
   (struct-copy diagnostic d
                [title "型が期待と一致しない"]
                [notes (list "Int と Bool は別の型である")]
                [help (list "束縛の型注釈を直す")]
                [secondary-labels (list (list other-span "ここで束縛した"))]
                [related (list (list 'defined-here other-span "ここで束縛した"))]))))

(test-case
 "message は複数行を許す"
 (define d (base-diagnostic))
 ;; 複数行を許す欄を誤って縛った実装は、この 1 行で落ちる。
 (check-true
  (diagnostic-valid?
   (struct-copy diagnostic d [message "第 1 行\n第 2 行"]))))

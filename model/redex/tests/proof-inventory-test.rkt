#lang racket

(require rackunit
         racket/file
         racket/string
         "../../../tools/proof-inventory.rkt")

(define req-one (string-append "ZZZ" "-901"))
(define req-two (string-append "ZZZ" "-902"))
(define req-unknown (string-append "ZZZ" "-999"))
(define thm-one (string-append "THM" "-901"))
(define thm-two (string-append "THM" "-902"))
(define thm-unknown (string-append "THM" "-903"))

(define fst-path "model/fstar/Example.fst")
(define fst-path-core "model/fstar/ExampleCore.fst")
(define surface-path "docs/specification/surface.md")
(define registry-path "docs/specification/requirements.md")
(define inventory-path "docs/specification/proof-inventory.md")
(define evidence-path "model/redex/tests/evidence.rkt")

(define (write-text root relative content)
  (define path (build-path root relative))
  (make-directory* (or (path-only path) root))
  (call-with-output-file path
    (lambda (output) (display content output))
    #:exists 'truncate))

(define (theorem-note thm [full "-"] [part "-"] [spec "surface.md§8"]
                      [rule "-"] [redex "-"] [assumptions "-"]
                      [scope "範囲を fixture で検査する"])
  (string-join
   (list (format "//@ THM: ~a" thm)
         (format "//@ REQ-FULL: ~a" full)
         (format "//@ REQ-PART: ~a" part)
         (format "//@ SPEC: ~a" spec)
         (format "//@ RULE: ~a" rule)
         (format "//@ REDEX: ~a" redex)
         (format "//@ ASSUMPTIONS: ~a" assumptions)
         (format "//@ SCOPE: ~a" scope))
   "\n"))

(define (registry-text)
  (string-append
   (format "### ~a\n\n- **状態**：G1\n\n" req-one)
   (format "### ~a\n\n- **状態**：P2\n" req-two)))

(define (surface-text [thms (list thm-one thm-two)])
  (string-append
   "## 8. 命題\n\n"
   (string-join
    (for/list ([thm (in-list thms)] [index (in-naturals 1)])
      (format "~a. **命題**（~a）：fixture。" index thm))
    "\n")
   "\n"))

(define (fst-text #:first [first-note (theorem-note thm-one)]
                  #:left [left-note (theorem-note thm-two)]
                  #:right [right-note
                           (theorem-note thm-two "-" "-" "surface.md§8"
                                         "-" "-" "-"
                                         "別の構文を覆う")]
                  #:helper [helper-note
                            (format "//@ AUX: helper ~a,~a" thm-one thm-two)]
                  #:example [example-note "//@ AUX: example -"])
  (string-append
   "module Example\n\n"
   first-note "\n"
   "val lex :\n  unit -> Tot bool\n\n"
   left-note "\n"
   "let left : Lemma True = ()\n\n"
   right-note "\n"
   "let right : Lemma True = ()\n\n"
   helper-note "\n"
   "let helper : Lemma True = ()\n\n"
   example-note "\n"
   "let example : Lemma True = ()\n"))

(define (core-module-text #:note [note (theorem-note thm-unknown "-" "-" "borrow.md§1")]
                          #:name [name "core_inv"])
  (string-append "module ExampleCore\n\n" note "\n"
                 "let " name " : Lemma True = ()\n"))

(define (proof-table [rows (list (cons thm-one "`lex`")
                                 (cons thm-two "`left`, `right`") )])
  (string-append
   "| THM | 宣言 |\n| --- | --- |\n"
   (string-join
    (for/list ([row (in-list rows)])
      (format "| ~a | ~a |" (car row) (cdr row)))
    "\n")
   "\n"))

(define (inventory-row id [state "未検証"] [propositions "-"]
                       [evidence "-"] [tests "-"])
  (format "| ~a | ~a | ~a | ~a | ~a |"
          id state propositions evidence tests))

(define (list-table [rows (list (inventory-row req-one)
                                (inventory-row req-two))])
  (string-append
   "| 要件 ID | 状態 | 命題 | 補助の証拠 | 根拠の試験 |\n"
   "| --- | --- | --- | --- | --- |\n"
   (string-join rows "\n") "\n"))

(define (inventory-text #:proof [proof (proof-table)]
                        #:rows [rows (list (inventory-row req-one)
                                           (inventory-row req-two))])
  (string-append "# 証明範囲\n\n## 4. 一覧\n\n"
                 proof "\n" (list-table rows)))

(define (evidence-text #:reqs [reqs (list req-one)]
                      #:case [case-name "根拠例"])
  (format "#lang racket\n;; [REQ: ~a]\n(test-case ~s (void))\n"
          (string-join reqs ", ") case-name))

(define (base-files)
  (hash fst-path (fst-text)
        surface-path (surface-text)
        registry-path (registry-text)
        inventory-path (inventory-text)
        "docs/specification/borrow.md" "## 1. 借用\n"
        evidence-path (evidence-text)))

(define (with-fixture overrides proc)
  (define root (make-temporary-file "proof-inventory~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (define files (hash-copy (base-files)))
      (for ([(relative content) (in-hash overrides)])
        (hash-set! files relative content))
      (for ([(relative content) (in-hash files)])
        (write-text root relative content))
      (proc root))
    (lambda () (delete-directory/files root))))

(define (run-fixture root #:fst-paths [fst-paths #f])
  (define output (open-output-string))
  (define error-output (open-output-string))
  (define actual-fst-paths
    (or fst-paths
        (append (list (build-path root fst-path))
                (if (file-exists? (build-path root fst-path-core))
                    (list (build-path root fst-path-core))
                    '()))))
  (define status
    (run-proof-inventory #:fst-paths actual-fst-paths
                         #:surface (build-path root surface-path)
                         #:registry (build-path root registry-path)
                         #:inventory (build-path root inventory-path)
                         #:spec-dir (build-path root "docs/specification")
                         #:root root
                         #:output output
                         #:error-output error-output))
  (list status (get-output-string output) (get-output-string error-output)))

(define (run-overrides overrides)
  (with-fixture overrides run-fixture))

(define (check-failure result pattern)
  (check-equal? (first result) 1)
  (check-regexp-match pattern (third result)))

(define (table-with-row id state propositions evidence tests)
  (inventory-text
   #:rows (list (inventory-row id state propositions evidence tests)
                (inventory-row req-two))))

(test-case "正常な一覧は exit 0 で終わる"
  (define result (run-overrides (hash)))
  (check-equal? (first result) 0)
  (check-regexp-match #px"Proof inventory OK: 2 件の要件、4 個の補題"
                      (second result)))

(test-case "注記の無い補題を報告する"
  (define result
    (run-overrides
     (hash fst-path "module Example\nlet missing_note : Lemma True = ()\n")))
  (check-failure result #px"missing_note"))

(test-case "局所の Lemma を持つ非補題は注記を要しない"
  (define result
    (run-overrides
     (hash fst-path
           "module Example\nlet outer : int =\n  let aux : Lemma True = ()\n  0\n"
           surface-path (surface-text '())
           inventory-path (inventory-text #:proof (proof-table '())))))
  (check-equal? (first result) 0))

(test-case "同名の val と let の組は一つの宣言として数える"
  (define fst
    (string-append (theorem-note thm-one) "\nval lemma : Lemma True\nlet lemma = ()\n"))
  (define inventory
    (inventory-text #:proof (proof-table (list (cons thm-one "`lemma`")))))
  (define result
    (run-overrides
     (hash fst-path fst
           surface-path (surface-text (list thm-one))
           inventory-path inventory)))
  (check-equal? (first result) 0)
  (check-regexp-match #px"1 個の補題" (second result)))

(test-case "自由文コメントが注記と補題の間にあると注記の欠落とする"
  (define result
    (run-overrides
     (hash fst-path
           (string-append (theorem-note thm-one)
                          "\n// 自由文\nlet separated : Lemma True = ()\n"))))
  (check-failure result #px"separated"))

(test-case "必須の欄の欠落を報告する"
  (define malformed
    (string-trim
     (string-replace (theorem-note thm-one) "//@ SCOPE: 範囲を fixture で検査する" "")))
  (define result (run-overrides (hash fst-path (fst-text #:first malformed))))
  (check-failure result #px"SCOPE"))

(test-case "欄の順序の誤りを報告する"
  (define note (theorem-note thm-one))
  (define reordered
    (string-replace note
                    "//@ REDEX: -\n//@ ASSUMPTIONS: -"
                    "//@ ASSUMPTIONS: -\n//@ REDEX: -"))
  (define result (run-overrides (hash fst-path (fst-text #:first reordered))))
  (check-failure result #px"順序"))

(test-case "同じ THM の注記が SCOPE だけ異なれば受理する"
  (check-equal? (first (run-overrides (hash))) 0))

(test-case "同じ THM の注記で SCOPE 以外の欄が食い違えば報告する"
  (define result
    (run-overrides
     (hash fst-path
           (fst-text #:right (theorem-note thm-two "-" req-one)))))
  (check-failure result #px"SCOPE 以外"))

(test-case "Tot を明示し命題の表に登録した val の命題の注記を受理する"
  (define result (run-overrides (hash)))
  (check-equal? (first result) 0))

(test-case "命題の表に無い val の命題の注記を報告する"
  (define extra-note (theorem-note thm-unknown))
  (define fst
    (string-append (fst-text) extra-note "\nval extra : unit -> Tot int\n"))
  (define surface (surface-text (list thm-one thm-two thm-unknown)))
  (define result (run-overrides (hash fst-path fst surface-path surface)))
  (check-failure result #px"extra"))

(test-case "Tot を明示しない val の命題の注記を報告する"
  (define fst
    (string-append (theorem-note thm-one)
                   "\nval not_total : unit -> int\n"))
  (define result (run-overrides (hash fst-path fst)))
  (check-failure result #px"Tot"))

(test-case "補助の補題に付いた命題の注記を命題の表との食い違いとして報告する"
  (define fst
    (fst-text #:helper (theorem-note thm-two "-" "-" "surface.md§8"
                                    "-" "-" "-" "helper の範囲")))
  (define result (run-overrides (hash fst-path fst)))
  (check-failure result #px"helper"))

(test-case "Lemma でない val に付いた補助の注記を報告する"
  (define fst (string-append (fst-text) "//@ AUX: example -\nval plain : int = 1\n"))
  (define result (run-overrides (hash fst-path fst)))
  (check-failure result #px"plain"))

(test-case "§4 の表に登録した Core の THM は surface.md §8 に無くても通る"
  (define result
    (run-overrides
     (hash fst-path-core (core-module-text)
           inventory-path
           (inventory-text #:proof
                           (proof-table (list (cons thm-one "`lex`")
                                              (cons thm-two "`left`, `right`")
                                              (cons thm-unknown "`core_inv`")))))))
  (check-equal? (first result) 0 (third result)))

(test-case "surface.md §8 の THM が §4 の表に無ければ落ちる"
  (define result
    (run-overrides (hash surface-path (surface-text (list thm-one thm-two thm-unknown)))))
  (check-failure result #px"surface.md.*表"))

(test-case "§4 の表に無い THM の注記は落ちる"
  (define result (run-overrides (hash fst-path-core (core-module-text))))
  (check-failure result #px"命題の表"))

(test-case "二つの module に同じ宣言名があれば報告する"
  (define note (theorem-note thm-one))
  (define result
    (run-overrides (hash fst-path-core (core-module-text #:note note #:name "lex"))))
  (check-failure result #px"lex.*重複"))

(test-case "注記の無い補助の宣言は他の module と同名でも重複にしない"
  (define result
    (run-overrides
     (hash fst-path-core
           "module ExampleCore\n\nlet helper : int = 0\n")))
  (check-false (regexp-match? #px"helper.*重複" (third result))))

(test-case "F* の module が一つも無ければ報告する"
  (define status
    (with-fixture (hash)
      (lambda (root)
        (run-fixture root #:fst-paths '()))))
  (check-equal? (first status) 1)
  (check-regexp-match #px"F\\* の module が無い" (third status)))

(test-case "AUX helper の複数 THM を受理し、無い THM を報告する"
  (define result
    (run-overrides
     (hash fst-path (fst-text #:helper
                              (format "//@ AUX: helper ~a,~a" thm-one thm-unknown)))))
  (check-equal? (first (run-overrides (hash))) 0)
  (check-failure result #px"AUX.*THM"))

(test-case "存在しない要件 ID を報告する"
  (define result
    (run-overrides
     (hash fst-path (fst-text #:first
                              (theorem-note thm-one req-unknown)))))
  (check-failure result (regexp (regexp-quote req-unknown))))

(test-case "存在しない SPEC の文書と REDEX の path を報告する"
  (define result
    (run-overrides
     (hash fst-path
           (fst-text #:first
                     (theorem-note thm-one "-" "-"
                                   "absent.md§1" "-" "missing-test.rkt")))))
  (check-failure result #px"absent.md")
  (check-regexp-match #px"missing-test.rkt" (third result)))

(test-case "一覧に無い要件と一覧にしか無い ID を報告する"
  (define result
    (run-overrides
     (hash inventory-path
           (inventory-text #:rows (list (inventory-row req-one)
                                        (inventory-row req-unknown))))))
  (check-failure result #px"要件 ID")
  (check-regexp-match (regexp (regexp-quote req-two)) (third result))
  (check-regexp-match (regexp (regexp-quote req-unknown)) (third result)))

(test-case "一覧の列数が違う行を報告する"
  (define inventory
    (inventory-text
     #:rows (list (string-append (inventory-row req-one) " | 余分な列 |")
                  (inventory-row req-two))))
  (check-failure (run-overrides (hash inventory-path inventory)) #px"列数"))

(test-case "REQ-FULL と一覧の状態の食い違いを報告する"
  (define fst (fst-text #:first (theorem-note thm-one req-one)))
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "未検証" thm-one)
                  (inventory-row req-two))))
  (define result
    (run-overrides (hash fst-path fst inventory-path inventory)))
  (check-failure result #px"証明済み"))

(test-case "命題と補助の証拠の欄の食い違いを報告する"
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "未検証" thm-two)
                  (inventory-row req-two))))
  (define result (run-overrides (hash inventory-path inventory)))
  (check-failure result #px"命題"))

(test-case "REQ-PART と AUX example を補助の証拠欄に反映する"
  (define fst
    (fst-text #:first (theorem-note thm-one "-" req-one)
              #:example (format "//@ AUX: example ~a" req-one)))
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "未検証" "-"
                                 (format "~a, `example`" thm-one))
                  (inventory-row req-two))))
  (check-equal? (first (run-overrides (hash fst-path fst inventory-path inventory))) 0))

(test-case "根拠の試験が要件を参照しない行を報告する"
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "テストのみ" "-" "-"
                                 (format "`~a`::`根拠例`" evidence-path))
                  (inventory-row req-two))))
  (define result
    (run-overrides
     (hash inventory-path inventory evidence-path (evidence-text #:reqs '()))))
  (check-failure result #px"参照"))

(test-case (string-append req-one ": 試験ファイル内の ID は req-coverage と同じ基準で数える")
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "テストのみ" "-" "-"
                                 (format "`~a`::`~a: 性質を assert する`"
                                         evidence-path req-one))
                  (inventory-row req-two))))
  (define evidence
    (format "#lang racket\n(test-case \"~a: 性質を assert する\" (check-true #t))\n"
            req-one))
  (check-equal? (first (run-overrides (hash inventory-path inventory
                                           evidence-path evidence)))
                0))

(test-case "[REQ: A, B] の二つ目の ID も参照と認める"
  (define evidence
    (evidence-text #:reqs (list req-one req-two)))
  (define tests (format "`~a`::`根拠例`" evidence-path))
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "テストのみ" "-" "-" tests)
                  (inventory-row req-two "テストのみ" "-" "-" tests))))
  (define result
    (run-overrides (hash inventory-path inventory evidence-path evidence)))
  (check-equal? (first result) 0))

(test-case "存在しない test-case 名を報告する"
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "テストのみ" "-" "-"
                                 (format "`~a`::`存在しない`" evidence-path))
                  (inventory-row req-two))))
  (define result (run-overrides (hash inventory-path inventory)))
  (check-failure result #px"存在しない"))

(test-case "test-case 名の部分一致は存在と認めない"
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "テストのみ" "-" "-"
                                 (format "`~a`::`根拠例`" evidence-path))
                  (inventory-row req-two))))
  (define result
    (run-overrides
     (hash inventory-path inventory
           evidence-path (evidence-text #:case "根拠例の続き"))))
  (check-failure result #px"根拠例"))

(test-case "bounded-row-check の名前を根拠として受理する"
  (define case-name (string-append req-one ": 性質を生成検査する"))
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "テストのみ" "-" "-"
                                 (format "`~a`::`~a`" evidence-path case-name))
                  (inventory-row req-two))))
  (define evidence
    (format "#lang racket\n(bounded-row-check ~s pattern property)\n" case-name))
  (check-equal? (first (run-overrides (hash inventory-path inventory
                                            evidence-path evidence)))
                0))

(test-case "許可リスト外の my-check だけでは根拠として認めない"
  (define case-name (string-append req-one ": 性質を検査する"))
  (define inventory
    (inventory-text
     #:rows (list (inventory-row req-one "テストのみ" "-" "-"
                                 (format "`~a`::`~a`" evidence-path case-name))
                  (inventory-row req-two))))
  (define evidence
    (format "#lang racket\n(my-check ~s pattern property)\n" case-name))
  (check-failure (run-overrides (hash inventory-path inventory
                                      evidence-path evidence))
                 #px"名前付き試験"))

(test-case "SCOPE に admit か assume の語がある注記を報告する"
  (define result
    (run-overrides
     (hash fst-path
           (fst-text #:first
                     (theorem-note thm-one "-" "-" "surface.md§8"
                                   "-" "-" "-" "admit の範囲")))))
  (check-failure result #px"SCOPE"))

(test-case "SCOPE の admitted のような語の一部は報告しない"
  (define result
    (run-overrides
     (hash fst-path
           (fst-text #:first
                     (theorem-note thm-one "-" "-" "surface.md§8"
                                   "-" "-" "-" "admitted を含む scope")))))
  (check-equal? (first result) 0))

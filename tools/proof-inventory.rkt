#lang racket

(require racket/file
         racket/list
         racket/match
         racket/path
         racket/runtime-path
         racket/set
         racket/string
         "req-coverage.rkt")

(provide annotation-errors
         inventory-errors
         main
         run-proof-inventory)

(define-runtime-path project-root "..")
(define declaration-rx #px"^(val|let(?: rec)?) +([A-Za-z_][A-Za-z0-9_']*)\\b")
(define thm-rx #px"THM-[0-9]{3}")
(define thm-id-rx #px"^THM-[0-9]{3}$")
(define requirement-rx #px"^[A-Z]{3}-[0-9]{3}$")
(define req-annotation-rx #px"\\[REQ: ([^]]*)\\]")
(define note-fields
  '("THM" "REQ-FULL" "REQ-PART" "SPEC" "RULE" "REDEX" "ASSUMPTIONS" "SCOPE"))
(define scope-forbidden-rx
  #px"(?<![A-Za-z0-9_])(admit|assume)(?![A-Za-z0-9_])")

(struct declaration (kind name type annotation-lines) #:transparent)
(struct parsed-note (kind fields) #:transparent)

(define (sorted-unique values)
  (sort (remove-duplicates values) string<?))

(define (duplicates values)
  (define counts
    (for/fold ([counts (hash)]) ([value (in-list values)])
      (hash-update counts value add1 0)))
  (sort (for/list ([(value count) (in-hash counts)] #:when (> count 1)) value)
        string<?))

(define (set-difference-list left right)
  (sort (set->list (set-subtract (list->set left) (list->set right))) string<?))

(define (type-before-body kind lines)
  (if (equal? kind "val")
      (string-join lines "\n")
      (let loop ([remaining lines] [before '()])
        (cond
          [(null? remaining) (string-join (reverse before) "\n")]
          [else
           (define line (car remaining))
           (define equals (regexp-match-positions #rx"=" line))
           (if equals
               (string-join
                (reverse (cons (substring line 0 (caar equals)) before))
                "\n")
               (loop (cdr remaining) (cons line before)))]))))

(define (preceding-annotation-lines lines start)
  (let loop ([index (sub1 start)] [found '()])
    (if (and (>= index 0)
             (string-prefix? (list-ref lines index) "//@"))
        (loop (sub1 index) (cons (list-ref lines index) found))
        found)))

(define (fst-declarations path)
  (define lines (file->lines path))
  (define starts
    (for/list ([line (in-list lines)] [index (in-naturals)]
               #:do [(define match (regexp-match declaration-rx line))]
               #:when match)
      (list index (cadr match) (caddr match))))
  (define ends
    (append (map car (cdr starts)) (list (length lines))))
  (define raw
    (for/list ([entry (in-list starts)] [end (in-list ends)])
      (define start (car entry))
      (define kind (cadr entry))
      (define name (caddr entry))
      (define body-lines (take (drop lines start) (- end start)))
      (declaration kind
                   name
                   (type-before-body kind body-lines)
                   (preceding-annotation-lines lines start))))
  (define val-names
    (for/set ([item (in-list raw)]
              #:when (equal? (declaration-kind item) "val"))
      (declaration-name item)))
  (for/list ([item (in-list raw)]
             #:unless (and (member (declaration-kind item) '("let" "let rec"))
                           (set-member? val-names (declaration-name item))))
    item))

(define (lemma-declaration? item)
  (regexp-match? #px"(?<![A-Za-z0-9_'])Lemma(?![A-Za-z0-9_'])"
                 (declaration-type item)))

(define (total-val? item)
  (and (equal? (declaration-kind item) "val")
       (regexp-match? #px"-> Tot " (declaration-type item))))

(define (parse-note-line line)
  (match (regexp-match #px"^//@ ([A-Z-]+):[ \t]*(.*)$" line)
    [(list _ field value) (cons field (string-trim value))]
    [_ #f]))

(define (parse-annotation item)
  (define lines (declaration-annotation-lines item))
  (cond
    [(null? lines) (values #f '())]
    [(string-prefix? (car lines) "//@ AUX:")
     (match (and (= (length lines) 1)
                 (regexp-match #px"^//@ AUX: (helper|example) (.+)$" (car lines)))
       [(list _ kind value)
        (values (parsed-note 'aux (hash "AUX-KIND" kind "AUX-VALUE" value)) '())]
       [_
        (values #f
                (list (format "~a: AUX 注記は一行の helper または example 形式で書く"
                              (declaration-name item))))])]
    [else
     (define parsed-lines (map parse-note-line lines))
     (define errors '())
     (define (report! message) (set! errors (cons message errors)))
     (unless (string-prefix? (car lines) "//@ THM:")
       (report! (format "~a: 注記は THM または AUX で始める"
                        (declaration-name item))))
     (unless (= (length lines) (length note-fields))
       (report! (format "~a: THM 注記は必須欄を 8 行で持つ"
                        (declaration-name item))))
     (when (ormap not parsed-lines)
       (report! (format "~a: THM 注記の欄の書式が不正"
                        (declaration-name item))))
     (define actual-fields (filter values parsed-lines))
     (define actual-order (map car actual-fields))
     (unless (equal? actual-order note-fields)
       (report! (format "~a: THM 注記の欄順序が不正"
                        (declaration-name item))))
     (define field-counts (map car actual-fields))
     (for ([field (in-list note-fields)]
           #:unless (member field field-counts))
       (report! (format "~a: 必須欄 ~a が無い" (declaration-name item) field)))
     (for ([field (in-list (duplicates field-counts))])
       (report! (format "~a: 欄 ~a が重複している" (declaration-name item) field)))
     (define fields
       (for/hash ([entry (in-list actual-fields)])
         (values (car entry) (cdr entry))))
     (for ([field (in-list note-fields)]
           #:when (equal? (hash-ref fields field #f) ""))
       (report! (format "~a: 欄 ~a の値が空" (declaration-name item) field)))
     (values (parsed-note 'thm fields) (reverse errors))]))

(define (comma-values value)
  (cond
    [(or (not value) (equal? value "-")) '()]
    [else (map string-trim (string-split value ","))]))

(define (well-formed-list? value pattern)
  (or (equal? value "-")
      (let ([parts (comma-values value)])
        (and (pair? parts)
             (andmap (lambda (part) (regexp-match? pattern part)) parts)))))

(define (surface-thm-ids path)
  (define lines (file->lines path))
  (define start
    (for/first ([line (in-list lines)] [index (in-naturals)]
                #:when (regexp-match? #px"^## 8\\." line))
      index))
  (if (not start)
      (values '() #f)
      (let* ([end (or (for/first ([line (in-list lines)] [index (in-naturals)]
                                  #:when (and (> index start)
                                              (regexp-match? #px"^## [^#]" line)))
                         index)
                       (length lines))]
             [section (take (drop lines (add1 start)) (- end start 1))])
        (values (append-map (lambda (line) (regexp-match* thm-rx line)) section) #t))))

(define (test-req-ids source)
  (regexp-match* test-id-rx source))

;; 根拠名は通常の test-case と、性質生成器の bounded-row-check に限る。
(define test-definition-forms '("test-case" "bounded-row-check"))

(define (named-test-definition? source case-name)
  (for/or ([form (in-list test-definition-forms)])
    (regexp-match?
     (pregexp (format "\\(~a[[:space:]]+\"~a\""
                      (regexp-quote form)
                      (regexp-quote case-name)))
     source)))

(define (annotation-errors fst-path surface-path registry-path spec-dir repo-root)
  (define definitions (fst-declarations fst-path))
  (define known-reqs (list->set (map car (registry-definitions registry-path))))
  (define errors '())
  (define thm-annotations '())
  (define aux-annotations '())
  (define (report! message) (set! errors (cons message errors)))
  (for ([item (in-list definitions)])
    (define name (declaration-name item))
    (define is-lemma (lemma-declaration? item))
    (define note-lines (declaration-annotation-lines item))
    (when (and is-lemma (null? note-lines))
      (report! (format "~a: Lemma に注記が無い" name)))
    (unless (null? note-lines)
      (define-values (note parse-errors) (parse-annotation item))
      (for ([message (in-list parse-errors)]) (report! message))
      (when note
        (cond
          [(eq? (parsed-note-kind note) 'thm)
           (define fields (parsed-note-fields note))
           (define thm (hash-ref fields "THM" #f))
           (when thm
             (unless (regexp-match? thm-id-rx thm)
               (report! (format "~a: THM ID の書式が不正" name)))
             (set! thm-annotations (cons (list thm name fields) thm-annotations)))
           (unless (or is-lemma (total-val? item))
             (report! (format "~a: 命題注記は Lemma または型に Tot を明示した val にだけ付ける"
                              name)))
           (for ([field (in-list '("REQ-FULL" "REQ-PART"))])
             (define value (hash-ref fields field #f))
             (when (and value (not (well-formed-list? value requirement-rx)))
               (report! (format "~a: ~a の要件 ID の書式が不正" name field)))
             (for ([id (in-list (comma-values value))]
                   #:unless (set-member? known-reqs id))
               (report! (format "~a: ~a が requirements.md に無い" name id))))
           (define scope (hash-ref fields "SCOPE" #f))
           (when (and scope (regexp-match? scope-forbidden-rx scope))
             (report! (format "~a: SCOPE に CI の F* 検査対象語がある" name)))
           (define spec-value (hash-ref fields "SPEC" #f))
           (when spec-value
             (for ([reference (in-list (comma-values spec-value))])
               (match (regexp-match #px"^(.+?)\\s*§\\s*([0-9]+(?:\\.[0-9]+)*)$"
                                    reference)
                 [(list _ document _section)
                  (unless (file-exists? (build-path spec-dir (string-trim document)))
                    (report! (format "~a: SPEC の文書 ~a が無い" name document)))]
                 [_ (report! (format "~a: SPEC の書式が不正" name))])))
           (define redex-value (hash-ref fields "REDEX" #f))
           (define redex-paths (comma-values redex-value))
           (when (and redex-value
                      (not (or (equal? redex-value "-")
                               (and (pair? redex-paths)
                                    (andmap (lambda (path) (not (equal? path "")))
                                            redex-paths)))))
             (report! (format "~a: REDEX の path が空" name)))
           (when redex-value
             (for ([path (in-list redex-paths)] #:unless (equal? path ""))
               (unless (file-exists? (build-path repo-root path))
                 (report! (format "~a: REDEX の path ~a が無い" name path)))))
           (define assumptions (hash-ref fields "ASSUMPTIONS" #f))
           (when (and assumptions
                      (not (well-formed-list? assumptions #px"^[A-Za-z_][A-Za-z0-9_']*$")))
             (report! (format "~a: ASSUMPTIONS の述語名の書式が不正" name)))
           (define rule-value (hash-ref fields "RULE" #f))
           (define rule-parts (comma-values rule-value))
           (when (and rule-value
                      (not (or (equal? rule-value "-")
                               (and (pair? rule-parts)
                                   (andmap (lambda (part) (not (equal? part "")))
                                            rule-parts)))))
             (report! (format "~a: RULE の値が空" name)))]
          [(eq? (parsed-note-kind note) 'aux)
           (set! aux-annotations (cons (list name (parsed-note-fields note)) aux-annotations))
           (unless is-lemma
             (report! (format "~a: AUX 注記は Lemma にだけ付ける" name)))
           (define kind (hash-ref (parsed-note-fields note) "AUX-KIND"))
           (define value (hash-ref (parsed-note-fields note) "AUX-VALUE"))
           (cond
             [(equal? kind "helper")
              (define ids (comma-values value))
              (unless (and (pair? ids) (andmap (lambda (id) (regexp-match? thm-id-rx id)) ids))
                (report! (format "~a: AUX helper の THM の書式が不正" name)))]
             [else
              (unless (or (equal? value "-")
                          (regexp-match? requirement-rx value))
                (report! (format "~a: AUX example の要件 ID の書式が不正" name)))
              (when (and (not (equal? value "-"))
                         (not (set-member? known-reqs value)))
                (report! (format "~a: AUX example の要件 ID ~a が無い" name value)))])]))))
  (define declared-thms (sorted-unique (map car thm-annotations)))
  (define surface-values (call-with-values (lambda () (surface-thm-ids surface-path)) list))
  (define surface-thms (first surface-values))
  (unless (second surface-values)
    (report! "surface.md に §8 の命題一覧が無い"))
  (for ([id (in-list (duplicates surface-thms))])
    (report! (format "surface.md §8 で ~a が重複している" id)))
  (for ([id (in-list (duplicates (map car thm-annotations)))])
    (define entries (filter (lambda (entry) (equal? (car entry) id)) thm-annotations))
    (define signatures
      (for/list ([entry (in-list entries)])
        (for/list ([field (in-list (drop-right note-fields 1))])
          (hash-ref (third entry) field #f))))
    (unless (andmap (lambda (signature) (equal? signature (car signatures)))
                    (cdr signatures))
      (report! (format "~a: 同じ THM の SCOPE 以外の欄が一致しない" id))))
  (for ([id (in-list (set-difference-list surface-thms declared-thms))])
    (report! (format "surface.md の ~a に命題注記が無い" id)))
  (for ([id (in-list (set-difference-list declared-thms surface-thms))])
    (report! (format "命題注記の ~a が surface.md §8 に無い" id)))
  (define known-thms (list->set declared-thms))
  (for ([entry (in-list aux-annotations)])
    (define name (first entry))
    (define fields (second entry))
    (when (equal? (hash-ref fields "AUX-KIND") "helper")
      (for ([id (in-list (comma-values (hash-ref fields "AUX-VALUE")))]
            #:unless (set-member? known-thms id))
        (report! (format "~a: AUX helper の THM ~a に命題注記が無い" name id)))))
  (sort (remove-duplicates errors) string<?))

(define (table-row? line)
  (string-prefix? (string-trim line) "|"))

(define (table-row-cells line)
  (define trimmed (string-trim line))
  (if (and (>= (string-length trimmed) 2)
           (char=? (string-ref trimmed 0) #\|)
           (char=? (string-ref trimmed (sub1 (string-length trimmed))) #\|))
      (map string-trim
           (string-split (substring trimmed 1 (sub1 (string-length trimmed))) "|"))
      '()))

(define (separator-row? cells)
  (and (pair? cells)
       (andmap (lambda (cell) (regexp-match? #px"^:?-+:?$" cell)) cells)))

(define (markdown-table path header)
  (define lines (file->lines path))
  (define start
    (for/first ([line (in-list lines)] [index (in-naturals)]
                #:when (equal? (table-row-cells line) header))
      index))
  (if (not start)
      (values '() (list (format "表の見出しが無い: ~a" (string-join header " | "))))
      (let* ([table-lines (takef (drop lines start) table-row?)]
             [separator (and (> (length table-lines) 1)
                             (table-row-cells (second table-lines)))]
             [rows (if (> (length table-lines) 2) (drop table-lines 2) '())]
             [cells (map table-row-cells rows)]
             [errors
              (append
               (if (and separator
                        (= (length separator) (length header))
                        (separator-row? separator))
                   '()
                   (list (format "表の区切り行が不正: ~a" (string-join header " | "))))
               (for/list ([row (in-list cells)] [index (in-naturals 1)]
                          #:unless (= (length row) (length header)))
                 (format "表の ~a 行目の列数が不正" index)))])
        (values (filter (lambda (row) (and (pair? row) (not (separator-row? row)))) cells)
                errors))))

(define (thm-declaration-map fst-path)
  (define mapping (make-hash))
  (for ([item (in-list (fst-declarations fst-path))])
    (define-values (note _errors) (parse-annotation item))
    (when (and note (eq? (parsed-note-kind note) 'thm))
      (define thm (hash-ref (parsed-note-fields note) "THM" #f))
      (when thm
        (hash-update! mapping thm (lambda (names) (cons (declaration-name item) names)) '()))))
  (for/hash ([(thm names) (in-hash mapping)])
    (values thm (sort names string<?))))

(define (list-field-map fst-path)
  (define full (make-hash))
  (define partial (make-hash))
  (define examples (make-hash))
  (for ([item (in-list (fst-declarations fst-path))])
    (define-values (note _errors) (parse-annotation item))
    (when note
      (cond
        [(eq? (parsed-note-kind note) 'thm)
         (define fields (parsed-note-fields note))
         (for ([id (in-list (comma-values (hash-ref fields "REQ-FULL" #f)))])
           (hash-update! full id
                         (lambda (thms) (cons (hash-ref fields "THM" "") thms))
                         '()))
         (for ([id (in-list (comma-values (hash-ref fields "REQ-PART" #f)))])
           (hash-update! partial id
                         (lambda (thms) (cons (hash-ref fields "THM" "") thms))
                         '()))]
        [(and (eq? (parsed-note-kind note) 'aux)
              (equal? (hash-ref (parsed-note-fields note) "AUX-KIND") "example"))
         (define id (hash-ref (parsed-note-fields note) "AUX-VALUE"))
         (unless (equal? id "-")
           (hash-update! examples id
                         (lambda (names) (cons (declaration-name item) names))
                         '()))])))
  (values full partial examples))

(define (expected-list-value values)
  (if (null? values) "-" (string-join (sorted-unique values) ", ")))

(define (test-references value)
  (if (equal? value "-")
      '()
      (for/list ([part (in-list (string-split value ", "))])
        (match (regexp-match #px"^`([^`]+)`::`([^`]+)`$" part)
          [(list _ path case-name) (cons path case-name)]
          [_ #f]))))

(define (inventory-errors inventory-path fst-path registry-path repo-root)
  (define errors '())
  (define (report! message) (set! errors (cons message errors)))
  (define known-reqs (map car (registry-definitions registry-path)))
  (define-values (proof-rows proof-table-errors)
    (markdown-table inventory-path '("THM" "宣言")))
  (define-values (requirement-rows requirement-table-errors)
    (markdown-table inventory-path '("要件 ID" "状態" "命題" "補助の証拠" "根拠の試験")))
  (for ([message (in-list (append proof-table-errors requirement-table-errors))])
    (report! message))
  (define proof-ids (for/list ([row (in-list proof-rows)] #:when (pair? row)) (car row)))
  (for ([id (in-list (duplicates proof-ids))])
    (report! (format "命題の表で ~a が重複している" id)))
  (define thm-map (thm-declaration-map fst-path))
  (for ([id (in-list (set-difference-list (hash-keys thm-map) proof-ids))])
    (report! (format "命題の表に ~a の宣言が無い: ~a"
                     id (string-join (hash-ref thm-map id) ", "))))
  (for ([id (in-list (set-difference-list proof-ids (hash-keys thm-map)))])
    (report! (format "命題の表に注記の無い ~a がある" id)))
  (for ([row (in-list proof-rows)] #:when (>= (length row) 2))
    (define id (first row))
    (define expected (hash-ref thm-map id '()))
    (define actual
      (if (equal? (second row) "-")
          '()
          (for/list ([part (in-list (string-split (second row) ", "))])
            (match (regexp-match #px"^`([^`]+)`$" part)
              [(list _ name) name]
              [_ part]))))
    (unless (equal? (sort actual string<?) expected)
      (report! (format "~a: 命題の表の宣言が注記と一致しない（注記: ~a）"
                       id (string-join expected ", ")))))
  (define row-ids (for/list ([row (in-list requirement-rows)] #:when (pair? row)) (car row)))
  (for ([id (in-list (duplicates row-ids))])
    (report! (format "一覧の要件 ID ~a が重複している" id)))
  (for ([id (in-list (set-difference-list known-reqs row-ids))])
    (report! (format "一覧に要件 ID ~a が無い" id)))
  (for ([id (in-list (set-difference-list row-ids known-reqs))])
    (report! (format "requirements.md に無い要件 ID ~a が一覧にある" id)))
  (define row-map (make-hash))
  (for ([row (in-list requirement-rows)] #:when (>= (length row) 5))
    (hash-set! row-map (first row) row))
  (define-values (full partial examples) (list-field-map fst-path))
  (for ([id (in-list known-reqs)])
    (define row (hash-ref row-map id #f))
    (when row
      (define state (second row))
      (define propositions (third row))
      (define supporting (fourth row))
      (define evidence (fifth row))
      (define full-thms (sorted-unique (hash-ref full id '())))
      (define partial-thms (sorted-unique (hash-ref partial id '())))
      (define example-names (sort (hash-ref examples id '()) string<?))
      (define expected-propositions (expected-list-value full-thms))
      (define expected-support
        (let ([parts (append partial-thms
                             (map (lambda (name) (format "`~a`" name)) example-names))])
          (if (null? parts) "-" (string-join parts ", "))))
      (unless (equal? propositions expected-propositions)
        (report! (format "~a: 一覧の命題欄が注記と一致しない" id)))
      (unless (equal? supporting expected-support)
        (report! (format "~a: 一覧の補助の証拠欄が注記と一致しない" id)))
      (unless (member state '("証明済み" "テストのみ" "未検証"))
        (report! (format "~a: 一覧の状態 ~a は不正" id state)))
      (when (and (member id (hash-keys full)) (not (equal? state "証明済み")))
        (report! (format "~a: REQ-FULL があるため状態は証明済みでなければならない" id)))
      (when (and (equal? state "証明済み") (null? full-thms))
        (report! (format "~a: 証明済みの状態に対応する REQ-FULL が無い" id)))
      (define references (test-references evidence))
      (when (and (not (equal? evidence "-"))
                 (ormap not references))
        (report! (format "~a: 根拠の試験は `path`::`test-case` の形で書く" id)))
      (cond
        [(equal? state "テストのみ")
         (when (null? references)
           (report! (format "~a: テストのみには根拠の試験が必要" id)))
         (for ([reference (in-list (filter values references))])
           (define path (build-path repo-root (car reference)))
           (define case-name (cdr reference))
           (cond
             [(not (file-exists? path))
              (report! (format "~a: 根拠の試験 path ~a が無い" id (car reference)))]
             [else
              (define source (file->string path))
              (unless (member id (test-req-ids source))
                (report! (format "~a: 根拠の試験 ~a が要件 ID を参照しない"
                                 id (car reference))))
              (unless (named-test-definition? source case-name)
                (report! (format "~a: 根拠の試験 ~a に名前付き試験 ~a が無い"
                                 id (car reference) case-name)))]))]
        [else
         (unless (equal? evidence "-")
           (report! (format "~a: テストのみ以外の状態は根拠の試験を持たない" id)))])))
  (sort (remove-duplicates errors) string<?))

(define (run-proof-inventory #:fst fst-path
                             #:surface surface-path
                             #:registry registry-path
                             #:inventory inventory-path
                             #:spec-dir spec-dir
                             #:root repo-root
                             #:output output
                             #:error-output error-output)
  (define errors
    (append (annotation-errors fst-path surface-path registry-path spec-dir repo-root)
            (inventory-errors inventory-path fst-path registry-path repo-root)))
  (if (pair? errors)
      (begin
        (for ([message (in-list errors)]) (fprintf error-output "~a\n" message))
        1)
      (begin
        (fprintf output "Proof inventory OK: ~a 件の要件、~a 個の補題\n"
                 (length (registry-definitions registry-path))
                 (count lemma-declaration? (fst-declarations fst-path)))
        0)))

(define (main)
  (exit
   (run-proof-inventory
    #:fst (build-path project-root "model/fstar/Topazolite.Surface.fst")
    #:surface (build-path project-root "docs/specification/surface.md")
    #:registry (build-path project-root "docs/specification/requirements.md")
    #:inventory (build-path project-root "docs/specification/proof-inventory.md")
    #:spec-dir (build-path project-root "docs/specification")
    #:root project-root
    #:output (current-output-port)
    #:error-output (current-error-port))))

(module+ main (main))

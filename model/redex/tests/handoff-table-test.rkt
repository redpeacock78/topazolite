#lang racket

(require racket/file
         racket/runtime-path
         racket/string
         rackunit)

(define-runtime-path repo-root "../../..")

(define (spec-file name)
  (build-path repo-root "docs/specification" name))

;; requirements.md の §4 の本文だけを取り出す。
(define (handoff-section-lines)
  (define lines (file->lines (spec-file "requirements.md")))
  (let loop ([rest lines] [inside? #f] [acc '()])
    (cond
      [(null? rest) (reverse acc)]
      [(regexp-match? #rx"^## 4\\. " (car rest)) (loop (cdr rest) #t acc)]
      [(and inside? (regexp-match? #rx"^## " (car rest))) (reverse acc)]
      [inside? (loop (cdr rest) #t (cons (car rest) acc))]
      [else (loop (cdr rest) #f acc)])))

;; "| a | b |" を ("a" "b") にする。区切りの空文字列を落とさないため
;; #:trim? #f で分けてから、先頭と末尾の "" を捨てる。
(define (row-cells line)
  (define parts (string-split line "|" #:trim? #f))
  (if (< (length parts) 3)
      '()
      (map string-trim (drop-right (cdr parts) 1))))

(define (table-rows)
  (for/list ([line (in-list (handoff-section-lines))]
             #:when (regexp-match? #rx"^\\|" line)
             #:unless (regexp-match? #rx"^\\|[-: |]+\\|$" line)
             #:unless (regexp-match? #rx"^\\| *項目 *\\|" line))
    (row-cells line)))

;; 記載元セルから ("trait.md" . "9") の並びを取り出す。
(define (citations cell)
  (for/list ([m (in-list (regexp-match* #px"`([^`]+\\.md)` *§([0-9]+)"
                                        cell
                                        #:match-select values))])
    (cons (cadr m) (caddr m))))

(define (all-citations)
  (append* (for/list ([row (in-list (table-rows))]) (citations (cadr row)))))

(define (heading-exists? name number)
  (define rx (pregexp (format "^#+ ~a\\. " number)))
  (for/or ([line (in-list (file->lines (spec-file name)))])
    (regexp-match? rx line)))

(test-case
 "the handoff table is not vacuous"
 (check-true (>= (length (table-rows)) 30))
 (check-true (>= (length (all-citations)) 30)))

(test-case
 "every handoff row has four columns"
 (for ([row (in-list (table-rows))])
   (check-equal? (length row) 4 (format "row: ~a" row))))

(test-case
 "every cited source file exists"
 (for ([cite (in-list (all-citations))])
   (check-true (file-exists? (spec-file (car cite)))
               (format "missing file: ~a" (car cite)))))

(test-case
 "every cited section heading exists"
 (for ([cite (in-list (all-citations))])
   (check-true (heading-exists? (car cite) (cdr cite))
               (format "missing heading: ~a §~a" (car cite) (cdr cite)))))

(test-case
 "all six source documents appear in the table"
 (define names (list->set (map car (all-citations))))
 (check-equal? names
               (set "trait.md" "structural-row.md"
                    "proof-value.md" "proof-search.md"
                    "backend-matrix.md" "diagnostic.md")))

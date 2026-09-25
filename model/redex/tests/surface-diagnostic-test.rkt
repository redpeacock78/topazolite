#lang racket

(require rackunit
         "../lexer.rkt"
         "../parser.rkt"
         "../diagnostic.rkt"
         "../diagnostic-render.rkt"
         "../source-map.rkt"
         "../surface-lower.rkt"
         "../traits.rkt")

(define surface-keys
  '(surface-invalid-byte
    surface-unknown-character
    surface-unterminated-string
    surface-invalid-escape
    surface-unexpected-token
    surface-unexpected-eof
    surface-duplicate-field
    surface-unknown-type-name
    surface-duplicate-type-alias
    surface-recursive-type-alias
    surface-reserved-type-name
    surface-projection-labels
    surface-duplicate-trait-decl
    surface-duplicate-impl-decl
    surface-unknown-trait-name
    surface-trait-name-collision
    surface-impl-requirement-mismatch
    surface-impl-composite-trait
    surface-derive-no-recipe))

;; v15 の 11 件に v17 の 1 件、v19 の 6 件、v20 の 1 件を足した。
;; since は版ごとに異なる。
(define surface-since
  (hasheq 'surface-projection-labels 17
          'surface-duplicate-trait-decl 19
          'surface-duplicate-impl-decl 19
          'surface-unknown-trait-name 19
          'surface-trait-name-collision 19
          'surface-impl-requirement-mismatch 19
          'surface-impl-composite-trait 19
          'surface-derive-no-recipe 20))

(test-case
 "19 件の key はすべて registry にあり、相は surface である"
 (for ([k (in-list surface-keys)])
   (define code (diagnostic-code-of 'surface k))
   (check-true (string? code) (format "~a が registry にある" k))
   (check-equal? (diagnostic-code-phase (diagnostic-code-row code)) 'surface)
   (check-equal? (diagnostic-code-since (diagnostic-code-row code))
                 (hash-ref surface-since k 15))))

(test-case
 "registry の surface 相はこの 19 件だけである"
 (define rows
   (for/list ([row (in-list diagnostic-registry)]
              #:when (eq? (diagnostic-code-phase row) 'surface))
     (diagnostic-code-key row)))
 (check-equal? (sort (map symbol->string rows) string<?)
               (sort (map symbol->string surface-keys) string<?)))

;; producer の一覧は網羅ではなく、実際に呼び出せる producer の代表例である。
;; derive の no-recipe 診断も lower-surface の producer である。
;; 3 つ目の欄は入力の byte 長である。primary span の上端をこれと比べる。
(define no-recipe-source "derive Printable for Bool\n0")
(define producers
  (list (list 'surface-invalid-byte        (lambda () (lex 'src (bytes 255)))            1)
        (list 'surface-unknown-character   (lambda () (lex 'src #"+"))                   1)
        (list 'surface-unterminated-string (lambda () (lex 'src #"\"a"))                 2)
        (list 'surface-invalid-escape      (lambda () (lex 'src #"\"a\\q\""))            5)
        (list 'surface-unexpected-token    (lambda () (parse (lex/string 'src "if x { 1 }"))) 10)
        (list 'surface-unexpected-eof      (lambda () (parse (lex/string 'src "")))      0)
        (list 'surface-projection-labels   (lambda () (parse (lex/string 'src "r.{}")))  4)
        (list 'surface-derive-no-recipe
              (lambda ()
                (lower-surface (parse (lex/string 'src no-recipe-source))
                               canonical-trait-env))
              (string-length no-recipe-source))))

(test-case
 "8 件の producer が registry と同じ code を返す"
 (for ([pr (in-list producers)])
   (define d ((second pr)))
   (check-true (diagnostic? d) (format "~a が Diagnostic を返す" (first pr)))
   (check-equal? (diagnostic-id d) (diagnostic-code-of 'surface (first pr)))))

(test-case
 "8 件の分類は SUR である"
 (for ([pr (in-list producers)])
   (check-equal? (diagnostic-category ((second pr))) 'SUR)))

(test-case
 "primary span は入力の byte 長の内側にある"
 (for ([pr (in-list producers)])
   (define s (diagnostic-primary-span ((second pr))))
   (define n (third pr))
   (check-true (and (exact-nonnegative-integer? (third s))
                    (exact-nonnegative-integer? (fourth s))
                    (<= 0 (third s))
                    (<= (third s) (fourth s))
                    (<= (fourth s) n))
               (format "~a の primary span が [0, ~a] の内側にある" (first pr) n))))

(test-case
 "多 field 射影の診断の primary span は波括弧の範囲である"
 (check-equal? (diagnostic-primary-span
                (parse (lex/string 'src "r.{}")))
               '(#:span src 2 4))
 (check-equal? (diagnostic-primary-span
                (parse (lex/string 'src "r.{a, a}")))
               '(#:span src 2 8)))

;; spec §12 の「3 つの renderer が全 19 件を描ける」である。producer の無い 11 件も
;; 対象にするため、registry の code から直に Diagnostic を組み立てる。
(define sm (make-source-map (hasheq 'src "let x = 1\n")))

(define (sample-diagnostic k)
  (define row (diagnostic-code-row (diagnostic-code-of 'surface k)))
  (make-diagnostic #:id (diagnostic-code-code row)
                   #:title (diagnostic-code-title row)
                   #:message (diagnostic-code-title row)
                   #:primary-span '(#:span src 4 5)
                   ;; source-chain の frame は (phase kind span) の 3 要素であり、
                   ;; 先頭の phase は surface でなければならない（diagnostic.rkt の
                   ;; source-chain-ok?）。
                   #:source-chain '((surface verbatim (#:span src 4 5)))))

(test-case
 "3 つの renderer が 19 件すべてを描ける"
 (for ([k (in-list surface-keys)])
   (define d (sample-diagnostic k))
   (check-true (diagnostic-valid? d) (format "~a の Diagnostic が schema に合う" k))
   (define t (render-terminal d sm))
   (check-true (string-contains? t (diagnostic-id d)) (format "~a の terminal" k))
   (check-true (hash? (render-lsp d sm)) (format "~a の lsp" k))
   (check-equal? (hash-ref (render-json d) 'id) (diagnostic-id d)
                 (format "~a の json" k))))

#lang racket/base

(require rackunit
         racket/list
         "../traits.rkt"
         "../type-equiv.rkt"
         "../rows.rkt")

(test-case "trait names are unique"
  (define names (map trait-name trait-table))
  (check-equal? (length names) (length (remove-duplicates names))))

(test-case "origin ids are unique across all trait tables"
  (define origins
    (append (map trait-origin trait-table)
            (map impl-oid impl-table)
            (map intersect-oid intersect-table)))
  (check-equal? (length origins) (length (remove-duplicates origins))))

(test-case "impl oids and names are unique"
  (check-equal? (length (map impl-oid impl-table))
                (length (remove-duplicates (map impl-oid impl-table))))
  (check-equal? (length (map impl-name impl-table))
                (length (remove-duplicates (map impl-name impl-table)))))

(test-case "every impl row names a declared trait"
  (for ([row (in-list impl-table)])
    (check-not-false
     (trait-row-by-name (impl-trait-name row))
     (format "unknown trait in impl row: ~s" (impl-name row)))))

(test-case "impl kinds are impl or derive, and both appear"
  (for ([row (in-list impl-table)])
    (check-true (and (memq (impl-kind row) '(impl derive)) #t)
                (format "~s" (impl-name row))))
  (check-true
   (> (length (filter (lambda (row) (eq? (impl-kind row) 'impl)) impl-table)) 0))
  (check-true
   (> (length (filter (lambda (row) (eq? (impl-kind row) 'derive)) impl-table)) 0)))

(test-case "requirement labels are unique within each template"
  (for ([row (in-list trait-table)])
    (check-true
     (field-row-unique? (trait-template row))
     (format "duplicate label in template of ~s" (trait-name row)))))

(test-case "instantiate-requirements replaces Self and yields normalizable types"
  (define row
    (instantiate-requirements
     (trait-template (trait-row-by-name 'Printable))
     'Int))
  (check-equal? row '((print (NFn (Int) String () ()) imm)))
  (for ([field (in-list row)])
    (define type (second field))
    (check-equal? (normalize-type type) type)))

(test-case "instantiate-requirements leaves no Self behind"
  (for ([trait-row (in-list trait-table)])
    (define row (instantiate-requirements (trait-template trait-row) 'Int))
    (check-false
     (memq 'Self (flatten row))
     (format "Self remained in ~s" (trait-name trait-row)))))

(test-case "intersect rows compose to their declared output"
  (for ([row (in-list intersect-table)])
    (define left (trait-row-by-name (intersect-left row)))
    (define right (trait-row-by-name (intersect-right row)))
    (define output (trait-row-by-name (intersect-output row)))
    (check-not-false left)
    (check-not-false right)
    (check-not-false output)
    (check-true (symbol<? (intersect-left row) (intersect-right row)))
    (define composed
      (field-row-⊕ (trait-template left) (trait-template right)))
    (check-not-false composed
                     (format "templates collide: ~s" (intersect-name row)))
    (check-true
     (field-row-equiv? composed (trait-template output) type-equiv?)
     (format "composed template does not match ~s" (intersect-output row)))))

(test-case "trait primitive names cover every impl and intersect row"
  (define names (trait-primitive-names))
  (for ([row (in-list impl-table)])
    (check-true (trait-primitive-name? (impl-name row)))
    (check-true (and (memq (impl-name row) names) #t)
                (format "~s" (impl-name row))))
  (for ([row (in-list intersect-table)])
    (check-true (trait-primitive-name? (intersect-name row)))
    (check-true (and (memq (intersect-name row) names) #t)
                (format "~s" (intersect-name row)))))

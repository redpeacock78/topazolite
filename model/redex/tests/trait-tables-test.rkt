#lang racket/base

(require rackunit
         racket/list
         "../traits.rkt"
         "../type-equiv.rkt"
         "../rows.rkt"
         "../type-shape.rkt"
         "../origins.rkt"
         "../search.rkt")

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

(test-case "duplicate labels in an impl target type are rejected"
  (define bad-impl
    '(o-bad impl-bad impl Printable
            (Record ((a Int imm) (a Bool imm)))
            root))
  (define trait-row (trait-row-by-name (impl-trait-name bad-impl)))
  (define requirements
    (instantiate-requirements
     (trait-template trait-row)
     (impl-target-type bad-impl)))
  (for ([field (in-list requirements)])
    (define type (second field))
    (check-false
     (and (equal? (normalize-type type) type)
          (type-shape-ok? type)))))

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

(test-case "TRT-006: 合成 trait は別の合成の成分になれる"
  ;; 左成分の PrintableSizable Int は、それ自体が合成候補である。
  ;; 右成分の Taggable Int は s-user から立つ。入れ子の合成が (root s-user)
  ;; で一意に解ける。
  (define goal (make-goal '(Implements Int PrintableSizableTaggable)))
  (define sigma (project-goal Γ-pc0 '(root s-user) goal))
  (check-equal? (length sigma) 1)
  (check-true (resolved? (resolve-candidates goal sigma)))
  ;; obligations-dischargeable? は typing と elaborate の共有経路であり、
  ;; sc-ctx を引数に取らず discharge? の既定値 '(root) を使う。Taggable Int は
  ;; trait 行が s-kernel、impl 行の対象型 scope が s-user であるため (root)
  ;; からは可視でなく、入れ子の合成もそこでは立たない。入れ子が成り立つ証拠は
  ;; 上の project-goal と resolve-candidates の対であり、この check-false は
  ;; 経路の違いを固定しているだけである。
  (check-false
   (obligations-dischargeable? '((Implements Int PrintableSizableTaggable))
                               Γ-pc0
                               default-classifier
                               default-oracle)))

(test-case "TRT-006: 入れ子の合成 origin は成分の連なりを保つ"
  ;; 三項の要求を二項の入れ子で表す。外側の origin から内側の合成 origin を
  ;; たどれることが、成分の provenance が消えていないことの証拠である。
  (define nested
    `(Derived (Reserved o-intersect-print-size-tag)
              (Compose PrintableSizableTaggable
                       (Derived (Reserved o-intersect-print-size)
                                (Compose PrintableSizable
                                         (Reserved o-impl-printable-int)
                                         (Reserved o-derive-sizable-int)))
                       (Reserved o-impl-taggable-int))))
  (check-true
   (proof-issuer-ok? R0 nested '(Implements Int PrintableSizableTaggable))))

(test-case "TRT-006: 入れ子を足しても intersect-table は非巡回である"
  (check-true (intersect-acyclic?)))

(test-case "TRT-007: 正典表のどの impl 行も合成 trait を対象にしていない"
  (check-true (impl-not-composite?))
  (check-true (impl-not-composite? impl-table intersect-table)))

(test-case "TRT-007: 合成 trait を対象にする impl 行は拒否される"
  (define composite (intersect-output (first intersect-table)))
  (define bad-impl
    (list 'o-bad-composite 'impl-bad-composite 'impl composite
          '(Record ((x Int imm)))
          'root))
  (check-false (impl-not-composite? (cons bad-impl impl-table) intersect-table))
  ;; 成分 trait への impl は禁止対象ではない。
  (define good-impl
    (list 'o-ok-component 'impl-ok-component 'impl
          (intersect-left (first intersect-table))
          '(Record ((x Int imm)))
          'root))
  (check-true (impl-not-composite? (cons good-impl impl-table) intersect-table)))

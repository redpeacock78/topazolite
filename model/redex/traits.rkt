#lang racket/base

(require racket/list
         racket/match
         "rows.rkt"
         "type-equiv.rkt"
         "type-shape.rkt")

(provide trait-table
         impl-table
         intersect-table
         trait-origin
         trait-name
         trait-scope
         trait-template
         impl-oid
         impl-name
         impl-kind
         impl-trait-name
         impl-target-type
         impl-target-scope
         intersect-oid
         intersect-name
         intersect-left
         intersect-right
         intersect-output
         trait-row-by-name
         trait-row-by-oid
         impl-row-by-oid
         impl-row-by-name
         impl-rows-by-trait
         intersect-row-by-oid
         intersect-row-by-name
         intersect-acyclic?
         scope-parent-table
         scope-ancestors
         scope-genealogy-ok?
         instantiate-requirements
         trait-primitive-name?
         trait-primitive-names)

;; trait 層の正典表。
;; ここに書かれた行だけが trait の意味論を定める。
;; 型と δ 規則と Proof 候補は、すべてこの 3 表から機械的に導出する。

;; trait-table の行: (tid tn sid_trait template)
;; template の Self はメタレベルの placeholder であり、型文法には属さない。
(define trait-table
  (list (list 'o-trait-printable 'Printable 'root
              (list (list 'print '(NFn (Self) String () ()) 'imm)))
        (list 'o-trait-sizable 'Sizable 'root
              (list (list 'size '(NFn (Self) Int () ()) 'imm)))
        (list 'o-trait-printable-sizable 'PrintableSizable 'root
              (list (list 'print '(NFn (Self) String () ()) 'imm)
                    (list 'size '(NFn (Self) Int () ()) 'imm)))
        (list 'o-trait-taggable 'Taggable 's-kernel
              (list (list 'tag '(NFn (Self) String () ()) 'imm)))
        (list 'o-trait-printable-taggable 'PrintableTaggable 'root
              (list (list 'print '(NFn (Self) String () ()) 'imm)
                    (list 'tag   '(NFn (Self) String () ()) 'imm)))))

;; impl-table の行: (oid nm kind tn τ sid_target)
;; 各行は、対応する実装 record が検査済みである信頼された宣言である。
(define impl-table
  (list (list 'o-impl-printable-int   'impl-printable-int   'impl   'Printable 'Int    'root)
        (list 'o-derive-sizable-int   'derive-sizable-int   'derive 'Sizable   'Int    'root)
        (list 'o-impl-printable-str-a 'impl-printable-str-a 'impl   'Printable 'String 'root)
        (list 'o-impl-printable-str-b 'impl-printable-str-b 'impl   'Printable 'String 'root)
        (list 'o-impl-taggable-bool   'impl-taggable-bool   'impl   'Taggable  'Bool   's-user)
        ;; derive-sizable-str は String の成分数を (Printable 2 件, Sizable 1 件) にし、
        ;; 合成候補の Ambiguous を観測できるようにする（設計 §5.5）。
        (list 'o-derive-sizable-str    'derive-sizable-str    'derive 'Sizable   'String 'root)
        ;; impl-taggable-int は対象型の scope が s-user であり、Taggable の trait 行は
        ;; s-kernel にある。(root) からは見えず (root s-user) からは見えるため、
        ;; 可視性が合成候補まで及ぶことを片側だけ動かして観測できる。
        (list 'o-impl-taggable-int     'impl-taggable-int     'impl   'Taggable  'Int    's-user)))

;; intersect-table の行: (oid nm tn_a tn_b tn_out)
(define intersect-table
  (list (list 'o-intersect-print-size 'intersect-printable-sizable
              'Printable 'Sizable 'PrintableSizable)
        (list 'o-intersect-print-tag 'intersect-printable-taggable
              'Printable 'Taggable 'PrintableTaggable)))

;; COH-001: scope の系譜。package と module の入れ子を親子で表す。
;; 可視性（search.rkt の scope-visible?）はこの表の祖先到達で決まる。
;; 各行は (sid parent) であり、親を持たない scope は #f を置く。
(define scope-parent-table
  '((root #f)
    (s-kernel root)
    (s-user root)))

(define (trait-origin row) (first row))
(define (trait-name row) (second row))
(define (trait-scope row) (third row))
(define (trait-template row) (fourth row))

(define (impl-oid row) (first row))
(define (impl-name row) (second row))
(define (impl-kind row) (third row))
(define (impl-trait-name row) (fourth row))
(define (impl-target-type row) (fifth row))
(define (impl-target-scope row) (sixth row))

(define (intersect-oid row) (first row))
(define (intersect-name row) (second row))
(define (intersect-left row) (third row))
(define (intersect-right row) (fourth row))
(define (intersect-output row) (fifth row))

(define (trait-row-by-name trait)
  (findf (lambda (row) (eq? (trait-name row) trait)) trait-table))
(define (trait-row-by-oid origin)
  (findf (lambda (row) (eq? (trait-origin row) origin)) trait-table))
(define (impl-row-by-oid origin)
  (findf (lambda (row) (eq? (impl-oid row) origin)) impl-table))
(define (impl-row-by-name name)
  (findf (lambda (row) (eq? (impl-name row) name)) impl-table))
(define (impl-rows-by-trait trait)
  (filter (lambda (row) (eq? (impl-trait-name row) trait)) impl-table))
(define (intersect-row-by-oid origin)
  (findf (lambda (row) (eq? (intersect-oid row) origin)) intersect-table))
(define (intersect-row-by-name name)
  (findf (lambda (row) (eq? (intersect-name row) name)) intersect-table))

;; COH-001: 自身を含む祖先の列。表に無い scope 識別子は親を持たないものと
;; して扱い、自身だけの列を返す。sid と sc-ctx は呼び出し側が組み立てる
;; 引数であり、表に無い識別子が渡り得る。
(define (scope-parent-row row) (first row))
(define (scope-parent-of row) (second row))

(define (scope-ancestors sid [rows scope-parent-table])
  (let loop ([sid sid] [seen '()])
    (cond
      [(memq sid seen) (reverse seen)]
      [else
       (define row
         (findf (lambda (r) (eq? (scope-parent-row r) sid)) rows))
       (define parent (and row (scope-parent-of row)))
       (if parent
           (loop parent (cons sid seen))
           (reverse (cons sid seen)))])))

;; COH-001: 系譜表の内部整合と、trait 行・impl 行の scope が表に載っている
;; ことを見る。表を引数に取るのは拒否の経路をテストから実行するためであり、
;; intersect-acyclic? と同じ形である。
(define (scope-genealogy-ok? [scope-rows scope-parent-table]
                             [trait-rows trait-table]
                             [impl-rows impl-table])
  (define shape-ok?
    (and (list? scope-rows)
         (for/and ([row (in-list scope-rows)])
           (and (list? row)
                (= (length row) 2)
                (symbol? (first row))
                (let ([parent (second row)])
                  (or (not parent) (symbol? parent)))))))
  (if (not shape-ok?)
      #f
      (let* ([sids (map scope-parent-row scope-rows)]
             [declared? (lambda (sid) (and (memq sid sids) #t))]
             [roots
              (filter (lambda (row) (not (scope-parent-of row)))
                      scope-rows)])
        (define (acyclic? row)
          (let descend ([sid (scope-parent-row row)] [path '()])
            (cond
              [(memq sid path) #f]
              [else
               (define next
                 (findf (lambda (r)
                          (eq? (scope-parent-row r) sid))
                        scope-rows))
               (define parent
                 (and next (scope-parent-of next)))
               (if parent
                   (descend parent (cons sid path))
                   #t)])))
        (and
         (for/and ([row (in-list scope-rows)])
           (define parent (scope-parent-of row))
           (or (not parent) (declared? parent)))
         (= (length sids) (length (remove-duplicates sids)))
         (= (length roots) 1)
         (for/and ([row (in-list scope-rows)]) (acyclic? row))
         (for/and ([row (in-list trait-rows)])
           (declared? (trait-scope row)))
         (for/and ([row (in-list impl-rows)])
           (declared? (impl-target-scope row)))))))

;; template 中の Self を型で置き換え、具体的な requirement 行を得る。
(define (instantiate-requirements template type)
  (define (substitute value)
    (cond
      [(eq? value 'Self) type]
      [(pair? value) (map substitute value)]
      [else value]))
  (for/list ([field (in-list template)])
    (list (first field) (substitute (second field)) (third field))))

;; trait 由来の kernel primitive 名は、impl 行と intersect 行から導く。
(define trait-primitive-names-list
  (append (map impl-name impl-table)
          (map intersect-name intersect-table)))

(define (trait-primitive-names) trait-primitive-names-list)
(define (trait-primitive-name? name)
  (and (memq name trait-primitive-names-list) #t))

;; Self を許す template 専用の型検査。Self は型位置だけに現れ、
;; instantiate 後は通常の型正規化へ渡せることを load 時に保証する。
(define (template-type? type)
  (match type
    ['Self #t]
    [(? symbol?) (and (memq type '(Int Bool Unit String Never Res)) #t)]
    [`(List ,element) (template-type? element)]
    [`(Option ,element) (template-type? element)]
    [`(Result ,ok-type ,error-type)
     (and (template-type? ok-type) (template-type? error-type))]
    [`(Owned ,inner) (template-type? inner)]
    [`(Record ,row) (template-row? row)]
    [`(Untrusted ,inner) (template-type? inner)]
    [`(Refined ,inner ,proposition)
     (and (template-type? inner) (template-proposition? proposition))]
    [`(Union ,left ,right)
     (and (template-type? left) (template-type? right))]
    [`(Intersection ,left ,right)
     (and (template-type? left) (template-type? right))]
    [`(NFn ,parameters ,return-type ,effects ,obligations)
     (and (andmap template-type? parameters)
          (template-type? return-type)
          (andmap template-effect? effects)
          (andmap template-proposition? obligations))]
    [`(TypeInfo ,kind) (template-kind? kind)]
    [`(Proof ,proposition) (template-proposition? proposition)]
    [_ #f]))

(define (metadata-symbol? value)
  (and (symbol? value) (not (eq? value 'Self))))

(define (template-kind? kind)
  (match kind
    ['Type #t]
    [`(,domain -> ,range)
     (and (template-kind? domain) (template-kind? range))]
    [_ #f]))

(define (template-effect? effect)
  (match effect
    [(or 'Suspend 'Partial 'Compile 'Own) #t]
    [`(Return ,boundary ,type)
     (and (metadata-symbol? boundary) (template-type? type))]
    [`(Yield ,type) (template-type? type)]
    [_ #f]))

(define (template-proposition? proposition)
  (match proposition
    [(or 'ValidNarrativeTrait 'TypeNarrativeCap) #t]
    [`(Prop ,name) (metadata-symbol? name)]
    [`(Presence ,label) (metadata-symbol? label)]
    [`(ValidNarrativeTrait ,trait) (metadata-symbol? trait)]
    [`(Implements ,type ,trait)
     (and (template-type? type) (metadata-symbol? trait))]
    [`(RequiresBoth ,left ,right)
     (and (metadata-symbol? left) (metadata-symbol? right))]
    [`(FieldType ,label ,type)
     (and (metadata-symbol? label) (template-type? type))]
    [_ #f]))

(define (template-row? row)
  (and (list? row)
       (field-row-unique? row)
       (for/and ([field (in-list row)])
         (match field
           [(list label type mutability)
            (and (metadata-symbol? label)
                 (memq mutability '(imm mut))
                 (template-type? type))]
           [_ #f]))))

;; TRT-004: 出力 trait から成分 trait へ向かう辺が非巡回であること。
;; 合成候補の生成（search.rkt）と合成 origin の発行者判定（origins.rkt）は、
;; どちらもこの辺を降りる再帰であり、巡回があると停止しない。
;; 祖先の連なりだけを path に積むため、同じ trait が別の枝に現れる表
;; （成分の共有）は巡回と見なさない。
(define (intersect-acyclic? [rows intersect-table])
  (define (rows-for trait)
    (filter (lambda (row) (eq? (intersect-output row) trait)) rows))
  (define (descend trait path)
    (cond
      [(memq trait path) #f]
      [else
       (define next (cons trait path))
       (for/and ([row (in-list (rows-for trait))])
         (and (descend (intersect-left row) next)
              (descend (intersect-right row) next)))]))
  (for/and ([row (in-list rows)])
    (descend (intersect-output row) '())))

;; 3 表の内部整合を load 時に検査する。
;; R0 と Γ0 との衝突は origins.rkt が append 後に検査する。
(define (check-tables!)
  (define (duplicate? values)
    (not (= (length values) (length (remove-duplicates values)))))

  (when (duplicate? (map trait-name trait-table))
    (error 'traits "duplicate trait name"))

  (define origins
    (append (map trait-origin trait-table)
            (map impl-oid impl-table)
            (map intersect-oid intersect-table)))
  (when (duplicate? origins)
    (error 'traits "duplicate origin id in the trait tables"))
  (when (duplicate? trait-primitive-names-list)
    (error 'traits "impl and intersect names collide"))

  (for ([row (in-list trait-table)])
    (unless (template-row? (trait-template row))
      (error 'traits "invalid requirement template in trait ~s"
             (trait-name row))))

  (for ([row (in-list impl-table)])
    (define trait-row (trait-row-by-name (impl-trait-name row)))
    (unless trait-row
      (error 'traits "impl ~s names an undeclared trait" (impl-name row)))
    (unless (memq (impl-kind row) '(impl derive))
      (error 'traits "impl ~s has an unknown kind" (impl-name row)))
    (define requirements
      (instantiate-requirements
       (trait-template trait-row)
       (impl-target-type row)))
    (unless (field-row-unique? requirements)
      (error 'traits "requirements of ~s have duplicate labels" (impl-name row)))
    (for ([field (in-list requirements)])
      (define type (second field))
      (unless (and (equal? (normalize-type type) type)
                   (type-shape-ok? type))
        (error 'traits
               "requirement of ~s is not a well-formed normal type"
               (impl-name row)))))

  (for ([row (in-list intersect-table)])
    (define left (trait-row-by-name (intersect-left row)))
    (define right (trait-row-by-name (intersect-right row)))
    (define output (trait-row-by-name (intersect-output row)))
    (unless (and left right output)
      (error 'traits "intersect ~s names an undeclared trait"
             (intersect-name row)))
    (unless (symbol<? (intersect-left row) (intersect-right row))
      (error 'traits "intersect ~s is not in canonical trait order"
             (intersect-name row)))
    (define composed
      (field-row-⊕ (trait-template left) (trait-template right)))
    (unless composed
      (error 'traits "intersect ~s composes colliding templates"
             (intersect-name row)))
    (unless (field-row-equiv? composed (trait-template output) type-equiv?)
      (error 'traits "intersect ~s does not match its output trait"
             (intersect-name row))))

  (unless (intersect-acyclic?)
    (error 'traits "intersect rows form a cycle in the trait name graph"))

  (unless (scope-genealogy-ok?)
    (error 'traits "scope parent table is malformed")))

(check-tables!)

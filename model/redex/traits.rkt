#lang racket/base

(require racket/list
         racket/match
         racket/set
         "erase.rkt"
         "policy.rkt"
         "rows.rkt"
         "type-equiv.rkt"
         "type-shape.rkt")

(provide trait-table
         impl-table
         intersect-table
         trait-origin
         trait-derived-origin
         trait-constant-name
         trait-resolution-origin
         impl-derived-origin
         intersect-derived-origin
         trait-row-shape-ok?
         trait-origin-ok?
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
         (struct-out trait-env)
         make-trait-env
         canonical-trait-env
         trait-row-by-name
         trait-row-by-oid
         impl-row-by-oid
         impl-row-by-name
         impl-rows-by-trait
         intersect-row-by-oid
         intersect-row-by-name
         intersect-acyclic?
         impl-not-composite?
         template-effect?
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
              (list (list 'print '(NFn (Self) String () () () User) 'imm)))
        (list 'o-trait-sizable 'Sizable 'root
              (list (list 'size '(NFn (Self) Int () () () User) 'imm)))
        (list 'o-trait-printable-sizable 'PrintableSizable 'root
              (list (list 'print '(NFn (Self) String () () () User) 'imm)
                    (list 'size '(NFn (Self) Int () () () User) 'imm)))
        (list 'o-trait-taggable 'Taggable 's-kernel
              (list (list 'tag '(NFn (Self) String () () () User) 'imm)))
        (list 'o-trait-printable-taggable 'PrintableTaggable 'root
              (list (list 'print '(NFn (Self) String () () () User) 'imm)
                    (list 'tag   '(NFn (Self) String () () () User) 'imm)))
        ;; COH-001: 生成 scope が s-kernel の合成 trait。成分はどちらも
        ;; (root s-user) から可視であり、出力 scope の可視性だけが落ちる。
        (list 'o-trait-sizable-taggable 'SizableTaggable 's-kernel
              (list (list 'size '(NFn (Self) Int () () () User) 'imm)
                    (list 'tag  '(NFn (Self) String () () () User) 'imm)))
        ;; TRT-006: 合成 trait を成分に取る合成の出力。三項の要求は二項の
        ;; 入れ子で表し、表そのものは二項の関係を保つ。
        (list 'o-trait-printable-sizable-taggable 'PrintableSizableTaggable 'root
              (list (list 'print '(NFn (Self) String () () () User) 'imm)
                    (list 'size  '(NFn (Self) Int () () () User) 'imm)
                    (list 'tag   '(NFn (Self) String () () () User) 'imm)))))

;; impl-table の行: (oid nm kind tn τ sid_target)
;; 各行は、対応する実装 record が検査済みである信頼された宣言である。
(define impl-table
  (list (list 'o-impl-printable-int   'impl-printable-int   'impl   'Printable 'Int    'root)
        (list 'o-derive-sizable-int   'derive-sizable-int   'derive 'Sizable   'Int    'root)
        (list 'o-impl-printable-str-a 'impl-printable-str-a 'impl   'Printable 'String 'root)
        (list 'o-impl-printable-str-b 'impl-printable-str-b 'impl   'Printable 'String 'root)
        (list 'o-impl-taggable-bool   'impl-taggable-bool   'impl   'Taggable  'Bool   's-user)
        ;; derive-sizable-str は String の成分数を (Printable 2 件, Sizable 1 件) にし、
        ;; 合成候補の Ambiguous を観測できるようにする（trait.md §6.2）。
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
              'Printable 'Taggable 'PrintableTaggable)
        (list 'o-intersect-size-tag 'intersect-sizable-taggable
              'Sizable 'Taggable 'SizableTaggable)
        (list 'o-intersect-print-size-tag 'intersect-printable-sizable-taggable
              'PrintableSizable 'Taggable 'PrintableSizableTaggable)))

;; COH-001: scope の系譜。package と module の入れ子を親子で表す。
;; 可視性（search.rkt の scope-visible?）はこの表の祖先到達で決まる。
;; 各行は (sid parent) であり、親を持たない scope は #f を置く。
(define scope-parent-table
  '((root #f)
    (s-kernel root)
    (s-user root)))

;; NAR-003: 第 1 欄は表の鍵であり Proof の origin ではない。Proof の origin は
;; trait-derived-origin が組み立てる。名前は既存の呼び出し側との互換で残す。
(define (trait-origin row) (first row))

;; NAR-003: trait の Proof が持つべき origin。第 1 欄 tid は表の鍵であり、
;; Proof の origin ではない。POL-001 の policy と同じく、親を
;; o-language-narrative に固定するのは Redex 項として親を一つ選ぶ必要が
;; あるためであり、o-type-narrative を親から外す意味ではない。
;; step の引数に tid ではなく trait 名を使うのは、正典が trait を名前で
;; 同定しており、proof-issuer-ok? が受け取る trait も名前であるためである。
(define (trait-derived-origin row)
  `(Derived (Reserved o-language-narrative) (Trait ,(trait-name row))))

(define (trait-constant-name row)
  (string->symbol (format "~a-trait" (trait-name row))))

;; NAR-004: impl 行と intersect 行の Proof が持つべき origin。親は
;; TraitResolution policy の origin である。trait の Proof が
;; o-language-narrative を直接の親に取るのと非対称なのは、正典で trait が
;; LanguageNarrative の予約語であるのに対し、impl と derive は
;; TraitResolutionNarrative の操作だからである。
;; step が oid を持つのは、対象型と trait 名が同じ impl 行が複数あるためで
;; ある（impl-printable-str-a と impl-printable-str-b）。nm は写さない。
;; oid から R0 を引けば復元でき、二重に持つと片方だけずれた origin が作れる。
(define (trait-resolution-origin)
  (policy-origin (policy-row-by-name 'TraitResolution)))

(define (impl-derived-origin row)
  `(Derived ,(trait-resolution-origin)
            (Impl ,(impl-oid row) ,(impl-kind row)
                  ,(impl-target-type row) ,(impl-trait-name row))))

(define (intersect-derived-origin row)
  `(Derived ,(trait-resolution-origin)
            (Intersect ,(intersect-oid row)
                       ,(intersect-left row)
                       ,(intersect-right row)
                       ,(intersect-output row))))

;; R0 を見ずに済む部分。第 1 欄が symbol であること、投影が組み立てる
;; step の引数が行の trait 名と一致すること、その名前が表に宣言済みで
;; あることを見る。
(define (trait-row-shape-ok? row [env canonical-trait-env])
  (match row
    [(list tid name _scope _template)
     (and (symbol? tid)
          (symbol? name)
          (eq? (trait-row-by-name name env) row)
          (match (trait-derived-origin row)
            [`(Derived (Reserved o-language-narrative) (Trait ,step-name))
             (eq? step-name name)]
            [_ #f]))]
    [_ #f]))

;; 予約 Narrative の id が R0 で実際にその値へ束縛されていることまで見る。
;; id の一致だけでは、R0 から予約 Narrative が消えても検査が通る。
(define (trait-origin-ok? r0 row [env canonical-trait-env])
  (and (trait-row-shape-ok? row env)
       (equal? (assq 'o-language-narrative r0)
               '(o-language-narrative languageNarrative))))

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

(define (trait-row-by-name trait [env canonical-trait-env])
  (hash-ref (trait-env-trait-by-name env) trait #f))
(define (trait-row-by-oid origin [env canonical-trait-env])
  (hash-ref (trait-env-trait-by-oid env) origin #f))
(define (impl-row-by-oid origin [env canonical-trait-env])
  (hash-ref (trait-env-impl-by-oid env) origin #f))
(define (impl-row-by-name name [env canonical-trait-env])
  (hash-ref (trait-env-impl-by-name env) name #f))
(define (impl-rows-by-trait trait [env canonical-trait-env])
  (hash-ref (trait-env-impl-by-trait env) trait '()))
(define (intersect-row-by-oid origin [env canonical-trait-env])
  (hash-ref (trait-env-intersect-by-oid env) origin #f))
(define (intersect-row-by-name name [env canonical-trait-env])
  (hash-ref (trait-env-intersect-by-name env) name #f))

(define (scope-parent-row row) (first row))
(define (scope-parent-of row) (second row))

;; COH-001: 自身を含む祖先の列。表に無い scope 識別子は親を持たないものと
;; して扱い、自身だけの列を返す。sid と sc-ctx は呼び出し側が組み立てる
;; 引数であり、表に無い識別子が渡り得る。
(define (scope-ancestors sid [rows (trait-env-scope-rows canonical-trait-env)])
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
(define (scope-genealogy-ok?
         [scope-rows (trait-env-scope-rows canonical-trait-env)]
         [trait-rows (trait-env-trait-rows canonical-trait-env)]
         [impl-rows (trait-env-impl-rows canonical-trait-env)])
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
  (check-spanless! 'instantiate-requirements type)
  (define (substitute value)
    (match value
      ['Self type]
      [`(Record ,fields) `(Record ,(substitute-row fields))]
      [(? pair?) (map substitute value)]
      [_ value]))
  (define (substitute-row fields)
    (for/list ([field (in-list fields)])
      (define t (substitute (second field)))
      ;; spec §6.2.1。Self を置き換えた後の型を正規化する。正規化できない形は
      ;; そのまま返し、診断は呼び出し側に任せる。
      (list (first field) (or (normalize-type t) t) (third field))))
  (substitute-row template))

(define (trait-primitive-names [env canonical-trait-env])
  (set->list (trait-env-primitive-names env)))
(define (trait-primitive-name? name [env canonical-trait-env])
  (set-member? (trait-env-primitive-names env) name))

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
    [`(NFn ,parameters ,return-type ,_in-effects ,effects ,obligations ,_origin)
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
    [(or 'Suspend 'Partial 'Compile 'Own 'Mutation) #t]
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
            (and (symbol? label)
                 (memq mutability '(imm mut))
                 (template-type? type))]
           [_ #f]))))

;; TRT-004: 出力 trait から成分 trait へ向かう辺が非巡回であること。
;; 合成候補の生成（search.rkt）と合成 origin の発行者判定（origins.rkt）は、
;; どちらもこの辺を降りる再帰であり、巡回があると停止しない。
;; 祖先の連なりだけを path に積むため、同じ trait が別の枝に現れる表
;; （成分の共有）は巡回と見なさない。
(define (intersect-acyclic?
         [rows (trait-env-intersect-rows canonical-trait-env)])
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

;; TRT-007: 合成 trait には直接の impl 行を置かない。
;; 合成 trait の実装は成分の impl から resolve-candidates が導出するものであり、
;; 直接行を許すと同じ (τ, tn) に導出経路と直接経路が併存し、coherence の一意性が
;; 表の側から破れる。
(define (impl-not-composite?
         [impl-rows (trait-env-impl-rows canonical-trait-env)]
         [intersect-rows (trait-env-intersect-rows canonical-trait-env)])
  (define composite-names
    (for/list ([row (in-list intersect-rows)])
      (intersect-output row)))
  (for/and ([row (in-list impl-rows)])
    (not (memq (impl-trait-name row) composite-names))))

(struct trait-env
  (trait-rows impl-rows intersect-rows scope-rows
   trait-by-name trait-by-oid impl-by-oid impl-by-name impl-by-trait
   intersect-by-oid intersect-by-name primitive-names)
  #:transparent)

;; 索引は行の並びから 1 度だけ作る。key-of が同じ鍵を 2 度返す場合は
;; 先に現れた行を残す。重複は check-env! が別に見る。
(define (index-by key-of rows)
  (for/fold ([h (hasheq)]) ([row (in-list rows)])
    (if (hash-has-key? h (key-of row))
        h
        (hash-set h (key-of row) row))))

(define (group-by-trait rows)
  (for/fold ([h (hasheq)]) ([row (in-list rows)])
    (hash-update h (impl-trait-name row)
                 (λ (acc) (append acc (list row)))
                 '())))

(define (make-trait-env #:trait trait-rows
                        #:impl impl-rows
                        #:intersect intersect-rows
                        #:scope scope-rows
                        #:fail fail)
  (let/ec return
    (define (bail reason kind key)
      (return (fail reason kind key)))
    (define env
      (trait-env trait-rows impl-rows intersect-rows scope-rows
                 (index-by trait-name trait-rows)
                 (index-by trait-origin trait-rows)
                 (index-by impl-oid impl-rows)
                 (index-by impl-name impl-rows)
                 (group-by-trait impl-rows)
                 (index-by intersect-oid intersect-rows)
                 (index-by intersect-name intersect-rows)
                 (list->seteq (append (map impl-name impl-rows)
                                      (map intersect-name intersect-rows)))))
    (check-env! env bail)
    env))

;; 3 表の内部整合を見る。R0 と Γ0 との衝突は origins.rkt が append 後に
;; 見る。鍵の重複だけは利用者の宣言が作りうるので bail で返す。残りは
;; 宣言の lowering が作らない誤りなので、error を上げたままにする。
(define (check-env! env bail)
  (define trait-rows (trait-env-trait-rows env))
  (define impl-rows (trait-env-impl-rows env))
  (define intersect-rows (trait-env-intersect-rows env))

  (define (duplicate-key keys)
    ;; 左から右へ見て、最初に 2 度目に現れた鍵を返す。
    (let loop ([keys keys] [seen (seteq)])
      (cond [(null? keys) #f]
            [(set-member? seen (car keys)) (car keys)]
            [else (loop (cdr keys) (set-add seen (car keys)))])))
  (define (check-unique! keys kind)
    (define dup (duplicate-key keys))
    (when dup (bail 'surface-trait-name-collision kind dup)))

  (check-unique! (map trait-name trait-rows) 'trait-name)

  ;; NAR-003 以降、trait 行の第 1 欄は R0 の ID ではなく表の鍵である。
  ;; この検査が守るのは鍵の一意性であり、trait-row-by-oid と search の
  ;; hook がこの鍵で行を引く。impl と intersect の第 1 欄は R0 の ID の
  ;; ままであり、3 つの表をまたいで衝突しないことを一度に見る。
  (check-unique! (append (map trait-origin trait-rows)
                         (map impl-oid impl-rows)
                         (map intersect-oid intersect-rows))
                 'origin-id)
  (check-unique! (append (map impl-name impl-rows)
                         (map intersect-name intersect-rows))
                 'primitive-name)

  (for ([row (in-list trait-rows)])
    (unless (template-row? (trait-template row))
      (error 'traits "invalid requirement template in trait ~s"
             (trait-name row))))

  (for ([row (in-list impl-rows)])
    (define trait-row (trait-row-by-name (impl-trait-name row) env))
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

  (for ([row (in-list intersect-rows)])
    (define left (trait-row-by-name (intersect-left row) env))
    (define right (trait-row-by-name (intersect-right row) env))
    (define output (trait-row-by-name (intersect-output row) env))
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

  (unless (intersect-acyclic? intersect-rows)
    (error 'traits "intersect rows form a cycle in the trait name graph"))

  (unless (impl-not-composite? impl-rows intersect-rows)
    (error 'traits "impl rows must not target a composite trait"))

  ;; NAR-003: 全行が期待する origin の形を組み立てられること。R0 の実値の
  ;; 照合は origins.rkt の make-trait-ledger が行う。この層は表そのものに
  ;; 閉じた検査だけを持つ。
  (for ([row (in-list trait-rows)])
    (unless (trait-row-shape-ok? row env)
      (error 'traits "trait row has a malformed origin shape: ~s"
             (trait-name row))))

  (unless (scope-genealogy-ok? (trait-env-scope-rows env)
                               trait-rows
                               impl-rows)
    (error 'traits "scope parent table is malformed")))

(define canonical-trait-env
  (make-trait-env #:trait trait-table
                  #:impl impl-table
                  #:intersect intersect-table
                  #:scope scope-parent-table
                  #:fail (λ (reason kind key)
                           (error 'traits "~a: ~s ~s" reason kind key))))

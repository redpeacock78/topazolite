#lang racket/base

(require racket/list
         rackunit
         "../origins.rkt"
         "../search.rkt"
         "../traits.rkt")

(test-case "TRT-004: 正典の intersect-table は非巡回である"
  (check-true (intersect-acyclic?)))

(test-case "TRT-004: 巡回する intersect fixture は拒否される"
  ;; 自己ループ。出力 trait が自分の成分に現れる。
  (check-false
   (intersect-acyclic? (list (list 'o-z 'z-name 'A 'B 'A))))
  ;; 2 行をまたぐ巡回。C は A から作られ、A は C から作られる。
  (check-false
   (intersect-acyclic? (list (list 'o-x 'x-name 'A 'B 'C)
                             (list 'o-y 'y-name 'C 'D 'A)))))

(test-case "TRT-004: 成分を共有するだけの表は巡回ではない"
  ;; 同じ trait が複数の行の成分に現れても、辺をたどって戻らなければよい。
  (check-true
   (intersect-acyclic? (list (list 'o-p 'p-name 'A 'B 'AB)
                             (list 'o-q 'q-name 'A 'C 'AC)))))

(define printable-int
  (impl-derived-origin (impl-row-by-name 'impl-printable-int)))
(define sizable-int
  (impl-derived-origin (impl-row-by-name 'derive-sizable-int)))
(define printable-str-a
  (impl-derived-origin (impl-row-by-name 'impl-printable-str-a)))
(define taggable-int
  (impl-derived-origin (impl-row-by-name 'impl-taggable-int)))
(define taggable-bool
  (impl-derived-origin (impl-row-by-name 'impl-taggable-bool)))

(define impl-print-int printable-int)
(define derive-size-int sizable-int)
(define intersect-ps
  (intersect-derived-origin
   (intersect-row-by-name 'intersect-printable-sizable)))
(define intersect-pt
  (intersect-derived-origin
   (intersect-row-by-name 'intersect-printable-taggable)))

(define compose-int
  `(Derived ,intersect-ps
            (Compose PrintableSizable ,printable-int ,sizable-int)))

(test-case "TRT-004: 正しい合成 origin は発行者判定を通る"
  (check-true (proof-issuer-ok? R0 compose-int
                                '(Implements Int PrintableSizable))))

;; [REQ: NAR-004]
(test-case "NAR-004: 合成 Proof の親は intersect の派生 origin である"
  (check-true
   (proof-issuer-ok? R0
                     `(Derived ,intersect-ps
                               (Compose PrintableSizable
                                        ,impl-print-int ,derive-size-int))
                     '(Implements Int PrintableSizable))))

(test-case "NAR-004: 旧形の親を持つ合成 origin は発行者検査で拒否される"
  ;; 新形の受理だけを見ると、旧形が並行して通る状態を検出できない。
  (check-false
   (proof-issuer-ok? R0
                     `(Derived (Reserved o-intersect-print-size)
                               (Compose PrintableSizable
                                        ,impl-print-int ,derive-size-int))
                     '(Implements Int PrintableSizable)))
  ;; 成分だけ旧形に戻したものも拒否される。
  (check-false
   (proof-issuer-ok? R0
                     `(Derived ,intersect-ps
                               (Compose PrintableSizable
                                        (Reserved o-impl-printable-int)
                                        (Reserved o-derive-sizable-int)))
                     '(Implements Int PrintableSizable))))

(test-case "TRT-004: 偽造した合成 origin は 4 通りとも拒否される"
  (define rejected (make-hash))
  (define (reject! tag origin proposition [r0 R0])
    (unless (proof-issuer-ok? r0 origin proposition)
      (hash-update! rejected tag add1 0)))
  ;; 1. intersect 行ではない既知の oid を issuer に置いたもの。
  ;;    未知の oid を使うと「知らないから落ちた」で済んでしまう。
  ;; Intersect step の oid 欄だけを impl 行の oid に偽造し、親と成分は正しいままにする。
  (reject! 'wrong-issuer
           `(Derived (Derived ,(trait-resolution-origin)
                              (Intersect o-impl-printable-int
                                         Printable Sizable PrintableSizable))
                     (Compose PrintableSizable
                              ,printable-int ,sizable-int))
           '(Implements Int PrintableSizable))
  ;; 2. 成分 origin の τ が命題の τ と食い違うもの。成分を origin へ
  ;;    埋め込まない設計ではこれが通る。
  (reject! 'component-type-mismatch
           compose-int
           '(Implements Bool PrintableSizable))
  ;; 3. 成分 origin の片方を User に差し替えたもの。
  (reject! 'user-component
           `(Derived ,intersect-ps
                     (Compose PrintableSizable User ,sizable-int))
           '(Implements Int PrintableSizable))
  ;; 4. 正しい origin のまま、iid を別の primitive へ束縛した R0 へ渡したもの。
  ;;    intersect-table を引くだけの実装はこれを通す。
  (reject! 'rebound-r0
           compose-int
           '(Implements Int PrintableSizable)
           (for/list ([entry (in-list R0)])
             (if (eq? (first entry) 'o-intersect-print-size)
                 (list 'o-intersect-print-size '(prim add))
                 entry)))
  (check-equal? (sort (hash-keys rejected) symbol<?)
                '(component-type-mismatch rebound-r0 user-component wrong-issuer))
  (for ([(tag n) (in-hash rejected)])
    (check-equal? n 1 (format "~s" tag))))

(test-case "TRT-004: 成分が合成でも同じ規則で降りる"
  ;; PrintableTaggable は Int でだけ成立する（Task 9 の impl-taggable-int）。
  (check-true
   (proof-issuer-ok? R0
                     `(Derived ,intersect-pt
                               (Compose PrintableTaggable
                                        ,printable-int
                                        ,taggable-int))
                     '(Implements Int PrintableTaggable)))
  ;; 対象型が違えば成分の発行者判定が落ちる。
  (check-false
   (proof-issuer-ok? R0
                     `(Derived ,intersect-pt
                               (Compose PrintableTaggable
                                        ,printable-int
                                        ,taggable-bool))
                     '(Implements Int PrintableTaggable))))

;; TRT-004: 合成候補の hook は成分の origin と hook を再帰的に保持する。
;; 主 fixture は Int の PrintableSizable にする。成分の impl 行が両方 root
;; scope であり、可視性を動かさずに hook の判定だけを見られるためである。
(define compose-hook
  (list 'compose 'o-trait-printable-sizable 'o-intersect-print-size
        (list printable-int
              '(o-trait-printable o-impl-printable-int))
        (list sizable-int
              '(o-trait-sizable o-derive-sizable-int))))

(define compose-origin
  `(Derived ,intersect-ps
            (Compose PrintableSizable
                     ,printable-int
                     ,sizable-int)))

(define compose-candidate
  (list 'Candidate
        (list 'ProofRep compose-origin '(Implements Int PrintableSizable))
        '(compose o-intersect-print-size impl-printable-int derive-sizable-int)
        'root 'default compose-hook))

(test-case "TRT-004: composite hook is accepted"
  (check-true (hook-ok? compose-candidate)))

(test-case "TRT-004: composite candidate is well-formed and coherent"
  (define goal (make-goal '(Implements Int PrintableSizable)))
  (check-true (wf-candidate? compose-candidate goal '(root)))
  (check-true (coherent-candidate? compose-candidate '(root))))

(test-case "TRT-004: composite hook with a swapped component is rejected"
  ;; 成分 hook を左右で入れ替えると intersect 行の左成分と食い違う。
  (define swapped
    (list 'Candidate
          (list 'ProofRep compose-origin '(Implements Int PrintableSizable))
          '(compose o-intersect-print-size derive-sizable-int impl-printable-int)
          'root 'default
          (list 'compose 'o-trait-printable-sizable 'o-intersect-print-size
                (list sizable-int
                      '(o-trait-sizable o-derive-sizable-int))
                (list printable-int
                      '(o-trait-printable o-impl-printable-int)))))
  (check-false (hook-ok? swapped)))

(test-case "TRT-004: composite hook whose origin disagrees is rejected"
  ;; hook の成分 origin と、origin 内の Compose の成分が一致しない。
  (define detached
    (list 'Candidate
          (list 'ProofRep compose-origin '(Implements Int PrintableSizable))
          '(compose o-intersect-print-size impl-printable-str-a derive-sizable-int)
          'root 'default
          (list 'compose 'o-trait-printable-sizable 'o-intersect-print-size
                (list printable-str-a
                      '(o-trait-printable o-impl-printable-str-a))
                (list sizable-int
                      '(o-trait-sizable o-derive-sizable-int)))))
  (check-false (hook-ok? detached)))

(test-case "TRT-004: an invisible component makes the composite incoherent"
  ;; impl-taggable-int の target scope は s-user、Taggable の生成 scope
  ;; は s-kernel である。root だけの系譜では右成分が coherent にならない。
  ;; hook 自体は形として正しいため、落ちる場所が coherence だけになる。
  (define tag-origin
    `(Derived ,intersect-pt
              (Compose PrintableTaggable
                       ,printable-int
                       ,taggable-int)))
  (define tag-candidate
    (list 'Candidate
          (list 'ProofRep tag-origin '(Implements Int PrintableTaggable))
          '(compose o-intersect-print-tag impl-printable-int impl-taggable-int)
          'root 'default
          (list 'compose 'o-trait-printable-taggable 'o-intersect-print-tag
                (list printable-int
                      '(o-trait-printable o-impl-printable-int))
                (list taggable-int
                      '(o-trait-taggable o-impl-taggable-int)))))
  (check-true  (hook-ok? tag-candidate))
  (check-false (coherent-candidate? tag-candidate '(root)))
  (check-true  (coherent-candidate? tag-candidate '(root s-user))))

(test-case "TRT-005: RequiresBoth hook is accepted only for its intersect row"
  (check-true
   (hook-ok?/parts '(RequiresBoth Printable Sizable)
                   (intersect-derived-origin
                    (intersect-row-by-name 'intersect-printable-sizable))
                   '(o-intersect-print-size)))
  ;; 行の左右と食い違う命題では通らない。
  (check-false
   (hook-ok?/parts '(RequiresBoth Printable Taggable)
                   (intersect-derived-origin
                    (intersect-row-by-name 'intersect-printable-sizable))
                   '(o-intersect-print-size)))
  ;; origin が hook の oid と食い違う場合も通らない。
  (check-false
   (hook-ok?/parts '(RequiresBoth Printable Sizable)
                   '(Reserved o-impl-printable-int)
                   '(o-intersect-print-size)))
  ;; 空 hook は従来どおり通る。
  (check-true
   (hook-ok?/parts '(RequiresBoth Printable Sizable)
                   (intersect-derived-origin
                    (intersect-row-by-name 'intersect-printable-sizable))
                   '())))

(test-case "TRT-005: RequiresBoth is implicit only for a declared intersect row"
  (check-true
   (obligations-dischargeable?
    '((RequiresBoth Printable Sizable))
    Γ-pc0))
  (check-true
   (obligations-dischargeable?
    '((RequiresBoth Printable Taggable))
    Γ-pc0))
  ;; 正典表に無い組は依然として解けない。
  (check-false
   (obligations-dischargeable?
    '((RequiresBoth Sizable PrintableTaggable))
    Γ-pc0)))

;; TRT-004: 合成 trait への所属が候補として立つ。
(test-case "TRT-004: composite Implements is dischargeable"
  (check-true
   (obligations-dischargeable?
    '((Implements Int PrintableSizable))
    Γ-pc0)))

(test-case "TRT-004: project-goal yields exactly one composite candidate"
  (define goal (make-goal '(Implements Int PrintableSizable)))
  (define sigma (project-goal Γ-pc0 '(root) goal))
  (check-equal? (length sigma) 1)
  (define c (first sigma))
  (check-equal? (candidate-prop c) '(Implements Int PrintableSizable))
  (check-equal? (candidate-origin c)
                `(Derived ,intersect-ps
                          (Compose PrintableSizable
                                   ,printable-int
                                   ,sizable-int)))
  (check-equal? (candidate-cid c)
                '(compose o-intersect-print-size
                          impl-printable-int
                          derive-sizable-int))
  (check-equal? (candidate-sid c) 'root)
  (check-equal? (candidate-pid c) 'default))

(test-case "TRT-004: the product of two Printable rows yields Ambiguous"
  ;; String は Printable を 2 行、Sizable を Task 9 の derive-sizable-str で
  ;; 1 行持つ。直積は 2 件になり、一意に解けない。
  (define goal (make-goal '(Implements String PrintableSizable)))
  (define sigma (project-goal Γ-pc0 '(root) goal))
  (check-equal? (length sigma) 2)
  (check-true (ambiguous? (resolve-candidates goal sigma)))
  (check-false
   (obligations-dischargeable? '((Implements String PrintableSizable)) Γ-pc0)))

(test-case "TRT-004: a missing component blocks the composite"
  ;; Bool は Printable を実装しない。片側が欠ければ直積は空になる。
  (define goal (make-goal '(Implements Bool PrintableSizable)))
  (check-equal? (project-goal Γ-pc0 '(root) goal) '())
  (check-false
   (obligations-dischargeable? '((Implements Bool PrintableSizable)) Γ-pc0)))

(test-case "TRT-004: composite candidates are stable across runs"
  (define goal (make-goal '(Implements Int PrintableSizable)))
  (check-equal? (project-goal Γ-pc0 '(root) goal)
                (project-goal Γ-pc0 '(root) goal)))

(test-case "TRT-004: an invisible component scope blocks the composite"
  ;; impl-taggable-int の target scope は s-user、Taggable の生成 scope
  ;; は s-kernel である。root だけの系譜では Taggable 成分が coherent になら
  ;; ず、合成も立たない。Printable 成分は両方の系譜で見えているため、動いて
  ;; いるのは Taggable 側の可視性だけである。
  (define goal (make-goal '(Implements Int PrintableTaggable)))
  (check-equal? (length (project-goal Γ-pc0 '(root) goal)) 0)
  (check-equal? (length (project-goal Γ-pc0 '(root s-user) goal)) 1))

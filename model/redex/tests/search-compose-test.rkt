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

(define printable-int '(Reserved o-impl-printable-int))
(define sizable-int   '(Reserved o-derive-sizable-int))

(define compose-int
  `(Derived (Reserved o-intersect-print-size)
            (Compose PrintableSizable ,printable-int ,sizable-int)))

(test-case "TRT-004: 正しい合成 origin は発行者判定を通る"
  (check-true (proof-issuer-ok? R0 compose-int
                                '(Implements Int PrintableSizable))))

(test-case "TRT-004: 偽造した合成 origin は 4 通りとも拒否される"
  (define rejected (make-hash))
  (define (reject! tag origin proposition [r0 R0])
    (unless (proof-issuer-ok? r0 origin proposition)
      (hash-update! rejected tag add1 0)))
  ;; 1. intersect 行ではない既知の oid を issuer に置いたもの。
  ;;    未知の oid を使うと「知らないから落ちた」で済んでしまう。
  (reject! 'wrong-issuer
           `(Derived (Reserved o-impl-printable-int)
                     (Compose PrintableSizable ,printable-int ,sizable-int))
           '(Implements Int PrintableSizable))
  ;; 2. 成分 origin の τ が命題の τ と食い違うもの。成分を origin へ
  ;;    埋め込まない設計ではこれが通る。
  (reject! 'component-type-mismatch
           compose-int
           '(Implements Bool PrintableSizable))
  ;; 3. 成分 origin の片方を User に差し替えたもの。
  (reject! 'user-component
           `(Derived (Reserved o-intersect-print-size)
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
                     `(Derived (Reserved o-intersect-print-tag)
                               (Compose PrintableTaggable
                                        ,printable-int
                                        (Reserved o-impl-taggable-int)))
                     '(Implements Int PrintableTaggable)))
  ;; 対象型が違えば成分の発行者判定が落ちる。
  (check-false
   (proof-issuer-ok? R0
                     `(Derived (Reserved o-intersect-print-tag)
                               (Compose PrintableTaggable
                                        ,printable-int
                                        (Reserved o-impl-taggable-bool)))
                     '(Implements Int PrintableTaggable))))

;; TRT-004: 合成候補の hook は成分の origin と hook を再帰的に保持する。
;; 主 fixture は Int の PrintableSizable にする。成分の impl 行が両方 root
;; scope であり、可視性を動かさずに hook の判定だけを見られるためである。
(define compose-hook
  (list 'compose 'o-trait-printable-sizable 'o-intersect-print-size
        (list '(Reserved o-impl-printable-int)
              '(o-trait-printable o-impl-printable-int))
        (list '(Reserved o-derive-sizable-int)
              '(o-trait-sizable o-derive-sizable-int))))

(define compose-origin
  '(Derived (Reserved o-intersect-print-size)
            (Compose PrintableSizable
                     (Reserved o-impl-printable-int)
                     (Reserved o-derive-sizable-int))))

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
                (list '(Reserved o-derive-sizable-int)
                      '(o-trait-sizable o-derive-sizable-int))
                (list '(Reserved o-impl-printable-int)
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
                (list '(Reserved o-impl-printable-str-a)
                      '(o-trait-printable o-impl-printable-str-a))
                (list '(Reserved o-derive-sizable-int)
                      '(o-trait-sizable o-derive-sizable-int)))))
  (check-false (hook-ok? detached)))

(test-case "TRT-004: an invisible component makes the composite incoherent"
  ;; impl-taggable-int の target scope は s-user、Taggable の生成 scope
  ;; は s-kernel である。root だけの系譜では右成分が coherent にならない。
  ;; hook 自体は形として正しいため、落ちる場所が coherence だけになる。
  (define tag-origin
    '(Derived (Reserved o-intersect-print-tag)
              (Compose PrintableTaggable
                       (Reserved o-impl-printable-int)
                       (Reserved o-impl-taggable-int))))
  (define tag-candidate
    (list 'Candidate
          (list 'ProofRep tag-origin '(Implements Int PrintableTaggable))
          '(compose o-intersect-print-tag impl-printable-int impl-taggable-int)
          'root 'default
          (list 'compose 'o-trait-printable-taggable 'o-intersect-print-tag
                (list '(Reserved o-impl-printable-int)
                      '(o-trait-printable o-impl-printable-int))
                (list '(Reserved o-impl-taggable-int)
                      '(o-trait-taggable o-impl-taggable-int)))))
  (check-true  (hook-ok? tag-candidate))
  (check-false (coherent-candidate? tag-candidate '(root)))
  (check-true  (coherent-candidate? tag-candidate '(root s-user))))

(test-case "TRT-005: RequiresBoth hook is accepted only for its intersect row"
  (check-true
   (hook-ok?/parts '(RequiresBoth Printable Sizable)
                   '(Reserved o-intersect-print-size)
                   '(o-intersect-print-size)))
  ;; 行の左右と食い違う命題では通らない。
  (check-false
   (hook-ok?/parts '(RequiresBoth Printable Taggable)
                   '(Reserved o-intersect-print-size)
                   '(o-intersect-print-size)))
  ;; origin が hook の oid と食い違う場合も通らない。
  (check-false
   (hook-ok?/parts '(RequiresBoth Printable Sizable)
                   '(Reserved o-impl-printable-int)
                   '(o-intersect-print-size)))
  ;; 空 hook は従来どおり通る。
  (check-true
   (hook-ok?/parts '(RequiresBoth Printable Sizable)
                   '(Reserved o-intersect-print-size)
                   '())))

(test-case "TRT-005: RequiresBoth is implicit only for a declared intersect row"
  (check-true
   (obligations-dischargeable?
    '((RequiresBoth Printable Sizable))
    Γ-pc0))
  ;; 正典表に無い組は依然として解けない。
  (check-false
   (obligations-dischargeable?
    '((RequiresBoth Sizable Taggable))
    Γ-pc0)))

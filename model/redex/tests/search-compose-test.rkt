#lang racket/base

(require racket/list
         rackunit
         "../origins.rkt"
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

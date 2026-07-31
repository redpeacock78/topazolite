#lang racket/base

(require racket/list
         racket/match)

(provide policy-table
         policy-name policy-origin policy-parents
         policy-operations policy-module
         policy-row-by-name
         reserved-narrative-ids
         reserved-narrative-values
         policy-row-shape-ok?
         policy-origin-ok?
         policy-wrap
         registered-policy-operations)

;; POL-001: 標準 Policy Narrative は二つの予約 Narrative から派生する。
;; policy は R0 の id を持たない。id を与えると、それが新しい trusted root に
;; なる。origin の親を o-language-narrative に固定するのは Redex 項として親を
;; 一つ選ぶ必要があるためであり、o-type-narrative を親から外す意味ではない。
;; 派生関係の 2 件は parents 欄が持つ。
(define reserved-narrative-ids '(o-language-narrative o-type-narrative))

(define reserved-narrative-values
  '((o-language-narrative languageNarrative)
    (o-type-narrative typeNarrative)))

;; 行: (名前 origin parents (操作 ...) 所有モジュール)
;; 登録するのは model に実装がある 5 件だけである。BindingPolicy と
;; OwnershipPolicy は実装が入るサイクルで足す。
(define (policy-row name operations module-name)
  (list name
        `(Derived (Reserved o-language-narrative) (Policy ,name))
        reserved-narrative-ids
        operations
        module-name))

(define policy-table
  (list (policy-row 'RowPolicy '(merge-record-types) 'typing.rkt)
        (policy-row 'VariancePolicy '(compat?) 'compat.rkt)
        (policy-row 'TraitResolution '(project-goal resolve-candidates) 'search.rkt)
        (policy-row 'ProofSearch '(discharge?) 'search.rkt)
        (policy-row 'Normalization '(normalize-type) 'type-equiv.rkt)))

(define (policy-name row)       (first row))
(define (policy-origin row)     (second row))
(define (policy-parents row)    (third row))
(define (policy-operations row) (fourth row))
(define (policy-module row)     (fifth row))

(define (policy-row-by-name name)
  (findf (lambda (row) (eq? (policy-name row) name)) policy-table))

(define (declared-policy-name? name)
  (and (findf (lambda (row) (eq? (policy-name row) name)) policy-table) #t))

;; R0 を見ない部分の検査。policy.rkt は origins.rkt を require できないため、
;; 実値照合は policy-origin-ok? が r0 を受け取って行う。
(define (policy-row-shape-ok? row)
  (match row
    [(list name origin parents operations _module)
     (and (equal? parents reserved-narrative-ids)
          (pair? operations)
          (match origin
            [`(Derived (Reserved o-language-narrative) (Policy ,step-name))
             (and (eq? step-name name)
                  (declared-policy-name? step-name))]
            [_ #f]))]
    [_ #f]))

;; 予約 Narrative の id が R0 で実際にその値へ束縛されていることまで見る。
;; id の一致だけでは、R0 から予約 Narrative が消えても検査が通る。
(define (policy-origin-ok? r0 row)
  (and (policy-row-shape-ok? row)
       (for/and ([entry (in-list reserved-narrative-values)])
         (equal? (assq (first entry) r0) entry))))

;; 登録済みの (policy名 . 操作名)。policy-check.rkt が宣言側と突き合わせる。
(define registered (box '()))
(define (registered-policy-operations) (reverse (unbox registered)))

;; POL-002: 素の実装を call-with-values で呼び、返却値のリストを検査へ渡す。
;; 検査が偽なら error。呼び出し側へ偽を返すと失敗返却と区別できない。
;; fail-closed の判定は操作ごとに違うため、所有モジュールの検査述語が持つ。
(define (policy-wrap policy-name-arg op-name impl check
                     #:project [project values])
  (define row (policy-row-by-name policy-name-arg))
  (unless row
    (error 'policy-wrap "unknown policy: ~s" policy-name-arg))
  (unless (memq op-name (policy-operations row))
    (error 'policy-wrap "policy ~s does not declare operation ~s"
           policy-name-arg op-name))
  (unless (policy-row-shape-ok? row)
    (error 'policy-wrap "policy row is malformed: ~s" policy-name-arg))
  (set-box! registered (cons (cons policy-name-arg op-name) (unbox registered)))
  (lambda args
    (define returns (call-with-values (lambda () (apply impl args)) list))
    (unless (check args returns)
      (error op-name
             "~s policy check failed: args=~s returns=~s"
             policy-name-arg args returns))
    (apply values (project returns))))

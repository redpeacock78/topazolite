#lang racket/base

(require racket/list
         racket/match
         rackunit
         "../compat.rkt"
         "../gen.rkt"
         "../origins.rkt"
         "../policy.rkt"
         "../search.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define limits (read-bounds))
(define attempts (bounds-attempts limits))

;; POL-001: policy は R0 の id を持たない。壊した行を 4 種類作り、
;; policy-origin-ok? がどの種類を拒否したかを観測してから加算する。
(define (broken-row kind base)
  (match-define (list name origin parents operations module-name) base)
  (case kind
    ;; 1: 手書きの Reserved id。これを受理すると policy が trusted root になる。
    [(reserved-id)
     (list name `(Reserved o-policy-trait) parents operations module-name)]
    ;; 2: 予約 Narrative でない親。
    [(foreign-parent)
     (list name
           `(Derived (Reserved o-merge) (Policy ,name))
           parents operations module-name)]
    ;; 3: policy-table に無い名前。行の名前も揃えて、名前照合だけを落とす。
    [(unknown-name)
     (list 'NotAPolicy
           '(Derived (Reserved o-language-narrative) (Policy NotAPolicy))
           parents operations module-name)]
    ;; 4: parents が予約 Narrative 2 件と一致しない行。
    [(short-parents)
     (list name origin '(o-language-narrative) operations module-name)]
    [else (error 'broken-row "unknown kind: ~s" kind)]))

(define broken-kinds '(reserved-id foreign-parent unknown-name short-parents))

(test-case "POL-001: 壊した policy 行は 4 種類とも拒否される"
  (call-with-search-seed
   limits
   (lambda ()
     (define rejected (make-hash))
     (define accepted-sound (box 0))
     (for ([_i (in-range attempts)])
       (define base (pick-one policy-table))
       (define kind (pick-one broken-kinds))
       ;; 正しい行は受理される。受理を観測してから加算する。
       (when (policy-origin-ok? R0 base)
         (set-box! accepted-sound (add1 (unbox accepted-sound))))
       ;; 壊した行は拒否される。拒否を観測してから種類ごとに加算する。
       (unless (policy-origin-ok? R0 (broken-row kind base))
         (hash-update! rejected kind add1 0)))
     (check-equal? (unbox accepted-sound) attempts)
     (for ([kind (in-list broken-kinds)])
       (check-true (positive? (hash-ref rejected kind 0))
                   (format "kind ~a was never rejected" kind)))
     (printf "POL-001: attempts=~a accepted=~a rejected=~s seed=~a\n"
             attempts (unbox accepted-sound)
             (sort (hash->list rejected) symbol<? #:key car)
             (bounds-seed limits)))))

(test-case "POL-001: R0 の実値が変われば正しい行も拒否される"
  ;; id の一致だけを見る実装はこの fixture を通す。
  (define rebound
    (cons '(o-language-narrative someOtherPrimitive)
          (filter (lambda (entry)
                    (not (eq? (car entry) 'o-language-narrative)))
                  R0)))
  (for ([row (in-list policy-table)])
    (check-true  (policy-origin-ok? R0 row))
    (check-false (policy-origin-ok? rebound row))))

;; POL-002: 5 policy の 6 操作それぞれで、正しい返却を受理し壊した返却を拒否
;; する。壊れた返却値は包まれた関数の外から作れないため、検査述語を直接呼ぶ。
;; 各要素は (policy 操作 検査述語 args 正しい returns 壊した returns)。
(define policy-return-cases
  (list
   (list 'Normalization 'normalize-type check-normalize-return
         '((Intersection Int Int))
         '(Int)
         ;; 非正規形を正規形と偽る返却。
         '((Intersection Int Int)))
   (list 'VariancePolicy 'compat? check-compat-return
         '(Int Int)
         '(#t)
         '(#f))
   (list 'RowPolicy 'merge-record-types check-merge-return
         '(())
         (list '(Record ((a Int imm) (z Int imm))) '())
         ;; label が降順であり、不変条件を破る。
         (list '(Record ((z Int imm) (a Int imm))) '()))
   (list 'TraitResolution 'project-goal check-project-goal-return
         (list Γ-pc0 '(root) (make-goal '(Implements Int Printable)))
         (list (project-goal Γ-pc0 '(root)
                             (make-goal '(Implements Int Printable))))
         ;; 別 goal の候補を混ぜた返却。
         (list (project-goal Γ-pc0 '(root)
                             (make-goal '(Implements String Printable)))))
   (list 'TraitResolution 'resolve-candidates check-resolve-return
         (list (make-goal '(Implements Int Printable))
               (project-goal Γ-pc0 '(root)
                             (make-goal '(Implements Int Printable))))
         (list (resolve-candidates
                (make-goal '(Implements Int Printable))
                (project-goal Γ-pc0 '(root)
                              (make-goal '(Implements Int Printable)))))
         ;; Σ に無い Proof を Resolved として返す。
         (list '(Resolved (ProofRep (Reserved o-merge) (Presence a)))))
   (list 'ProofSearch 'discharge? check-discharge-return
         '()
         (list #t 'Finite '(Resolved p))
         (list #t 'Finite 'Absent))))

(test-case "POL-002: 6 操作それぞれで検査が受理と拒否の両方を出す"
  (call-with-search-seed
   limits
   (lambda ()
     (define accepted (make-hash))
     (define rejected (make-hash))
     (for ([_i (in-range attempts)])
       (match-define (list policy op check args good bad)
         (pick-one policy-return-cases))
       (define key (cons policy op))
       ;; 受理と拒否を観測してから加算する。
       (when (check args good) (hash-update! accepted key add1 0))
       (unless (check args bad) (hash-update! rejected key add1 0)))
     (for ([entry (in-list policy-return-cases)])
       (define key (cons (first entry) (second entry)))
       (check-true (positive? (hash-ref accepted key 0))
                   (format "~s never accepted a sound return" key))
       (check-true (positive? (hash-ref rejected key 0))
                   (format "~s never rejected a broken return" key)))
     (printf "POL-002: attempts=~a operations=~a seed=~a\n"
             attempts (length policy-return-cases) (bounds-seed limits)))))

;; TRT-004: 合成候補の数は成分候補数の直積であり、resolve は三分岐すべてを出す。
;; 目標の型ごとに (n, m) が (1,1)・(2,1)・(0,0) になる。
;; 件数の等式は、PrintableSizable を出力する intersect 行が 1 行だけであり、
;; かつ PrintableSizable の直接の impl 行が無いことに依存する。表へ 2 行目や
;; 直接の実装を足すと、この等式は成り立たなくなる。
(define composite-targets '(Int String Bool))

(test-case "TRT-004: 直積の件数と三分岐"
  (call-with-search-seed
   limits
   (lambda ()
     (define resolved-count (box 0))
     (define ambiguous-count (box 0))
     (define absent-count (box 0))
     (for ([_i (in-range attempts)])
       (define target (pick-one composite-targets))
       (define goal (make-goal `(Implements ,target PrintableSizable)))
       (define left
         (project-goal Γ-pc0 '(root)
                       (make-goal `(Implements ,target Printable))))
       (define right
         (project-goal Γ-pc0 '(root)
                       (make-goal `(Implements ,target Sizable))))
       (define sigma (project-goal Γ-pc0 '(root) goal))
       ;; 直積の件数は成分候補数の積である。
       (check-equal? (length sigma) (* (length left) (length right)))
       ;; 分岐は resolve の結果を観測してから加算する。
       (define result (resolve-candidates goal sigma))
       (cond
         [(resolved? result)
          (set-box! resolved-count (add1 (unbox resolved-count)))]
         [(ambiguous? result)
          (set-box! ambiguous-count (add1 (unbox ambiguous-count)))]
         [(absent? result)
          (set-box! absent-count (add1 (unbox absent-count)))]))
     (check-true (positive? (unbox resolved-count)))
     (check-true (positive? (unbox ambiguous-count)))
     (check-true (positive? (unbox absent-count)))
     (printf "TRT-004: attempts=~a resolved=~a ambiguous=~a absent=~a seed=~a\n"
             attempts (unbox resolved-count) (unbox ambiguous-count)
             (unbox absent-count) (bounds-seed limits)))))

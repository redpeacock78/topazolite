#lang racket/base

(require racket/list
         rackunit
         "../policy.rkt"
         "../search.rkt"
         "../type-equiv.rkt"
         "../compat.rkt"
         "../typing.rkt")

;; 予約 Narrative を正しく束縛した R0 の最小 fixture。
(define r0-ok
  '((o-language-narrative languageNarrative)
    (o-type-narrative typeNarrative)))

;; languageNarrative を別の値へ束縛した R0。id の一致だけを見る実装はこれを通す。
(define r0-broken
  '((o-language-narrative someOtherValue)
    (o-type-narrative typeNarrative)))

(test-case "POL-001: policy-table の 5 行がすべて規定の形を持つ"
  (check-equal? (map policy-name policy-table)
                '(RowPolicy VariancePolicy TraitResolution
                  ProofSearch Normalization))
  (for ([row (in-list policy-table)])
    (check-equal? (policy-origin row)
                  `(Derived (Reserved o-language-narrative)
                            (Policy ,(policy-name row))))
    (check-equal? (policy-parents row) reserved-narrative-ids)
    (check-true (policy-row-shape-ok? row))
    (check-true (policy-origin-ok? r0-ok row))))

(test-case "POL-001: policy 由来の Reserved id は存在しない"
  ;; policy 行は R0 の id を持たない。origin の親は予約 Narrative だけである。
  (for ([row (in-list policy-table)])
    (check-equal? (second (policy-origin row))
                  '(Reserved o-language-narrative))))

(test-case "POL-001: policy-origin-ok? は R0 の実値まで見る"
  (define rejected (box 0))
  (for ([row (in-list policy-table)])
    (unless (policy-origin-ok? r0-broken row)
      (set-box! rejected (add1 (unbox rejected)))))
  (check-equal? (unbox rejected) (length policy-table)))

(test-case "POL-001: policy-row-shape-ok? は四つの壊れた行を拒否する"
  (define counts (make-hash))
  (define (reject! tag row)
    (unless (policy-row-shape-ok? row)
      (hash-update! counts tag add1 0)))
  ;; 1. policy へ独自の Reserved id を与えた行
  (reject! 'own-reserved-id
           '(TraitResolution (Reserved o-policy-trait)
                             (o-language-narrative o-type-narrative)
                             (project-goal) search.rkt))
  ;; 2. 予約 Narrative 以外を親に持つ行
  (reject! 'foreign-parent
           '(TraitResolution (Derived (Reserved o-merge)
                                      (Policy TraitResolution))
                             (o-language-narrative o-type-narrative)
                             (project-goal) search.rkt))
  ;; 3. policy-table に無い名前を Policy step に持つ行
  (reject! 'unknown-name
           '(TraitResolution (Derived (Reserved o-language-narrative)
                                      (Policy NotAPolicy))
                             (o-language-narrative o-type-narrative)
                             (project-goal) search.rkt))
  ;; 4. parents が予約 Narrative 2 件と一致しない行
  (reject! 'bad-parents
           '(TraitResolution (Derived (Reserved o-language-narrative)
                                      (Policy TraitResolution))
                             (o-language-narrative)
                             (project-goal) search.rkt))
  (check-equal? (sort (hash-keys counts) symbol<?)
                '(bad-parents foreign-parent own-reserved-id unknown-name))
  (for ([(tag n) (in-hash counts)])
    (check-equal? n 1 (format "~s" tag))))

(test-case "policy-wrap は未知の policy 名を登録時に拒否する"
  (check-exn exn:fail?
             (lambda ()
               (policy-wrap 'NotAPolicy 'op values (lambda (as vs) #t)))))

(test-case "policy-wrap は行に無い操作を登録時に拒否する"
  (check-exn exn:fail?
             (lambda ()
               (policy-wrap 'RowPolicy 'not-an-operation
                            values (lambda (as vs) #t)))))

(test-case "POL-002: policy-wrap は検査を呼び、偽なら error を送出する"
  (define wrapped
    (policy-wrap 'RowPolicy 'merge-record-types
                 (lambda (x) x)
                 (lambda (args returns) (equal? returns '(ok)))))
  (check-equal? (wrapped 'ok) 'ok)
  (check-exn exn:fail? (lambda () (wrapped 'broken))))

(test-case "POL-002: policy-wrap は多値を保ち、射影で絞れる"
  (define two-values
    (policy-wrap 'RowPolicy 'merge-record-types
                 (lambda () (values 1 2))
                 (lambda (args returns) (equal? returns '(1 2)))))
  (check-equal? (call-with-values two-values list) '(1 2))
  (define projected
    (policy-wrap 'ProofSearch 'discharge?
                 (lambda () (values #t 'Finite 'Resolved))
                 (lambda (args returns) (= (length returns) 3))
                 #:project (lambda (vs) (list (first vs)))))
  (check-equal? (projected) #t))

(test-case "POL-002/Normalization: 正規化は冪等で、#f は素通りする"
  (check-equal? (normalize-type '(Union Int Int)) 'Int)
  (define normalized (normalize-type '(Union String Int)))
  (check-equal? (normalize-type normalized) normalized)
  ;; 正規化できない型の fail-closed 返却。例外にしてはならない。
  (check-false (normalize-type '(Intersection Int String))))

(test-case "Normalization: 検査述語は #f を素通りし、非冪等な返却を弾く"
  ;; #f は正規化できない型の fail-closed 返却であり、検査の対象外である。
  (check-true
   (check-normalize-return (list '(Intersection Int String)) '(#f)))
  (check-true (check-normalize-return '(Int) '(Int)))
  ;; (Union Int Int) は Int へ正規化されるため、返却としては冪等でない。
  (check-false
   (check-normalize-return '(Int) '((Union Int Int)))))

(test-case "Normalization: normalize-type は policy として登録されている"
  (check-true
   (and (member '(Normalization . normalize-type)
                (registered-policy-operations))
        #t)))

(test-case "POL-002/VariancePolicy: 同値な二型は互換である"
  (check-true (compat? 'Int 'Int))
  (check-true (compat? '(Record ((a Int imm))) '(Record ((a Int imm)))))
  ;; 非互換の判定は素通りする。compat? に fail-closed 返却は無い。
  (check-false (compat? 'Int 'String)))

(test-case "VariancePolicy: 検査は同値互換に限る（G5 で強化する）"
  ;; check-compat-return を直接呼び、同値でない組には制約が無いことを固定する。
  (check-true (check-compat-return '(Int String) '(#f)))
  (check-true (check-compat-return '(Int String) '(#t)))
  (check-false (check-compat-return '(Int Int) '(#f))))

(test-case "POL-002/RowPolicy: 合流 row は label 一意かつ昇順である"
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((z Int imm) (a Int imm)))
                       '(Record ((a Int imm) (z Int imm)))))])
    (check-equal? merged '(Record ((a Int imm) (z Int imm))))
    (check-true (wf-context? witnesses))))

(test-case "RowPolicy: 空 row の合流は fail-closed ではない"
  ;; typing-join-test.rkt の mutable 衝突と同じ形。(Record ()) は成功返却で
  ;; あり、検査述語は不変条件を実際に適用する。
  (define applied (box 0))
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((a Int mut)))
                       '(Record ((a String mut)))))])
    (check-equal? merged '(Record ()))
    (check-equal? witnesses '())
    (when (equal? merged '(Record ())) (set-box! applied (add1 (unbox applied)))))
  (check-equal? (unbox applied) 1)
  ;; 検査述語の側でも、#f だけが fail-closed であることを固定する。
  (check-true (check-merge-return '(()) (list #f '())))
  (check-false (check-merge-return '(()) (list '(Record ((b Int imm) (a Int imm))) '()))))

(test-case "POL-002/ProofSearch: discharge? は真偽値 1 値を返し続ける"
  (check-true (discharge? Γ-pc0 default-classifier default-oracle
                          (make-goal '(Implements Int Printable))))
  (check-false (discharge? Γ-pc0 default-classifier default-oracle
                           (make-goal '(Implements Bool Printable)))))

(test-case "ProofSearch: 受理は Finite/Productive かつ Resolved に限る"
  (check-true  (check-discharge-return '() (list #t 'Finite '(Resolved p))))
  (check-true  (check-discharge-return '() (list #f 'Finite 'Absent)))
  (check-false (check-discharge-return '() (list #t 'Finite 'Absent)))
  (check-false (check-discharge-return '() (list #t 'Unknown '(Resolved p))))
  (check-false (check-discharge-return '() (list #t 'Finite '(Ambiguous (p q))))))

(test-case "POL-002/TraitResolution: project-goal の返却はすべて wf である"
  (define goal (make-goal '(Implements Int Printable)))
  (define sigma (project-goal Γ-pc0 '(root) goal))
  (check-equal? (length sigma) 1)
  (check-true (wf-Σ? sigma goal '(root)))
  (check-true (check-project-goal-return (list Γ-pc0 '(root) goal) (list sigma)))
  ;; 空リストは fail-closed 返却であり素通りする。
  (check-equal? (project-goal Γ-pc0 '(root)
                             (make-goal '(Implements Bool Printable)))
                '()))

(test-case "TraitResolution: Resolved は 1 件、Ambiguous は 2 件以上"
  (define goal (make-goal '(Implements String Printable)))
  (define sigma (project-goal Γ-pc0 '(root) goal))
  (define result (resolve-candidates goal sigma))
  (check-true (ambiguous? result))
  (check-true (check-resolve-return (list goal sigma) (list result)))
  (check-false (check-resolve-return (list goal sigma) (list (list 'Ambiguous '(p)))))
  (check-false (check-resolve-return (list goal '()) (list (list 'Resolved 'p)))))

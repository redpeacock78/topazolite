#lang racket

;; [REQ: OWN-004] mut 欄から imm 欄へ潜る RSD と借用境界。
;; Task 1b の監査で、RSD 対象値が生きた借用から別名参照される経路は到達しない。

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../compat.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../ownership.rkt"
         "../region.rkt"
         "../resource-type.rkt"
         "../type-equiv.rkt"
         "../validators.rkt"
         "../typing.rkt"
         (only-in "row005-property-support.rkt" R well-formed-generated-type?))

(define mut-actual
  '(Record ((a (Record ((o (Owned Res) imm) (x Int imm))) mut))))
(define imm-expected
  '(Record ((a (Record ((x Int imm))) imm))))
(define target-type
  '(Record ((a (Record ((x Int imm))) imm))))

(define (diagnostic-id-of result)
  (match result
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (find-rsd value)
  (match value
    [`(Discharge (ProofRep (Reserved o-narrow)
                          (RemainderSafelyDropped ,actual ,target)) ,_)
     (list actual target)]
    [(? list?) (for/or ([child (in-list value)]) (find-rsd child))]
    [_ #f]))

(define (contains-rsd? value)
  (and (find-rsd value) #t))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (configuration-core configuration)
  (match configuration [`(cfg ,core ,_ ,_ ,_ ,_) core]))

(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (check-config-trace configs callables expected-type)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected-type))
    (check-not-false row
                     (format "config ~a の runtime row が無い: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected-type row)
                (format "config ~a が不正: ~s" index configuration))))

(define inner-actual '(Record ((o (Owned Res) imm) (x Int imm))))
(define inner-expected '(Record ((x Int imm))))
(define mut-optional-universe
  (list
   `(Record ((a ,inner-actual mut)))
   `(Record ((a ,inner-expected imm)))
   `(Record ((a ,inner-expected mut)))
   `(Record ((a ,inner-actual mut opt)))
   `(Record ((a ,inner-expected imm opt)))
   `(Record ((a ,inner-actual mut) (b Int imm)))
   `(Record ((a ,inner-expected imm) (b Int imm)))))
(define eligible-universe
  (remove-duplicates
   (filter well-formed-generated-type? (append R mut-optional-universe))
   equal?))

(define (drop-obligation? kind)
  (match kind [`(drop-obligation ,_ ,_) #t] [_ #f]))

(define (accepted-member-kind? actual expected kind)
  (or (eq? kind 'ok)
      (eq? kind 'nested-drop)
      (and (drop-obligation? kind)
           (rsd-eligible? actual expected))))

(define (union-type? type)
  (and (pair? type) (eq? (car type) 'Union)))

(define (union-members type)
  (if (union-type? type)
      (append-map union-members (cdr type))
      (list type)))

(define (let-conversion-program)
  `(Fn ((source ,mut-actual)) ,imm-expected (Own)
       (Let (record let ,imm-expected) (Move source) record)))

(define (apply-conversion-program)
  `(Fn ((source ,mut-actual)) ,imm-expected (Own)
       (Apply (Fn ((record ,imm-expected)) ,imm-expected (Own)
                  record)
              (Move source))))

(test-case "mut の共通欄から expected imm 欄へ潜り、内側 Owned を除く"
  (check-equal?
   (remainder-removal-shape mut-actual imm-expected)
   '((a nested #f ((o drop #f)))))
  (check-equal? (remainder-target-type mut-actual imm-expected) target-type)
  (check-equal? (remainder-removal-shape mut-actual target-type)
                '((a nested #f ((o drop #f)))))
  (check-true (rsd-eligible? mut-actual imm-expected))
  ;; Core の owned-narrowing-kind はこの Task でも変えない。
  (check-equal? (owned-narrowing-kind mut-actual imm-expected compat?)
                `(drop-obligation ,mut-actual ,imm-expected)))

(test-case "最上位の注釈付き Let は mut から imm への RSD を挿入する"
  (define result (elab (let-conversion-program)))
  (check-false (diagnostic-id-of result) (format "elab が拒否: ~s" result))
  (match-define (list core function-type row callables) result)
  (define erased (erase-core core))
  (check-equal? (find-rsd erased) (list mut-actual target-type))
  (check-equal? (core-type-of erased '() callables) (list function-type row)))

(test-case "Apply 引数は mut から imm への RSD を挿入する"
  (define result (elab (apply-conversion-program)))
  (check-false (diagnostic-id-of result) (format "elab が拒否: ~s" result))
  (match-define (list core function-type row callables) result)
  (define erased (erase-core core))
  (check-equal? (find-rsd erased) (list mut-actual target-type))
  (check-equal? (core-type-of erased '() callables) (list function-type row)))

(test-case "両経路の RSD は token を Dropped にし変換後の値を imm にする"
  (define value
    '(Rec ((a mut (Rec ((o imm (OwnedLeaf (tok 81) (resource 81)))
                       (x imm 7)))))))
  (for ([program (in-list (list (let-conversion-program)
                                (apply-conversion-program)))])
    (match-define (list core _function-type _row callables)
      (match (elab program)
        [(list core function-type row callables)
         (list core function-type row callables)]
        [`(err ,diagnostic)
         (fail-check (format "変換 fixture が拒否された: ~s" diagnostic))]))
    (define execution (execution-core core callables))
    (define application `(Apply ,execution (Move 0)))
    (define start
      `(cfg (Scope (0) ,application)
            ((0 ,value (declared ,mut-actual)))
            ((0 Available))
            (((tok 81) Available))
            ()))
    (define-values (configs rules) (trace-g2 start))
    (check-not-false (member 'R-DischargeRemainder rules))
    (check-config-trace configs callables imm-expected)
    (check-equal? (configuration-tokens (last configs))
                  '(((tok 81) Dropped)))
    (define final-core (erase-core (configuration-core (last configs))))
    (check-true
     (let walk ([term final-core])
       (match term
         [`(Rec ,fields)
          (or (match (assoc 'a fields)
                [`(a imm ,_) #t]
                [_ #f])
              (ormap walk fields))]
         [(? list?) (ormap walk term)]
         [_ #f]))
     (format "変換後の欄 a が imm でない: ~s" final-core))))

(test-case "expected の mut 欄は非同値な Owned 損失を受理しない"
  (define expected-mut
    '(Record ((a (Record ((x Int imm))) mut))))
  (check-equal? (remainder-removal-shape mut-actual expected-mut) '())
  (check-false (rsd-eligible? mut-actual expected-mut))
  (check-equal?
   (diagnostic-id-of
    (elab `(Fn ((source ,mut-actual)) Int ()
             (Let (record let ,expected-mut) (Move source) 1))))
   "E-TYP-012"))

(test-case "optional の actual 欄から必須欄へは再帰せず、必須から optional へは再帰する"
  (define actual-optional
    '(Record ((a (Record ((o (Owned Res) imm) (x Int imm))) mut opt))))
  (define expected-required
    '(Record ((a (Record ((x Int imm))) imm))))
  (define actual-required
    '(Record ((a (Record ((o (Owned Res) imm) (x Int imm))) mut))))
  (define expected-optional
    '(Record ((a (Record ((x Int imm))) imm opt))))
  (check-equal? (remainder-removal-shape actual-optional expected-required) '())
  (check-false (rsd-eligible? actual-optional expected-required))
  (check-equal?
   (remainder-removal-shape actual-required expected-optional)
   '((a nested #f ((o drop #f)))))
  (check-true (rsd-eligible? actual-required expected-optional)))

(test-case "適格な drop-obligation と nested-drop は全て実際に欄を除く"
  (for* ([actual (in-list eligible-universe)]
         [expected (in-list eligible-universe)]
         #:when (compat? actual expected))
    (define kind
      (owned-narrowing-kind/for-elaboration actual expected compat?))
    (when (or (drop-obligation? kind) (eq? kind 'nested-drop))
      (check-true (rsd-eligible? actual expected)
                  (format "不適格な kind ~s: ~s => ~s" kind actual expected)))))

(test-case "RSD の Proof target は nested 欄を imm にして shape を保つ"
  (check-equal? (remainder-target-type mut-actual imm-expected) target-type)
  (check-true (rsd-proof-pair-ok? mut-actual target-type compat?))
  (check-false (rsd-proof-pair-ok?
                mut-actual
                '(Record ((a (Record ((x Int imm))) mut)))
                compat?)))

(test-case "mut 欄を含む RSD の一歩で shape の drop token だけを除く"
  (define proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,mut-actual ,target-type)))
  (define value
    '(Rec ((a mut (Rec ((o imm (OwnedLeaf (tok 82) (resource 82)))
                       (x imm 7)))))))
  (define start
    `(cfg (Discharge ,proof ,value) () () (((tok 82) Available)) ()))
  (check-true (redex-match? G2m v value)
              (format "手書きの mut 欄値が G2m の value でない: ~s" value))
  (match (raw-steps-g2/named start)
    [(list (list 'R-DischargeRemainder next))
     (check-equal?
      (configuration-core next)
      '(Rec ((a imm (Rec ((x imm 7)))))))
     (check-equal? (configuration-tokens next) '(((tok 82) Dropped))
                   (format "RSD 後の構成: ~s" next))]
    [other (fail-check (format "mut 欄の除去が一歩で進まない: ~s" other))])
  (define shape (remainder-removal-shape mut-actual imm-expected))
  (check-equal? shape '((a nested #f ((o drop #f))))))

(test-case "T-Discharge は適格で target が一致する RSD Proof だけを受理する"
  (define (owner-for-target target)
    (define proof
      `(ProofRep (Reserved o-narrow)
                 (RemainderSafelyDropped ,mut-actual ,target)))
    (define sink-type `(NFn (,target) Int () () () User))
    (define owner-type `(NFn (,sink-type ,mut-actual) Int () () () User))
    (values
     `(Lam User owner (sink p)
        (Handle (Return owner Int) (answer -> answer)
          (Scope ()
            (Let (x let ,mut-actual) p
              (Apply sink (Discharge ,proof (Forward x)))))))
     `((owner ,owner-type) (sink ,sink-type))))
  (define-values (valid-owner valid-callables)
    (owner-for-target target-type))
  (check-equal? (core-type-of valid-owner '() valid-callables)
                (list (second (assoc 'owner valid-callables)) '()))
  (define target-mut '(Record ((a (Record ((x Int imm))) mut))))
  (define-values (invalid-owner invalid-callables)
    (owner-for-target target-mut))
  (check-equal?
   (diagnostic-id (core-type-of/diagnostic invalid-owner '() invalid-callables))
   "E-OWN-028")
  (define-values (identity-owner identity-callables)
    (owner-for-target mut-actual))
  (check-equal? (core-type-of identity-owner '() identity-callables)
                (list (second (assoc 'owner identity-callables)) '()))
  (check-true (rsd-proof-pair-ok? mut-actual mut-actual compat?))
  (define identity-proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,mut-actual ,mut-actual)))
  (define identity-value
    '(Rec ((a mut (Rec ((o imm (OwnedLeaf (tok 83) (resource 83)))
                       (x imm 7)))))))
  (define identity-start
    `(cfg (Discharge ,identity-proof ,identity-value)
          () () (((tok 83) Available)) ()))
  (define-values (identity-configs identity-rules)
    (trace-g2 identity-start))
  (check-equal? identity-rules '(R-DischargeRemainder))
  (check-config-trace identity-configs '() mut-actual)
  (check-equal? (configuration-tokens (last identity-configs))
                '(((tok 83) Available)))
  (for* ([actual (in-list eligible-universe)]
         [expected (in-list eligible-universe)]
         #:when (and (compat? actual expected)
                     (rsd-eligible? actual expected)))
    (define target (remainder-target-type actual expected))
    (check-true (rsd-proof-pair-ok? actual target compat?)
                (format "生成 target が Proof gate を通らない: ~s => ~s"
                        actual target))))

(test-case "RSD 対象の Owned token は live borrow の root から Move できない"
  (define (core rho)
    `(Scope (1)
       (Let (borrowed let (Borrowed ,mut-actual ,rho)) (Borrow 1)
         (Move 1))))
  (define ir (build-region-ir (core 0)))
  (define rho (region->rho ir (region-at ir '(0 0))))
  (define result
    (type-of/raw (annotate-regions (core rho) ir)
                 (list (list 1 mut-actual)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'move-borrowed))

(test-case "借用経由の copy-out は Owned 欄を含む値を複製しない"
  (check-false (copy-out-ok? mut-actual))
  (define core `(Scope (1) (Read (Borrow 1))))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw (annotate-regions core ir)
                 (list (list 1 mut-actual)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'read-uncopyable-payload))

(test-case "BorrowMutRef の Assign は Owned token を含む payload を作らない"
  (define core
    '(Scope (1)
       (Assign (ProjBorrow (BorrowMut 1) a) 0)))
  (define place-type `(Record ((a ,inner-actual mut))))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw (annotate-regions core ir)
                 (list (list 1 place-type)) '() '()
                 (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-owned-payload))

(test-case "適格でない重複欄の対は fail-closed で RSD に使えない"
  (define duplicate-actual
    '(Record ((a (Owned Res) imm) (a Int imm))))
  (define duplicate-expected '(Record ((a Int imm))))
  (check-false (rsd-eligible? duplicate-actual duplicate-expected)))

(test-case "Union 判定で各 member の drop と nested-drop の適格性を保つ"
  (define saw-union? #f)
  (for* ([actual (in-list eligible-universe)]
         [expected (in-list eligible-universe)]
         #:when (and (compat? actual expected)
                     (not (type-equiv? actual expected)))
         [actual-union
          (in-value (normalize-type `(Union ,actual ,expected)))]
         #:when (union-type? actual-union))
    (for ([expected-type (in-list (list expected
                                        (normalize-type
                                         `(Union ,expected ,actual))))])
      (when expected-type
        (define kind
          (owned-narrowing-kind/for-elaboration
           actual-union expected-type compat?))
        (when (eq? kind 'ok)
          (set! saw-union? #t)
          (for ([member (in-list (union-members actual-union))])
            (check-true
             (for/or ([candidate (in-list (union-members expected-type))])
               (and (compat? member candidate)
                    (accepted-member-kind?
                     member candidate
                     (owned-narrowing-kind/for-elaboration
                      member candidate compat?))))
             (format "Union の member に不適格な判定が残る: ~s => ~s"
                     member expected-type)))))))
  (check-true saw-union? "Union の適格性 property が一度も実行されなかった"))

#lang racket

(require racket/list
         racket/match
         racket/set
         rackunit
         redex/reduction-semantics
         "../compat.rkt"
         "../borrow.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../obs.rkt"
         "../ownership.rkt"
         "../pr-lang.rkt"
         "../pr-machine.rkt"
         "../pr-obs.rkt"
         "../region.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define option-owned '(Option (Owned Res)))
(define zero-record-type
  `(Record ((carry ,option-owned imm) (kept Int imm))))
(define fuel 1000)

(define (field label type mode optional?)
  (if optional?
      (list label type mode 'opt)
      (list label type mode)))

(define (boolean-patterns length)
  (for/list ([mask (in-range (expt 2 length))])
    (for/list ([index (in-range length)])
      (bitwise-bit-set? mask index))))

(define (mode-patterns length)
  (for/list ([mask (in-range (expt 2 length))])
    (for/list ([index (in-range length)])
      (if (bitwise-bit-set? mask index) 'mut 'imm))))

(define zero-spec '(zero))

(define top-specs
  (append
   (for*/list ([optional? (in-list (boolean-patterns 1))]
               [present? (in-list (boolean-patterns 1))]
               [modes (in-list (mode-patterns 1))])
     (list 'top 1 optional? present? modes))
   ;; 1 欄は各軸の全組合せ、2 欄は必須と optional、present と Absent、
   ;; imm と mut の混在、および欄順序を確かめる標本である。
   '((top 2 (#f #f) (#t #t) (imm mut))
     (top 2 (#t #t) (#f #f) (imm imm))
     (top 2 (#f #t) (#t #f) (mut imm))
     (top 2 (#t #f) (#f #t) (imm mut)))))

(define nested-specs
  (append
   (for*/list ([optional? (in-list (boolean-patterns 1))]
               [present? (in-list (boolean-patterns 1))]
               [modes (in-list (mode-patterns 1))]
               [outer-optional? (in-list '(#f #t))]
               [expected-outer-optional? (in-list '(#f #t))]
               [outer-state (in-list '(present absent))])
     (list 'nested 1 optional? present? modes
           outer-optional? expected-outer-optional? outer-state))
   ;; 1 欄は各軸の全組合せ、2 欄は必須と optional、present と Absent、
   ;; imm と mut の混在、および欄順序を確かめる標本である。
   '((nested 2 (#f #f) (#t #t) (imm mut) #f #t present)
     (nested 2 (#t #t) (#t #f) (imm mut) #t #t present)
     (nested 2 (#f #f) (#f #f) (mut imm) #t #t absent)
     (nested 2 (#t #t) (#f #f) (imm mut) #t #t present)
     (nested 2 (#t #t) (#t #t) (imm mut) #f #f present))))

(define all-specs (append (list zero-spec) top-specs nested-specs))

(define (spec-exclusion spec)
  (match spec
    ['(zero) #f]
    [`(top ,_ ,optional? ,present? ,_)
     (and (for/or ([optional (in-list optional?)]
                   [present (in-list present?)])
            (and (not optional) (not present)))
          'required-removal-absent)]
    [`(nested ,_ ,optional? ,present? ,_ ,outer-optional?
              ,expected-outer-optional? ,outer-state)
     (cond
       [(and outer-optional? (not expected-outer-optional?))
        'optional-to-required]
       [(and (eq? outer-state 'absent) (not outer-optional?))
        'required-outer-absent]
       [(and (eq? outer-state 'present)
             (for/or ([optional (in-list optional?)]
                      [present (in-list present?)])
               (and (not optional) (not present))))
        'required-removal-absent]
       [else #f])]))

(define (owned-value token)
  `(Construct ,option-owned some (OwnLeaf (resource ,token))))

(define (count-producers term)
  (cond
    [(equal? term '(producer-owned)) 1]
    [(pair? term) (apply + (map count-producers term))]
    [else 0]))

(define (producer-source type fields serial first-token)
  (define arity (count-producers fields))
  (define function-name (string->symbol (format "source-~a" serial)))
  (define parameters
    (for/list ([index (in-range arity)])
      (string->symbol (format "raw-~a-~a" serial index))))
  (define places
    (for/list ([index (in-range arity)])
      (string->symbol (format "place-~a-~a" serial index))))
  (define next-index 0)
  (define (replace-producers term)
    (cond
      [(equal? term '(producer-owned))
       (define place (list-ref places next-index))
       (set! next-index (add1 next-index))
       `(Move ,place)]
      [(pair? term) (map replace-producers term)]
      [else term]))
  (define record-fields (replace-producers fields))
  (define body
    `(Handle (Return source-boundary ,type)
             (return-value -> return-value)
             (Scope ()
               ,(for/fold ([inner `(Let (record let ,type)
                                        (Rec ,record-fields)
                                        (Move record))])
                          ([parameter (in-list (reverse parameters))]
                           [place (in-list (reverse places))])
                  `(Let (,place let ,option-owned) ,parameter ,inner)))))
  (define callables
    `((,function-name
       (NFn ,(make-list arity option-owned) ,type () (Own) () User))))
  (values
   `(Apply (Lam User ,function-name ,parameters ,body)
           ,@(for/list ([index (in-range arity)])
               (owned-value (+ first-token index))))
   callables))

(define (removed-fields optional? present? modes first-token)
  (for/list ([optional (in-list optional?)]
             [present (in-list present?)]
             [mode (in-list modes)]
             [index (in-naturals)])
    (define label (string->symbol (format "drop-~a" index)))
    (define token (+ first-token index))
    (list (field label option-owned mode optional)
          (list label mode
                (if present
                    '(producer-owned)
                    `(Absent ,option-owned)))
          (and present token))))

(define (make-case spec serial)
  (define first-token (+ 1000 (* serial 10)))
  (match spec
    ['(zero)
     (define actual zero-record-type)
     (define-values (source callables)
       (producer-source actual
                        '((carry imm (producer-owned)) (kept imm 17))
                        serial first-token))
     (hash 'group 'zero 'actual actual 'expected actual 'source source
           'callables callables
           'token-ids '(0) 'removed-token-ids '()
           'removal-count 0 'sink? #t 'outer-state 'n/a
           'inner-optional '() 'inner-present '())]
    [`(top ,count ,optional? ,present? ,modes)
     (define removed
       (removed-fields optional? present? modes first-token))
     (define actual
       (normalize-type
        `(Record ,(cons '(kept Int imm) (map first removed)))))
     (define expected '(Record ((kept Int imm))))
     (define-values (source callables)
       (producer-source actual
                        (cons '(kept imm 17) (map second removed))
                        serial first-token))
     (define token-ids
       (range (length (filter values (map third removed)))))
     (hash 'group 'top 'actual actual 'expected expected 'source source
           'callables callables
           'token-ids token-ids 'removed-token-ids token-ids
           'removal-count count 'sink? #f 'outer-state 'n/a
           'inner-optional optional? 'inner-present present?)]
    [`(nested ,count ,optional? ,present? ,modes
              ,outer-optional? ,expected-outer-optional? ,outer-state)
     (define removed
       (removed-fields optional? present? modes first-token))
     (define actual-inner
       (normalize-type
        `(Record ,(cons '(inner-kept Int imm) (map first removed)))))
     (define expected-inner '(Record ((inner-kept Int imm))))
     (define actual
       (normalize-type
        `(Record ((kept Int imm)
                  ,(field 'box actual-inner 'imm outer-optional?)))))
     (define expected
       (normalize-type
        `(Record ((kept Int imm)
                  ,(field 'box expected-inner 'imm expected-outer-optional?)))))
     (define inner-source
       `(Rec ,(cons '(inner-kept imm 23) (map second removed))))
     (define box-source
       (if (eq? outer-state 'absent)
           `(Absent ,actual-inner)
           inner-source))
     (define-values (source callables)
       (producer-source actual
                        `((kept imm 17) (box imm ,box-source))
                        serial first-token))
     (define token-ids
       (if (eq? outer-state 'absent)
           '()
           (range (length (filter values (map third removed))))))
     (hash 'group 'nested 'actual actual 'expected expected 'source source
           'callables callables
           'token-ids token-ids 'removed-token-ids token-ids
           'removal-count count 'sink? #f 'outer-state outer-state
           'inner-optional optional? 'inner-present present?)]))

(define included-specs (filter (lambda (spec) (not (spec-exclusion spec))) all-specs))
(define excluded-specs (filter spec-exclusion all-specs))
(define cases
  (for/list ([spec (in-list included-specs)] [serial (in-naturals)])
    (make-case spec serial)))

(define (count-group group)
  (count (lambda (case) (eq? (hash-ref case 'group) group)) cases))

(define (count-excluded reason)
  (count (lambda (spec) (eq? (spec-exclusion spec) reason)) excluded-specs))

(define (shape-drop-count shape)
  (for/sum ([entry (in-list shape)])
    (match entry
      [`(,_ drop ,_) 1]
      [`(,_ nested ,_ ,child) (shape-drop-count child)]
      [_ 0])))

(define (configuration-core configuration)
  (match configuration [`(cfg ,core ,_ ,_ ,_ ,_) core]))

(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (target-core configuration)
  (match configuration [`(pcfg ,core ,_ ,_ ,_) core]))

(define (trace-core core)
  (let loop ([current (inject-g2 core)] [configs '()] [rules '()] [steps 100])
    (when (zero? steps)
      (error 'trace-core "評価 fuel を使い切った: ~s" current))
    (define next (raw-steps-g2/named current))
    (check-true (<= (length next) 1)
                (format "Core が非決定的: ~s" current))
    (match next
      ['() (values (append configs (list current)) rules)]
      [(list (list rule after))
       (loop after (append configs (list current))
             (append rules (list rule)) (sub1 steps))])))

(define (trace-target target)
  (let loop ([current (inject-pr target)] [configs '()] [rules '()] [steps 100])
    (when (zero? steps)
      (error 'trace-target "PR 評価 fuel を使い切った: ~s" current))
    (define next (apply-reduction-relation/tag-with-names -->pr/rules current))
    (check-true (<= (length next) 1)
                (format "PR が非決定的: ~s" current))
    (match next
      ['() (values (append configs (list current)) rules)]
      [(list (list rule after))
       (loop after (append configs (list current))
             (append rules (list (string->symbol rule))) (sub1 steps))])))

(define (check-core-trace configs callables)
  (define rows
    (for/list ([configuration (in-list configs)] [index (in-naturals)])
      (define row
        (runtime-row configuration callables 'Unit))
      (check-not-false row
                       (format "runtime row が無い config ~a: ~s"
                               index configuration))
      (check-true (config-ok? configuration callables 'Unit row)
                  (format "config-ok? が偽の config ~a: ~s"
                          index configuration))
      row))
  (for ([before (in-list rows)] [after (in-list (cdr rows))]
        [index (in-naturals)])
    (check-true (row-subset? after before)
                (format "Core の row が増えた config ~a: ~s -> ~s"
                        index before after))))

(define (sorted-token-entries tokens)
  (sort tokens < #:key (lambda (entry) (second (first entry)))))

(define (token-state configuration token)
  (match (assoc `(tok ,token) (configuration-tokens configuration))
    [(list _ state) state]
    [_ #f]))

(define (dropped-transition-count configs token)
  (for/sum ([before (in-list configs)] [after (in-list (cdr configs))]
            #:when (and (not (eq? (token-state before token) 'Dropped))
                        (eq? (token-state after token) 'Dropped)))
    1))

(define (dropped-at-rsd configs rules)
  (for/sum ([rule (in-list rules)] [index (in-naturals)]
            #:when (eq? rule 'R-DischargeRemainder))
    (define before (configuration-tokens (list-ref configs index)))
    (define after (configuration-tokens (list-ref configs (add1 index))))
    (for/sum ([entry (in-list after)]
              #:when (and (eq? (second entry) 'Dropped)
                          (not (match (assoc (first entry) before)
                                 [(list _ state) (eq? state 'Dropped)]
                                 [_ #f]))))
      1)))

(define (pr-drop-count rules)
  (count (lambda (rule) (eq? rule 'R-PR-Drop)) rules))

(define (lower-ok core)
  (define-values (status result) (lower core 'racket-cs))
  (check-eq? status 'ok (format "lower が失敗: ~s" result))
  result)

(define (lower-value-ok value)
  (define-values (status result) (lower-value value 'racket-cs))
  (check-eq? status 'ok (format "lower-value が失敗: ~s" result))
  result)

(define (case-core case)
  (define actual (hash-ref case 'actual))
  (define expected (hash-ref case 'expected))
  (define source (hash-ref case 'source))
  (define proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,actual ,expected)))
  (define continuation
    (if (hash-ref case 'sink?)
        '(Yield 17 (Drop (Move result)))
        '(Yield 17 unit)))
  `(Scope ()
     (Let (result let ,expected)
       (Discharge ,proof ,source)
       ,continuation)))

(test-case "RSD の有限宇宙の件数と除外理由を固定する"
  (check-equal? (length all-specs) 82)
  (check-equal? (length cases) 42)
  (check-equal? (count-group 'zero) 1)
  (check-equal? (count-group 'top) 10)
  (check-equal? (count-group 'nested) 31)
  (check-equal? (count-excluded 'required-removal-absent) 8)
  (check-equal? (count-excluded 'required-outer-absent) 16)
  (check-equal? (count-excluded 'optional-to-required) 16)
  (check-equal? (length excluded-specs) 40))

(test-case "RSD の Core と PR の有限性質を全 42 組で確かめる"
  (for ([case (in-list cases)] [index (in-naturals)])
    (define actual (hash-ref case 'actual))
    (define expected (hash-ref case 'expected))
    (define shape (remainder-removal-shape actual expected))
    (define group (hash-ref case 'group))
    (define label (format "case ~a (~a): ~s => ~s" index group actual expected))
    (check-true (compat? actual expected) label)
    (check-equal? (shape-drop-count shape) (hash-ref case 'removal-count) label)
    (check-equal?
     (owned-narrowing-kind actual expected compat?)
     (if (eq? group 'zero)
         'ok
         `(drop-obligation ,actual ,expected))
     label)
    (when (eq? group 'zero)
      ;; 等しい型対では Proof は受理され、空 shape の R-DischargeRemainder が
      ;; 0 token を除去する。残った leaf は続く Drop が回収する。
      (check-equal? shape '() label))
    (define core (case-core case))
    (define callables (hash-ref case 'callables))
    (define typed (core-type-of core '() callables))
    (unless (and (list? typed) (pair? typed) (eq? (first typed) 'Unit))
      (error 'remainder-drop-property-test
             "Core が型付けできない (~a): ~s ; type=~s ; raw=~s"
             label core typed
             (type-of/raw core '() callables '() (empty-region-ctx))))
    (define target (lower-ok core))
    (check-true (set-member? (effect-kinds-of target) 'own) label)

    (define-values (core-configs core-rules) (trace-core core))
    (check-core-trace core-configs callables)
    (check-true (redex-match? G2m v (configuration-core (last core-configs)))
                label)
    (check-not-false (member 'R-DischargeRemainder core-rules) label)
    (check-equal? (dropped-at-rsd core-configs core-rules)
                  (length (hash-ref case 'removed-token-ids))
                  label)

    (define token-ids (hash-ref case 'token-ids))
    (define final-tokens (configuration-tokens (last core-configs)))
    (check-equal?
     (sorted-token-entries final-tokens)
     (sorted-token-entries
      (for/list ([token (in-list token-ids)])
        (list `(tok ,token) 'Dropped)))
     (format "Scope 後の token は全て一度だけ Dropped: ~a" label))
    (for ([token (in-list token-ids)])
      (check-equal? (dropped-transition-count core-configs token) 1
                    (format "token ~a の drop は一度だけ: ~a" token label)))
    (check-equal? (length (filter (lambda (entry)
                                    (eq? (second entry) 'Dropped))
                                  final-tokens))
                  (length token-ids)
                  label)

    (define-values (target-configs target-rules) (trace-target target))
    (check-true (redex-match? PR pv (target-core (last target-configs))) label)
    (define core-drops
      (length (filter (lambda (entry) (eq? (second entry) 'Dropped))
                      final-tokens)))
    (check-equal? core-drops (pr-drop-count target-rules) label)
    (define core-observation (obs-eval-g2 core 1 fuel))
    (define target-observation (obs-eval-pr target 1 fuel))
    (check-equal? (second core-observation) 'observed label)
    (check-equal?
     target-observation
     (list (map lower-value-ok (first core-observation))
           (second core-observation))
     label)

    (when (and (eq? group 'nested)
               (= (hash-ref case 'removal-count) 1)
               (eq? (hash-ref case 'outer-state) 'present)
               (equal? (hash-ref case 'inner-optional) '(#t))
               (equal? (hash-ref case 'inner-present) '(#f)))
      ;; Present な外側欄の内側で optional Owned 欄が Absent。
      ;; PR は PMatch の none 枝を通り、Core と PR の実 drop 数はともに 0。
      (check-equal? token-ids '() label)
      (check-equal? core-drops 0 label)
      (check-equal? (pr-drop-count target-rules) 0 label))))

#lang racket

(require rackunit
         racket/list
         racket/match
         "../compat.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../obs.rkt"
         "../ownership.rkt"
         "../pr-obs.rkt"
         "../search.rkt"
         "../type-equiv.rkt"
         "../typing.rkt"
         "../validators.rkt")

(define option-owned '(Option (Owned Res)))
(define wide-record
  `(Record ((x ,option-owned imm) (y Int imm))))
(define narrow-record '(Record ((y Int imm))))
(define wide-function `(NFn (Unit) ,wide-record (Own) ()))
(define narrow-function `(NFn (Unit) ,narrow-record (Own) ()))

(define (elaborate-ok source)
  (match (elab source)
    [(list core type row callables) (list core type row callables)]
    [other (fail-check (format "elaborate に失敗した: ~s" other))]))

(define (tree-contains? tree predicate)
  (or (predicate tree)
      (and (pair? tree)
           (or (tree-contains? (car tree) predicate)
               (tree-contains? (cdr tree) predicate)))))

(define (tree-count tree predicate)
  (+ (if (predicate tree) 1 0)
     (if (pair? tree)
         (+ (tree-count (car tree) predicate)
            (tree-count (cdr tree) predicate))
         0)))

(define (contains-rsd? tree)
  (tree-contains?
   tree
   (lambda (node)
     (match node
       [`(Discharge (ProofRep (Reserved o-narrow)
                             (RemainderSafelyDropped ,_ ,_)) ,_) #t]
       [_ #f]))))

(define (find-adapters tree)
  (match tree
    [`(Let (,name let ,actual) ,closure
           (Curry (Lam User ,callable ,binders ,body) ,argument))
     #:when (equal? name argument)
     (cons (list name actual callable binders body closure)
           (append (find-adapters body) (find-adapters closure)))]
    [(? pair?) (append (find-adapters (car tree)) (find-adapters (cdr tree)))]
    [_ '()]))

(define (union-injection-summary tree)
  (match tree
    [`(UnionInject ,found ,member ,payload)
     (cons (list found member) (union-injection-summary payload))]
    [(? pair?) (append (union-injection-summary (car tree))
                       (union-injection-summary (cdr tree)))]
    [_ '()]))

(define (find-rsd-proof tree)
  (match tree
    [`(Discharge (ProofRep (Reserved o-narrow)
                          (RemainderSafelyDropped ,actual ,target)) ,_)
     (list actual target)]
    [(? pair?) (or (find-rsd-proof (car tree)) (find-rsd-proof (cdr tree)))]
    [_ #f]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 180])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-configs configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row (format "runtime-row が無い config ~a: ~s"
                                 index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "config-ok? が偽の config ~a: ~s"
                        index configuration))))

(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (check-rsd-run source token-count #:required-rule [required-rule #f])
  (match-define (list core type row callables) (elaborate-ok source))
  (define erased (erase-core core))
  (check-true (contains-rsd? erased))
  (check-equal? (core-type-of erased '() callables) (list type row))
  (define execution (execution-core core callables))
  (define-values (status target) (lower (erase-core execution) 'racket-cs))
  (check-eq? status 'ok)
  (check-equal? (compare-observations execution target 1) 'match)
  (define-values (configs rules)
    (trace-g2 `(cfg (Scope () ,execution) () () () ())))
  (check-configs configs callables type)
  (when required-rule (check-not-false (memq required-rule rules)))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (length (configuration-tokens (last configs))) token-count)
  (check-equal? (map second (configuration-tokens (last configs)))
                (make-list token-count 'Dropped))
  (void))

;; properties-lowering-test.rkt の compare-observations と同じく、source が timeout
;; した比較は discard とする。
(define limits (read-bounds))
(define source-fuel (bounds-fuel limits))
(define (lowered-value value)
  (define-values (status result) (lower-value value 'racket-cs))
  (and (eq? status 'ok) result))
(define (obs-eval-pr/adaptive target depth start-fuel)
  (let loop ([fuel start-fuel] [remaining 4])
    (define result (obs-eval-pr target depth fuel))
    (cond
      [(not (eq? (second result) 'timeout)) result]
      [(<= remaining 1) #f]
      [else (loop (* 2 fuel) (sub1 remaining))])))
(define (compare-observations core target depth)
  (define source (obs-eval-g2 core depth source-fuel))
  (cond
    [(eq? (second source) 'timeout) 'discard]
    [else
     (define target-result (obs-eval-pr/adaptive target depth source-fuel))
     (cond
       [(not target-result) 'discard]
       [(and (equal? (map lowered-value (first source))
                     (first target-result))
             (eq? (second source) (second target-result)))
        'match]
       [else 'mismatch])]))

(define (owned-option-value token)
  `(Construct some (Types (Owned Res)) (Apply acquire ,token)))

(define (wide-record-value token)
  `(Rec ((x imm ,(owned-option-value token)) (y imm 7))))

(define (resource-record-argument token)
  `(Apply (Fn ((x ,option-owned)) ,wide-record (Own)
              (Rec ((x imm (Move x)) (y imm 8))))
          ,(owned-option-value token)))

(define (check-rsd-elaboration? source)
  (match-define (list core type row callables) (elaborate-ok source))
  (define erased (erase-core core))
  (check-true (contains-rsd? erased))
  (check-equal? (core-type-of erased '() callables) (list type row)))

(test-case "返り値の内側の RSD adapter は実行時に token を Dropped にする"
  (define source
    `(Apply
      (Fn ((callback ,wide-function)) ,narrow-record (Own)
        (Let (adapted const ,narrow-function) callback
          (Apply adapted unit)))
      (Fn ((ignored Unit)) ,wide-record (Own) ,(wide-record-value 201))))
  (check-rsd-run source 1))

(test-case "引数の内側の RSD は Forward 後に資源を除去する"
  (define actual `(NFn (,narrow-record) Unit () ()))
  (define expected `(NFn (,wide-record) Unit () ()))
  (define source
    `(Apply
      (Fn ((callback ,actual)) Unit (Own)
        (Let (adapted const ,expected) callback
          (Apply adapted ,(resource-record-argument 202))))
      (Fn ((argument ,narrow-record)) Unit () unit)))
  (check-rsd-run source 1))

(test-case "rebuild-record の NFn 共通欄は adapter 内で RSD を使う"
  (define actual-record `(Record ((f ,wide-function imm))))
  (define expected-record `(Record ((f ,narrow-function imm))))
  (define source
    `(Apply
      (Fn ((record ,actual-record)) ,narrow-record (Own)
        (Let (converted const ,expected-record) record
          (Apply (Proj converted f) unit)))
      (Rec ((f imm
             (Fn ((ignored Unit)) ,wide-record (Own) ,(wide-record-value 203)))))))
  (check-rsd-run source 1))

(test-case "decompose の Record 枝は NFn adapter と RSD を作る"
  (define actual-left
    `(Record ((o ,option-owned imm) (f ,wide-function imm) (tag String imm))))
  (define actual-right
    `(Record ((o ,option-owned imm) (f ,wide-function imm) (tag Int imm))))
  (define actual-union `(Union ,actual-left ,actual-right))
  (define expected-record
    `(Record ((o ,option-owned imm) (f ,narrow-function imm)
              (tag (Union String Int) imm))))
  (define injector
    `(Fn ((record ,actual-left)) ,actual-union (Own) (Move record)))
  (define input
    `(Rec ((o imm ,(owned-option-value 204))
          (f imm (Fn ((ignored Unit)) ,wide-record (Own)
                     ,(wide-record-value 205)))
          (tag imm "left"))))
  (define source
    `(Apply (Fn ((value ,actual-union)) ,narrow-record (Own)
        (Let (converted const ,expected-record) (Move value)
          (Apply (Proj converted f) unit)))
      (Apply ,injector ,input)))
  (check-rsd-run source 2))

(test-case "Union の損失候補は損失の無い候補より後に選ぶ"
  (define owned-function `(NFn (Unit) ,wide-record (Own) ()))
  (define narrow-function `(NFn (Unit) ,narrow-record (Own) ()))
  (define actual
    `(Record ((o ,option-owned imm) (f ,owned-function imm) (tag Int imm))))
  (define lossy `(Record ((f ,narrow-function imm))))
  (define safe
    `(Record ((o ,option-owned imm) (f ,owned-function imm)
              (tag (Union Int Bool) imm))))
  (define safe-core
    `(Record ((o ,option-owned imm)
              (f (NFn (Unit) ,wide-record () (Own) () User) imm)
              (tag (Union Bool Int) imm))))
  (for ([members (in-list (list (list lossy safe) (list safe lossy)))])
    (define expected (normalize-type `(Union ,@members)))
    (check-true (compat? actual safe))
    (check-eq? (owned-narrowing-kind/for-elaboration actual safe compat?) 'ok)
    (define source
      `(Fn ((callback ,owned-function)) ,expected (Own)
           (Rec ((o imm ,(owned-option-value 209))
                 (f imm callback)
                 (tag imm 1)))))
    (match-define (list core type row callables) (elaborate-ok source))
    (check-equal? (core-type-of (erase-core core) '() callables)
                  (list type row))
    (check-true
     (for/or ([injection (in-list (union-injection-summary (erase-core core)))])
       (type-equiv? (second injection) safe-core))
     (format "members=~s, UnionInject 候補=~s"
             members
             (union-injection-summary (erase-core core))))))

(test-case "NFn 内側の RSD 候補は第 4 層で曖昧になる"
  (define wide
    '(Record ((x (Owned Res) imm) (y Int imm) (z Bool imm))))
  (define narrow-y '(Record ((y Int imm))))
  (define narrow-z '(Record ((z Bool imm))))
  (define wide-function `(NFn (Unit) ,wide (Own) ()))
  (define expected-y `(NFn (Unit) ,narrow-y (Own) ()))
  (define expected-z `(NFn (Unit) ,narrow-z (Own) ()))
  (define actual
    `(Record ((o ,option-owned imm) (f ,wide-function imm))))
  (define expected `(Union (Record ((f ,expected-y imm)))
                           (Record ((f ,expected-z imm)))))
  (check-equal?
   (match (elab `(Fn ((value ,actual)) ,expected (Own) (Move value)))
     [`(err ,diagnostic) (diagnostic-id diagnostic)]
     [other (fail-check (format "曖昧性を期待したが成功した: ~s" other))])
   (diagnostic-code-of 'elaborate 'ambiguous-union-member)))

(test-case "入れ子 adapter の RSD は閉包生成 row に漏れない"
  (define inner-wide `(NFn (Unit) ,wide-record (Own) ()))
  (define inner-narrow `(NFn (Unit) ,narrow-record (Own) ()))
  (define outer-actual `(NFn (,inner-narrow) Unit () ()))
  (define outer-expected `(NFn (,inner-wide) Unit () ()))
  (define source
    `(Fn ((callback ,outer-actual)) Unit ()
         (Let (adapted const ,outer-expected) callback unit)))
  (match-define (list core type row callables) (elaborate-ok source))
  (define erased (erase-core core))
  (check-true (contains-rsd? erased))
  (define adapters (find-adapters erased))
  (check-true (>= (length adapters) 2))
  (for ([adapter (in-list adapters)])
    (match-define (list _name _actual _callable _binders _body closure) adapter)
    (define-values (status lowered-closure) (lower closure 'racket-cs))
    (check-eq? status 'ok)
    (check-equal? (effect-kinds-of lowered-closure) (set)))
  (match-define (list _name _actual callable binders body _closure)
    (first adapters))
  (match (core-type-of `(Lam User ,callable ,binders ,body) '() callables)
    [(list `(NFn ,_ ,_ ,latent-in ,latent-out ,_ ,_) lambda-row)
     (check-equal? lambda-row '())
     (check-equal? latent-in '())
     (check-equal? latent-out '())]
    [other
     (fail-check (format "外側 adapter の ε_b が空: ~s" other))])
  (check-equal? (core-type-of erased '() callables) (list type row)))

(test-case "高階 adapter の Curry は R-CurryVal で進み全 config を保つ"
  (define inner-wide `(NFn (Unit) ,wide-record (Own) ()))
  (define inner-narrow `(NFn (Unit) ,narrow-record (Own) ()))
  (define outer-actual `(NFn (,inner-narrow) Unit (Own) ()))
  (define outer-expected `(NFn (,inner-wide) Unit (Own) ()))
  (define source
    `(Apply
      (Fn ((callback ,outer-actual)) Unit (Own)
        (Let (adapted const ,outer-expected) callback
          (Apply adapted
                 (Fn ((ignored Unit)) ,wide-record (Own)
                   ,(wide-record-value 213)))))
      (Fn ((inner ,inner-narrow)) Unit (Own)
        (Let (discard const ,narrow-record) (Apply inner unit) unit))))
  (check-rsd-run source 1 #:required-rule 'R-CurryVal))

(test-case "入れ子の Union 欄の資源引数 RSD を全 trace で検査する"
  (define field-union (normalize-type `(Union ,narrow-record String)))
  (define source-record `(Record ((payload ,wide-record imm))))
  (define target-record `(Record ((payload ,field-union imm))))
  (define actual `(NFn (,target-record) Unit () ()))
  (define expected `(NFn (,source-record) Unit () ()))
  (define argument
    `(Rec ((payload imm ,(wide-record-value 208)))))
  (define source
    `(Apply (Fn ((callback ,actual)) Unit (Own)
        (Let (adapted const ,expected) callback
          (Apply adapted ,argument)))
      (Fn ((argument ,target-record)) Unit () unit)))
  (check-rsd-run source 1))

(test-case "identity-conversion? は Core の損失判定を使う"
  (define wide-f `(NFn (Unit) ,wide-record () () () User))
  (define narrow-f `(NFn (Unit) ,narrow-record () () () User))
  (define context '())
  (check-false (identity-conversion? wide-f narrow-f context '()))
  (define safe '(Record ((a Int imm) (o (Owned Res) imm))))
  (check-equal? (identity-conversion? safe safe context '())
                (tag-compat? safe safe context))
  (define drop-actual
    '(Record ((a (Owned (Record ((h Int imm))) ) imm) (b Int imm))))
  (define drop-expected '(Record ((b Int imm))))
  (define target (remainder-target-type drop-actual drop-expected))
  (check-false (identity-conversion? drop-actual drop-expected context '()))
  (check-true (identity-conversion? target drop-expected context '())))

(test-case "Core の owned-narrowing-kind は NFn 内側損失を拒否する"
  (define wide-f `(NFn (Unit) ,wide-record () () () User))
  (define narrow-f `(NFn (Unit) ,narrow-record () () () User))
  (check-equal? (owned-narrowing-kind wide-f narrow-f compat?) 'reject))

(test-case "inner 文脈の NFn 損失は E-OWN-029 のまま"
  ;; 公開入力の NFn 成分は top で判定するため、Owned payload が inner 境界を固定する。
  (define wide-f `(Owned (NFn (Unit) ,wide-record () () () User)))
  (define narrow-f `(Owned (NFn (Unit) ,narrow-record () () () User)))
  (check-equal? (owned-narrowing-kind/for-elaboration wide-f narrow-f compat?)
                'reject))

(test-case "候補試行で未選択 adapter の callable と連番を残さない"
  (define wide-f `(NFn (Unit) ,wide-record (Own) ()))
  (define narrow-f `(NFn (Unit) ,narrow-record (Own) ()))
  (define safe-f `(NFn (Unit) ,wide-record ((Yield Int) Own) ()))
  (define source
    `(Fn ((f ,wide-f) (g ,wide-f)) ,narrow-f (Own)
         (Let (selected const (Union ,safe-f ,narrow-f)) f
           (Let (next const ,narrow-f) g next))))
  (match-define (list core _type _row callables) (elaborate-ok source))
  (check-equal? (map first callables) '(callable0 callable1))
  (check-equal? (length (find-adapters (erase-core core))) 1))

(test-case "PR lowering は引数と返り値の RSD adapter の観測を保つ"
  (for ([source
         (in-list
          (list
           `(Apply
             (Fn ((callback ,wide-function)) ,narrow-record (Own)
               (Let (adapted const ,narrow-function) callback
                 (Apply adapted unit)))
             (Fn ((ignored Unit)) ,wide-record (Own) ,(wide-record-value 211)))
           `(Apply
             (Fn ((callback (NFn (,narrow-record) Unit () ()))) Unit (Own)
               (Let (adapted const (NFn (,wide-record) Unit () ())) callback
                 (Apply adapted ,(resource-record-argument 212))))
             (Fn ((argument ,narrow-record)) Unit () unit))))])
    (match-define (list core _type _row callables) (elaborate-ok source))
    (define execution (execution-core core callables))
    (define-values (status target) (lower (erase-core execution) 'racket-cs))
    (check-eq? status 'ok)
    (check-equal? (compare-observations execution target 1) 'match)))

(test-case "NFn の引数と返り値で mut から imm への RSD を使う"
  (define mut-actual
    '(Record ((a (Record ((o (Owned Res) imm) (x Int imm))) mut))))
  (define imm-expected '(Record ((a (Record ((x Int imm))) imm))))
  (define actual-return `(NFn (Unit) ,mut-actual () ()))
  (define expected-return `(NFn (Unit) ,imm-expected () ()))
  (define return-source
    `(Fn ((callback ,actual-return)) ,expected-return () callback))
  (check-rsd-elaboration? return-source)
  (define actual-arg `(NFn (,imm-expected) Unit () ()))
  (define expected-arg `(NFn (,mut-actual) Unit () ()))
  (check-rsd-elaboration? `(Fn ((callback ,actual-arg)) ,expected-arg () callback)))

#lang racket

;; [REQ: OWN-004] Union の成分選択で損失の無い型を優先し、選んだ成分だけを RSD で包む。

(require rackunit
         racket/list
         racket/match
         "../compat.rkt"
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lexer.rkt"
         "../machine.rkt"
         "../ownership.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define option-owned '(Option (Owned Res)))
(define source-type
  `(Record ((a Int imm) (o ,option-owned imm))))
(define source-value
  `(Rec ((a imm 7)
         (o imm (Construct some (Types (Owned Res))
                           (Apply acquire 13))))))
(define drop-member '(Record ((a (Union Int String) imm))))
(define keep-member
  `(Record ((a (Union Int Bool) imm) (o ,option-owned imm))))
(define drop-union `(Union ,drop-member String))
(define nested-wide
  '(Record ((x Int imm) (o (Option (Owned Res)) imm))))
(define nested-narrow '(Record ((x Int imm))))
(define (nested-member value-type)
  `(Record ((value ,value-type imm) (bad (Option Int) imm))))
(define nested-free (nested-member `(Union ,nested-wide Bool)))
(define nested-lossy (nested-member `(Union ,nested-narrow Bool)))
(define nested-actual (nested-member nested-wide))
(define (nested-wide-value n)
  `(Rec ((x imm 7)
         (o imm (Construct some (Types (Owned Res)) (Apply acquire ,n))))))

(define (apply-function argument-type argument body result-type [row '(Own)])
  `(Apply (Fn ((argument ,argument-type)) ,result-type ,row ,body) ,argument))

(define (contains? predicate tree)
  (or (predicate tree)
      (and (pair? tree) (ormap (lambda (child) (contains? predicate child)) tree))))

(define (count-head head tree)
  (if (pair? tree)
      (+ (if (eq? (car tree) head) 1 0)
         (for/sum ([child (in-list tree)]) (count-head head child)))
      0))

(define (contains-rsd? tree)
  (contains? (lambda (node)
               (and (pair? node)
                    (eq? (car node) 'Discharge)
                    (regexp-match? #rx"RemainderSafelyDropped"
                                   (format "~s" node))))
             tree))

(define (nodes-with-head head tree)
  (append (if (and (pair? tree) (eq? (car tree) head)) (list tree) '())
          (if (pair? tree)
              (append-map (lambda (child) (nodes-with-head head child)) tree)
              '())))

(define (symbols-in tree)
  (cond [(symbol? tree) (list tree)]
        [(pair? tree) (append-map symbols-in tree)]
        [else '()]))

(define (union-inject-member core expected-union)
  (for/or ([node (in-list (reverse (nodes-with-head 'UnionInject core)))])
    (match node
      [`(UnionInject ,union-type ,member ,_)
       (and (type-equiv? union-type expected-union) member)]
      [_ #f])))

(define (checked source)
  (match (elab source)
    [(list core type row callables)
     (define erased (erase-core core))
     (check-equal? (core-type-of erased '() callables) (list type row)
                   (format "Core type mismatch for ~s" source))
     (list erased type row callables)]
    [`(err ,diagnostic)
     (fail-check (format "elaborate が拒否した: ~s" diagnostic))]))

(define (rejected-id source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [other (fail-check (format "elaborate が受理した: ~s" other))]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 160])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps
       (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (run-checked source)
  (match-define (list core type _row callables) (checked source))
  (define executable (execution-core core callables))
  (define-values (configs rules)
    (trace-g2 `(cfg (Scope () ,executable) () () () ())))
  (for ([configuration (in-list configs)])
    (define row (runtime-row configuration callables type))
    (check-not-false row)
    (check-true (config-ok? configuration callables type row)))
  (values (last configs) rules))

(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (make-application argument-type argument union-type)
  (apply-function argument-type argument `(Move argument) union-type))

(define (make-plain-application argument-type argument result-type)
  `(Apply (Fn ((argument ,argument-type)) ,result-type () argument) ,argument))

(define (make-union-value union-type member value)
  (apply-function member value '(Move argument) union-type))

(define (check-rsd-and-dropped source token-count)
  (match-define (list core _type _row _callables) (checked source))
  (check-true (contains-rsd? core))
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final))
                (make-list token-count 'Dropped))
  core)

(define nested-owned-wide
  '(Record ((x Int imm) (o (Option (Owned Res)) imm))))
(define nested-owned-narrow '(Record ((x Int imm))))
(define (nested-owned-record type)
  `(Record ((p ,type imm))))
(define (owned-option-value n)
  `(Construct some (Types (Owned Res)) (Apply acquire ,n)))

(test-case "層 4 は payload に RSD を挿入し、選んだ Union member の型で実行する"
  (define source (make-application source-type source-value drop-union))
  (define-values (core _type _row _callables) (apply values (checked source)))
  (define selected-member (union-inject-member core drop-union))
  (check-true (type-equiv? selected-member drop-member))
  (check-equal? (count-head 'Discharge core) 1)
  (check-true (contains-rsd? core))
  (match (findf (lambda (node)
                  (and (pair? node) (eq? (car node) 'Discharge)
                       (contains? (lambda (part)
                                    (and (pair? part)
                                         (eq? (car part) 'RemainderSafelyDropped)))
                                  node)))
                (nodes-with-head 'Discharge core))
    [`(Discharge (ProofRep (Reserved o-narrow)
                           (RemainderSafelyDropped ,actual ,target)) ,_)
     (check-equal? actual source-type)
     (check-equal? target '(Record ((a Int imm))))]
    [other (fail-check (format "RSD の鍵が成分の対でない: ~s" other))])
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "Record decompose の一つ目の対で外側残余を保持する"
  (define member-wide
    '(Record ((p (Record ((x Int imm) (o (Option (Owned Res)) imm))) imm))))
  (define member-plain
    '(Record ((p (Record ((x Int imm))) imm))))
  (define actual (normalize-type `(Union ,member-wide ,member-plain)))
  (define expected (nested-owned-record nested-owned-narrow))
  (define wide-value
    `(Rec ((p imm (Rec ((x imm 1) (o imm ,(owned-option-value 132))))))))
  (define source
    (make-application actual
                      (make-union-value actual member-wide wide-value)
                      expected))
  (check-rsd-and-dropped source 1)
  (void))

(test-case "Record decompose の二つ目の対で枝だけの Owned 残余を落とす"
  (define member-owned '(Record ((a Int imm) (extra (Option (Owned Res)) imm))))
  (define member-plain '(Record ((a Int imm))))
  (define actual (normalize-type `(Union ,member-owned ,member-plain)))
  (define expected '(Record ((a Int imm))))
  (define owned-value
    `(Rec ((a imm 1) (extra imm ,(owned-option-value 133)))))
  (define source
    (make-application actual
                      (make-union-value actual member-owned owned-value)
                      expected))
  (check-rsd-and-dropped source 1)
  (void))

(test-case "Union decompose は選んだ Union member へ RSD を挿入する"
  (define member-wide '(Record ((a Int imm) (extra (Option (Owned Res)) imm))))
  (define member-narrow '(Record ((a Int imm))))
  (define actual (normalize-type `(Union ,member-wide String)))
  (define expected (normalize-type `(Union ,member-narrow String)))
  (define wide-value
    `(Rec ((a imm 1) (extra imm ,(owned-option-value 134)))))
  (define source
    (make-application actual
                      (make-union-value actual member-wide wide-value)
                      expected))
  (define core (check-rsd-and-dropped source 1))
  (check-not-false
   (for/or ([node (in-list (nodes-with-head 'UnionInject core))])
     (match node
       [`(UnionInject ,union-type ,member ,_)
        (and (type-equiv? union-type expected)
             (type-equiv? member member-narrow))]
       [_ #f])))
  (void))

(test-case "imm Record の鎖にある Union 欄の入れ子 Owned 損失を RSD で回収する"
  (define actual `(Record ((p ,nested-owned-wide imm))))
  (define field-union (normalize-type `(Union ,nested-owned-narrow String)))
  (define expected `(Record ((p ,field-union imm))))
  (define value `(Rec ((p imm ,(nested-wide-value 145)))))
  (define source (make-application actual value expected))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (contains-rsd? core))
  (check-true (type-equiv? (union-inject-member core field-union)
                           nested-owned-narrow))
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "Record decompose は二つの対の Owned 残余を両方落とす"
  (define member-wide
    '(Record ((p (Record ((x Int imm) (o (Option (Owned Res)) imm))) imm)
              (extra (Option (Owned Res)) imm))))
  (define member-plain
    '(Record ((p (Record ((x Int imm))) imm))))
  (define actual (normalize-type `(Union ,member-wide ,member-plain)))
  (define expected (nested-owned-record nested-owned-narrow))
  (define wide-value
    `(Rec ((p imm (Rec ((x imm 1) (o imm ,(owned-option-value 135)))))
           (extra imm ,(owned-option-value 136)))))
  (define source
    (make-application actual
                      (make-union-value actual member-wide wide-value)
                      expected))
  (check-rsd-and-dropped source 2)
  (void))

(test-case "actual Union の Owned payload の曖昧な候補は順序によらず E-TYP-031"
  (define actual-left
    '(Record ((o (Owned (Union Int Bool)) imm))))
  (define actual-right
    '(Record ((o (Owned (Union Bool String)) imm))))
  (define expected-left
    '(Record ((o (Owned (Union Int (Union Bool String))) imm))))
  (define expected-right
    '(Record ((o (Owned (Union Int (Union Bool (Union String Unit)))) imm))))
  (define actual (normalize-type `(Union ,actual-left ,actual-right)))
  (for ([members (in-list
                  (list (list expected-left expected-right)
                        (list expected-right expected-left)))])
    (define expected (normalize-type `(Union ,@members)))
    (check-equal? (rejected-id
                   `(Fn ((argument ,actual)) ,expected (Own)
                        (Move argument)))
                  (diagnostic-code-of 'elaborate 'ambiguous-union-member))))

(test-case "損失のある tag-compat? 候補より、損失の無い作り直し候補を選ぶ"
  (define expected (normalize-type `(Union (Record ((a Int imm))) ,keep-member)))
  (define source (make-application source-type source-value expected))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (type-equiv? (union-inject-member core expected) keep-member))
  (check-false (contains-rsd? core))
  (define-values (final rules) (run-checked source))
  (check-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Available)))

(test-case "M1 の作り直し候補を M2 の損失候補より選ぶ"
  (define m1
    `(Record ((a (Union Int Bool) imm) (o ,option-owned imm))))
  (define m2 '(Record ((a (Union Int String) imm))))
  (define expected (normalize-type `(Union ,m1 ,m2)))
  (define-values (core _type _row _callables)
    (apply values (checked (make-application source-type source-value expected))))
  (check-true (type-equiv? (union-inject-member core expected) m1))
  (check-false (contains-rsd? core))
  (define-values (final _rules)
    (run-checked (make-application source-type source-value expected)))
  (check-equal? (map second (configuration-tokens final)) '(Available)))

(test-case "D/K では tag-compat? の損失候補 D より K を選ぶ"
  (define d '(Record ((a Int imm))))
  (define k keep-member)
  (define expected (normalize-type `(Union ,d ,k)))
  (check-true (tag-compat? source-type d))
  (check-false (tag-compat? source-type k))
  (check-equal? (owned-narrowing-kind source-type d compat?)
                `(drop-obligation ,source-type ,d))
  (check-equal? (owned-narrowing-kind source-type k compat?) 'ok)
  (define source (make-application source-type source-value expected))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (type-equiv? (union-inject-member core expected) k))
  (check-false (contains-rsd? core))
  (define-values (final _rules) (run-checked source))
  (check-equal? (map second (configuration-tokens final)) '(Available)))

(test-case "tag-compat? の層でも ok の成分を drop-obligation より先に選ぶ"
  (define actual
    `(Record ((a Int imm) (b Int imm) (o ,option-owned imm))))
  (define value
    '(Rec ((a imm 1)
           (b imm 2)
           (o imm (Construct some (Types (Owned Res)) (Apply acquire 13))))))
  (define safe `(Record ((a Int imm) (o ,option-owned imm))))
  (define lossy '(Record ((a Int imm))))
  (define expected (normalize-type `(Union ,safe ,lossy)))
  (check-true (tag-compat? actual safe))
  (check-true (tag-compat? actual lossy))
  (check-equal? (owned-narrowing-kind actual safe compat?) 'ok)
  (check-equal? (owned-narrowing-kind actual lossy compat?)
                `(drop-obligation ,actual ,lossy))
  (define-values (core _type _row _callables)
    (apply values (checked (make-application actual value expected))))
  (check-true (type-equiv? (union-inject-member core expected) safe))
  (check-false (contains-rsd? core)))

(test-case "入れ子の Union 欄では損失の無い成分を先に選ぶ"
  (define actual-value
    `(Rec ((value imm ,(nested-wide-value 13))
          (bad imm (Construct some (Types Int) 1)))))
  (for ([expected
         (in-list
          (list (normalize-type `(Union ,nested-lossy ,nested-free))
                (normalize-type `(Union ,nested-free ,nested-lossy))))])
    (define source (make-application nested-actual actual-value expected))
    (match-define (list core _type _row _callables) (checked source))
    (check-true (type-equiv? (union-inject-member core expected) nested-free))
    (check-false (contains-rsd? core))
    (define-values (final _rules) (run-checked source))
    (check-equal? (map second (configuration-tokens final)) '(Available))))

(test-case "入れ子の Union 欄で唯一の損失候補を RSD 付きで選ぶ"
  (define expected (normalize-type `(Union ,nested-lossy String)))
  (define source
    (make-application
     nested-actual
     `(Rec ((value imm ,(nested-wide-value 13))
           (bad imm (Construct some (Types Int) 1))))
     expected))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (type-equiv? (union-inject-member core expected) nested-lossy))
  (check-true (contains-rsd? core))
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "層 2 の入れ子損失候補と層 4 の root 損失候補は曖昧になる"
  (define actual
    '(Record ((value (Record ((x Int imm) (o (Option (Owned Res)) imm))) imm)
              (root (Option (Owned Res)) imm))))
  (define tier2-inner-loss
    '(Record ((value (Union (Record ((x Int imm))) Bool) imm)
              (root (Option (Owned Res)) imm))))
  (define tier4-root-loss
    '(Record ((value (Union (Record ((x Int imm)
                                     (o (Option (Owned Res)) imm))) Bool) imm))))
  (for ([members (in-list
                  (list (list tier2-inner-loss tier4-root-loss)
                        (list tier4-root-loss tier2-inner-loss)))])
    (define expected (normalize-type `(Union ,@members)))
    (check-equal?
     (rejected-id `(Fn ((argument ,actual)) ,expected (Own) (Move argument)))
     (diagnostic-code-of 'elaborate 'ambiguous-union-member))))

(test-case "同じ層 2 の候補は順序によらず ambiguous になる"
  (define actual '(Record ((a Int imm))))
  (define value '(Rec ((a imm 1))))
  (define left '(Record ((a (Union Int Bool) imm))))
  (define right '(Record ((a (Union Int String) imm))))
  (for ([members (in-list (list (list left right) (list right left)))])
    (check-equal?
     (rejected-id
      (make-plain-application actual value (normalize-type `(Union ,@members))))
     (diagnostic-code-of 'elaborate 'ambiguous-union-member))))

(test-case "同じ層 4 の候補は順序によらず ambiguous になる"
  (define actual source-type)
  (define left '(Record ((a (Union Int Bool) imm))))
  (define right '(Record ((a (Union Int String) imm))))
  (for ([members (in-list (list (list left right) (list right left)))])
    (check-equal?
     (rejected-id
      (make-application actual source-value
                        (normalize-type `(Union ,@members))))
     (diagnostic-code-of 'elaborate 'ambiguous-union-member))))

;; c3b で NFn 内側の残余損失を adapter 内の RSD で回収する。
(test-case "NFn の返り値の内側だけの損失を adapter 内の RSD で回収する"
  (define wide
    '(NFn (Unit) (Record ((x (Owned Res) imm) (y Int imm))) () ()))
  (define narrow
    '(NFn (Unit) (Record ((y Int imm))) () ()))
  (define expected `(Union ,narrow String))
  (define source `(Fn ((value ,wide)) ,expected () value))
  (match-define (list core type row callables) (checked source))
  (check-true (contains-rsd? core))
  (check-equal? (core-type-of core '() callables) (list type row)))

(test-case "Owned payload の内側の損失は互換性 gate で拒否する"
  (define actual
    (normalize-type `(Owned (Union ,nested-owned-wide Bool))))
  (define expected
    (normalize-type `(Owned (Union ,nested-owned-narrow Bool))))
  (check-false (compat? actual expected))
  (check-equal? (owned-narrowing-kind/for-elaboration actual expected compat?)
                'reject)
  (check-equal?
   (rejected-id `(Fn ((value ,actual)) ,expected (Own) (Move value)))
   (diagnostic-code-of 'elaborate 'type-mismatch)))

(test-case "mut 欄の内側の Union の損失は互換性 gate で拒否する"
  (define actual
    '(Record ((p (Union (Record ((x Int imm)
                                 (o (Option (Owned Res)) imm))) Bool) mut))))
  (define expected
    '(Record ((p (Union (Record ((x Int imm))) Bool) mut))))
  (check-false (compat? actual expected))
  (check-equal? (owned-narrowing-kind/for-elaboration actual expected compat?)
                'ok)
  (check-equal?
   (rejected-id `(Fn ((value ,actual)) ,expected (Own) (Move value)))
   (diagnostic-code-of 'elaborate 'type-mismatch)))

(test-case "Owned 残余と NFn adapter を Union 変換で回収する"
  (define actual-fn '(NFn ((Union Int Bool)) Unit () ()))
  (define expected-fn '(NFn (Int) Unit () ()))
  (define actual
    `(Record ((f ,actual-fn imm) (o ,option-owned imm))))
  (define target-member `(Record ((f ,expected-fn imm))))
  (define expected `(Union ,target-member String))
  (define expected-core
    '(Union (Record ((f (NFn (Int) Unit () () () User) imm))) String))
  (define value
    `(Rec ((f imm (Fn ((argument (Union Int Bool))) Unit () unit))
          (o imm (Construct some (Types (Owned Res))
                            (Apply acquire 59))))))
  (define source (make-application actual value expected))
  (match-define (list core result-type _row _callables) (checked source))
  (check-true (type-equiv? result-type expected-core)
              (format "結果型が期待 Union と一致しない: ~s / ~s"
                      result-type expected-core))
  (check-true (contains-rsd? core))
  (check-true
   (contains?
    (lambda (node)
      (match node
        [`(Let (,name let ,_) ,_
               (Curry (Lam User ,_ ,_ ,_) ,argument))
         (equal? name argument)]
        [_ #f]))
    core))
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "3 要素 Let は Union 注釈へ RSD を挿入する"
  (define expected drop-union)
  (define source
    (apply-function source-type source-value
                    `(Let (result let ,expected) (Move argument) result)
                    expected))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (contains-rsd? core))
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "check Eliminate は枝を Union へ inject する"
  (define expected '(Union Int String))
  (define source
    `(Apply (Fn ((value ,expected)) Unit () unit)
            (Eliminate (Construct true (Types))
              ((true () -> 1)
               (false () -> "s")))))
  (match-define (list core _type _row _callables) (checked source))
  (check-equal? (count-head 'UnionInject core) 2))

(test-case "synth Eliminate の Union 上界は Core の型付けと一致する"
  (define source
    '(Eliminate (Construct true (Types))
       ((true () -> 1)
        (false () -> "s"))))
  (match-define (list core type _row _callables) (checked source))
  (check-true (match type [`(Union ,_ ,_) #t] [_ #f]))
  (check-equal? (count-head 'UnionInject core) 2))

(test-case "明示型引数の Construct は Union expected の check を通る"
  (define source
    '(Apply (Fn ((value (Union Bool Int))) Unit () unit)
            (Construct true (Types))))
  (match-define (list core _type _row _callables) (checked source))
  (check-equal? (count-head 'UnionInject core) 1))

(test-case "Reassign は層 4 の成分へ RSD を挿入する"
  (define target (normalize-type `(Union ,drop-member String)))
  (define source
    `(Let (slot mut ,target)
          (Rec ((a imm 1)))
          (Let (argument let ,source-type)
               ,source-value
               (Reassign slot (Move argument)))))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (contains-rsd? core))
  (check-true (type-equiv? (union-inject-member core target) drop-member))
  (define-values (final _rules) (run-checked source))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "Reassign は層 3 の成分へ RSD を挿入する"
  (define source-member
    `(Record ((a (Union Int Bool) imm) (o ,option-owned imm))))
  (define target-member '(Record ((a (Union Int Bool) imm))))
  (define target `(Union ,target-member String))
  (define value
    `(Rec ((a imm 1)
          (o imm (Construct some (Types (Owned Res))
                            (Apply acquire 13))))))
  (define source
    (apply-function source-member value
                    `(Let (slot mut ,target) "s"
                         (Reassign slot (Move argument)))
                    'Unit '(Own Mutation)))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (contains-rsd? core))
  (check-true (type-equiv? (union-inject-member core target) target-member)
              (format "selected ~s in ~s" (union-inject-member core target) core))
  (define-values (final _rules) (run-checked source))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "Reassign に compatible な member が無ければ従来の key を保つ"
  (check-equal?
   (rejected-id
    '(Let (slot mut (Union Int String))
          1
          (Reassign slot (Construct true (Types)))))
   (diagnostic-code-of 'elaborate 'reassign-type-mismatch)))

(test-case "Reassign の NFn 損失を adapter 内の RSD で回収する"
  ;; c3b で代入時に作る NFn adapter の返り値損失を RSD で回収する。
  (define wide
    '(NFn (Unit) (Record ((x (Owned Res) imm) (y Int imm))) (Partial) ()))
  (define narrow
    '(NFn (Unit) (Record ((y Int imm))) (Partial) ()))
  (define source
    `(Fn ((callback ,wide)) Unit (Mutation)
         (Let (slot mut (Union ,narrow String))
              "s"
              (Reassign slot callback))))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (contains-rsd? core)))

(test-case "成分試行の union 名と後続 owned binder の連番を保つ"
  (define nested-source-type
    `(Record ((a (Record ((x Int imm) (y Int imm))) imm)
              (o ,option-owned imm))))
  (define member
    '(Record ((a (Record ((x (Union Int Bool) imm)
                          (y Int imm))) imm))))
  (define expected `(Union ,member String))
  (define source
    `(Fn ((argument ,nested-source-type))
         (NFn ((Owned Res)) Unit (Own) ()) (Own)
         (Let (chosen const ,expected)
              (Move argument)
              (Fn ((p (Owned Res))) Unit (Own) (Drop p)))))
  (match-define (list core _type _row _callables) (checked source))
  (define (generated-indices prefix)
    (sort
     (remove-duplicates
      (filter values
              (for/list ([name (in-list (symbols-in core))])
                (define matched
                  (regexp-match
                   (pregexp (format "^~a([0-9]+)(?:⟨[0-9]+⟩)?$" prefix))
                   (symbol->string name)))
                (and matched (string->number (second matched))))))
     <))
  (check-equal? (generated-indices "union") '(0 1))
  (check-equal? (generated-indices "owned") '(0 1)))

(test-case "Surface lowering 後の Union programme も Core で型付けできる"
  (define low
    (lower-surface
     (parse (lex/string 'src "fn widen(x: Int) -> Int | String { x }\nwiden(1)"))
     canonical-trait-env))
  (check-true (lowered? low))
  (define result (elab (lowered-term low)))
  (match result
    [(list core type row callables)
     (define-values (_final _rules) (run-checked (lowered-term low)))
     (check-equal? (core-type-of (erase-core core) '() callables)
                   (list type row))
     (check-true (match type [`(Union ,_ ,_) #t] [_ #f]))]
    [`(err ,diagnostic)
     (fail-check (format "Surface Union programme が拒否された: ~s" diagnostic))]))

(test-case "Rec の直接 check は合成失敗時も RSD の無い成分を先に選ぶ"
  (define wide '(Record ((x Int imm) (o (Option (Owned Res)) imm))))
  (define narrow '(Record ((x Int imm))))
  (define safe-member
    `(Record ((value (Union ,wide Bool) imm) (bad (Option Int) imm))))
  (define lossy-member
    `(Record ((value (Union ,narrow Bool) imm) (bad (Option Int) imm))))
  (define expected (normalize-type `(Union ,lossy-member ,safe-member)))
  (define wide-value
    `(Rec ((x imm 7)
           (o imm (Construct some (Types (Owned Res))
                             (Apply acquire 13))))))
  (define literal
    '(Rec ((value imm (Move argument)) (bad imm (Construct some 1)))))
  (define source
    (apply-function
     wide wide-value
     (apply-function expected literal 'unit 'Unit '())
     'Unit '(Own)))
  (match-define (list core _type _row _callables) (checked source))
  (check-false (contains-rsd? core))
  (check-true (type-equiv? (union-inject-member core expected) safe-member))
  (define-values (final _rules) (run-checked source))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "Rec の直接 check は合成可能でも入れ子の損失が無い成分を選ぶ"
  (define expected (normalize-type `(Union ,nested-lossy ,nested-free)))
  (define literal
    '(Rec ((value imm (Move argument))
           (bad imm (Construct some (Types Int) 1)))))
  (define source
    (apply-function
     nested-wide (nested-wide-value 13)
     (apply-function expected literal 'unit 'Unit '())
     'Unit '(Own)))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (type-equiv? (union-inject-member core expected) nested-free))
  (check-false (contains-rsd? core))
  (define-values (final _rules) (run-checked source))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "Rec の直接 check は内側の未選択試行の RSD で外側を損失層へ移さない"
  (define wide '(Record ((x Int imm) (o (Option (Owned Res)) imm))))
  (define narrow '(Record ((x Int imm))))
  (define (member-with-value value-type)
    `(Record ((value ,value-type imm) (bad (Option Int) imm))))
  (define inner-safe
    `(Union ,(member-with-value `(Union ,wide Bool))
            ,(member-with-value `(Union ,narrow Bool))))
  (define inner-lossy
    `(Union ,(member-with-value `(Union ,narrow Bool)) String))
  (define safe-outer
    `(Record ((payload ,inner-safe imm) (bad (Option Int) imm))))
  (define lossy-outer
    `(Record ((payload ,inner-lossy imm) (bad (Option Int) imm))))
  (define expected (normalize-type `(Union ,safe-outer ,lossy-outer)))
  (define wide-value
    `(Rec ((x imm 7)
           (o imm (Construct some (Types (Owned Res))
                             (Apply acquire 13))))))
  (define inner-literal
    '(Rec ((value imm (Move argument)) (bad imm (Construct some 1)))))
  (define inner-loss-literal
    '(Rec ((value imm (Move p)) (bad imm (Construct some 1)))))
  (define outer-literal
    `(Rec ((payload imm ,inner-literal)
          (bad imm (Construct some 1)))))
  (define source
    (apply-function
     wide wide-value
     (apply-function expected outer-literal 'unit 'Unit '())
     'Unit '(Own)))
  (define inner-loss-source
    `(Apply (Fn ((p ,wide)) ,inner-lossy (Own) ,inner-loss-literal)
            ,wide-value))
  (match-define (list inner-core _inner-type _inner-row _inner-callables)
    (checked inner-loss-source))
  (check-true (contains-rsd? inner-core)
              "損失のある内側の成分を試行の陽性対照にする")
  (match-define (list core _type _row _callables) (checked source))
  (check-false (contains-rsd? core))
  (check-true (type-equiv? (union-inject-member core expected) safe-outer))
  (define-values (final _rules) (run-checked source))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "リテラルの RSD 候補 4a は rebuild 候補 4b より先に選ぶ"
  (define payload '(Record ((x Int imm) (o (Option (Owned Res)) imm))))
  (define m1 '(Record ((a (Union Int Bool) imm))))
  (define m2 `(Record ((a (Union Int Bool) imm)
                       (o (Record ((x Int imm))) imm))))
  (define expected (normalize-type `(Union ,m1 ,m2)))
  (define payload-value
    `(Rec ((x imm 7)
           (o imm (Construct some (Types (Owned Res))
                             (Apply acquire 13))))))
  (define source
    (apply-function
     payload payload-value
     (apply-function expected '(Rec ((a imm 1) (o imm (Move argument))))
                      'unit 'Unit '())
     'Unit '(Own)))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (type-equiv? (union-inject-member core expected) m2))
  (check-true (contains-rsd? core))
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "同じリテラル成分が 4a と 4b の両方に届いても一度だけ選ぶ"
  (define payload '(Record ((x Int imm) (o (Option (Owned Res)) imm))))
  (define selected-member
    `(Record ((a (Union Int Bool) imm) (o (Record ((x Int imm))) imm))))
  (define expected (normalize-type `(Union ,selected-member String)))
  (define payload-value
    `(Rec ((x imm 7)
           (o imm (Construct some (Types (Owned Res))
                             (Apply acquire 13))))))
  (define source
    (apply-function
     payload payload-value
     (apply-function expected '(Rec ((a imm 1) (o imm (Move argument))))
                      'unit 'Unit '())
     'Unit '(Own)))
  (match-define (list core _type _row _callables) (checked source))
  (check-true (type-equiv? (union-inject-member core expected) selected-member))
  (check-true (contains-rsd? core))
  (define-values (final rules) (run-checked source))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (map second (configuration-tokens final)) '(Dropped)))

(test-case "合成できる Rec の完全一致、層 1、層 2 は check-against-expected と同じ成分を選ぶ"
  (define cases
    (list
     (list '(Record ((a Int imm))) '(Rec ((a imm 1)))
           '(Union (Record ((a Int imm))) String)
           '(Record ((a Int imm))))
     (list '(Record ((a Int imm) (b Int imm)))
           '(Rec ((a imm 1) (b imm 2)))
           '(Union (Record ((a Int imm) (b Int imm opt))) String)
           '(Record ((a Int imm) (b Int imm opt))))
     (list '(Record ((a Int imm))) '(Rec ((a imm 1)))
           '(Union (Record ((a (Union Int Bool) imm))) String)
           '(Record ((a (Union Int Bool) imm))))))
  (for ([case (in-list cases)])
    (match-define (list actual value expected selected) case)
    (define direct-literal
      `(Apply (Fn ((argument ,expected)) Unit () unit) ,value))
    (define synthesized-value
      `(Apply (Fn ((record ,actual)) Unit ()
                  (Apply (Fn ((argument ,expected)) Unit () unit)
                         record))
              ,value))
    (match-define (list direct-core _direct-type _direct-row _direct-callables)
      (checked direct-literal))
    (match-define (list synthesized-core _type _row _callables)
      (checked synthesized-value))
    (check-true (type-equiv? (union-inject-member direct-core expected)
                             selected))
    (check-true (type-equiv?
                 (union-inject-member synthesized-core expected)
                 selected))))

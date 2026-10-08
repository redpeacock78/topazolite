#lang racket

(require rackunit
         racket/list
         racket/match
         "../compat.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../ownership.rkt"
         "../resource-type.rkt"
         "../type-equiv.rkt"
         "../type-shape.rkt"
         "../typing.rkt")

(provide (all-defined-out))

(define a-types
  '(Int Bool (Union Int Bool) (Union Int String)
    (Record ((a Int imm)))
    (Owned (Union Int String))
    (Owned (Union Bool String))
    (Owned (Record ((a Int imm))))))

(define b-shapes
  '(#f (b Int imm) (b Int mut) (b Int imm opt)
    (b (Option (Owned Res)) imm)))

(define R
  (for*/list ([a (in-list a-types)] [b (in-list b-shapes)])
    (normalize-type `(Record ((a ,a imm) ,@(if b (list b) '()))))))

(define R_a
  (filter (lambda (type) (= (length (second type)) 1)) R))

(define (well-formed-generated-type? type)
  (and type
       (type-normal? type)
       (type-shape-ok? type)
       (not (owned-union-member? type))))

(define (narrowing-kind actual expected)
  (owned-narrowing-kind actual expected compat?))

(define (case-class actual expected)
  (cond
    [(not (and (well-formed-generated-type? actual)
               (well-formed-generated-type? expected)))
     'invalid-type]
    [(not (compat? actual expected)) 'not-compatible]
    [else
     (match (narrowing-kind actual expected)
       ['ok 'ok]
       [`(drop-obligation ,_ ,_) 'drop-obligation]
       [_ 'owned-narrowing-rejected])]))

(define (conversion-program actual expected #:check-result? [check-result? #f])
  (define effect-row
    (if (or (resource-type? actual) (resource-type? expected)) '(Own) '()))
  (define body
    `(Let (converted let ,expected)
          ,(if (resource-type? actual) '(Move argument) 'argument)
          ,(if (resource-type? expected) '(Move converted) 'converted)))
  (if check-result?
      `(Fn ((argument ,actual)) ,expected ,effect-row ,body)
      `(Fn ((argument ,actual)) #:infer ,effect-row ,body)))

(define (diagnostic-key diagnostic)
  (define row (diagnostic-code-row (diagnostic-id diagnostic)))
  (and row (diagnostic-code-key row)))

(define (count-head head tree)
  (cond
    [(pair? tree)
     (+ (if (eq? (car tree) head) 1 0)
        (for/sum ([child (in-list (cdr tree))])
          (count-head head child)))]
    [else 0]))

(define (find-core-form head tree)
  (cond
    [(and (pair? tree) (eq? (car tree) head)) tree]
    [(list? tree)
     (for/or ([child (in-list tree)])
       (find-core-form head child))]
    [else #f]))

;; let 注釈で隠れないよう、UnionEliminate を同型の値を返す producer から
;; Let 束縛した Core の文脈で型付けし、Core の枝合流型を直接検査する。
(define (check-core-branch-merge! core actual upper callables)
  (define erased (erase-core core))
  (define union-eliminate (find-core-form 'UnionEliminate erased))
  (when union-eliminate
    (define source-name
      (match union-eliminate
        [`(UnionEliminate (Move ,name) ,_branches) name]
        [`(UnionEliminate ,(? symbol? name) ,_branches) name]
        [_ #f]))
    (check-not-false source-name "UnionEliminate の変換元 binder が見つからない")
    (define source-signature
      `(NFn (Unit) ,actual () ,(if (resource-type? actual) '(Own) '()) () User))
    (define merge-core
      `(Scope ()
              (Let (,source-name let ,actual)
                   (Apply row005-branch-source unit)
                   ,union-eliminate)))
    (match (core-type-of merge-core '() callables
                         `((row005-branch-source ,source-signature)))
      [(list core-type _row)
       (check-equal? core-type upper)]
      [other
       (fail-check
        (format "作り直した UnionEliminate の Core 型付けに失敗: ~s" other))])))

;; 推論 mode は変換後の型を測り、check mode は指定型への検査を強制する。
;; Core 型付けとの一致も各 programme で検査し、失敗を捨てない。
(define (run-conversion actual expected #:check-result? [check-result? #f])
  (match (elab (conversion-program actual expected
                                   #:check-result? check-result?))
    [`(err ,diagnostic)
     (list 'rejected (diagnostic-key diagnostic))]
    [(list core function-type row callables)
     (define core-type
       (core-type-of (erase-core core) '() callables))
     (check-equal? core-type (list function-type row))
     (match function-type
       [`(NFn ,_ ,result-type ,_ ,_ ,_ ,_)
        (check-true (well-formed-generated-type? result-type))
        (list 'accepted result-type core callables)]
       [_
        (fail-check (format "Fn の推論型が NFn でない: ~s" function-type))])]))

(define (make-union types)
  (normalize-type
   (for/fold ([result (last types)]) ([type (in-list (reverse (drop-right types 1)))])
     `(Union ,result ,type))))

(define (row-labels-common rows)
  (filter (lambda (label)
            (for/and ([row (in-list rows)]) (assoc label row)))
          (map first (first rows))))

(define (join-failure-reason types)
  (define rows (map second types))
  (for/or ([label (in-list (row-labels-common rows))])
    (define field-types
      (sort-then-dedup
       (map (lambda (row) (second (assoc label row))) rows)))
    (let loop ([acc (first field-types)] [remaining (rest field-types)])
      (cond
        [(null? remaining) #f]
        [else
         (define next (first remaining))
         (define joined (tag-upper-bound acc next))
         (if joined
             (loop joined (rest remaining))
             (cond
               [(and (owned-type? acc) (owned-type? next))
                'owned-owned-without-upper-bound]
               [(or (owned-type? acc) (owned-type? next))
                'one-owned-one-unowned]
               [else
                (define union (normalize-type `(Union ,acc ,next)))
                (cond
                  [(not union) 'non-normalizable-union]
                  [(owned-union-member? union) 'owned-union-member]
                  [else 'unexpected-join-failure])]))]))))

(define (increment! counts key)
  (hash-update! counts key add1 0))

(define (sorted-counts counts)
  (sort (hash->list counts) string<?
        #:key (lambda (entry) (symbol->string (car entry)))))

(define (count-normalization-and-shape! counts types)
  (cond
    [(ormap (lambda (type) (not (normalize-type type))) types)
     (increment! counts 'normalization-failure)
     #f]
    [(ormap (lambda (type) (not (well-formed-generated-type? type))) types)
     (increment! counts 'invalid-type)
     #f]
    [else #t]))

(define (convert-pair-group cases expected-total)
  (define counts (make-hash))
  (for ([case (in-list cases)])
    (match-define (list actual expected) case)
    (if (not (count-normalization-and-shape! counts (list actual expected)))
        (void)
        (match (case-class actual expected)
          ['not-compatible (increment! counts 'not-compatible)]
          [(or 'drop-obligation 'owned-narrowing-rejected)
           (match (run-conversion actual expected #:check-result? #t)
             [`(accepted ,result-type ,core ,_callables)
              (check-equal? (case-class actual expected) 'drop-obligation)
              (check-equal? result-type expected)
              (check-not-false
               (find-core-form 'RemainderSafelyDropped core)
               (format "drop-obligation の check に RSD が無い: ~s => ~s"
                       actual expected))
              (increment! counts 'drop-obligation)]
             [`(rejected ,key)
              (check-equal? (case-class actual expected)
                            'owned-narrowing-rejected)
              (check-not-false
               (memq key '(owned-narrowing-needs-proof
                           owned-narrowing-rejected))
               (format "OWN-004 の拒否理由が予期しない: ~s => ~s: ~s"
                       actual expected key))
              (increment! counts 'owned-narrowing-rejected)]
             [other
              (fail-check
               (format "OWN-004 の check が予期せぬ結果: ~s => ~s: ~s"
                       actual expected other))])]
          ['invalid-type (increment! counts 'invalid-type)]
          ['ok
           (match (run-conversion actual expected)
             [`(accepted ,_ ,_ ,_) (increment! counts 'accepted)]
             [`(rejected ambiguous-union-member)
              (increment! counts 'ambiguous-union-member)]
             [other
              (fail-check
               (format "互換かつ OWN-004 が ok の convert が予期せず失敗した: ~s => ~s: ~s"
                       actual expected other))])])))
  (check-equal? (apply + (hash-values counts)) expected-total)
  counts)

(define (branch-join-program types)
  (define names
    (for/list ([index (in-range (length types))])
      (string->symbol (format "branch~a" index))))
  (define (branch-body selected)
    (define selected-name (list-ref names selected))
    (define selected-type (list-ref types selected))
    (define result
      (if (resource-type? selected-type)
          `(Move ,selected-name)
          selected-name))
    (for/fold ([body result])
              ([name (in-list names)] [type (in-list types)] [index (in-naturals)]
               #:when (and (not (= index selected)) (resource-type? type)))
      `(Let (discard const Unit) (Drop (Move ,name)) ,body)))
  `(Fn ,(append (map list names types) '((flag Bool)))
       #:infer (Own)
       (Eliminate flag
         ((true () -> ,(branch-body 0))
          (false () -> ,(branch-body 1))))))

(define (run-branch-join types upper)
  (match (elab (branch-join-program types))
    [`(err ,diagnostic) (list 'rejected (diagnostic-key diagnostic))]
    [(list core function-type row callables)
     (define core-type (core-type-of (erase-core core) '() callables))
     (check-equal? core-type (list function-type row))
     (match function-type
       [`(NFn ,_ ,result-type ,_ ,_ ,_ ,_)
        (check-true (well-formed-generated-type? result-type))
        (check-equal? result-type upper)
        (list 'accepted result-type core callables)]
       [_ (fail-check (format "branch join の Fn 型が NFn でない: ~s"
                              function-type))])]))

(define (run-join-conversion types upper)
  (if (= (length types) 2)
      (run-branch-join types upper)
      (run-conversion (make-union types) upper)))

(define (join-group cases expected-total)
  (define counts (make-hash))
  (for ([types (in-list cases)])
    (if (not (count-normalization-and-shape! counts types))
        (void)
        (let ([upper (row005-join types)])
          (cond
            [(not upper)
             (define reason (join-failure-reason types))
             (check-not-equal? reason 'unexpected-join-failure
                               (format "ROW-005 の未説明な join 拒否: ~s" types))
             (check-not-equal? reason 'non-normalizable-union)
             (increment! counts reason)]
            [else
             (check-true (well-formed-generated-type? upper))
             (define kinds
               (for/list ([type (in-list types)])
                 (check-true (compat? type upper)
                             (format "join 上界が枝と非互換: ~s => ~s" type upper))
                 (narrowing-kind type upper)))
             (define rejected-kind (findf (lambda (kind) (not (eq? kind 'ok))) kinds))
             (if rejected-kind
                 (if (match rejected-kind
                       [`(drop-obligation ,_ ,_) #t]
                       [_ #f])
                     (match (run-join-conversion types upper)
                       [(list 'accepted result-type core callables)
                        (check-equal? result-type upper)
                        (check-not-false
                         (find-core-form 'RemainderSafelyDropped core)
                         (format "drop-obligation の join に RSD が無い: ~s => ~s"
                                 types upper))
                        (when (> (length (remove-duplicates types equal?)) 1)
                          (check-not-false
                           (or (find-core-form 'Eliminate core)
                               (find-core-form 'UnionEliminate core))
                                      (format "枝合流の Core を含まない join Core: ~s"
                                              types)))
                        (check-core-branch-merge! core (make-union types) upper
                                                  callables)
                        (increment! counts 'accepted-with-rsd)]
                       [other
                        (fail-check
                         (format "drop-obligation の join が RSD で受理されない: ~s => ~s: ~s"
                                 types upper other))])
                     (begin
                       (increment! counts 'owned-narrowing-rejected)
                       (match (run-join-conversion types upper)
                         [`(rejected ,key)
                          (check-not-false
                           (memq key '(owned-narrowing-needs-proof
                                       owned-narrowing-rejected))
                           (format "OWN-004 の拒否理由が予期しない: ~s" key))]
                         [other
                          (fail-check
                           (format "OWN-004 が拒否すべき join が通った: ~s => ~s: ~s"
                                   types upper other))])))
                 (match (run-join-conversion types upper)
                   [(list 'accepted result-type core callables)
                    (check-equal? result-type upper)
                    (when (> (length (remove-duplicates types equal?)) 1)
                      (check-not-false
                       (or (find-core-form 'Eliminate core)
                           (find-core-form 'UnionEliminate core))
                       (format "枝合流の Core を含まない join Core: ~s"
                               types)))
                    (check-core-branch-merge! core (make-union types) upper
                                              callables)
                    (increment! counts 'accepted)]
                   [`(rejected ambiguous-union-member)
                    (increment! counts 'ambiguous-union-member)]
                   [other
                    (fail-check
                     (format "OWN-004 が ok の join の作り直しが失敗した: ~s => ~s: ~s"
                             types upper other))]))]))))
  (check-equal? (apply + (hash-values counts)) expected-total)
  counts)

;; 2 型の join では branch join と並行して旧来の Union → 上界 convert も検査する。
;; c2b2b2 で decompose の判定が変わるとき、この経路の差分を追えるようにする。
(define (join-record-convert-group cases)
  (define counts (make-hash))
  (for ([types (in-list cases)])
    (if (not (count-normalization-and-shape! counts types))
        (void)
        (let ([upper (row005-join types)])
          (cond
            [(not upper) (increment! counts 'no-row005-upper)]
            [else
             (check-true (well-formed-generated-type? upper))
             (define kinds
               (for/list ([type (in-list types)])
                 (check-true (compat? type upper))
                 (narrowing-kind type upper)))
             (define rejected-kind
               (findf (lambda (kind) (not (eq? kind 'ok))) kinds))
             (cond
               [(not rejected-kind)
                (match (run-conversion (make-union types) upper)
                  [`(accepted ,result-type ,_core ,_callables)
                   (check-equal? result-type upper)
                   (increment! counts 'convert-accepted)]
                  [other
                   (fail-check
                    (format "ok の join が Union → 上界 convert で失敗した: ~s => ~s: ~s"
                            types upper other))])]
               [(match rejected-kind [`(drop-obligation ,_ ,_) #t] [_ #f])
                (match (run-conversion (make-union types) upper)
                  [`(accepted ,result-type ,core ,_callables)
                   (check-equal? result-type upper)
                   (check-not-false
                    (find-core-form 'RemainderSafelyDropped core)
                    (format "drop-obligation の Union convert に RSD が無い: ~s => ~s"
                            types upper))
                   (increment! counts 'convert-accepted)]
                  [`(rejected ,key)
                   (check-not-false
                    (memq key '(owned-narrowing-needs-proof
                                owned-narrowing-rejected))
                    (format "drop-obligation の Union convert が予期しない key: ~s"
                            key))
                   (fail-check
                    (format "drop-obligation の Union convert が拒否された: ~s => ~s: ~s"
                            types upper key))]
                  [other
                   (fail-check
                    (format "drop-obligation の Union → 上界 convert が失敗した: ~s => ~s: ~s"
                            types upper other))])]
               [else
                (fail-check
                 (format "join-record の上界に drop-obligation 以外の narrowing がある: ~s => ~s: ~s"
                         types upper rejected-kind))])]))))
  (check-equal? (apply + (hash-values counts)) (length cases))
  counts)

(define convert-record-cases
  (for*/list ([actual (in-list R)] [expected (in-list R)])
    (list actual expected)))

(define convert-union-cases
  (for*/list ([i (in-range (length R_a))]
              [j (in-range (add1 i) (length R_a))]
              [expected (in-list R)])
    (list (make-union (list (list-ref R_a i) (list-ref R_a j))) expected)))

(define join-record-cases
  (for*/list ([i (in-range (length R))]
              [j (in-range i (length R))])
    (list (list-ref R i) (list-ref R j))))

(define join-three-cases
  (for*/list ([i (in-range (length R_a))]
              [j (in-range (add1 i) (length R_a))]
              [k (in-range (add1 j) (length R_a))])
    (list (list-ref R_a i) (list-ref R_a j) (list-ref R_a k))))

(define task8-a-bool (normalize-type '(Record ((a Bool imm)))))
(define task8-a-int (normalize-type '(Record ((a Int imm)))))
(define task8-a-bool-or-int
  (normalize-type '(Record ((a (Union Bool Int) imm)))))
(define task8-two-way-case
  (list (make-union (list task8-a-bool task8-a-int)) task8-a-bool-or-int))
(define task8-three-way-types
  (filter (lambda (type)
            (member type (list task8-a-bool task8-a-int task8-a-bool-or-int) equal?))
          R_a))

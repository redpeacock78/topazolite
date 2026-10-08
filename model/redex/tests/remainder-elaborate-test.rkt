#lang racket

;; [REQ: OWN-004] OWN-004 の drop obligation を elaboration が RSD にする。

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define owned '(Owned Res))
(define nested-actual
  `(Record ((a (Record ((y Int imm) (z ,owned imm))) imm))))
(define nested-target
  '(Record ((a (Record ((y Int imm))) imm))))
(define direct-actual
  `(Record ((a ,owned imm) (b Int imm))))
(define direct-target '(Record ((b Int imm))))
(define rejected-nfn-actual
  `(NFn (Unit) ,nested-actual () () () User))
(define rejected-nfn-target
  `(NFn (Unit) ,nested-target () () () User))

(define (diagnostic-id-of result)
  (match result
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (find-rsd value)
  (match value
    [`(Discharge (ProofRep (Reserved o-narrow)
                          (RemainderSafelyDropped ,actual ,target)) ,_)
     (list actual target)]
    [(? list?)
     (for/or ([child (in-list value)]) (find-rsd child))]
    [_ #f]))

(define option-owned '(Option (Owned Res)))
(define runtime-inner-wide
  '(Record ((kept Int imm) (owned (Option (Owned Res)) imm))))
(define runtime-inner-narrow '(Record ((kept Int imm))))
(define runtime-wide `(Record ((a ,runtime-inner-wide imm))))
(define runtime-narrow `(Record ((a ,runtime-inner-narrow imm))))

(define (runtime-source number)
  (define record-value
    `(Rec ((a imm
            (Rec ((kept imm 7)
                  (owned imm (Move source))))))))
  `(Apply
    (Fn ((source ,option-owned)) ,runtime-narrow (Own)
      (Let (record let ,runtime-wide)
           ,record-value
           (Move record)))
    (Construct some (Types (Owned Res)) (Apply acquire ,number))))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 80])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-config-trace configs callables expected-type)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected-type))
    (check-not-false row
                     (format "runtime row を得られない config ~a: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected-type row)
                (format "不正な中間 config ~a: ~s" index configuration))))

(define (configuration-tokens configuration)
  (match configuration
    [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(test-case "check の narrowing は Reserved o-narrow の RSD を挿入する"
  (define result
    (elab `(Fn ((p ,direct-actual)) ,direct-target (Own) (Move p))))
  (check-false (diagnostic-id-of result))
  (match-define (list core function-type row callables) result)
  (define erased (erase-core core))
  (check-equal? (find-rsd erased) (list direct-actual direct-target))
  (check-equal? (core-type-of erased '() callables)
                (list function-type row)))

(test-case "入れ子 Owned の check narrowing も RSD で受理する"
  (define result
    (elab `(Fn ((p ,nested-actual)) ,nested-target (Own) (Move p))))
  (check-false (diagnostic-id-of result))
  (match-define (list core function-type row callables) result)
  (check-equal? (find-rsd (erase-core core))
                (list nested-actual nested-target))
  (check-equal? (core-type-of (erase-core core) '() callables)
                (list function-type row)))

(test-case "NFn の返り値内の損失は引き続き E-OWN-029 で拒否する"
  (define source
    `(Fn ((source (NFn (Unit) ,nested-actual () ())))
         Int ()
         (Apply (Fn ((p (NFn (Unit) ,nested-target () ())))
                   Int () 1)
                source)))
  (check-equal? (diagnostic-id-of (elab source)) "E-OWN-029"))

(test-case "RSD 実行は型を保ち、生成 token をすべて Dropped にする"
  (match-define (list core result-type row callables)
    (match (elab (runtime-source 51))
      [(list core result-type row callables)
       (list core result-type row callables)]
      [`(err ,diagnostic)
       (fail-check (format "runtime fixture が elaborate で拒否された: ~s"
                           diagnostic))]))
  (define erased (erase-core core))
  (check-equal? (find-rsd erased) (list runtime-wide runtime-narrow))
  (check-equal? (core-type-of erased '() callables)
                (list result-type row))
  (check-equal? result-type runtime-narrow)
  (define executable (execution-core core callables))
  (define start `(cfg ,executable () () () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-config-trace configs callables runtime-narrow)
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped))))

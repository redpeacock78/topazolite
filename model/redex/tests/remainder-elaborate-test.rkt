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

(define let-top-wide
  `(Record ((owned ,option-owned imm) (kept Int imm))))
(define let-top-narrow '(Record ((kept Int imm))))
(define const-mixed-wide
  `(Record ((owned ,option-owned imm) (kept Int imm) (extra Bool imm))))
(define const-mixed-narrow '(Record ((kept Int imm))))

(define (owned-option-value number)
  `(Construct some (Types (Owned Res)) (Apply acquire ,number)))

(define (owned-record-source type fields)
  `(Apply (Fn () ,type (Own) (Rec ,fields))))

(define (run-owned-let source token-count has-rsd?)
  (define result (elab source))
  (match result
    [`(err ,diagnostic)
     (fail-check (format "let の RSD programme が elaborate で拒否された: ~s"
                         diagnostic))]
    [(list core result-type row callables)
     (define erased (erase-core core))
     (check-equal? (core-type-of erased '() callables)
                   (list result-type row))
     (check-equal? (and (find-rsd erased) #t) has-rsd?)
     (define executable (execution-core core callables))
     (define-values (configs rules)
       (trace-g2 `(cfg (Scope () ,executable) () () () ())))
     (check-equal? (and (member 'R-DischargeRemainder rules) #t)
                   has-rsd?)
     (check-config-trace configs callables result-type)
     (check-equal? (configuration-core (last configs)) 1)
     (check-equal? (map second (configuration-tokens (last configs)))
                   (make-list token-count 'Dropped))]))

(define (configuration-core configuration)
  (match configuration
    [`(cfg ,core ,_ ,_ ,_ ,_) core]))

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

(test-case "let の最上位 Owned 残余は束縛型に残し RSD を挿入しない"
  (run-owned-let
   `(Let (record let ,let-top-narrow)
         ,(owned-record-source
           let-top-wide
           `((owned imm ,(owned-option-value 61)) (kept imm 7)))
         (Let (discard const Unit) (Drop (Move record)) 1))
   1 #f))

(test-case "let の入れ子 Owned 損失は RSD で回収する"
  (run-owned-let
   `(Let (record let ,runtime-narrow)
         ,(owned-record-source
           runtime-wide
           `((a imm (Rec ((kept imm 7)
                          (owned imm ,(owned-option-value 62)))))))
         1)
   1 #t))

(test-case "const の最上位 Owned 残余は RSD で回収する"
  (run-owned-let
   `(Let (record const ,let-top-narrow)
         ,(owned-record-source
           let-top-wide
           `((owned imm ,(owned-option-value 63)) (kept imm 7)))
         1)
   1 #t))

(test-case "const は RSD 後にも残る非 Owned 残余を拒否する"
  (define source
    `(Let (record const ,const-mixed-narrow)
          ,(owned-record-source
            const-mixed-wide
            `((owned imm ,(owned-option-value 64))
              (kept imm 7)
              (extra imm (Construct true (Types)))))
          1))
  (check-equal? (diagnostic-id-of (elab source)) "E-RCD-001"))

(test-case "mut は入れ子 Owned 損失を除いた後に束縛できる"
  (run-owned-let
   `(Let (record mut ,runtime-narrow)
         ,(owned-record-source
           runtime-wide
           `((a imm (Rec ((kept imm 7)
                          (owned imm ,(owned-option-value 65)))))))
         1)
   1 #t))

(test-case "型の合わない注釈付き Let は type-mismatch を先に出す"
  (check-equal?
   (diagnostic-id-of
    (elab '(Fn ((source Int)) Int () (Let (bound let Bool) source 0))))
   "E-TYP-012"))

#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../erase.rkt"
         "../driver.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../pr-machine.rkt"
         "../borrow.rkt"
         "../compat.rkt"
         "../region.rkt"
         "../resource-type.rkt"
         "../span-core.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         "../type-shape.rkt"
         "../uniquify.rkt"
         "../typing.rkt")

(define (type-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok (list type _row)) type]
    [_ 'ill-typed]))

(define (row-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok (list _type row)) row]
    [_ 'ill-typed]))

(define (key-of core [callables '()] [environment '()])
  (match (type-of/raw core '() callables environment)
    [(list 'ok _) 'ok]
    [(list 'fail key _node _details ...) key]))

(define (type-of/with-ir core [callables '()] [environment '()])
  (define ir (build-region-ir (erase-core core)))
  (type-of/raw core '() callables environment
               (region-ctx ir '() (hash) (hash))))

(define (key-of/with-ir core [callables '()] [environment '()])
  (match (type-of/with-ir core callables environment)
    [(list 'ok _) 'ok]
    [(list 'fail key _node _details ...) key]))

(define (initial core [tokens '()])
  `(cfg (Scope () ,core) () () ,tokens ()))

(define (g2-trace start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 60])
    (when (zero? fuel)
      (error 'g2-trace "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps (error 'g2-trace "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (check-config-trace configs callables expected)
  (define rows
    (for/list ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config callables expected))
      (check-not-false row
                       (format "runtime row を得られない config ~a: ~s"
                               index config))
      (check-true (config-ok? config callables expected row)
                  (format "不正な中間 config ~a: ~s" index config))
      row))
  (for ([before (in-list rows)] [after (in-list (cdr rows))]
        [index (in-naturals)])
    (check-true (row-subset? after before)
                (format "config ~a から次の config で row が増えた: ~s -> ~s"
                        index before after))))

(define (elaborate-compiled expression)
  (match (elab expression)
    [`(err ,diagnostic) diagnostic]
    [(list core type row callables)
     (define ledger (current-trait-ledger))
     (define executable
       (call-with-trait-ledger
        ledger
        (lambda () (execution-core core callables))))
     (compiled core type row callables ledger executable)]))

(define (check-compiled-source-core artifact)
  (unless (compiled? artifact)
    (fail-check (format "コンパイル結果が診断になった: ~s" artifact)))
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (lambda ()
     (check-equal?
      (core-type-of (erase-core (compiled-core artifact)) '()
                    (compiled-callables artifact))
      (list (compiled-type artifact) (compiled-row artifact)))))
  artifact)

(define (run-compiled-execution-core artifact)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (lambda ()
     (define-values (configs rules)
       (g2-trace
        (initial (compiled-execution-core artifact) '())))
     (check-config-trace configs (compiled-callables artifact)
                         (compiled-type artifact))
     (list (last configs) rules))))

(define (apply-function input-type input-value body return-type row)
  `(Apply
    (Fn ((argument ,input-type)) ,return-type ,row ,body)
    ,input-value))

(define (accepted source)
  (define artifact (check-compiled-source-core (elaborate-compiled source)))
  (list (erase-core (compiled-core artifact))
        (compiled-type artifact)
        (compiled-row artifact)))

(define (rejected-code source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [other (fail-check (format "elaborate が受理した: ~s" other))]))

(define (code key) (diagnostic-code-of 'elaborate key))

(define (count-nodes head tree)
  (cond [(and (pair? tree) (eq? (car tree) head))
         (add1 (apply + (map (lambda (t) (count-nodes head t)) (cdr tree))))]
        [(pair? tree) (apply + (map (lambda (t) (count-nodes head t)) tree))]
        [else 0]))

;; erase した Core の RecRewrite entry を外側から順に集める。
(define (rec-rewrite-entries tree)
  (match tree
    [`(RecRewrite ,input (,entries ...))
     (append entries
             (rec-rewrite-entries input)
             (append-map (lambda (entry) (rec-rewrite-entries (last entry)))
                         entries))]
    [(? pair?) (append-map rec-rewrite-entries tree)]
    [_ '()]))

(define int-or-bool (normalize-type '(Union Int Bool)))

(test-case "check の位置で Record の欄を inject で作り直す"
  (match-define (list core _ _)
    (accepted
     `(Fn ((x (Record ((a Int imm))))) Int ()
          (Apply (Fn ((r (Record ((a ,int-or-bool imm))))) Int () 0) x))))
  (check-equal? (count-nodes 'RecRewrite core) 1)
  (match (rec-rewrite-entries core)
    [(list (list 'a _ 'Int 'imm (== int-or-bool) _)) (void)]
    [other (fail-check (format "entry が想定と違う: ~s" other))]))

(test-case "束縛の位置の作り直しは残余の欄を型に残す"
  (match-define (list _ type _)
    (accepted
     `(Let (x const (Record ((a Int imm) (b Bool imm))))
           (Rec ((a imm 1) (b imm (Construct true (Types)))))
           (Let (r let (Record ((a ,int-or-bool imm)))) x r))))
  (check-equal? type `(Record ((a ,int-or-bool imm) (b Bool imm)))))

(test-case "mut の欄の entry は出力でも mut を保つ"
  (match-define (list core type _)
    (accepted
     `(Let (x let (Record ((a Int mut)))) (Rec ((a mut 1)))
           (Let (r let (Record ((a ,int-or-bool mut)))) x r))))
  (check-equal? type `(Record ((a ,int-or-bool mut))))
  (match (rec-rewrite-entries core)
    [(list (list 'a _ 'Int 'mut _ _)) (void)]
    [other (fail-check (format "entry が想定と違う: ~s" other))]))

(test-case "imm の欄を mut の expected へ作り直さない"
  (check-equal?
   (rejected-code
    `(Fn ((x (Record ((a Int imm))))) Int ()
         (Let (r let (Record ((a ,int-or-bool mut)))) x 0)))
   (code 'type-mismatch)))

(test-case "入れ子の Record は欄の本体に内側の RecRewrite を持つ"
  (match-define (list core _ _)
    (accepted
     `(Fn ((x (Record ((p (Record ((a Int imm))) imm))))) Int ()
          (Apply (Fn ((r (Record ((p (Record ((a ,int-or-bool imm))) imm)))))
                     Int () 0)
                 x))))
  (check-equal? (count-nodes 'RecRewrite core) 2))

(test-case "optional の欄は present と Absent の両方で作り直せる"
  (define source-type '(Record ((a Int imm) (o Int imm opt))))
  (define target-type `(Record ((a ,int-or-bool imm) (o ,int-or-bool imm opt))))
  (for ([value (list '(Rec ((a imm 1) (o imm 2))) '(Rec ((a imm 1))))])
    (define artifact
      (check-compiled-source-core
       (elaborate-compiled
        `(Let (x const ,source-type) ,value
              (Let (r let ,target-type) x r)))))
    (check-equal? (compiled-type artifact) target-type)
    (void (run-compiled-execution-core artifact))))

;; Surface の Rec は root Owned の欄を owned-record-field で拒否する。
;; そのため、root Owned の欄を持つ Record は仮引数から作り、Core を静的に調べる。
(define (owned-field-entries source-type target-type)
  (match-define (list core _ _)
    (accepted
     `(Fn ((argument ,source-type)) ,target-type (Own)
          (Let (r let ,target-type) (Move argument) r))))
  (rec-rewrite-entries core))

(define (entry-of label entries)
  (for/first ([entry (in-list entries)] #:when (eq? (first entry) label))
    entry))

(test-case "root Owned の欄は identity entry で印だけを変える"
  (define entries
    (owned-field-entries
     '(Record ((o (Owned Res) mut) (a Int imm)))
     `(Record ((o (Owned Res) imm) (a ,int-or-bool imm)))))
  (match (entry-of 'o entries)
    [(list 'o binder '(Owned Res) 'imm '(Owned Res) body)
     (check-equal? body binder)]
    [other (fail-check (format "Owned の欄の identity entry が無い: ~s" other))]))

(test-case "Owned 欄の payload widening は tag-compat? だけが受理する"
  (define source-payload int-or-bool)
  (define target-payload '(Union Int (Union Bool String)))
  (check-true (tag-compat? `(Owned ,source-payload) `(Owned ,target-payload)))
  (check-false (compat? `(Owned ,source-payload) `(Owned ,target-payload)))
  ;; payload 型を変えず、別欄 a の変換がある場合に o を entry へ入れない。
  (define same-mark
    (owned-field-entries
     `(Record ((o (Owned ,source-payload) imm) (a Int imm)))
     `(Record ((o (Owned ,source-payload) imm) (a ,int-or-bool imm)))))
  (check-false (entry-of 'o same-mark))
  (check-not-false (entry-of 'a same-mark))
  (match (entry-of 'o
                   (owned-field-entries
                    `(Record ((o (Owned ,source-payload) mut) (a Int imm)))
                    `(Record ((o (Owned ,source-payload) imm)
                              (a ,int-or-bool imm)))))
    [(list 'o binder input-type 'imm output-type body)
     (check-equal? input-type `(Owned ,source-payload))
     (check-equal? output-type `(Owned ,source-payload))
     (check-equal? body binder)]
    [other (fail-check (format "Owned 欄の identity entry が想定と違う: ~s" other))]))

(test-case "Owned 欄の payload widening は束縛と check の両位置で拒否する"
  (define source-type
    `(Record ((o (Owned ,int-or-bool) imm) (a Int imm))))
  (define expected-type
    '(Record ((o (Owned (Union Int (Union Bool String))) imm)
              (a (Union Int Bool) imm))))
  (check-equal?
   (rejected-code
    `(Fn ((argument ,source-type)) Int (Own)
         (Let (r let ,expected-type) (Move argument) 0)))
   (code 'type-mismatch))
  (check-equal?
   (rejected-code
    `(Fn ((argument ,source-type)) ,expected-type (Own)
         (Move argument)))
   (code 'type-mismatch)))

(test-case "RecRewrite の entry binder は入力の symbol と衝突しない"
  (match-define (list core _ _)
    (accepted
     `(Fn ((union0 (Record ((a Int imm))))) Int ()
          (Apply (Fn ((r (Record ((a ,int-or-bool imm))))) Int () 0) union0))))
  (for ([entry (in-list (rec-rewrite-entries core))])
    (check-not-equal? (second entry) 'union0)))

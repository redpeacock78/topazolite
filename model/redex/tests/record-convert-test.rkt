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
         "../ownership.rkt"
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

(define (generated-union-indices tree)
  (sort
   (remove-duplicates
    (filter values
            (for/list ([atom (in-list (flatten tree))]
                       #:when (symbol? atom))
              (match (regexp-match #px"^union([0-9]+)(⟨[0-9]+⟩)?$"
                                   (symbol->string atom))
                [(list _ index _suffix) (string->number index)]
                [_ #f]))))
   <))

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

(define (entry-bodies-in-L? core)
  (for/and ([entry (in-list (rec-rewrite-entries core))])
    (define body (last entry))
    (and (zero? (count-nodes 'Scope body))
         (zero? (count-nodes 'Move body)))))

(define int-or-bool (normalize-type '(Union Int Bool)))

;; 実行する作り直し試験の Owned leaf は Option の中に置く。
(define owned-leaf '(Option (Owned Res)))
(define owned-leaf-value
  '(Construct some (Types (Owned Res)) (Apply acquire 13)))

(define (bool-eliminate then-branch else-branch)
  `(Eliminate (Construct true (Types))
              ((true () -> ,then-branch)
               (false () -> ,else-branch))))

(define (apply-no-args return-type body)
  `(Apply (Fn () ,return-type () ,body)))

(define (union-record-source type value body return-type row)
  (apply-function type value body return-type row))

(define record-a-int '(Record ((a Int imm))))
(define record-a-wide
  '(Record ((a (Union Int (Union String Bool)) imm))))

(define (record-with-a-b b-type)
  `(Record ((a Int imm) (b ,b-type imm))))

(define residual-diff-eliminate
  (bool-eliminate
   '(Rec ((a imm 1) (b imm 2)))
   '(Rec ((a imm 1) (b imm (Construct true (Types)))))))

(define (record-from-eliminate expression)
  `(Rec ((boxed imm ,expression))))

(define (decompose-record-function member-types expected result-type)
  (define source-type (normalize-type `(Union ,@member-types)))
  (define source-resource? (resource-type? source-type))
  (define result-resource? (resource-type? result-type))
  `(Fn ((argument ,source-type)) ,result-type
       ,(if result-resource? '(Own) '())
       (Let (r let ,expected)
            ,(if source-resource? '(Move argument) 'argument)
            ,(if result-resource? '(Move r) 'r))))

(test-case "check の Eliminate は枝の残余を const の拒否へ伝える"
  (check-equal?
   (rejected-code
    `(Let (r const ,record-a-int) ,residual-diff-eliminate 0))
   (code 'const-record-residual)))

(test-case "check の Eliminate は残余を join し let から読める"
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      `(Let (r let ,record-a-int) ,residual-diff-eliminate (Proj r b)))))
  (check-equal? (compiled-type artifact) (normalize-type '(Union Int Bool))))

(test-case "Record 欄内の check Eliminate は異なる残余を ROW-005 で join する"
  (void
   (check-compiled-source-core
    (elaborate-compiled
     `(Let (r const (Record ((boxed ,record-a-int imm))))
        ,(record-from-eliminate residual-diff-eliminate)
        0)))))

(test-case "注釈付き Let の check Eliminate は異なる残余を ROW-005 で join する"
  (void
   (check-compiled-source-core
    (elaborate-compiled
     `(Let (r let ,record-a-int) ,residual-diff-eliminate 0)))))

(test-case "Record 欄内の Union-valued Eliminate は各段の残余を join する"
  (define left-c '(Record ((a Int imm) (b Int imm) (c Bool imm))))
  (define left-d '(Record ((a Int imm) (b Int imm) (d Bool imm))))
  (define right-c '(Record ((a Int imm) (b String imm) (c Bool imm))))
  (define right-d '(Record ((a Int imm) (b String imm) (d Bool imm))))
  (define left-union (normalize-type `(Union ,left-c ,left-d)))
  (define right-union (normalize-type `(Union ,right-c ,right-d)))
  (define (union-value union-type record-type)
    (apply-no-args union-type
                   (match record-type
                     [`(Record ,row)
                      `(Rec ,(for/list ([field (in-list row)])
                               (match field
                                 [`(a Int imm) '(a imm 1)]
                                 [`(b Int imm) '(b imm 2)]
                                 [`(b String imm) '(b imm "s")]
                                 [`(c Bool imm) '(c imm (Construct true (Types)))]
                                 [`(d Bool imm) '(d imm (Construct false (Types)))])))])))
  (void
   (check-compiled-source-core
    (elaborate-compiled
     `(Let (r const (Record ((boxed ,record-a-int imm))))
        (Rec ((boxed imm
               ,(bool-eliminate
                 (union-value left-union left-c)
                 (union-value right-union right-c)))))
        0)))))

(test-case "UnionEliminate は異なる残余を join して let へ渡す"
  (define left (record-with-a-b 'Int))
  (define right (record-with-a-b 'String))
  (define source-type (normalize-type `(Union ,left ,right)))
  (define result-type
    (row005-join
     (list left right)))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (union-record-source
       source-type
       '(Rec ((a imm 1) (b imm 2)))
       `(Let (r let ,record-a-int) argument (Proj r b))
       '(Union Int String) '()))))
  (check-equal? result-type
                '(Record ((a Int imm) (b (Union Int String) imm))))
  (check-equal? (compiled-type artifact) '(Union Int String)))

(test-case "check Eliminate は tag 互換な狭い Union の Core 型を保つ"
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      `(Apply
        (Fn ((flag Bool) (left (Union Int String))
             (right (Union Int String)))
            ,record-a-wide ()
            (Rec ((a imm
                   ,(bool-eliminate 'left 'right)))))
        (Construct true (Types)) 1 "s"))))
  (define core (erase-core (compiled-core artifact)))
  (define (find-eliminate term)
    (cond
      [(and (pair? term) (eq? (car term) 'Eliminate)) term]
      [(pair? term)
       (for/or ([child (in-list term)]) (find-eliminate child))]
      [else #f]))
  (define (find-lam term)
    (match term
      [`(Lam ,_ ,_ (,parameters ...) ,body)
       (define eliminate (find-eliminate body))
       (and eliminate (list parameters eliminate))]
      [(? pair?)
       (for/or ([child (in-list term)]) (find-lam child))]
      [_ #f]))
  (match (find-lam core)
    [(list parameters eliminate)
     (define names
       (for/list ([parameter (in-list parameters)])
         (match parameter
           [`(#:bind ,name ,_) name]
           [(? symbol? name) name])))
     (check-equal?
      (type-of
       eliminate '()
       (map list names '(Bool (Union Int String) (Union Int String))))
      '(Union Int String))]
    [_ (fail-check (format "Eliminate を持つ Lam が無い: ~s" core))]))

(define (owned-residual-record extra-type)
  `(Record ((a Int imm) (o ,owned-leaf imm) (b ,extra-type imm))))

(define (owned-residual-value extra-type extra-value)
  `(Rec ((a imm 1) (o imm ,owned-leaf-value) (b imm ,extra-value))))

(define (owned-residual-program binding-mode source-type source-value result-type)
  (union-record-source
   source-type source-value
   `(Let (r ,binding-mode ,record-a-int) (Move argument)
      ,(if (eq? binding-mode 'let) '(Move r) 0))
   result-type '(Own)))

(test-case "共有 Owned 残余の Union 分解を let で保持して実行する"
  (define left (owned-residual-record 'Int))
  (define right (owned-residual-record 'Bool))
  (define source-type (normalize-type `(Union ,left ,right)))
  (define result-type (row005-join (list left right)))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (owned-residual-program
       'let source-type (owned-residual-value 'Int 2) result-type))))
  (define-values (final-config _rules)
    (apply values (run-compiled-execution-core artifact)))
  (match final-config
    [`(cfg ,value ,_heap ,_states ,tokens ,_trace)
     (check-equal? (length (collect-tokens value)) 1)
     (check-equal? (length tokens) 1)
     (check-equal? (map second tokens) '(Available))]))

(test-case "同名 Owned 残余の payload を両方向から join する"
  (define left
    '(Record ((a Int imm) (o (Owned (Union Int String)) imm))))
  (define right
    '(Record ((a Int imm) (o (Owned (Union Bool String)) imm))))
  (define expected '(Record ((a Int imm))))
  (define upper
    (normalize-type
     '(Record ((a Int imm)
               (o (Owned (Union Int (Union Bool String))) imm)))))
  (for ([members (in-list (list (list left right) (list right left)))])
    (check-equal? (row005-join members) upper)
    (void
     (check-compiled-source-core
      (elaborate-compiled
       (decompose-record-function members expected upper))))))

(test-case "同名 Owned 残余と非資源の残余は join できない"
  (define left
    '(Record ((a Int imm) (o (Owned Res) imm))))
  (define right '(Record ((a Int imm) (o Int imm))))
  (check-equal?
   (rejected-code
    `(Fn ((argument ,(normalize-type `(Union ,left ,right)))) Int (Own)
         (Let (r let ,record-a-int) (Move argument) 0)))
   (code 'type-mismatch)))

(test-case "必須欄と optional 欄の分解は optional を保つ"
  (define required '(Record ((a Int imm) (b Int imm))))
  (define optional '(Record ((a Int imm) (b Bool imm opt))))
  (define expected '(Record ((a Int imm))))
  (define upper
    (normalize-type
     '(Record ((a Int imm) (b (Union Int Bool) imm opt)))))
  (check-equal? (row005-join (list required optional)) upper)
  (void
   (check-compiled-source-core
    (elaborate-compiled
     (decompose-record-function (list required optional) expected upper)))))

(test-case "mut と imm の同名欄は imm へ join して作り直せる"
  (define mutable '(Record ((a Int imm) (b Int mut))))
  (define immutable '(Record ((a Int imm) (b Bool imm))))
  (define expected '(Record ((a Int imm))))
  (define upper
    (normalize-type '(Record ((a Int imm) (b (Union Int Bool) imm)))))
  (check-equal? (row005-join (list mutable immutable)) upper)
  (void
   (check-compiled-source-core
    (elaborate-compiled
     (decompose-record-function (list mutable immutable) expected upper)))))

(test-case "片方の成分だけにある Owned 残余は needs-proof で拒否する"
  (define left (owned-residual-record 'Int))
  (define right '(Record ((a Int imm) (b Bool imm))))
  (define source-type (normalize-type `(Union ,left ,right)))
  (check-equal?
   (rejected-code
    (owned-residual-program
     'let source-type (owned-residual-value 'Int 2)
     (row005-join (list left right))))
   (code 'owned-narrowing-needs-proof)))

(test-case "共有 Owned 残余を const で束縛すると残余で拒否する"
  (define left (owned-residual-record 'Int))
  (define right (owned-residual-record 'Bool))
  (define source-type (normalize-type `(Union ,left ,right)))
  (check-equal?
   (rejected-code
    (owned-residual-program
     'const source-type (owned-residual-value 'Int 2)
     (row005-join (list left right))))
   (code 'const-record-residual)))

(test-case "check の位置の Record リテラルを const で受けると残余で拒否する"
  ;; 余剰欄があるため既存の record-literal-checkable? は合成経路へ進み、
  ;; この const-record-residual の拒否は Task 4 より前から成立している。
  (check-equal?
   (rejected-code
    '(Let (r const (Record ((a Int imm))))
       (Rec ((a imm 1) (b imm 2)))
       0))
   (code 'const-record-residual)))

(test-case "check の位置の Record リテラルを let で受けると残余を読める"
  ;; 本体で残余の欄 b を読めることで、束縛型が残余を含むことを確かめる。
  (void
   (check-compiled-source-core
    (elaborate-compiled
     '(Let (r let (Record ((a Int imm))))
        (Rec ((a imm 1) (b imm 2)))
        (Proj r b))))))

(test-case "束縛の位置の inject は Owned の残余の損失を拒否する"
  (define source `(Record ((a Int imm) (o ,owned-leaf imm))))
  (define target (normalize-type '(Union (Record ((a Int imm))) Int)))
  (check-equal?
   (rejected-code
    (apply-function source
                    `(Rec ((a imm 1) (o imm ,owned-leaf-value)))
                    `(Let (u let ,target) (Move argument) 0)
                    'Int '(Own)))
   (code 'owned-narrowing-rejected)))

(test-case "束縛の位置の decompose の非 Record 分岐は Owned の残余の損失を拒否する"
  (define source `(Record ((a Int imm) (o ,owned-leaf imm))))
  (define usrc (normalize-type `(Union ,source Int)))
  (define target (normalize-type '(Union (Record ((a Int imm))) Int)))
  (check-equal?
   (rejected-code
    (apply-function usrc
                    `(Rec ((a imm 1) (o imm ,owned-leaf-value)))
                    `(Let (u let ,target) (Move argument) 0)
                    'Int '(Own)))
   (code 'owned-narrowing-rejected)))

(test-case "check の位置の恒等は狭い Union を Core の型に保つ"
  ;; Record の欄 a は check の位置であり、狭い型から広い Union への
  ;; convert は tag-compat? の恒等になる。
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function '(Union Int String) 1
                      '(Let (r let
                               (Record ((a (Union Int (Union String Bool)) imm))))
                            (Rec ((a imm argument)))
                            0)
                      'Int '()))))
  (define erased (erase-core (compiled-core artifact)))
  (match erased
    [`(Apply (Lam ,_ ,_ (,parameter)
                  (Handle ,_ ,_ (Scope ()
                                       (Let (,name let ,_) ,record ,_)))) ,_)
     (check-equal?
      (type-of record '() `((,parameter (Union Int String))))
      '(Record ((a (Union Int String) imm))))]
    [other (fail-check (format "check した Record の Core を見つけられない: ~s"
                               other))]))

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

(test-case "Owned 欄の payload widening は compat? と tag-compat? が受理する"
  (define source-payload int-or-bool)
  (define target-payload '(Union Int (Union Bool String)))
  (check-true (tag-compat? `(Owned ,source-payload) `(Owned ,target-payload)))
  ;; c2b1 では Owned の唯一の所有者が旧い view を保てないため、通常の互換も受理する。
  (check-true (compat? `(Owned ,source-payload) `(Owned ,target-payload)))
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

(test-case "Owned 欄の payload widening は束縛と check の両位置で受理する"
  (define source-type
    `(Record ((o (Owned ,int-or-bool) imm) (a Int imm))))
  (define expected-type
    '(Record ((o (Owned (Union Int (Union Bool String))) imm)
              (a (Union Int Bool) imm))))
  ;; tag を保つ Owned payload widening は束縛と check の両位置で受理する。
  (void
   (accepted
    `(Fn ((argument ,source-type)) Int (Own)
         (Let (r let ,expected-type) (Move argument) 0))))
  (void
   (accepted
    `(Fn ((argument ,source-type)) ,expected-type (Own)
         (Move argument)))))

(test-case "RecRewrite の entry binder は入力の symbol と衝突しない"
  (match-define (list core _ _)
    (accepted
     `(Fn ((union0 (Record ((a Int imm))))) Int ()
          (Apply (Fn ((r (Record ((a ,int-or-bool imm))))) Int () 0) union0))))
  (for ([entry (in-list (rec-rewrite-entries core))])
    (check-not-equal? (second entry) 'union0)))

(define a-int '(Record ((a Int imm))))
(define a-int-or-bool `(Record ((a ,int-or-bool imm))))
(define a-int-or-string '(Record ((a (Union Int String) imm))))

(test-case "tag-compat? の候補が無いとき作り直しで届く成分へ inject する"
  (define target `(Union ,a-int-or-bool String))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      `(Let (x const ,a-int) (Rec ((a imm 1)))
            (Let (u let ,target) x u)))))
  (check-equal? (compiled-type artifact) (normalize-type target))
  (check-equal? (count-nodes 'RecRewrite (erase-core (compiled-core artifact))) 1)
  (void (run-compiled-execution-core artifact)))

(test-case "作り直しで届く成分が 2 つなら ambiguous-union-member"
  (check-equal?
   (rejected-code
    `(Let (x const ,a-int) (Rec ((a imm 1)))
          (Let (u let (Union ,a-int-or-bool ,a-int-or-string)) x u)))
   (code 'ambiguous-union-member)))

(test-case "tag-compat? で受理される成分を作り直しの成分より先に選ぶ"
  (define wide '(Record ((a Int imm) (b Int imm))))
  (define rebuild-only
    `(Record ((a ,int-or-bool imm) (b Int imm))))
  ;; 第一段の候補集合が a-int だけであることを固定する。
  (check-true (tag-compat? wide a-int))
  (check-false (tag-compat? wide rebuild-only))
  (match-define (list core _ _)
    (accepted
     `(Let (x const ,wide) (Rec ((a imm 1) (b imm 2)))
           (Let (u let (Union ,a-int ,rebuild-only)) x u))))
  (check-equal? (count-nodes 'RecRewrite core) 0))

(test-case "OWN-004 で拒否される成分は作り直しの候補に数えない"
  (define source `(Record ((a Int imm) (o ,owned-leaf imm))))
  (define keeps-owned
    `(Record ((a (Union Int String) imm) (o ,owned-leaf imm))))
  (define target `(Union ,a-int-or-bool ,keeps-owned))
  (check-equal? (owned-narrowing-kind source a-int-or-bool compat?)
                `(drop-obligation ,source ,a-int-or-bool))
  (check-equal? (owned-narrowing-kind source keeps-owned compat?) 'ok)
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function source
                      `(Rec ((a imm 1) (o imm ,owned-leaf-value)))
                      `(Let (u let ,target) (Move argument) u)
                      (normalize-type target) '(Own)))))
  (check-true
   (for/or ([entry (in-list (rec-rewrite-entries
                             (erase-core (compiled-core artifact))))])
     (equal? (fifth entry) '(Union Int String))))
  (void (run-compiled-execution-core artifact)))

(test-case "作り直しの試行は生名の counter を進めない"
  ;; 試行が counter を戻さないと、同じ変換を本番で行うとき欠番が出る。
  (match-define (list core _ _)
    (accepted
     `(Let (x const ,a-int) (Rec ((a imm 1)))
           (Let (u let (Union ,a-int-or-bool String)) x u))))
  (define generated (generated-union-indices core))
  (check-equal? generated (range (length generated))))

(define owned-a-b `(Record ((a Int imm) (o ,owned-leaf imm) (b Bool imm))))
(define owned-a-c `(Record ((a Int imm) (o ,owned-leaf imm) (c String imm))))
(define owned-a `(Record ((a Int imm) (o ,owned-leaf imm))))

(test-case "entry の本体の Union から Record への分解は L の形になる"
  (define source `(Record ((p (Union ,owned-a-b ,owned-a-c) imm) (n Int imm))))
  (define target `(Record ((p ,owned-a imm) (n ,int-or-bool imm))))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function
       source
       `(Rec ((p imm (Rec ((a imm 1) (o imm ,owned-leaf-value)
                           (b imm (Construct true (Types))))))
              (n imm 2)))
       `(Let (r let ,target) (Move argument) r)
       target '(Own)))))
  (define core (erase-core (compiled-core artifact)))
  (check-true (entry-bodies-in-L? core) (format "L の外の形: ~s" core))
  (check-equal? (count-nodes 'UnionEliminate core) 1)
  (void (run-compiled-execution-core artifact)))

(test-case "entry の本体の Union 分解の中で作り直してから inject する"
  ;; decompose（Record でない分岐）→ 成分の inject の 2 の段 → 内側の RecRewrite。
  (define member-source `(Record ((a Int imm) (o ,owned-leaf imm))))
  (define member-target
    `(Record ((a ,int-or-bool imm) (o ,owned-leaf imm))))
  (define source `(Record ((p (Union ,member-source Bool) imm))))
  (define target `(Record ((p (Union ,member-target Bool) imm))))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function
       source
       `(Rec ((p imm (Rec ((a imm 1) (o imm ,owned-leaf-value))))))
       `(Let (r let ,target) (Move argument) r)
       target '(Own)))))
  (define core (erase-core (compiled-core artifact)))
  (check-true (entry-bodies-in-L? core) (format "L の外の形: ~s" core))
  (check-equal? (count-nodes 'RecRewrite core) 2)
  (define-values (final-config _rules)
    (apply values (run-compiled-execution-core artifact)))
  (match final-config
    [`(cfg ,value ,_heap ,_states ,tokens ,_trace)
     (check-equal? (length (collect-tokens value)) 1)
     (check-equal? (length tokens) 1)]))

(test-case "外の文脈の資源型の成分の枝は従来どおり encoding を作る"
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      (apply-function
       `(Union ,owned-a-b ,owned-a-c)
       `(Rec ((a imm 1) (o imm ,owned-leaf-value)
              (b imm (Construct true (Types)))))
       `(Let (r let ,owned-a) (Move argument) r)
       owned-a '(Own)))))
  (check-true
   (positive? (count-nodes 'Scope (erase-core (compiled-core artifact))))))

(define (union-inject-members tree)
  (cond
    [(not (pair? tree)) '()]
    [else
     (append
      (match tree
        [`(UnionInject ,_ ,member ,_) (list member)]
        [_ '()])
      (append-map union-inject-members tree))]))

(define optional-b-union
  '(Union (Record ((a Int imm) (b Int imm)))
          (Record ((a Int imm) (b Bool imm opt)))))

(test-case "Union の expected の Rec リテラルは optional の成分へ Absent を補って入る"
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      `(Apply (Fn ((argument ,optional-b-union)) Int () 0)
              (Rec ((a imm 1)))))))
  (check-equal?
   (union-inject-members (erase-core (compiled-core artifact)))
   (list '(Record ((a Int imm) (b Bool imm opt)))))
  (void (run-compiled-execution-core artifact)))

(test-case "Union の expected の Rec リテラルは optional の成分が 2 つあると曖昧で拒否する"
  (check-equal?
   (rejected-code
    '(Apply (Fn ((argument (Union (Record ((a Int imm) (b Bool imm opt)))
                                  (Record ((a Int imm) (c Int imm opt))))))
                Int () 0)
            (Rec ((a imm 1)))))
   (code 'ambiguous-union-member)))

(test-case "余剰の欄を持つ Rec リテラルは optional の成分を選ばず幅の成分へ入る"
  (define width-member '(Record ((a Int imm))))
  (define expected
    `(Union (Record ((a Int imm) (b Bool imm opt))) ,width-member))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      `(Apply (Fn ((argument ,expected)) Int () 0)
              (Rec ((a imm 1) (c imm 2)))))))
  (check-equal?
   (union-inject-members (erase-core (compiled-core artifact)))
   (list width-member)))

(test-case "余剰の欄を持つ Rec リテラルは optional の成分しか無ければ拒否する"
  (check-equal?
   (rejected-code
    '(Apply (Fn ((argument (Union (Record ((a Int imm) (b Bool imm opt)))
                                  Int)))
                       Int () 0)
            (Rec ((a imm 1) (c imm 2)))))
   (code 'type-mismatch)))

(test-case "リテラル候補と作り直し候補の両方へ届く Rec は曖昧で拒否する"
  (define rebuild-member '(Record ((a (Union Int Bool) imm))))
  (define literal-member
    '(Record ((a Int imm) (c Int imm) (d Bool imm opt))))
  (define source-type '(Record ((a Int imm) (c Int imm))))
  (check-equal? (owned-narrowing-kind source-type rebuild-member compat?) 'ok)
  (check-false (tag-compat? source-type rebuild-member))
  (check-false (tag-compat? source-type literal-member))
  (check-equal?
   (rejected-code
    `(Apply (Fn ((argument (Union ,rebuild-member ,literal-member)))
                Int () 0)
            (Rec ((a imm 1) (c imm 2)))))
   (code 'ambiguous-union-member)))

(test-case "候補試行で合成に失敗する欄も expected に check できれば Union へ入る"
  (define expected
    '(Union (Record ((a Int imm) (option (Option Int) imm))) String))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      `(Apply (Fn ((argument ,expected)) Int () 0)
              (Rec ((a imm 1) (option imm (Construct some 1))))))))
  (check-equal?
   (union-inject-members (erase-core (compiled-core artifact)))
   (list '(Record ((a Int imm) (option (Option Int) imm)))))
  (void (run-compiled-execution-core artifact)))

(test-case "リテラル候補の試行は union-counter を本番へ漏らさない"
  (define source-union
    '(Union (Record ((a Int imm) (b Bool imm)))
            (Record ((a Int imm) (c Bool imm)))))
  (define expected
    '(Union (Record ((payload (Record ((a Int imm))) imm) (bad Bool imm)))
            (Record ((payload (Record ((a Int imm))) imm) (bad Int imm)))))
  (define artifact
    (check-compiled-source-core
     (elaborate-compiled
      `(Fn ((u ,source-union)) ,expected ()
           (Rec ((payload imm u) (bad imm 1)))))))
  (define generated
    (generated-union-indices (erase-core (compiled-core artifact))))
  (check-not-false (member 0 generated))
  (check-equal? generated (range (length generated))))

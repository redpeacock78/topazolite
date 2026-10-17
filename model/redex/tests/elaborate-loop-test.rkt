#lang racket

(require rackunit
         racket/list
         racket/set
         redex/reduction-semantics
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../typing.rkt"
         "../type-equiv.rkt"
         "../ucore.rkt")

(define (elaborated-core expression)
  (match (elab expression)
    [(list core type row callables)
     (check-equal? (core-type-of/diagnostic (erase-core core) '() callables)
                   (list type row))
     (list (erase-core core) type row callables)]
    [other (fail-check (format "elaboration success を期待したが ~s" other))]))

(define (loop-form body [arguments '()] [result-type 'Unit]
                   [parameters '()] [function 'loop])
  `(Loop ,function ,parameters ,result-type () ,body ,arguments))

(define (loop-shape-error? failure)
  (and (exn:fail? failure)
       (regexp-match? #rx"loop 印の形の違反" (exn-message failure))))

(define (check-loop-shape-error expression)
  (check-exn loop-shape-error? (λ () (elab expression))
             (format "loop 印の形の内部エラーを期待した: ~s" expression)))

(define (loop-program scrutinee loop-expression after
                      #:declared [declared '(Record ((name String imm)))]
                      #:initial [initial '(Rec ((name imm "A") (id imm 1)))]
                      #:return [return-type 'String]
                      #:row [row '(Partial Mutation)])
  `(Apply
    (Fn ((flag Bool) (g (NFn () Bool () ())))
        ,return-type ,row
      (Let (value mut ,declared) ,initial
        (Let (ignored const Unit) ,loop-expression ,after)))
    (Construct true (Types))
    (Fn () Bool () (Construct true (Types)))))

(define (elab-error-id expression)
  (match (elab expression)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (count-form tree tag)
  (+ (if (and (pair? tree) (eq? (car tree) tag)) 1 0)
     (if (pair? tree)
         (apply + (map (λ (part) (count-form part tag)) tree))
         0)))

(define (contains-reassign-view? tree type)
  (cond
    [(and (list? tree) (= (length tree) 4) (eq? (first tree) 'Reassign))
     (type-equiv? (third tree) type)]
    [(pair? tree) (ormap (λ (part) (contains-reassign-view? part type)) tree)]
    [else #f]))

(define (callable-references tree)
  (define here
    (match tree
      [`(Lam ,_ ,callable ,_ ,_) (list callable)]
      [`(Recur ,callable ,_ ,_ ,_ ,_) (list callable)]
      [_ '()]))
  (append here
          (if (pair? tree)
              (append-map callable-references tree)
              '())))

(define (recur-body-in tree)
  (or (match tree
        [`(Recur ,_ ,_ ,_ ,body ,_) body]
        [_ #f])
      (and (pair? tree)
           (or (recur-body-in (car tree))
               (recur-body-in (cdr tree))))))

(define (normalize-loop-fresh-names tree)
  (cond
    [(symbol? tree)
     (define text (symbol->string tree))
     (cond
       [(regexp-match? #rx"^union[0-9]+$" text) 'union]
       [(regexp-match? #rx"^boundary[0-9]+$" text) 'boundary]
       [else
        (string->symbol (regexp-replace #rx"⟨[0-9]+⟩$" text ""))])]
    [(pair? tree)
     (cons (normalize-loop-fresh-names (car tree))
           (normalize-loop-fresh-names (cdr tree)))]
    [else tree]))

(define (normalize-reassign-values tree)
  (match tree
    [`(Reassign ,target ,view ,_rhs) `(Reassign ,target ,view rhs)]
    [(cons head tail)
     (cons (normalize-reassign-values head)
           (normalize-reassign-values tail))]
    [_ tree]))

(test-case "Loop は UCore と UCore+ の形を持ち annotate と erase が往復する"
  (define raw '(Loop loop ((x Int)) Int () x (initial)))
  (check-true (redex-match? UCore e raw))
  (define annotated (annotate-surface raw))
  (check-true (redex-match? UCore+ e annotated))
  (check-equal? (erase-surface annotated) raw))

(test-case "loop 印は Recur と初回 Apply と同じ Core へ elaborate される"
  (define body
    '(Let (changed const Unit)
          (Reassign value (Rec ((name imm "B"))))
       (Apply loop)))
  (define loop-expression
    `(Let (value mut (Record ((name String imm)))) (Rec ((name imm "A")))
       (Loop loop () Unit (Partial Mutation) ,body ())))
  (define recur-expression
    `(Let (value mut (Record ((name String imm)))) (Rec ((name imm "A")))
       (Recur loop () Unit (Partial Mutation) ,body (Apply loop))))
  (check-equal? (elaborated-core loop-expression)
                (elaborated-core recur-expression)))

(test-case "loop 印の back-edge から shape を広げ本検査で受理する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define body
      `(Eliminate ,scrutinee
         ((true () ->
           (Let (changed const Unit)
                (Reassign value
                          (Rec ((name imm "B")
                                (active imm (Construct true (Types))))))
             (Apply loop)))
          (false () -> unit))))
    (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
    (define recur `(Recur loop () Unit (Partial Mutation) ,body (Apply loop)))
    (define program (loop-program scrutinee marker '(Proj value name)))
    (define inaccessible
      (loop-program scrutinee marker '(Proj value active)))
    (check-equal? (second (elaborated-core program)) 'String)
    (check-equal? (elab-error-id inaccessible) "E-RCD-004")
    (check-equal?
     (elab-error-id (loop-program scrutinee recur '(Proj value name)))
     "E-VAR-013")))

(test-case "loop の有限な余剰欄 Union は三成員へ収束する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define transitions
      `(Let (from-relay const Unit)
            (Reassign value
                      (Rec ((name imm "V") (tag imm (Proj relay tag)))))
         (Let (from-source const Unit)
              (Reassign relay
                        (Rec ((name imm "R") (tag imm (Proj source tag)))))
           (Apply loop))))
    (define body
      `(Eliminate ,scrutinee
         ((true () -> ,transitions)
          (false () -> unit))))
    (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
    (define post-loop
      '(Eliminate (Proj value tag)
         ((Int i -> unit) (String s -> unit) (Bool b -> unit))))
    (define program
      `(Apply
        (Fn ((flag Bool) (g (NFn () Bool () ()))
             (seed (Union Int String)))
            Unit (Partial Mutation)
          (Let (value mut (Record ((name String imm))))
            (Rec ((name imm "A") (tag imm seed)))
            (Let (relay mut (Record ((name String imm))))
                 (Rec ((name imm "S") (tag imm "S")))
              (Let (source const (Record ((name String imm) (tag Bool imm))))
                   (Rec ((name imm "B") (tag imm (Construct true (Types)))))
                (Let (ignored const Unit) ,marker ,post-loop)))))
        (Construct true (Types))
        (Fn () Bool () (Construct true (Types)))
        1))
    (match (elaborated-core program)
      [(list core type _row _callables)
       (check-equal? type 'Unit)
       ;; 2 本文代入に、value と relay の入口 view 再構成が 1 件ずつ加わる。
       (check-equal? (count-form core 'Reassign) 4)])))

(test-case "loop の自己包含 Record は余剰欄を拡幅して停止する"
  (define body
    '(Let (changed const Unit)
          (Reassign value (Rec ((name imm "a") (child imm value))))
       (Apply loop)))
  (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define initial '(Rec ((name imm "A") (child imm 1))))
    (define name-program
      (loop-program scrutinee marker '(Proj value name) #:initial initial))
    (define child-program
      (loop-program scrutinee marker '(Proj value child) #:initial initial))
    (check-equal? (second (elaborated-core name-program)) 'String)
    (check-equal? (elab-error-id child-program) "E-RCD-004")))

(test-case "loop の data wrapper 内の自己値も停止して受理される"
  (define body
    '(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm "a")
                          (child imm
                                 (Construct some
                                            (Types (Record ((name String imm))))
                                            value)))))
       (Apply loop)))
  (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define initial
      '(Rec ((name imm "A")
             (child imm (Construct some (Types Int) 1)))))
    (define program
      (loop-program scrutinee marker '(Proj value name) #:initial initial))
    (check-equal? (second (elaborated-core program)) 'String)))

(test-case "loop の入れ子 Record は停止し名前だけを残す"
  (define body
    '(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm (Proj value name))
                          (id imm (Rec ((child imm value)))))))
       (Apply loop)))
  (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define initial '(Rec ((name imm "A") (id imm 1))))
    (define name-program
      (loop-program scrutinee marker '(Proj value name) #:initial initial))
    (define id-program
      (loop-program scrutinee marker '(Proj value id) #:initial initial))
    (check-equal? (second (elaborated-core name-program)) 'String)
    ;; 本検査後も id は C* から除かれているため、この対照形は拒否される。
    (check-equal? (elab-error-id id-program) "E-RCD-004")))

(test-case "loop の id を読む自己包含形は C* の本検査で拒否する"
  (define body
    '(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm (Proj value name))
                          (id imm (Rec ((child imm (Proj value id))))))))
       (Apply loop)))
  (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (check-equal?
     (elab-error-id
      (loop-program scrutinee marker '(Proj value name)
                    #:initial '(Rec ((name imm "A") (id imm 1)))))
     "E-RCD-004")))

(test-case "loop の余剰欄に Owned を含む値は loop 印の前に拒否する"
  (define (resource-program scrutinee extra-value)
    `(Apply
      (Fn ((make (NFn () (Owned Int) (Own) ()))
           (flag Bool)
           (g (NFn () Bool () ())))
        String (Partial Mutation Own)
        (Let (value mut (Record ((name String imm))))
             (Rec ((name imm "A")))
          (Let (ignored const Unit)
               (Loop loop () Unit (Partial Mutation Own)
                 (Eliminate ,scrutinee
                   ((true () ->
                     (Let (changed const Unit)
                          (Reassign value
                                    (Rec ((name imm "B") (extra imm ,extra-value))))
                       (Apply loop)))
                    (false () -> unit)))
                 ())
            (Proj value name))))
      (Fn () (Owned Int) (Own) (Apply acquire 13))
      (Construct true (Types))
      (Fn () Bool () (Construct true (Types)))))
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define direct (resource-program scrutinee '(Apply make)))
    (check-equal? (elab-error-id direct) "E-OWN-007")
    (check-equal?
     (elab-error-id
      (resource-program
       scrutinee
       '(Construct some (Types (Owned Int)) (Apply make))))
     "E-VAR-012")))

(test-case "Return 脱出は C* の view で合流する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define body
      `(Eliminate ,scrutinee
         ((true () ->
           (Let (changed const Unit)
                (Reassign value
                          (Rec ((name imm "B") (id imm 2))))
             (Return value)))
          (false () ->
           (Let (changed const Unit)
                (Reassign value
                          (Rec ((name imm "B")
                                (id imm (Rec ((child imm 1)))))))
             unit)))))
    (define marker `(Loop loop () Unit (Return Partial Mutation) ,body ()))
    (define program
      (loop-program scrutinee marker '(Rec ((name imm "done")))
                    #:declared '(Record ((name String imm)))
                    #:initial '(Rec ((name imm "A") (id imm 1)))
                    #:return '(Record ((name String imm)))))
    (define-values (core type _row _callables)
      (apply values (elaborated-core program)))
    (check-true (type-equiv? type '(Record ((name String imm)))))
    (check-true
     (contains-reassign-view? core '(Record ((name String imm)))))))

(test-case "C* の下で読めない欄は本検査で拒否する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define body
      `(Eliminate ,scrutinee
         ((true () ->
           (Let (observed const Int) (Proj value id)
             (Let (changed const Unit)
                  (Reassign value (Rec ((name imm "B"))))
               (Apply loop))))
          (false () -> unit))))
    (define expression
      (loop-program scrutinee
                    `(Loop loop () Unit (Partial Mutation) ,body ())
                    '(Proj value name)))
    (check-equal? (elab-error-id expression) "E-RCD-004")))

(test-case "正常出口が無い loop は C0 を保ち view 再代入を挿入しない"
  (define expression
    '(Apply
      (Fn ((flag Bool) (g (NFn () Bool () ()))) Int (Partial)
        (Let (value mut (Record ((name String imm))))
             (Rec ((name imm "A") (id imm 1)))
          (Loop loop () Int (Return Partial) (Return (Proj value id)) ())))
      (Construct true (Types))
      (Fn () Bool () (Construct true (Types)))))
  (match (elab expression)
    [(list core type row callables)
     (check-equal? type 'Int)
     (check-equal? (core-type-of/diagnostic (erase-core core) '() callables)
                   (list type row))
     (check-equal? (count-form (erase-core core) 'Reassign) 0)]
    [other (fail-check (format "脱出だけの loop を期待したが ~s" other))]))

(test-case "T の欄と同じ幅で loop 内の余剰欄を代入できる"
  (define body
    '(Let (changed const Unit)
          (Reassign value (Rec ((name imm "B") (id imm 1))))
       (Apply loop)))
  (define expression
    (loop-program 'flag
                  `(Loop loop () Unit (Partial Mutation) ,body ())
                  '(Proj value name)
                  #:initial '(Rec ((name imm "A")))))
  (check-equal? (second (elaborated-core expression)) 'String))

(test-case "loop 内で作った closure は C* の view を pin する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define closure-type '(NFn () String () ()))
    (define body
      `(Eliminate ,scrutinee
         ((true () ->
           (Let (changed const Unit)
                (Reassign value
                          (Rec ((name imm "B")
                                (active imm (Construct true (Types))))))
             (Let (closure const ,closure-type)
                  (Fn () String () (Proj value name))
               (Let (changed-again const Unit)
                    (Reassign value (Rec ((name imm "C"))))
                 unit))))
          (false () ->
           (Let (changed const Unit)
                (Reassign value
                          (Rec ((name imm "D")
                                (active imm (Construct false (Types))))))
             (Apply loop))))))
    (define expression
      (loop-program scrutinee
                    `(Loop loop () Unit (Partial Mutation) ,body ())
                    '(Proj value name)))
    (check-equal? (second (elaborated-core expression)) 'String)
    (check-equal?
     (elab-error-id
      (loop-program scrutinee
                    `(Loop loop () Unit (Partial Mutation) ,body ())
                    '(Proj value active)))
     "E-RCD-004")))

(test-case "loop 印の外側にある pin は loop の view を固定する"
  (define closure-type '(NFn () Int () ()))
  (define (with-outer-pin loop-expression)
    `(Apply
      (Fn ((flag Bool) (g (NFn () Bool () ()))) Int (Partial Mutation)
        (Let (value mut (Record ((name String imm))))
             (Rec ((name imm "A") (id imm 1)))
          (Let (closure const ,closure-type)
               (Fn () Int () (Proj value id))
            (Let (ignored const Unit)
                 ,loop-expression
              (Apply closure)))))
      (Construct true (Types))
      (Fn () Bool () (Construct true (Types)))))
  (define compatible-body
    '(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm "B") (id imm 2)
                          (active imm (Construct true (Types))))))
       (Apply loop)))
  (define expression
    (with-outer-pin
     `(Loop loop () Unit (Partial Mutation) ,compatible-body ())))
  (check-equal? (second (elaborated-core expression)) 'Int)
  (define incompatible-body
    '(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm "B")
                          (active imm (Construct true (Types))))))
       (Apply loop)))
  (define incompatible
    (with-outer-pin
     `(Loop loop () Unit (Partial Mutation) ,incompatible-body ())))
  (check-equal? (elab-error-id incompatible) "E-VAR-013"))

(test-case "loop 試行の callable と fresh 名は C0 での Recur と一致する"
  (define closure-type '(NFn () String () ()))
  (define body
    `(Let (closure const ,closure-type)
          (Fn () String () (Proj value name))
       (Apply loop)))
  (define loop-expression
    (loop-program 'flag
                  `(Loop loop () Unit (Partial) ,body ())
                  '(Proj value name)
                  #:row '(Partial)))
  (define recur-expression
    (loop-program 'flag
                  `(Recur loop () Unit (Partial) ,body (Apply loop))
                  '(Proj value name)
                  #:row '(Partial)))
  (check-equal? (elaborated-core loop-expression)
                (elaborated-core recur-expression)))

(test-case "C* と異なる本体でも callable 表は出力 Core と一致する"
  (define closure-type '(NFn () String () ()))
  (define body
    `(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm "B")
                          (active imm (Construct true (Types))))))
       (Let (closure const ,closure-type)
            (Fn () String () (Proj value name))
         (Apply loop))))
  (match (elab
          (loop-program 'flag
                        `(Loop loop () Unit (Partial Mutation) ,body ())
                        '(Proj value name)))
    [(list core type row callables)
     (check-equal? (core-type-of/diagnostic (erase-core core) '() callables)
                   (list type row))
     (check-equal? (sort (map first callables) symbol<?)
                   (sort (remove-duplicates
                          (callable-references (erase-core core)))
                         symbol<?))]
    [other (fail-check (format "C* の loop を期待したが ~s" other))]))

(test-case "loop の入れ子でも外側の trial の pin 抑止を保つ"
  (define inner-body
    '(Let (changed const Unit)
          (Reassign value
                    (Rec ((name imm "B")
                          (active imm (Construct true (Types))))))
       (Apply inner)))
  (define outer-body
    `(Let (inner-result const Unit)
          (Loop inner () Unit (Partial Mutation) ,inner-body ())
       (Apply outer)))
  (define expression
    (loop-program 'flag
                  `(Loop outer () Unit (Partial Mutation) ,outer-body ())
                  '(Proj value name)))
  (check-equal? (second (elaborated-core expression)) 'String))

(test-case "同名の内側 mut binder は loop の対象を shadow する"
  (define body
    '(Let (inner-result const Unit)
          (Let (value mut (Record ((name String imm))))
               (Rec ((name imm "inner")))
            (Let (changed const Unit)
                 (Reassign value
                           (Rec ((name imm "B")
                                 (active imm (Construct true (Types))))))
              unit))
       (Let (observed const String) (Proj value name)
         (Apply loop))))
  (define expression
    (loop-program 'flag
                  `(Loop loop () Unit (Partial Mutation) ,body ())
                  '(Proj value name)))
  (check-equal? (second (elaborated-core expression)) 'String))

(test-case "閉包捕捉の間で shape を変える枝も C* で受理する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define closure-type '(NFn () String () ()))
    (define body
      `(Eliminate ,scrutinee
         ((true () ->
           (Let (changed const Unit)
                (Reassign value
                          (Rec ((name imm "B")
                                (active imm (Construct true (Types))))))
             (Let (closure const ,closure-type)
                  (Fn () String () (Proj value name))
               (Let (changed-again const Unit)
                    (Reassign value
                              (Rec ((name imm "C") (id imm 2))))
                 unit))))
          (false () ->
           (Let (changed const Unit)
                (Reassign value
                          (Rec ((name imm "D")
                                (active imm (Construct false (Types))))))
             (Apply loop))))))
    (define loop-expression
      `(Loop loop () Unit (Partial Mutation) ,body ()))
    (check-equal?
     (second (elaborated-core
              (loop-program scrutinee loop-expression '(Proj value name))))
     'String)
    (check-equal?
     (elab-error-id
     (loop-program scrutinee loop-expression '(Proj value active)))
     "E-RCD-004")))

(test-case "試行の fallthrough と failure Return は成功・失敗後に漏れない"
  (define narrative
    '(NarrativeExpr
      (Eliminate flag
        ((true () -> unit)
         (false () -> unit)))))
  (define success-body
    `(Let (matched const Unit) ,narrative
       (Let (bound const (Option Unit))
            (NarrativeExpr
             (TryBind ignored
                      (Construct some (Types Unit) unit)
                      (Construct some (Types Unit) unit)))
         (Apply loop))))
  (define (wrap loop-expression body)
    `(Apply
      (Fn ((flag Bool) (g (NFn () Bool () ()))) (Option Unit) (Partial)
        (Let (value mut (Record ((name String imm))))
             (Rec ((name imm "A") (id imm 1)))
          (Let (ignored const Unit)
               ,(match loop-expression
                  ['loop `(Loop loop () Unit (Partial) ,body ())]
                  ['recur `(Recur loop () Unit (Partial) ,body (Apply loop))])
            (Return (Construct some (Types Unit) unit)))))
      (Construct true (Types))
      (Fn () Bool () (Construct true (Types)))))
  (check-equal?
   (elaborated-core (wrap 'loop success-body))
   (elaborated-core (wrap 'recur success-body)))
  (define failing-body
    `(Let (matched const Unit) ,narrative
       (Let (bound const (Option Unit))
            (NarrativeExpr
             (TryBind ignored
                      (Construct some (Types Unit) unit)
                      (Construct some (Types Unit) unit)))
         (Let (missing const Int) (Proj value missing)
           (Apply loop)))))
  (check-equal? (elab-error-id (wrap 'loop failing-body)) "E-RCD-004")
  (check-equal? (elab-error-id (wrap 'recur failing-body)) "E-RCD-004"))

(test-case "loop 試行は probe 中の注釈つき Let を受け止め後続の flow を使う"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define probed-when
      '(NarrativeExpr
        (Let (inner const Unit)
             (Eliminate (Proj value id)
               ((Int i -> unit) (String s -> unit)))
          (Return unit))))
    (define trial-rhs
      `(Let (edge const Unit) (Apply loop) ,probed-when))
    (define body
      `(Let (%stmt const Unit) ,trial-rhs
         (Let (changed const Unit)
              (Reassign value (Rec ((name imm "B") (id imm "s"))))
           (Apply loop))))
    (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
    (define after
      '(Eliminate (Proj value id)
         ((Int i -> unit) (String s -> unit))))
    (define loop-result
      (elaborated-core
       (loop-program scrutinee marker after #:return 'Unit)))
    (check-equal?
     (second loop-result)
     'Unit)
    (define recur-result
      (elaborated-core
       (loop-program
        scrutinee
        `(Recur loop () Unit (Partial Mutation) ,body (Apply loop))
        after #:declared '(Record ((name String imm)
                                  (id (Union Int String) imm)))
        #:return 'Unit)))
    ;; C0→C* の前置変換、Reassign RHS の再構成形、fresh 名を除き、
    ;; Recur 本体の構造は C* で直接書いた Recur と一致する。
    (check-equal?
     (normalize-loop-fresh-names
      (normalize-reassign-values (recur-body-in (first loop-result))))
     (normalize-loop-fresh-names
      (normalize-reassign-values (recur-body-in (first recur-result)))))
    (check-equal? (rest loop-result) (rest recur-result))
    (define unannotated-body
      `(Let (statement const) ,trial-rhs
         (Let (changed const Unit)
              (Reassign value (Rec ((name imm "B") (id imm "s"))))
           (Apply loop))))
    (define unannotated-marker
      `(Loop loop () Unit (Partial Mutation) ,unannotated-body ()))
    (check-equal?
     (elab-error-id
     (loop-program scrutinee unannotated-marker after #:return 'Unit))
     "E-TYP-029")))

(test-case "loop 試行は when を持つ注釈付き Let を飛ばし C* で本検査する"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define when-expression
      '(NarrativeExpr
        (Let (matched-value const Unit)
             (Eliminate (Proj value id)
               ((Int i -> unit) (String s -> unit)))
          (Return unit))))
    (define body
      `(Let (edge const Unit) (Apply loop)
         (Let (matched const Unit) ,when-expression
           (Let (changed const Unit)
                (Reassign value (Rec ((name imm "B") (id imm "s"))))
             (Apply loop)))))
    (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
    (define after
      '(Eliminate (Proj value id)
         ((Int i -> unit) (String s -> unit))))
    (check-equal?
     (second (elaborated-core
              (loop-program scrutinee marker after #:return 'Unit)))
     'Unit)
    (define unannotated-body
      `(Let (edge const Unit) (Apply loop)
         (Let matched ,when-expression
           (Let (changed const Unit)
                (Reassign value (Rec ((name imm "B") (id imm "s"))))
             (Apply loop)))))
    (check-equal?
     (elab-error-id
      (loop-program scrutinee
                    `(Loop loop () Unit (Partial Mutation)
                       ,unannotated-body ())
                    after #:return 'Unit))
     "E-TYP-029")))

(test-case "loop 試行の診断 catch は escape と when box を戻し back-edge を残す"
  (for ([scrutinee (in-list '(flag (Apply g)))])
    (define attempt
      '(Eliminate flag
         ((true () ->
           (Let (tried const (Option Unit))
                (NarrativeExpr
                 (TryBind ignored
                          (Construct some (Types Unit) unit)
                          (Construct some (Types Unit) unit)))
             (Return unit)))
          (false () -> (BlockBody unit)))))
    (define narrative
      `(NarrativeExpr
        (Eliminate ,scrutinee
          ((true () -> (BlockBody unit))
           (false () ->
             (BlockBody
              (Let (caught const Unit)
                   (Let (before const Unit) ,attempt
                     (Eliminate (Proj value id)
                       ((Int i -> unit) (String s -> unit))))
                unit)))))))
    (define body
      `(Let (%stmt const Unit)
            (Let (edge const Unit) (Apply loop) ,narrative)
         (Let (changed const Unit)
              (Reassign value (Rec ((name imm "B") (id imm "s"))))
           (Apply loop))))
    (define marker `(Loop loop () Unit (Partial Mutation) ,body ()))
    (define after
      '(Eliminate (Proj value id)
         ((Int i -> unit) (String s -> unit))))
    (check-equal?
     (second (elaborated-core
              (loop-program scrutinee marker after #:return 'Unit)))
     'Unit)))

(test-case "安定した C0 を保ち、loop の前後に不要な Reassign を挿さない"
  (define body
    '(Let (observed const Int) (Proj value id)
       (Let (changed const Unit)
            (Reassign value
                      (Rec ((name imm "B") (id imm 1))))
         (Apply loop))))
  (define expression
    (loop-program 'flag
                  `(Loop loop () Unit (Partial Mutation) ,body ())
                  '(Proj value id)
                  #:return 'Int))
  (match (elab expression)
    [(list core type row callables)
     (check-equal? type 'Int)
     (check-equal? (core-type-of/diagnostic (erase-core core) '() callables)
                   (list type row))
     (check-equal? (count-form (erase-core core) 'Reassign) 1)]
    [other (fail-check (format "C0 が安定する loop を期待したが ~s" other))]))

(test-case "loop 印の初回 Apply は変数と literal の引数を既存 Recur へ渡す"
  (for ([argument (in-list '(initial 7))])
    (define loop-expression
      `(Let (initial const Int) 7
         (Loop loop ((item Int)) Int () item (,argument))))
    (define recur-expression
      `(Let (initial const Int) 7
         (Recur loop ((item Int)) Int () item (Apply loop ,argument))))
    (check-equal? (elaborated-core loop-expression)
                  (elaborated-core recur-expression))))

(test-case "loop 印の仮引数は関数名を shadow できない"
  (check-loop-shape-error (loop-form 'unit '() 'Unit '((loop Unit)))))

(test-case "loop 印は本体に自己呼出しがなくても既存 Recur へ elaborate される"
  (define loop-expression '(Loop loop () Unit () unit ()))
  (define recur-expression '(Recur loop () Unit () unit (Apply loop)))
  (check-equal? (elaborated-core loop-expression)
                (elaborated-core recur-expression)))

(test-case "loop 印は不正な初回引数と関数参照を拒否する"
  (check-loop-shape-error
   (loop-form '(Apply loop) '((Apply g))))
  (check-loop-shape-error
   (loop-form '(Apply loop) '(loop))))

(test-case "loop 印は本体の関数値利用と間接呼出しを拒否する"
  (check-loop-shape-error
   (loop-form '(Let (h const Unit) loop unit)))
  (check-loop-shape-error
   (loop-form '(Apply (Let (h const Unit) loop h))))
  (check-loop-shape-error
   (loop-form '(Apply g loop)))
  (check-loop-shape-error
   (loop-form '(IfSome ((loop unit)))))
  (check-loop-shape-error
   (loop-form '(Apply loop) '() '#:infer)))

(test-case "loop 印の #:infer 禁止は自己呼出しの有無に依存しない"
  (check-loop-shape-error (loop-form 'unit '() '#:infer)))

(test-case "loop 印は遅延した callable の内側の呼出しを拒否する"
  (for ([body
         (in-list
          (list '(Fn () Unit () (Apply loop))
                '(Recur inner () Unit () (Apply loop) unit)
                '(FnDecl inner () Unit () (Apply loop) unit)
                '(Loop inner () Unit () (Apply loop) ())
                '(Curry identity (Apply loop))))])
    (check-loop-shape-error (loop-form body))))

(test-case "loop 印の関数名は全ての束縛形で shadow できない"
  (for ([body
         (in-list
          (list '(Let (loop const Unit) unit unit)
                '(Fn ((loop Unit)) Unit () unit)
                '(Recur loop () Unit () unit unit)
                '(Recur inner ((loop Unit)) Unit () unit unit)
                '(FnDecl loop () Unit () unit unit)
                '(FnDecl inner ((loop Unit)) Unit () unit unit)
                '(Loop loop () Unit () unit ())
                '(Loop inner ((loop Unit)) Unit () unit (unit))
                '(Eliminate (Construct true (Types))
                            ((true (loop) -> unit)))
                '(Eliminate 1 ((Int loop -> unit)))
                '(TryBind loop (Construct some (Types Int) 1) unit)))])
    (check-loop-shape-error (loop-form body))))

(test-case "loop 印の関数名と仮引数は予約名として検査される"
  (define reserved (string->symbol "loop⟨1⟩"))
  (for ([expression
         (in-list
          (list `(Loop ,reserved () Unit () unit ())
                `(Loop loop ((,reserved Int)) Int () ,reserved (,reserved))))])
    (for ([term (in-list (list expression (annotate-surface expression)))])
      (match (elab term)
        [`(err ,diagnostic)
         (check-equal? (diagnostic-id diagnostic) "E-SYN-005")]
        [other (fail-check (format "予約束縛子の拒否を期待したが ~s" other))]))))

(test-case "Loop の本体で捕捉した外側 mut は closure 作成後も pin される"
  (define expression
    '(Let (value mut (Record ((name String imm))))
          (Rec ((name imm "A") (id imm 1)))
       (Let (f const)
            (Fn ((ignored Int)) String ()
                (Loop inner () String () (Proj value name) ()))
         (Reassign value
                   (Rec ((name imm "B")
                         (active imm (Construct true (Types)))))))))
  (match (elab expression)
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-VAR-013" (format "~s" diagnostic))]
    [other (fail-check (format "Loop 内の捕捉による pin を期待したが ~s" other))]))

(test-case "Loop の初回引数に現れる外側 mut も closure の捕捉に含める"
  (define expression
    '(Let (value mut (Record ((name String imm))))
          (Rec ((name imm "A") (id imm 1)))
       (Let (f const)
            (Fn ((ignored Int)) String ()
                (Loop inner ((item (Record ((name String imm))))) String ()
                      (Proj item name) (value)))
         (Reassign value
                   (Rec ((name imm "B")
                         (active imm (Construct true (Types)))))))))
  (match (elab expression)
    [`(err ,diagnostic)
     (check-equal? (diagnostic-id diagnostic) "E-VAR-013" (format "~s" diagnostic))]
    [other (fail-check (format "Loop の初回引数による pin を期待したが ~s" other))]))

(test-case "loop-join は候補が無いか入力が収まらないとき T へ戻る"
  (define declared '(Record ((name String imm))))
  (define candidate '(Record ((name String imm) (id Int imm))))
  (check-equal? (loop-join (list candidate candidate) declared '()
                           (λ (_input _candidate) #t))
                (normalize-type candidate))
  (check-equal? (loop-join (list candidate) declared '()
                           (λ (_input _candidate) #f))
                declared)
  (check-equal? (loop-join (list candidate '(Record ((other Bool imm))))
                           'Never '() (λ (_input _candidate) #t))
                'Never)
  (check-equal? (loop-join '(Int String) '(Union Int String) '()
                           (λ (_input _candidate) #t))
                '(Union Int String)))

(test-case "loop-type-depth は Union を除く各型構成子を一段として数える"
  (check-equal? (loop-type-depth 'Int) 0)
  (check-equal? (loop-type-depth '(Record ((a Int imm)))) 1)
  (check-equal? (loop-type-depth '(Union Int String)) 0)
  (check-equal? (loop-type-depth '(Data Box ((Record ((a Int imm)))))) 2)
  (check-equal? (loop-type-depth '(NFn ((Record ((a Int imm)))) Unit () () () User)) 2)
  (check-equal? (loop-type-depth '(Owned (Record ((a Int imm))))) 2)
  (check-equal? (loop-type-depth '(Borrowed (Union Int String) r)) 1))

(test-case "loop-cycle? は正規化で同値な型を履歴から検出する"
  (check-true
   (loop-cycle? '(Union String Int)
                (list '(Union Int String) '(Record ()))))
  (check-false (loop-cycle? '(Record ((a Int imm))) '())))

(test-case "loop-excess-fields は Union の対応 Record に共通する欄だけを除外する"
  (define declared
    '(Record ((f (Union (Record ((a Int imm) (k Int imm)))
                        (Record ((b Int imm) (k String imm)))) imm))))
  (define view
    '(Record ((f (Record ((a Int imm) (b Int imm) (k Int imm))) imm))))
  (define fields (loop-excess-fields view declared))
  (check-equal? (map loop-excess-key-field fields) '(b))
  (check-equal? (loop-excess-key-path (first fields)) '((field f)))
  (check-equal? (loop-excess-key-correspondence (first fields))
                '(((field f) (union 0)))))

(test-case "loop-widen は一方の Union 成員の除去鍵で他方の欄を落とさない"
  (define declared
    '(Union (Record ((kind Int imm)))
            (Record ((id Int imm) (kind String imm)))))
  (define previous
    '(Union (Record ((id Int imm) (kind Int imm)))
            (Record ((id Int imm) (kind String imm)))))
  (define key
    (first
     (filter (λ (candidate) (eq? (loop-excess-key-field candidate) 'id))
             (loop-excess-fields previous declared))))
  (define-values (widened removed)
    (loop-widen previous previous declared (set key)))
  (check-true (set-member? removed key))
  (define int-row
    (for/or ([member (in-list (union-members widened))])
      (match member
        [`(Record ,row)
         (and (equal? (second (assq 'kind row)) 'Int) row)]
        [_ #f])))
  (define string-row
    (for/or ([member (in-list (union-members widened))])
      (match member
        [`(Record ,row)
         (and (equal? (second (assq 'kind row)) 'String) row)]
        [_ #f])))
  (check-false (assq 'id int-row))
  (check-not-false (assq 'id string-row)))

(test-case "loop-widen は S1-S2-S1 の移行後に同じ除去鍵を再適用する"
  (define declared
    '(Union (Record ((kind Int imm)))
            (Union (Record ((id Int imm) (kind String imm)))
                   (Record ((other Bool imm))))))
  (define s1
    '(Union (Record ((id Int imm) (kind Int imm)))
            (Record ((other Bool imm)))))
  (define s1-deeper
    '(Union (Record ((id (Record ((child Int imm))) imm) (kind Int imm)))
            (Record ((other Bool imm)))))
  (define-values (first-view removed1)
    (loop-widen s1 s1-deeper declared (set)))
  (check-equal? (set-count removed1) 1)
  (define s2
    '(Union (Record ((id Int imm) (kind String imm)))
            (Record ((other Bool imm)))))
  (define-values (second-view removed2)
    (loop-widen first-view s2 declared removed1))
  (define s1-again
    '(Union (Record ((id Int imm) (kind Int imm)))
            (Record ((other Bool imm)))))
  (define-values (third removed3)
    (loop-widen second-view s1-again declared removed2))
  (define int-row
    (for/or ([member (in-list (union-members third))])
      (match member
        [`(Record ,row)
         (and (equal? (second (assq 'kind row)) 'Int) row)]
        [_ #f])))
  (check-true (set-member? removed3 (first (set->list removed1))))
  (check-false (assq 'id int-row)))

(test-case "loop-widen は除去後に宣言型へ収まらなければ T を返す"
  (define declared '(Record ((a Int imm))))
  (define previous '(Record ((a String imm) (extra Int imm))))
  (define next '(Record ((a String imm) (extra (Record ((child Int imm))) imm))))
  (define-values (widened _removed)
    (loop-widen previous next declared (set)))
  (check-true (type-equiv? widened declared)))

(test-case "loop-excess-fields は Owned と NFn 返り値をたどり引数と data は不透明"
  (define declared
    '(Record ((data (Data Box ((Record ((kept Int imm))))) imm)
              (fn (NFn ((Record ((arg Int imm))))
                       (Record ((kept String imm))) () () () User) imm)
              (owned (Owned (Record ((kept Bool imm)))) imm))))
  (define view
    '(Record ((data (Data Box ((Record ((extra Int imm) (kept Int imm))))) imm)
              (fn (NFn ((Record ((arg-extra Int imm) (arg Int imm))))
                       (Record ((extra String imm) (kept String imm))) () () () User) imm)
              (owned (Owned (Record ((extra Bool imm) (kept Bool imm)))) imm))))
  (define fields (loop-excess-fields view declared))
  (check-equal? (sort (map loop-excess-key-field fields) symbol<?)
                '(extra extra))
  (check-equal? (length fields) 2)
  (check-not-false (member '((field fn) (nfn-return))
                           (map loop-excess-key-path fields)))
  (check-not-false (member '((field owned) (Owned-payload))
                           (map loop-excess-key-path fields)))
  (check-false
   (member '((field fn) (nfn-parameter 0))
           (map loop-excess-key-path fields)))
  (check-false
   (member '((field data) (Data-argument 0))
           (map loop-excess-key-path fields))))

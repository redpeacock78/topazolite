#lang racket

(require rackunit
         redex/reduction-semantics
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../typing.rkt"
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

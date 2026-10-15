#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define (compile source) (compile-source/string 'src source))

(define (compile-code source)
  (match (compile source)
    [(? diagnostic? diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define (elab-code expression)
  (match (elab expression)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define (check-row-sum form row)
  `(Fn () (TypeInfo Type) ,row ,form))

(define (contains-identity-owned-let? expression)
  (or (match expression
        [`(Let (,name ,_ (Owned Res)) ,_ ,body)
         (and (symbol? name) (eq? name body))]
        [_ #f])
      (and (list? expression)
           (ormap contains-identity-owned-let? expression))))

(define (find-narrowing-proof expression)
  (match expression
    [`(Discharge (ProofRep (Reserved o-narrow)
                          (RemainderSafelyDropped ,actual ,target)) ,_)
     (list actual target)]
    [(? list?)
     (for/or ([part (in-list expression)]) (find-narrowing-proof part))]
    [_ #f]))

(test-case "SUR-014a: block の末尾の when は期待型で検査される"
  (define source
    (string-append
     "fn f(b: Bool) -> Option<Int> {\n"
     "  let y = 1\n"
     "  when b {\n"
     "    true => some(1)\n"
     "    false => none\n"
     "  }\n"
     "}\n"
     "f(true)"))
  (check-equal? (compile-code source) 'ok))

(test-case "SUR-014a: 注釈付き Let の右辺の block も期待型で検査される"
  (define source
    (string-append
     "fn g(b: Bool) -> Option<Int> {\n"
     "  let r: Option<Int> = {\n"
     "    let y = 1\n"
     "    when b {\n"
     "      true => some(1)\n"
     "      false => none\n"
     "    }\n"
     "  }\n"
     "  r\n"
     "}\n"
     "g(true)"))
  (check-equal? (compile-code source) 'ok))

(test-case "SUR-014a: Let の検査は NarrativeExpr の Core と config を通す"
  (define expression
    '(Fn ((b Bool)) (Option Int) ()
         (Let (x const Bool) b
              (NarrativeExpr
               (Eliminate x
                          ((true () -> (Construct some (Types Int) 1))
                           (false () -> (Construct none (Types Int)))))))))
  (match (elab expression)
    [(list core type row callables)
     (check-equal? (core-type-of (erase-core core) '() callables)
                   (list type row))
     (check-true (config-ok? (inject-g2m (erase-core core))
                             callables type row))]
    [other (fail-check (format "elaboration success を期待したが ~s" other))]))

(test-case "SUR-014a: 検査位置の資源 identity Let は束縛子を直接渡す"
  (match (elab '(Fn () (Owned Res) (Own)
                    (Let (x let) (Apply acquire 1) x)))
    [(list core _type _row _callables)
     (check-true (contains-identity-owned-let? (erase-core core)))]
    [other (fail-check (format "identity Let の成功を期待したが ~s" other))]))

(test-case "SUR-014a: Let の検査でも右辺の Fn に期待型を渡す"
  (define expression
    '(Fn () Int ()
         (Let (f const (NFn (Int) Int () ()))
              (Fn ((x #:infer)) #:infer () x)
              (Apply f 1))))
  (check-equal? (elab-code expression) 'ok))

(test-case "SUR-014a: 3 形の Let の検査で右辺と本体の Effect row を合併する"
  (define forms
    (list '(Let (x let) (Yield 1 1) (TypeMake (Spec List Int)))
          '(Let (x const Int) (Yield 1 1) (TypeMake (Spec List Int)))
          '(Let x (Yield 1 1) (TypeMake (Spec List Int)))))
  (for ([form (in-list forms)])
    (check-equal?
     (elab-code (check-row-sum form '((Yield Int) Compile)))
     'ok)
    (check-equal?
     (elab-code (check-row-sum form '((Yield Int))))
     (diagnostic-code-of 'elaborate 'undeclared-function-effect))
    (check-equal?
     (elab-code (check-row-sum form '(Compile)))
     (diagnostic-code-of 'elaborate 'undeclared-function-effect))))

(test-case "SUR-014a: 検査位置の資源 Let は未使用値を破棄する"
  (match
      (elab '(Apply
              (Fn () Unit (Own)
                  (Let (item let (Owned Res))
                       (Apply acquire 1)
                       unit))))
    [(list core _type _row _callables)
     (match (run-g2 (inject-g2m (erase-core core)) 10000)
       [`(cfg unit ,_heap ,states ,tokens ,_events)
        (check-equal? states '((0 Dropped)))
        (check-equal? tokens '(((tok 0) Dropped)))]
       [other (fail-check (format "資源 Let の実行結果を期待したが ~s" other))])]
    [other (fail-check (format "資源 Let の elaboration 成功を期待したが ~s" other))]))

(test-case "SUR-014a: 検査位置の資源 Let は合成位置と同じ narrowing を行う"
  (define wide
    '(Record ((kept Int imm) (owned (Option (Owned Res)) imm))))
  (define narrow '(Record ((kept Int imm))))
  (define source
    '(Rec ((owned imm (Construct some (Types (Owned Res))
                                (Apply acquire 1)))
           (kept imm 7))))
  (define let-form `(Let (record const ,narrow) ,source unit))
  (define synthesized
    (elab `(Let (record const ,narrow) ,source unit)))
  (define checked
    (elab `(Fn () Unit (Own) ,let-form)))
  (define synth-core (first synthesized))
  (define checked-core (first checked))
  (check-equal? (find-narrowing-proof (erase-core synth-core))
                (list wide narrow))
  (check-equal? (find-narrowing-proof (erase-core checked-core))
                (find-narrowing-proof (erase-core synth-core))))

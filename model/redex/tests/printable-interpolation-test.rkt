#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         (prefix-in backend: "../lowering.rkt")
         "../machine.rkt"
         "../origins.rkt"
         "../pr-machine.rkt"
         "../traits.rkt")

(define int-impl
  "impl Printable for Int { print: fn(x: Int) -> String { return \"i\" } }\n")

(define (compile source) (compile-source/string 'src source))
(define (code source)
  (define result (compile source))
  (and (diagnostic? result) (diagnostic-id result)))
(define (error-id result)
  (match result [`(err ,diagnostic) (diagnostic-id diagnostic)] [_ #f]))

(define (run-artifact artifact)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (λ ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core artifact))) 10000)
       [`(cfg ,value ,_heap ,_states ,_tokens ,_events) value]
       [other (fail-check (format "terminal config expected, got ~s" other))]))))

(define (run-main source)
  (define artifact (compile source))
  (check-true (compiled? artifact)
              (if (diagnostic? artifact)
                  (format "compile failed with ~a" (diagnostic-id artifact))
                  "compiled result expected"))
  (and (compiled? artifact) (run-artifact artifact)))

(define (run-backend-value artifact backend-name)
  (call-with-trait-ledger
   (compiled-ledger artifact)
   (λ ()
     (define-values (status target)
       (backend:lower (compiled-execution-core artifact) backend-name))
     (unless (eq? status 'ok)
       (fail-check (format "backend lowering failed: ~s" target)))
     (match (run-pr (inject-pr target) 10000)
       [`(pcfg ,value () () ()) value]
       [other (fail-check (format "unexpected backend result ~s" other))]))))

(define (elab-with expression [providers (hasheq)])
  (call-with-trait-ledger
   canonical-trait-ledger
   (λ ()
     (parameterize ([current-trait-providers providers])
       (elab expression)))))

(define (elab-observation result)
  (match result
    [`(err ,diagnostic)
     `(err ,(diagnostic-id diagnostic) ,(diagnostic-primary-span diagnostic)
           ,(diagnostic-expected diagnostic) ,(diagnostic-found diagnostic))]
    [(list _core type row _callables) `(ok ,type ,row)]
    [other `(unexpected ,other)]))

(define (surface-observation source)
  (define artifact (compile source))
  (if (compiled? artifact)
      `(ok ,(run-artifact artifact))
      `(err ,(diagnostic-id artifact))))

(define p5-extra-row
  '(o-test-printable-int impl-test-printable-int impl Printable Int root))

(define p5-ledger
  (let* ([base canonical-trait-env]
         [env (make-trait-env
               #:trait (trait-env-trait-rows base)
               #:impl (append (trait-env-impl-rows base) (list p5-extra-row))
               #:intersect (trait-env-intersect-rows base)
               #:scope (trait-env-scope-rows base)
               #:fail (λ (reason kind key)
                        (error 'printable-interpolation-test "~a ~a ~a" reason kind key)))])
    (make-trait-ledger
     env
     #:fail (λ (reason kind key)
              (error 'printable-interpolation-test "~a ~a ~a" reason kind key)))))

(define p5-expression
  '(Let p1 (Rec ((print imm (Fn ((x Int)) String () "one"))))
     (Let p2 (Rec ((print imm (Fn ((x Int)) String () "two"))))
       (StrHole 1))))

(define p5-providers
  (hasheq 'o-impl-printable-int 'p1
          'o-test-printable-int 'p2))

(define span0 '(#:span #:synthetic 0 0))
(define p8-int-annotated-let
  `(Let ,span0 ((#:bind value ,span0) const (#:ty Int ,span0))
     (StrHole ,span0 (#:lit "x" ,span0))
     (#:lit unit ,span0)))

(define p10-hole
  '(Let p
     (Rec ((print imm (Fn ((x Int)) String () "i"))))
     (Apply
      (Fn ((xs (List Int))) Int ()
        (Loop loop ((rest #:infer)) Int #:infer
          (Eliminate rest
            ((nil () -> 0)
             (cons (x tail) ->
               (Let tmp (StrHole (Apply loop tail)) (Apply loop tail)))))
          (xs)))
      (Construct cons (Types Int) 1 (Construct nil (Types Int))))))

(define p10-print
  '(Let p
     (Rec ((print imm (Fn ((x Int)) String () "i"))))
     (Apply
      (Fn ((xs (List Int))) Int ()
        (Loop loop ((rest #:infer)) Int #:infer
          (Eliminate rest
            ((nil () -> 0)
             (cons (x tail) ->
               (Let tmp (Apply (Proj p print) (Apply loop tail))
                 (Apply loop tail)))))
          (xs)))
      (Construct cons (Types Int) 1 (Construct nil (Types Int))))))

(define (accepted-when-source hole)
  (string-append
   int-impl
   "let result = when true {\n"
   "  true => \"a${" hole "}\"\n"
   "  false => \"b\"\n"
   "}\nresult"))

(define (rejected-when-source hole)
  (string-append
   int-impl
   "fn f(flag: Bool) -> Int { return when flag {\n"
   "  true => { let ignored = \"a${" hole "}\"\n 1 }\n"
   "  false => { let ignored = 2\n ignored }\n"
   "} }\nf(true)"))

(test-case "[REQ: SUR-002] P1 impl Printable for Int の後の Int の穴は print の結果へ連結する"
  (define source (string-append int-impl "\"a${1}\""))
  (check-equal? (run-main source) "ai")
  (define artifact (compile source))
  (for ([backend (in-list '(racket-cs racketscript))])
    (check-equal? (run-backend-value artifact backend) "ai")))

(test-case "P2 実装が無い Int の穴は現行と同じ E-TYP-012 である"
  (define result (compile "\"a${1}\""))
  (check-equal? (diagnostic-id result) "E-TYP-012")
  (check-equal? (diagnostic-primary-span result) '(#:span src 4 5))
  (check-equal? (diagnostic-expected result) 'String)
  (check-equal? (diagnostic-found result) 'Int))

(test-case "P3 String の穴は Printable を引かず、実装値が二つあっても Ambiguous にならない"
  (define result
    (elab-with
     '(Let p1 (Rec ((print imm (Fn ((x String)) String () "one"))))
        (Let p2 (Rec ((print imm (Fn ((x String)) String () "two"))))
          (StrHole "x")))
     (hasheq 'o-impl-printable-str-a 'p1
             'o-impl-printable-str-b 'p2)))
  (check-false (error-id result)))

(test-case "P4 impl より前の関数の穴は E-TYP-012、後の関数の穴は受理する"
  (check-equal?
   (code (string-append "fn f() -> String { return \"${1}\" }\n" int-impl "f()"))
   "E-TYP-012")
  (check-equal?
   (run-main (string-append int-impl "fn f() -> String { return \"${1}\" }\nf()"))
   "i"))

(test-case "P5 Int の行を二つ持つ実装値の表で Int の穴は E-PRF-004 である"
  (call-with-trait-ledger
   p5-ledger
   (λ ()
     (parameterize ([current-trait-providers p5-providers])
       (check-equal? (error-id (elab p5-expression)) "E-PRF-004")))))

(test-case "P6 Owned の穴は既存の E-TYP-012 と primary span を保ち、非正規化型は穴まで到達しない"
  (define source "\"${acquire(1)}\"")
  (define result (compile source))
  (check-equal? (diagnostic-id result) "E-TYP-012")
  (check-equal? (diagnostic-primary-span result) '(#:span src 3 13))
  ;; Intersection を含む仮引数型は prepare-fn の resolve-annotation
  ;; (elaborate.rkt:877-941, 3250-3262) が本体検査より先に E-TYP-005 で拒否する。
  (define non-normalizable
    (elab '(Fn ((x (Intersection String Int))) String () (StrHole x))))
  (define without-hole
    (elab '(Fn ((x (Intersection String Int))) String () "x")))
  (check-equal? (elab-observation non-normalizable)
                (elab-observation without-hole))
  (check-equal? (error-id non-normalizable) "E-TYP-005"))

(test-case "P7 入れ子の補間の内側の穴も Printable で変換する"
  (check-equal? (run-main (string-append int-impl "\"o${\"m${1}\"}o\"")) "omio"))

(test-case "P8 合成位置と String 以外の check 位置の StrHole は String を返す式である"
  (check-false (error-id (elab '(StrHole "x"))))
  (check-equal? (error-id (elab p8-int-annotated-let)) "E-TYP-012"))

(test-case "P9 現行で受理される穴と穴の合成失敗の診断は変わらない"
  (check-equal? (run-main "let s = \"x\"\n\"a${s}b\"") "axb")
  (check-false (code "fn f() -> String { return \"${return \"r\"}\" }\nf()"))
  (check-equal? (code "\"${x => x}\"") "E-TYP-025"))

(test-case "P10 loop の row 試行の中の穴は明示の print の呼出しと同じ受理、型、row になる"
  (define providers (hasheq 'o-impl-printable-int 'p))
  (define hole-observation (elab-observation (elab-with p10-hole providers)))
  (define print-observation (elab-observation (elab-with p10-print providers)))
  (check-match print-observation `(ok Int ,_))
  (check-equal? hole-observation print-observation))

(test-case "P11 when の arm の中の穴は明示の print の呼出しと同じ受理と診断になる"
  (check-equal? (surface-observation (accepted-when-source "1"))
                (surface-observation (accepted-when-source "Printable.print(1)")))
  (check-equal? (surface-observation (rejected-when-source "1"))
                (surface-observation (rejected-when-source "Printable.print(1)"))))

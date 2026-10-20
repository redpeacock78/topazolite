#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../typing.rkt"
         "../classify.rkt"
         "../type-equiv.rkt"
         "../ucore.rkt")

(define (elab-error-id expression)
  (match (elab expression)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(define (elab-row expression)
  (match (elab expression)
    [(list _core _type row _callables) row]
    [other (fail-check (format "elaboration success を期待したが ~s" other))]))

(define (loop-shape-error? failure)
  (and (exn:fail? failure)
       (regexp-match? #rx"loop 印の形の違反" (exn-message failure))))

(define list-value
  '(Construct cons (Types Int) 1 (Construct nil (Types Int))))

;; xs : List<Int> を走査する loop 印。row と仮引数の型を引数で変える。
(define (list-loop body #:row [row '#:infer] #:param-type [param-type '#:infer]
                   #:argument [argument 'xs])
  `(Loop loop ((rest ,param-type)) Unit ,row
     (Eliminate rest
       ((nil () -> unit)
        (cons (x tail) -> (Let (%stmt const Unit) ,body (Apply loop tail)))))
     (,argument)))

(define (in-function loop-expression #:row [row '()] #:result [result 'Unit])
  `(Apply (Fn ((xs (List Int))) ,result ,row ,loop-expression) ,list-value))

(define (find-recur-context tree callables [environment '()])
  (match tree
    [`(Lam ,_ ,function (,parameters ...) ,body)
     (match (assoc function callables)
       [(list _ `(NFn (,parameter-types ...) ,_ ,_ ,_ ,_ ,_))
        (find-recur-context
         body callables
         (append (map list parameters parameter-types)
                 (list (list function (second (assoc function callables))))
                 environment))]
       [_ (find-recur-context body callables environment)])]
    [`(Let (,name ,mode ,type) ,bound ,body)
     (or (find-recur-context bound callables environment)
         (find-recur-context body callables
                             (cons (if (eq? mode 'mut)
                                       (list name type 'mut)
                                       (list name type))
                                   environment)))]
    [`(Recur ,_ ,_ ,_ ,_ ,_) (list tree environment)]
    [(? list? parts)
     (for/or ([part (in-list parts)])
       (find-recur-context part callables environment))]
    [_ #f]))

(define (body-row body environment callables)
  (match (core-type-of/normal body '() callables environment)
    [(list _type row _normal-type) row]
    [other (fail-check (format "本体の Core 型検査成功を期待したが ~s" other))]))

;; loop の Recur について分類、本体の signature row、本体の row を返す。
(define (loop-recur-facts expression)
  (match (elab expression)
    [(list core _type _row callables)
     (match-define (list recur environment)
       (find-recur-context (erase-core core) callables))
     (match-define `(Recur ,callable ,function (,parameters ...) ,body ,_continuation)
       recur)
     (define signature (second (assoc callable callables)))
     (match-define `(NFn (,parameter-types ...) ,_ ,_ ,latent-row ,_ ,_) signature)
     (define body-environment
       (append (map list parameters parameter-types)
               (list (list function signature))
               environment))
     (list (classify-recur-body function parameters body body-environment callables)
           latent-row
           (body-row body body-environment callables))]
    [other (fail-check (format "elaboration success を期待したが ~s" other))]))

(define (partial-program outer-row)
  `(Apply
    (Fn ((xs (List Int))
         (partial-callee (NFn () Unit (Partial) ())))
        Unit ,outer-row
      ,(list-loop '(Apply partial-callee)))
    ,list-value
    (Fn () Unit (Partial) unit)))

(define (return-only-program)
  `(Apply
    (Fn ((xs (List Int))) Unit ()
      (Loop loop ((rest #:infer)) Unit #:infer
        (Eliminate rest
          ((nil () -> (Return unit))
           (cons (x tail) -> (Return unit))))
        (xs)))
    ,list-value))

(define (yield-program loop-row outer-row)
  `(Apply
    (Fn ((xs (List Int))
         (yield-callee (NFn () Unit ((Yield Int)) ())))
        Unit ,outer-row
      ,(list-loop '(Apply yield-callee) #:row loop-row))
    ,list-value
    (Fn () Unit ((Yield Int)) (Yield 1 unit))))

(define (no-self-yield-program)
  `(Apply
    (Fn ((yield-callee (NFn () Unit ((Yield Int)) ())))
        Unit (Partial (Yield Int))
      (Loop loop () Unit #:infer (Apply yield-callee) ()))
    (Fn () Unit ((Yield Int)) (Yield 1 unit))))

(test-case "R1 effect の無い本体の #:infer の loop は Finite structural で row は空になる（試験 16）"
  (match-define (list classification latent-row _) (loop-recur-facts (in-function (list-loop 'unit))))
  (check-equal? classification '(Finite structural))
  (check-equal? latent-row '())
  (check-equal? (elab-row (in-function (list-loop 'unit))) '()))

(test-case "R2 Partial を呼ぶ本体の loop は Unknown で、mut の追跡対象が無くても row の固定点を回す（試験 21）"
  (match-define (list classification latent-row _) (loop-recur-facts (partial-program '(Partial))))
  (check-equal? classification 'Unknown)
  (check-not-false (member 'Partial latent-row))
  (check-equal? (elab-error-id (partial-program '())) "E-EFF-002"))

(test-case "R3 本体が必ず return で抜ける loop でも Return の label を失わない"
  (match-define (list _classification latent-row _body-row)
    (loop-recur-facts (return-only-program)))
  (check-true
   (for/or ([label (in-list latent-row)])
     (match label [`(Return ,_ Unit) #t] [_ #f]))))

(test-case "R5 Yield だけを呼ぶ自己呼び出しありの loop は Unknown で Rfinal に Partial を持つ（試験 22）"
  (match-define (list classification latent-row _)
    (loop-recur-facts (yield-program '#:infer '(Partial (Yield Int)))))
  (check-equal? classification 'Unknown)
  (check-true (row-equiv? latent-row '(Partial (Yield Int))))
  (check-equal? (elab-error-id (yield-program '((Yield Int)) '(Partial (Yield Int))))
                "E-REC-002"))

(test-case "R6 自己呼び出しの無い #:infer の loop は Unknown で、Rfinal は本体の row に Partial を足したものになる（試験 23）"
  (match-define (list classification latent-row body-row*)
    (loop-recur-facts (no-self-yield-program)))
  (check-equal? classification 'Unknown)
  (check-false (member 'Partial body-row*))
  (check-true (row-equiv? latent-row (cons 'Partial body-row*))))

(test-case "R7 明示の row の loop 印は従来どおり検査だけを行う"
  (check-equal? (elab-row (in-function (list-loop 'unit #:row '()))) '()))

(test-case "R8 #:infer の仮引数に List でない値を渡すと E-TYP-012 で拒否する"
  (check-equal? (elab-error-id (in-function (list-loop 'unit #:argument 1))) "E-TYP-012"))

(test-case "#:infer Loop の非原子的な初回実引数は型推論より前に形検査で拒否する"
  ;; loop 印の固定点は変数か literal の初回実引数だけを受け付ける。
  (check-exn loop-shape-error?
             (λ ()
               (elab
                (in-function (list-loop 'unit #:argument '(Apply make-list)))))))

(test-case "#:infer Loop の仮引数数と初回実引数数の不一致は E-ARI-001"
  (check-equal? (elab-error-id '(Loop loop ((rest #:infer)) Unit #:infer unit ()))
                "E-ARI-001"))

(test-case "S14b 014c1b で反転する Move の初回実引数は既存の loop shape gate で拒否する"
  (define loop
    '(Loop loop ((rest #:infer)) Unit #:infer
       (Eliminate rest
         ((nil () -> unit)
          (cons (x tail) -> (Apply loop tail))))
       ((Move xs))))
  (check-exn loop-shape-error?
             (λ ()
               (elab `(Fn ((xs (List (Owned Res)))) Unit () ,loop)))))

(test-case "S14b 014c1b で反転する Let の Move 値を変数経由で渡すと E-OWN-010"
  (define loop
    '(Loop loop ((rest #:infer)) Unit #:infer
       (Eliminate rest
         ((nil () -> unit)
          (cons (x tail) -> (Apply loop tail))))
       (ys)))
  (check-equal?
   (elab-error-id
    `(Fn ((xs (List (Owned Res)))) Unit ()
       (Let (ys let (List (Owned Res))) (Move xs) ,loop)))
   "E-OWN-010"))

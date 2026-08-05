#lang racket

(require racket/match
         redex/reduction-semantics
         "pr-lang.rkt")

;; 公開面を machine.rkt より広く取る。δpr を出すのは Task 15 の
;; lowering-arith-test.rkt が shim 名の意味論を項の簡約を経ずに引くためであり、
;; 予約行の名前が未定義であることも同じ metafunction で固定する。bool-tag-true と
;; bool-tag-false の理由は下のコメントに書く。いずれも読み取り専用の公開であり、
;; 目標機械の規則を外から書き換える口は開けない。
(provide -->pr
         -->pr/rules
         δpr
         inject-pr
         run-pr
         bool-tag-true
         bool-tag-false)

;; k:true と k:false は lowering の tag-code(true) / tag-code(false) の像である
;; （spec §6.4、§9）。δpr が Bool を返す以上どれかの tag を選ばざるを得ず、選んだ
;; tag が lowering の像と食い違うと PMatch の枝が選べない。目標機械が源の符号化に
;; 依存するのはこの 2 つだけである。値を 1 箇所に置いて provide するのは、Task 12
;; の lowering 側テストが (tag-code 'true) との一致をこの束縛で固定するためであり、
;; 綴りを写した定数を両側に置くとテストが自分自身を確かめる形になる。
(define bool-tag-true 'k:true)
(define bool-tag-false 'k:false)

;; spec §9 の表。Int は任意精度整数なので、shim の意味論は Racket の演算その
;; ものである。固定幅の切り詰めが意味論に入るのは Phase 2 以降であり、そのとき
;; ここの実装も変わる。禁じているのは生成物が Host の演算を直接指すことであっ
;; て、模型の実装手段ではない。
(define-metafunction PR
  δpr : pnm pv ... -> any
  [(δpr tz:add integer_1 integer_2)
   ,(+ (term integer_1) (term integer_2))]
  [(δpr tz:sub integer_1 integer_2)
   ,(- (term integer_1) (term integer_2))]
  [(δpr tz:mul integer_1 integer_2)
   ,(* (term integer_1) (term integer_2))]
  [(δpr tz:lt integer_1 integer_2)
   ,(if (< (term integer_1) (term integer_2))
        `(PTagged ,bool-tag-true)
        `(PTagged ,bool-tag-false))]
  [(δpr tz:le integer_1 integer_2)
   ,(if (<= (term integer_1) (term integer_2))
        `(PTagged ,bool-tag-true)
        `(PTagged ,bool-tag-false))]
  [(δpr tz:eq integer_1 integer_2)
   ,(if (= (term integer_1) (term integer_2))
        `(PTagged ,bool-tag-true)
        `(PTagged ,bool-tag-false))]
  [(δpr tz:acquire integer) (PResource integer)]
  [(δpr pnm pv ...) undefined])

;; machine.rkt の substitute* と同じ理由で、arity 不一致と重複束縛子を #f に
;; 落として規則を不発火にする。metafunction の例外にしない。
(define-metafunction PR
  psubstitute* : pc (px ...) (pv ...) -> any
  [(psubstitute* pc_body (px ...) (pv_arg ...))
   (substitute pc_body (px pv_arg) ...)
   (side-condition
    (and (= (length (term (px ...))) (length (term (pv_arg ...))))
         (not (check-duplicates (term (px ...))))))]
  [(psubstitute* pc_body (px ...) (pv_arg ...)) #f])

(define (pr-unique-binders? core)
  (and (match core
         [`(PLam ,parameters ,_) (not (check-duplicates parameters))]
         [`(PClosure ,environment ,parameters ,_)
          (not (or (check-duplicates parameters)
                   (check-duplicates (map first environment))))]
         [`(,_ ,parameters -> ,_)
          #:when (list? parameters)
          (not (check-duplicates parameters))]
         [_ #t])
       (or (not (list? core))
           (andmap pr-unique-binders? core))))

(define -->pr/rules
  (reduction-relation
   PR
   #:domain pconfig

   (--> (pcfg (in-hole PE (PPrim pnm pv_arg ...)) PH PΩ θ)
        (pcfg (in-hole PE pv_result) PH PΩ θ)
        (where pv_result (δpr pnm pv_arg ...))
        R-PR-Prim)))

(define (raw-steps-pr configuration)
  (if (pr-unique-binders? configuration)
      (apply-reduction-relation -->pr/rules configuration)
      '()))

(define -->pr
  (reduction-relation
   PR
   #:domain pconfig
   (--> pconfig_before
        pconfig_after
        (where (pconfig_prefix ... pconfig_after pconfig_suffix ...)
               ,(raw-steps-pr (term pconfig_before)))
        R-Step)))

(define (inject-pr core)
  (unless (redex-match? PR pc core)
    (raise-argument-error 'inject-pr "PR computation" core))
  `(pcfg (PScopeExit () ,core) () () ()))

(define (run-pr configuration fuel)
  (unless (redex-match? PR pconfig configuration)
    (raise-argument-error 'run-pr "PR configuration" configuration))
  (unless (exact-nonnegative-integer? fuel)
    (raise-argument-error 'run-pr "exact-nonnegative-integer?" fuel))
  (let loop ([current configuration]
             [remaining fuel])
    (define next
      (remove-duplicates (apply-reduction-relation -->pr current) equal?))
    (cond
      [(null? next) current]
      [(zero? remaining) 'timeout]
      [(null? (cdr next)) (loop (car next) (sub1 remaining))]
      [else
       (error 'run-pr "nondeterministic reduction from ~e to ~e" current next)])))

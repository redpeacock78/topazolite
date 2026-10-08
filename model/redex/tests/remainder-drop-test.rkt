#lang racket

;; [REQ: PRF-005] 構造型 narrowing で余剰 field を drop する場合の
;; RemainderSafelyDropped Proof の構築と消費。

(require rackunit
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../lang.rkt"
         "../type-equiv.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../region.rkt"
         "../machine.rkt"
         "../gen.rkt"
         "../typing.rkt")

(define owned '(Owned Res))
(define actual `(Record ((x ,owned imm) (y Int imm))))
(define expected '(Record ((y Int imm))))

(define wide `(Record ((a ,owned imm) (b Int imm))))
(define narrow '(Record ((b Int imm))))
(define phi `(RemainderSafelyDropped ,wide ,narrow))
(define proof `(ProofRep (Reserved o-narrow) ,phi))

;; 基底が φ の τ_actual より広く、余剰欄にも Owned がある組。
(define wider
  `(Record ((a ,owned imm) (b Int imm) (c ,owned imm))))

;; 入れ子の欄で Owned を失う対。kind は 'reject である。
(define reject-wide `(Record ((a (Record ((p ,owned imm))) imm))))
(define reject-narrow '(Record ((a (Record ()) imm))))
(define reject-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,reject-wide ,reject-narrow)))

;; 余剰が Int だけの width narrowing。kind は 'ok である。
(define ok-wide '(Record ((a Int imm) (b Int imm))))
(define ok-narrow '(Record ((b Int imm))))
(define ok-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,ok-wide ,ok-narrow)))

;; 基底の型と一致しない narrowing の型対。Discharge の基底検査で拒む。
(define other-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,ok-wide ,narrow)))

;; 残余 drop 以外の義務。混在の検査に使う。
(define cap-proof '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))

(define acquire '(PrimVal (Reserved o-acquire) acquire))
(define option-owned '(Option (Owned Res)))
(define runtime-wide
  '(Record ((kept Int imm) (owned (Option (Owned Res)) imm))))
(define runtime-narrow '(Record ((kept Int imm))))
(define runtime-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,runtime-wide ,runtime-narrow)))

(define runtime-source-callables
  `((rsd-record-source
     (NFn (,option-owned) ,runtime-wide () (Own) () User))))

(define (runtime-source number)
  `(Apply
    (Lam User rsd-record-source (raw-owned)
      (Handle (Return rsd-source-boundary ,runtime-wide)
              (return-value -> return-value)
              (Scope ()
                (Let (stored let ,option-owned) raw-owned
                  (Let (record let ,runtime-wide)
                    (Rec ((owned imm (Move stored)) (kept imm 7)))
                    (Move record))))))
    (Construct ,option-owned some ,(owned-leaf number))))

(define (owned-leaf number)
  `(OwnLeaf (Apply ,acquire ,number)))

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

(define (configuration-core configuration)
  (match configuration [`(cfg ,core ,_ ,_ ,_ ,_) core]))

(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (configuration-events configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,_ ,events) events]))

(define (contains-rsd? value)
  (match value
    [`(Discharge (ProofRep ,_ (RemainderSafelyDropped ,_ ,_)) ,_) #t]
    [(? list?) (ormap contains-rsd? value)]
    [_ #f]))

(define (check-config-trace configs callables expected-type)
  (define rows
    (for/list ([configuration (in-list configs)] [index (in-naturals)])
      (define row (runtime-row configuration callables expected-type))
      (check-not-false row
                       (format "runtime row を得られない config ~a: ~s"
                               index configuration))
      (check-true (config-ok? configuration callables expected-type row)
                  (format "不正な中間 config ~a: ~s" index configuration))
      row))
  (for ([before (in-list rows)] [after (in-list (cdr rows))]
        [index (in-naturals)])
    (check-true (row-subset? after before)
                (format "config ~a から次の config で row が増えた: ~s -> ~s"
                        index before after))))

(define (manual-rsd-rules proof value tokens)
  (map first
       (raw-steps-g2/named
        `(cfg (Discharge ,proof ,value) () () ,tokens ()))))

(define (manual-runtime-wide-value token)
  `(Rec ((kept imm 7)
         (owned imm
                (Construct ,option-owned some
                           (OwnedLeaf (tok ,token) (resource 1)))))))

(define (run-rsd inner [wrapper values])
  (define core (wrapper `(Discharge ,runtime-proof ,inner)))
  (define-values (configs rules)
    (trace-g2 `(cfg ,core () () () ())))
  (values core configs rules))

(define narrowing-environment
  `((f (NFn (,narrow) ,narrow () () () User))
    (g (NFn (,reject-narrow) ,reject-narrow () () () User))
    (h (NFn (,ok-narrow) ,ok-narrow () () () User))
    (k (NFn (,ok-narrow) ,ok-narrow () () (TypeNarrativeCap) User))
    (wide-source (NFn (Unit) ,wide () (Own) () User))
    (wider-source (NFn (Unit) ,wider () (Own) () User))
    (reject-wide-source (NFn (Unit) ,reject-wide () (Own) () User))))

(define wide-value '(Apply wide-source unit))
(define wider-value '(Apply wider-source unit))
(define reject-wide-value '(Apply reject-wide-source unit))
(define ok-wide-value '(Rec ((a imm 1) (b imm 2))))

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (key-of-with-callables core callables [places '()])
  (match (type-of/raw core places callables '() (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (type-of core [environment '()])
  (first (core-type-of core '() '() environment)))

(test-case
 "RemainderSafelyDropped は φ として言語に合う"
 (check-true
  (redex-match? G2 φ
                (list 'RemainderSafelyDropped actual expected))))

(test-case
 "両側の型を正規化してから比べる"
 ;; 同じ row を別の欄順で書いた 2 つの型は、正規化すると同じ鍵になる。
(define reordered `(Record ((y Int imm) (x ,owned imm))))
 (check-true
  (proposition-equiv? `(RemainderSafelyDropped ,actual ,expected)
                      `(RemainderSafelyDropped ,reordered ,expected))))

(test-case
 "発行者は Reserved o-narrow だけを認める"
 (define phi `(RemainderSafelyDropped ,actual ,expected))
 (check-true  (proof-issuer-ok? R0 '(Reserved o-narrow) phi))
 (check-false (proof-issuer-ok? R0 '(Reserved o-merge) phi)))

(test-case
 "探索の既定分類はこの命題を拾わない"
 ;; spec §4.3。既定節 [_ #f] が効くことを、明示の節を足さずに押さえる。
 (check-equal?
  (default-classifier
    (make-goal `(RemainderSafelyDropped ,actual ,expected))
    Γ-pc0)
  'Unknown))

(test-case
 "置き場所で出現の可否が入れ替わる"
 ;; spec §4.3。proof-occurrence-ok? は 2 つ目の引数で Discharge の proof 欄
 ;; を走っているかを受け取る。既定は #f であり、search.rkt の
 ;; transportable-proof はこの既定のまま呼ぶ。
 (define phi `(RemainderSafelyDropped ,actual ,expected))
 (check-false (proof-occurrence-ok? phi))
 (check-true  (proof-occurrence-ok? phi #t)))

(test-case
 "単独の ProofRep は forged になり、Discharge の中の同じ値は通る"
 ;; spec §4.3。verify-origins は項を一様に走るため、Discharge の proof 欄
 ;; だけを見分ける分岐が要る。この 2 件が同時に成り立つことを押さえる。
 ;; 後者は正当な Discharge を forged にしないことの回帰である。
 (define proof
   `(ProofRep (Reserved o-narrow)
              (RemainderSafelyDropped ,actual ,expected)))
 (check-equal? (term (verify-origins ,R0 ,proof))
               `(forged ,proof))
 (check-equal? (term (verify-origins ,R0 (Discharge ,proof 1)))
               'ok))

(test-case "Proof 無しの narrowing は owned-narrowing-needs-proof である"
  (check-equal? (key-of `(Apply f ,wide-value) narrowing-environment)
                'owned-narrowing-needs-proof))

(test-case "基底が τ_actual より広く余剰に Owned があると通らない"
  (check-equal? (key-of `(Apply f (Discharge ,proof ,wider-value))
                        narrowing-environment)
                'owned-narrowing-needs-proof))

(test-case "Discharge で包むと通り、型は τ_expected である"
  (check-equal? (type-of `(Apply f (Discharge ,proof ,wide-value))
                         narrowing-environment)
                narrow))

(test-case "RSD の row は内側が pure value でも Own を持つ"
  (define source-type
    '(Record ((kept Int imm) (owned (Option (Owned Res)) imm))))
  (define target-type '(Record ((kept Int imm))))
  (define source-proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,source-type ,target-type)))
  ;; OwnLeaf は token を作るが Effect row は持たない。
  (define source
    `(Rec ((kept imm 7)
          (owned imm
                 (Construct ,option-owned some
                            (OwnLeaf (resource 41)))))))
  (define core `(Discharge ,source-proof ,source))
  (check-equal? (core-type-of source '() '()) (list source-type '()))
  (check-equal? (core-type-of core '() '()) (list target-type '(Own))))

(test-case "nested drop obligation は Discharge で包むと受理される"
  (check-equal? (key-of `(Apply g (Discharge ,reject-proof
                                               ,reject-wide-value))
                        narrowing-environment)
                'ok))

(test-case "'ok を返す narrowing を包んでも通る"
  (check-equal? (type-of `(Apply h (Discharge ,ok-proof
                                               ,ok-wide-value))
                         narrowing-environment)
                ok-narrow))

(test-case "φ の τ_actual が基底の型と一致しないと通らない"
  (check-equal? (key-of `(Apply f (Discharge ,other-proof
                                              ,wide-value))
                        narrowing-environment)
                'type-mismatch))

(test-case "残余 drop と他の義務を重ねると discharge-mixed-obligation である"
  (check-equal? (key-of `(Apply k
                              (Discharge ,proof
                                         (Discharge ,cap-proof
                                                    ,ok-wide-value)))
                        narrowing-environment)
                'discharge-mixed-obligation))

(test-case "2 枚重ねると discharge-remainder-chain である"
  (check-equal? (key-of `(Apply f
                              (Discharge ,proof
                                         (Discharge ,proof ,wide-value)))
                        narrowing-environment)
                'discharge-remainder-chain))

(test-case "origin が o-narrow 以外なら受理しない"
  (check-equal?
   (key-of `(Apply f
                    (Discharge (ProofRep (Reserved o-type-narrative) ,phi)
                               ,wide-value))
            narrowing-environment)
   'discharge-proof-issuer))

(test-case "RSD の除去欄の token は Dropped になり、値から欄が消える"
  (define inner (runtime-source 31))
  (define-values (core configs rules)
    (run-rsd inner (lambda (term) `(Scope () ,term))))
  (check-equal? (key-of-with-callables core runtime-source-callables) 'ok)
  (check-equal? (core-type-of core '() runtime-source-callables)
                (list runtime-narrow '(Own)))
  (check-config-trace configs runtime-source-callables runtime-narrow)
  (check-equal? (configuration-core (last configs))
                '(Rec ((kept imm 7))))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped)))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-false (member 'R-Discharge rules)))

(test-case "入れ子の除去欄を RSD で drop し、保持欄を残す"
  (define nested-wide
    `(Record ((inside (Record ((kept Int imm)
                               (owned ,option-owned imm))) imm)
              (outer-kept Int imm))))
  (define nested-narrow
    '(Record ((inside (Record ((kept Int imm))) imm)
              (outer-kept Int imm))))
  (define nested-proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,nested-wide ,nested-narrow)))
  (define source
    `(Rec ((inside imm
                   (Rec ((owned imm
                                (Construct ,option-owned some
                                           (OwnLeaf (resource 51))))
                         (kept imm 7))))
          (outer-kept imm 9))))
  (define core `(Scope () (Discharge ,nested-proof ,source)))
  (check-equal? (core-type-of source '() '()) (list nested-wide '()))
  (check-equal? (core-type-of core '() '()) (list nested-narrow '(Own)))
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-config-trace configs '() nested-narrow)
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (configuration-core (last configs))
                '(Rec ((inside imm (Rec ((kept imm 7))))
                      (outer-kept imm 9))))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped))))

(test-case "Absent の除去欄は token 無しで欄だけを取り除く"
  (define optional-wide
    `(Record ((kept Int imm) (owned ,option-owned imm opt))))
  (define optional-proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,optional-wide ,runtime-narrow)))
  (define core
    `(Scope ()
       (Discharge ,optional-proof
         (Rec ((owned imm (Absent ,option-owned)) (kept imm 9))))))
  (define-values (configs _rules) (trace-g2 `(cfg ,core () () () ())))
  (check-equal? (core-type-of core '() '()) (list runtime-narrow '(Own)))
  (check-config-trace configs '() runtime-narrow)
  (check-equal? (configuration-core (last configs))
                '(Rec ((kept imm 9))))
  (check-equal? (configuration-tokens (last configs)) '()))

(test-case "RSD の内側で Yield した保持値と除去欄は重ならず trace が型付けできる"
  (define core
    `(Scope ()
       (Discharge ,runtime-proof
         (Yield 5 ,(runtime-source 34)))))
  (check-equal? (key-of-with-callables core runtime-source-callables) 'ok)
  (define-values (configs rules) (trace-g2 `(cfg ,core () () () ())))
  (check-config-trace configs runtime-source-callables runtime-narrow)
  (define yield-index (index-of rules 'R-Yield))
  (check-not-false yield-index)
  (check-not-false
   (member '(obs 5)
           (configuration-events (list-ref configs (add1 yield-index)))))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped))))

(test-case "R-DischargeRemainder は値の形が型と合わなければ発火しない"
  (define malformed
    `(Rec ((kept imm 7)
          (owned imm
                 (Construct ,option-owned some
                            (OwnedLeaf (tok 81) (resource 1))))
          (extra imm 9))))
  (check-false
   (member 'R-DischargeRemainder
           (manual-rsd-rules runtime-proof malformed
                             '(((tok 81) Available)))))
  (check-equal?
   (manual-rsd-rules runtime-proof (manual-runtime-wide-value 81)
                     '(((tok 81) Available)))
   '(R-DischargeRemainder)))

(test-case "R-DischargeRemainder は Available でない除去 token を拒む"
  (define value (manual-runtime-wide-value 82))
  (check-false
   (member 'R-DischargeRemainder
           (manual-rsd-rules runtime-proof value '(((tok 82) Dropped)))))
  (check-equal?
   (manual-rsd-rules runtime-proof value '(((tok 82) Available)))
   '(R-DischargeRemainder)))

(test-case "R-DischargeRemainder は除去欄間で重複する token を拒む"
  (define two-owned-wide
    `(Record ((kept Int imm)
              (left ,option-owned imm)
              (right ,option-owned imm))))
  (define two-owned-proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,two-owned-wide ,runtime-narrow)))
  (define (two-owned-value left-token right-token)
    `(Rec ((kept imm 7)
           (left imm
                 (Construct ,option-owned some
                            (OwnedLeaf (tok ,left-token) (resource 1))))
           (right imm
                  (Construct ,option-owned some
                             (OwnedLeaf (tok ,right-token) (resource 2)))))))
  (check-false
   (member 'R-DischargeRemainder
           (manual-rsd-rules two-owned-proof (two-owned-value 83 83)
                             '(((tok 83) Available)))))
  (check-equal?
   (manual-rsd-rules two-owned-proof (two-owned-value 83 84)
                     '(((tok 83) Available) ((tok 84) Available)))
   '(R-DischargeRemainder)))

(test-case "Owned を含まない残余の欄は値に残る"
  (define wider-type
    `(Record ((extra Int imm) (kept Int imm) (owned ,option-owned imm))))
  (define proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,wider-type ,runtime-narrow)))
  (define inner
    `(Apply
      (Lam User rsd-record-source-extra (raw-owned)
        (Handle (Return rsd-extra-boundary ,wider-type)
                (return-value -> return-value)
                (Scope ()
                  (Let (stored let ,option-owned) raw-owned
                    (Let (record let ,wider-type)
                      (Rec ((owned imm (Move stored)) (kept imm 7) (extra imm 9)))
                      (Move record))))))
      (Construct ,option-owned some ,(owned-leaf 32))))
  (define callables
    `((rsd-record-source-extra
       (NFn (,option-owned) ,wider-type () (Own) () User))))
  (define core `(Scope () (Discharge ,proof ,inner)))
  (define-values (configs _rules) (trace-g2 `(cfg ,core () () () ())))
  (check-equal? (core-type-of core '() callables)
                (list runtime-narrow '(Own)))
  (check-config-trace configs callables runtime-narrow)
  (check-equal? (configuration-core (last configs))
                '(Rec ((kept imm 7) (extra imm 9))))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped))))

(test-case "RSD の内側が値でない間は R-Discharge が発火しない"
  (define start `(cfg (Discharge ,runtime-proof (Error 0)) () () () ()))
  (define names (map first (raw-steps-g2/named start)))
  (check-false (member 'R-Discharge names))
  (check-equal? names '()))

(test-case "RSD の内側が還元可能な非値の間は R-Discharge で剥がさない"
  (define start
    `(cfg (Discharge ,runtime-proof ,(runtime-source 35)) () () () ()))
  (define names (map first (raw-steps-g2/named start)))
  (check-equal? names '(R-Delta)))

(test-case "RSD の内側の資源型 Let は値を作ってから RSD で drop する"
  (define inner
    `(Let (stored let ,runtime-wide)
          ,(runtime-source 33)
          (Move stored)))
  (define core `(Scope (0) (Discharge ,runtime-proof ,inner)))
  (define places '((0 Res)))
  (define start `(cfg ,core ((0 (resource 1))) ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-equal? (core-type-of core places runtime-source-callables)
                (list runtime-narrow '(Own)))
  (check-config-trace configs runtime-source-callables runtime-narrow)
  (check-not-false (member 'R-LetOwnedB rules))
  (check-not-false (member 'R-DischargeRemainder rules))
  (check-equal? (configuration-core (last configs))
                '(Rec ((kept imm 7))))
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped))))

(test-case "RSD 以外の φ の Discharge は R-Discharge で剥がれる"
  (define start `(cfg (Discharge ,cap-proof unit) () () () ()))
  (check-equal? (map first (raw-steps-g2/named start)) '(R-Discharge)))

(define interrupt-wide
  `(Record ((owned ,option-owned imm) (signal Unit imm))))
(define interrupt-narrow '(Record ((signal Unit imm))))
(define interrupt-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,interrupt-wide ,interrupt-narrow)))
(define interrupt-worker
  `(Lam User interrupt-worker (raw-owned raw-unit)
     (Handle (Return interrupt-worker-boundary ,interrupt-wide)
             (return-record -> return-record)
             (Scope ()
               (Let (stored let ,option-owned) raw-owned
                 (Let (record let ,interrupt-wide)
                   (Rec ((owned imm (Move stored)) (signal imm raw-unit)))
                   (Move record)))))))
(define interrupt-consumer
  '(Lam User interrupt-consumer (raw-owned raw-record)
     (Handle (Return interrupt-consumer-boundary Unit)
             (return-value -> return-value)
             (Scope ()
               (Let (transferred let (Option (Owned Res))) raw-owned unit)))))
(define interrupt-callables
  `((interrupt-consumer
     (NFn ((Option (Owned Res)) ,interrupt-narrow) Unit () () () User))
    (interrupt-worker
     (NFn ((Option (Owned Res)) Unit) ,interrupt-wide () (Own) () User))))
(define interrupt-outer-leaf
  `(Construct ,option-owned some ,(owned-leaf 41)))

(define (interrupted-rsd-core mode)
  (define interrupt
    (if (eq? mode 'error)
        '(Error 0)
        '(Perform (Return rsd-interrupt Unit) unit)))
  (define rsd-inner
    `(Apply ,interrupt-worker
            (Construct ,option-owned some ,(owned-leaf 42))
            ,interrupt))
  (define computation
    `(Apply ,interrupt-consumer
            ,interrupt-outer-leaf
            (Discharge ,interrupt-proof ,rsd-inner)))
  (case mode
    [(error) `(Scope () ,computation)]
    [(perform)
     `(Handle (Return rsd-interrupt Unit) (answer -> answer)
        (Scope () ,computation))]))

(define (check-rsd-interruption mode expected-rule expected-core)
  (define core (interrupted-rsd-core mode))
  (define places (if (eq? mode 'error) '((0 Res)) '()))
  (define heap (if (eq? mode 'error) '((0 (resource 99))) '()))
  (define states (if (eq? mode 'error) '((0 Available)) '()))
  (define expected-row '(Own))
  (define start `(cfg ,core ,heap ,states () ()))
  (check-equal? (key-of-with-callables core interrupt-callables places) 'ok)
  (check-equal? (core-type-of core places interrupt-callables)
                (list 'Unit expected-row))
  (define-values (configs rules) (trace-g2 start))
  (check-config-trace configs interrupt-callables 'Unit)
  (check-not-false (member expected-rule rules))
  (define index (index-of rules expected-rule))
  (define before (list-ref configs index))
  (define after (list-ref configs (add1 index)))
  (check-true (contains-rsd? (configuration-core before))
              "中断直前の捨てる frame に RSD が残る")
  (check-equal? (configuration-events before)
                (configuration-events after)
                "中断規則は θ を変えない")
  (check-equal? (configuration-tokens (last configs))
                '(((tok 0) Dropped) ((tok 1) Dropped)))
  (check-equal? (configuration-core (last configs)) expected-core))

(test-case "RSD を含む Error frame と外側の Apply frame は共に回収される"
  (check-rsd-interruption 'error 'R-ScopeError '(Error 0)))

(test-case "RSD を含む Perform frame は ScopeAbort で回収され handler へ届く"
  (check-rsd-interruption 'perform 'R-ScopeAbort 'unit))

#lang racket

(require rackunit
         racket/list
         racket/match
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../borrow-gen.rkt"
         "../borrow.rkt"
         "../region.rkt"
         "../origins.rkt"
         "../compat.rkt"
         "../diagnostic.rkt"
         "../ownership.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define (config-trace+rules initial)
  (let loop ([current initial] [configs (list initial)] [fuel 10000])
    (when (zero? fuel)
      (error 'config-trace "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs '())]
      [(list (list _rule next))
       (define-values (rest-configs rest-rules)
         (loop next (append configs (list next)) (sub1 fuel)))
       (values rest-configs (cons _rule rest-rules))]
      [steps (error 'config-trace "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (config-trace initial)
  (define-values (configs _rules) (config-trace+rules initial))
  configs)

(define (check-configs configs expected callables)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row
                     (format "config ~a の runtime-row: ~s" index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "config ~a の config-ok?: ~s" index configuration))))

(define (check-source-trace source
                            #:require-rules [required-rules '()]
                            #:forbid-rules [forbidden-rules '()]
                            #:return-trace? [return-trace? #f])
  (define compiled (compile-source/string 'src source))
  (check-true (compiled? compiled)
              (format "compile 成功を期待した: ~s" compiled))
  (define trace
    (and
     (compiled? compiled)
     (call-with-trait-ledger
      (compiled-ledger compiled)
      (lambda ()
        (define-values
          (configs rules)
          (config-trace+rules
           (inject-g2m (erase-core (compiled-execution-core compiled)))))
        (check-configs configs (compiled-type compiled)
                       (compiled-callables compiled))
        (for ([rule (in-list required-rules)])
          (check-not-false (member rule rules)
                           (format "trace に ~a がある: ~s" rule rules)))
        (for ([rule (in-list forbidden-rules)])
          (check-false (member rule rules)
                       (format "trace に ~a が無い: ~s" rule rules)))
        (list compiled configs rules)))))
  (if return-trace? trace (void)))

(define (count-form term wanted)
  (cond
    [(pair? term)
     (+ (if (eq? (car term) wanted) 1 0)
        (count-form (car term) wanted)
        (count-form (cdr term) wanted))]
    [else 0]))

(define (check-rsd-step trace expected callables)
  (match-define (list _compiled configs rules) trace)
  (define index (index-of rules 'R-DischargeRemainder))
  (check-not-false index "trace includes R-DischargeRemainder")
  (when index
    (define after (list-ref configs (add1 index)))
    (define row (runtime-row after callables expected))
    (check-not-false row "the config immediately after RSD has a runtime row")
    (when row
      (check-true (config-ok? after callables expected row)
                  (format "config immediately after RSD: ~s" after)))
    (check-not-false
     (find-term
      (lambda (term)
        (match term
          [`(Rec ,fields) (and (assoc 'name fields) (assoc 'id fields))]
          [_ #f]))
      (config-heap after))
     "RSD 後の heap に hidden ではない nested id が残る")))

(define (joined-view-source condition result-type body)
  (string-append
   (if (string=? condition "g(b)")
       "fn g(value: Bool) -> Bool { return value }\n"
       "")
   "type Profile = { name: String }\n"
   "type View = { profile: Profile }\n"
   "fn f(b: Bool) -> " result-type " ! Mutation {\n"
   "  let mut value: View = { profile: { name: \"A\", id: 1 }, root: 0 }\n"
   "  if " condition " {\n"
   "    value = { profile: { name: \"B\" }, active: true }\n"
   "  } else { () }\n"
   body
   "}\nf(false)"))

(define (check-final-core trace expected)
  (when trace
    (match-define (list _compiled configs _rules) trace)
    (check-equal? (config-core (last configs)) expected)))

(define (check-config-trace initial expected [callables '()])
  (check-configs (config-trace initial) expected callables))

(define (const-config value view)
  `(cfg (Let (saved const ,view) ,value saved) () () () ()))

(define (rewrite-config value entry-type output-type)
  (define core
    `(RecRewrite (Rec ((item imm ,value)))
       ((item field ,entry-type imm ,output-type field))))
  `(cfg ,core () () () ()))

(define (entry-result-type output-type)
  `(Record ((item ,output-type imm))))

(define (replace-symbol term target replacement)
  (cond
    [(eq? term target) replacement]
    [(pair? term)
     (cons (replace-symbol (car term) target replacement)
           (replace-symbol (cdr term) target replacement))]
    [else term]))

(define (find-core-point core predicate)
  (let walk ([term core] [point '()])
    (cond
      [(predicate term) point]
      [else
       (for/or ([child (in-list (core-children term))]
                [index (in-naturals)])
         (walk child (append point (list index))))])))

(define (prepare-config-core core [callables '()])
  (define region-ir (build-region-ir core))
  (define filled (fill-region-placeholders core region-ir))
  (define borrow-point
    (find-core-point core (lambda (node) (match node [`(Borrow ,_) #t] [_ #f]))))
  (check-not-false borrow-point "借用 Core の Borrow point がある")
  (define rho (region->rho region-ir (region-at region-ir borrow-point)))
  (define filled-core (replace-symbol filled 'ph rho))
  (define filled-callables (replace-symbol callables 'ph rho))
  (define annotated (annotate-regions filled-core region-ir))
  (define mut-types (box (hash)))
  (define callable-contexts (box (hash)))
  (match (type-of/raw*+borrows annotated '() filled-callables '()
                                (region-ctx region-ir '() (hash) (hash))
                                #:mut-types mut-types
                                #:callable-contexts callable-contexts)
    [(list 'ok (list type _row table sigma renamed _sidecar))
     (define machine-core
       (annotate-callable-contexts
        (annotate-mut-binding-types
         (materialize-regions region-ir renamed table sigma)
         (unbox mut-types))
        (unbox callable-contexts) 'renamed))
     (values (inject-g2m machine-core) type)]
    [other (fail (format "Core の config trace 準備に失敗: ~s" other))]))

(define (find-term predicate term)
  (cond
    [(predicate term) term]
    [(pair? term)
     (or (find-term predicate (car term))
         (find-term predicate (cdr term)))]
    [else #f]))

(define (config-core configuration)
  (match configuration [`(cfg ,core ,_ ,_ ,_ ,_) core]))

(define (config-heap configuration)
  (match configuration [`(cfg ,_ ,heap ,_ ,_ ,_) heap]))

(define (check-prepared-rsd-trace core callables expected final-value)
  (let-values ([(initial type) (prepare-config-core core callables)])
     (check-equal? type expected)
     (define-values (configs rules) (config-trace+rules initial))
     (define rows
       (for/list ([configuration (in-list configs)])
         (runtime-row configuration callables expected)))
     (define first-live
       (for/first ([row (in-list rows)] [index (in-naturals)] #:when row)
         index))
     (define active-start (or first-live 0))
     (define rsd-index
       (for/first ([rule (in-list rules)] [index (in-naturals)]
                   #:when (eq? rule 'R-DischargeRemainder))
         index))
     (define rsd-position (or rsd-index 0))
     (define before-config (list-ref configs rsd-position))
     (define before-core (config-core before-config))
     (define after-core (config-core (list-ref configs (add1 rsd-position))))
     (define rsd-input
       (find-term
        (lambda (term)
          (match term
            [`(Discharge (ProofRep (Reserved o-narrow)
                                  (RemainderSafelyDropped ,_ ,_))
                         (Rec ,_))
             #t]
            [_ #f]))
        before-core))
     (define before-fields
       (match rsd-input [`(Discharge ,_ (Rec ,fields)) fields] [_ '()]))
     (define after-record
       (find-term
        (lambda (term)
          (match term
            [`(Rec ,fields)
             (and (assoc 'id fields) (assoc 'name fields))]
            [_ #f]))
        after-core))
     (define after-fields
       (match after-record [`(Rec ,fields) fields] [_ '()]))
     (check-not-false first-live "trace に runtime-row がある config がある")
     (check-not-false rsd-index "trace が R-DischargeRemainder を通る")
     (for ([configuration (in-list (drop configs active-start))]
           [row (in-list (drop rows active-start))]
           [index (in-naturals active-start)])
       (check-not-false row (format "config ~a の runtime-row" index))
       (check-true (config-ok? configuration callables expected row)
                   (format "config ~a の config-ok?" index)))
     (check-true (<= active-start rsd-position)
                 "RSD config は runtime-row が検査される範囲内")
     (check-not-false rsd-input "RSD 前に Record literal がある")
     (check-not-false (assoc 'hidden before-fields) "RSD 前に hidden がある")
     (define hidden-ref
       (find-term
        (lambda (term)
          (match term [`(BorrowRef ,_ ,_ ,_) #t] [_ #f]))
        (third (assoc 'hidden before-fields))))
     (check-not-false hidden-ref "RSD 前の hidden が BorrowRef")
     ;; R-LetB は Borrowed を置換するため、heap には BorrowRef の owner が残る。
     (define owner-slot (assoc (second hidden-ref) (config-heap before-config)))
     (check-not-false owner-slot "RSD 前 config の heap に BorrowRef の owner がある")
     (check-equal? (second owner-slot) '(resource 601))
     (check-not-false after-record "RSD 後に id と name を持つ Record がある")
     (check-false (assoc 'hidden after-fields) "RSD が hidden を物理的に除く")
     (check-equal? (third (assoc 'id after-fields)) 17
                   "RSD が id を物理的に残す")
     (check-equal? (third (assoc 'name after-fields)) "A")
     (check-equal? (config-core (last configs)) final-value)))

(test-case "A1: 仮引数の wide な実値を const に束縛する trace は変数と Apply g で保たれる"
  (define prefix
    (string-append
     "type Named = { name: String }\n"
     "type Wide = { name: String, id: Int }\n"
     "fn receive(n: Named) -> String {\n"
     "  const y: Named = n\n"
     "  return y.name\n"
     "}\n"))
  (check-source-trace
   (string-append
    prefix
    "fn caller(w: Wide) -> String { return receive(w) }\n"
    "caller({ name: \"A\", id: 1 })"))
  (check-source-trace
   (string-append
    prefix
    "fn g() -> Wide { return { name: \"A\", id: 1 } }\n"
    "fn caller() -> String { return receive(g()) }\n"
    "caller()")))

(test-case "A1: 分岐後の const は両枝の residual let を変数と Apply g で受ける"
  (for ([condition (in-list '("b" "yes(b)"))])
    (define prefix
      (if (string=? condition "b")
          ""
          "fn yes(value: Bool) -> Bool { return value }\n"))
    (check-source-trace
     (string-append
      "type Named = { name: String }\n"
      prefix
      "fn f(b: Bool) -> String {\n"
      "  const y: Named = if " condition " {\n"
      "    let x: Named = { name: \"A\", id: 1 }\n"
      "    leave x\n"
      "  } else {\n"
      "    let x: Named = { name: \"B\", id: 2 }\n"
      "    leave x\n"
      "  }\n"
      "  return y.name\n"
      "}\n"
      "f(true)"))))

(test-case "const と RecRewrite の view は入れ子幅・optional・mutability・Union・NFn 変位を受ける"
  (define narrow-record '(Record ((name String imm))))
  (define wide-record '(Record ((id Int imm) (name String imm))))
  (define nested-wide
    '(Record ((profile (Record ((id Int imm) (name String imm))) imm))))
  (define nested-view
    '(Record ((profile (Record ((name String imm))) imm))))
  (define narrow-union '(Union Int String))
  (define wide-union '(Union Bool (Union Int String)))
  (define narrow-function `(NFn () ,narrow-record () () () User))
  (define wide-function `(NFn () ,wide-record () () () User))
  (define cases
    (list
     (list 'nested
           nested-wide nested-view
           '(Rec ((profile imm (Rec ((name imm "A") (id imm 1))))))
           nested-view)
     (list 'required-optional
           '(Record ((a Int imm))) '(Record ((a Int imm opt)))
           '(Rec ((a imm 1))) '(Record ((a Int imm opt))))
     (list 'mut-to-imm
           '(Record ((a Int mut))) '(Record ((a Int imm)))
           '(Rec ((a mut 1))) '(Record ((a Int imm))))
     (list 'union-field
           `(Record ((choice ,narrow-union imm)))
           `(Record ((choice ,wide-union imm)))
           `(Rec ((choice imm (UnionVal ,narrow-union Int 1))))
           `(Record ((choice ,wide-union imm))))
     (list 'nfn-field
           `(Record ((call ,wide-function imm)))
           `(Record ((call ,narrow-function imm)))
           '(Rec ((call imm
                       (Lam User returns-record ()
                         (Rec ((name imm "A") (id imm 1)))))))
           `(Record ((call ,narrow-function imm))))))
  (for ([case (in-list cases)])
    (define name (first case))
    (define actual (second case))
    (define view (third case))
    (define value (fourth case))
    (define expected-row (fifth case))
    (define callables
      (if (eq? name 'nfn-field)
          `((returns-record ,wide-function))
          '()))
    (check-config-trace (const-config value view) view callables)
    (check-config-trace (rewrite-config value actual view)
                        (entry-result-type expected-row)
                        callables)))

(test-case "Reassign の config 許容は required の実値を optional な C に保つ"
  (define view '(Record ((a Int imm opt))))
  (define actual '(Rec ((a imm 2))))
  (define initial '(Rec ((a imm 1))))
  (define config
    `(cfg (Reassign (MutSlot 0) ,view ,actual)
          ((0 ,initial (declared ,view))) ((0 Available)) () ()))
  (check-config-trace config 'Unit))

(test-case "RSD は hidden borrow だけを除き id を残し、その実値を const view が受ける"
  (define borrowed '(Borrowed Res ph))
  (define actual
    `(Record ((hidden ,borrowed imm) (id Int imm) (name String imm))))
  (define view '(Record ((name String imm))))
  (define proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,actual ,view)))
  (define value
    '(Rec ((hidden imm borrow) (id imm 17) (name imm "A"))))
  (define g-type '(NFn () Bool () () () User))
  (define elimination
    `((true () ->
       (Let (saved const ,view) (Discharge ,proof ,value)
         (Proj saved name)))
      (false () -> "none")))
  (for ([source (in-list '(variable apply))])
    (define execution
      (if (eq? source 'variable)
          `(Let (flag const Bool) (Construct Bool true)
             (Eliminate flag ,elimination))
          `(Let (g const ,g-type) (Lam User g () (Construct Bool true))
             (Eliminate (Apply g) ,elimination))))
    (define core
      `(Scope ()
         (Let (owner let (Owned Res)) (resource 601)
           (Scope ()
             (Let (borrow let ,borrowed) (Borrow owner) ,execution)))))
    (define callables (if (eq? source 'apply) `((g ,g-type)) '()))
    (check-prepared-rsd-trace core callables 'String "A")))

(test-case "config view は tag 差を受けるが隠れた Owned/borrow を拒否する"
  (define narrow '(Record ((name String imm))))
  (define wider '(Record ((id Int imm) (name String imm))))
  (define borrowed
    '(Record ((hidden (Borrowed Int 0) imm) (name String imm))))
  (define owned
    '(Record ((hidden (Owned Res) imm) (name String imm))))
  (define narrow-union '(Union Int String))
  (define wide-union '(Union Bool (Union Int String)))
  (define narrow-function `(NFn () ,narrow () () () User))
  (define wide-function `(NFn () ,wider () () () User))
  (for ([pair (in-list
               (list
                (list wider narrow)
                (list '(Record ((a Int imm)))
                      '(Record ((a Int imm opt))))
                (list '(Record ((a Int mut)))
                      '(Record ((a Int imm))))
                (list `(Record ((choice ,narrow-union imm)))
                      `(Record ((choice ,wide-union imm))))
                (list `(Record ((call ,wide-function imm)))
                      `(Record ((call ,narrow-function imm))))
                (list narrow-union wide-union)
                (list wide-function narrow-function)))])
    (check-true (config-view-compatible? (first pair) (second pair))
                (format "expected config view compatibility: ~s" pair)))
  (for ([pair (in-list
               (list
                (list '(Record ((a Int imm opt))) '(Record ((a Int imm))))
                (list '(Record ((a Int imm))) '(Record ((a Int mut))))
                (list '(Union Bool (Union Int String)) '(Union Int String))
                (list '(Record ((a Int mut))) '(Record ((a Bool mut))))
                (list '(Option (Record ((id Int imm) (name String imm))))
                      '(Option (Record ((name String imm)))))
                (list '(Result (Record ((id Int imm) (name String imm))) Int)
                      '(Result (Record ((name String imm))) Int))
                (list borrowed narrow)
                (list owned narrow)
                (list `(NFn () ,borrowed () () () User)
                      `(NFn () ,narrow () () () User))))])
    (check-false (config-view-compatible? (first pair) (second pair))
                 (format "expected rejection of config view: ~s" pair)))
  ;; RSD で hidden だけを除いた後は、残った非資源 id を view から隠せる。
  (check-true (config-view-compatible? wider narrow)))

(test-case "非 Record の Union/NFn view は const と RecRewrite entry で受理される"
  (define narrow-union '(Union Int String))
  (define wide-union '(Union Bool (Union Int String)))
  (define narrow-record '(Record ((name String imm))))
  (define wide-record '(Record ((id Int imm) (name String imm))))
  (define narrow-function `(NFn () ,narrow-record () () () User))
  (define wide-function `(NFn () ,wide-record () () () User))
  (for ([case (in-list
               (list
                (list narrow-union wide-union
                      `(UnionVal ,narrow-union Int 1))
                (list wide-function narrow-function
                      '(Lam User returns-record ()
                         (Rec ((name imm "A") (id imm 1)))))))])
    (define actual (first case))
    (define view (second case))
    (define value (third case))
    (check-true (config-view-compatible? actual view))
    (define callables
      (if (equal? actual wide-function)
          `((returns-record ,actual))
          '()))
    (check-config-trace (const-config value view) view callables)
    (check-config-trace (rewrite-config value actual view)
                        (entry-result-type view)
                        callables)))

(test-case "Non-Record config Reassign の NFn 返り値拡張は変数と Apply g で受理される"
  (define narrow-record '(Record ((name String imm))))
  (define wide-record '(Record ((id Int imm) (name String imm))))
  (define actual `(NFn () ,wide-record () (Partial) () User))
  (define view `(NFn () ,narrow-record () (Partial) () User))
  (define initial-value
    '(Lam User initial () (Rec ((name imm "A")))))
  (define callables
    `((initial ,view)
      (candidate ,actual)
      (g (NFn () ,actual () () () User))))
  (check-false (reassign-narrowing? actual view))
  (check-false (rsd-proof-pair-ok? actual view tag-compat?))
  (check-true (config-view-compatible? actual view))
  (check-equal?
   (core-type-of
    `(Reassign cell ,view
       (Lam User candidate () (Rec ((name imm "B") (id imm 2)))))
    '() `((candidate ,actual)) `((cell ,view mut)))
   'ill-typed)
  (for ([rhs-kind (in-list '(variable apply))])
    (define candidate
      `(Lam User candidate () (Rec ((name imm "B") (id imm 2)))))
    (define assigned-rhs
      (if (eq? rhs-kind 'variable)
          `(Let (candidate const ,actual) ,candidate
             (Reassign (MutSlot 0) ,view candidate))
          `(Let (g const (NFn () ,actual () () () User))
               (Lam User g () ,candidate)
             (Reassign (MutSlot 0) ,view (Apply g)))))
    (define initial
      `(cfg ,assigned-rhs ((0 ,initial-value (declared ,view)))
            ((0 Available)) () ()))
    (check-config-trace initial 'Unit callables)))

(test-case "Owned の config 拒否と source の const/entry 契約は不変"
  (define view '(Record ((name String imm))))
  (define owned-wide
    '(Record ((hidden (Owned Res) imm) (id Int imm) (name String imm))))
  (define owned-value
    '(Rec ((hidden imm (OwnedLeaf (tok 90) (resource 91)))
          (id imm 17)
          (name imm "A"))))
  (check-false (config-view-compatible? owned-wide view))
  (check-false
   (config-ok? (const-config owned-value view) '() view '()))
  (check-equal?
   (core-type-of
    `(Let (saved const ,view) (Rec ((id imm 1) (name imm "A"))) saved)
    '() '())
   'ill-typed)
  (define bad-entry
    `(RecRewrite (Rec ((item imm (Rec ((id imm 1) (name imm "A"))))))
       ((item field ,view imm ,view field))))
  (check-equal? (core-type-of bad-entry '() '()) 'ill-typed))

(test-case "Owned RSD の後に残る id を RecRewrite entry が view 互換で受ける"
  (define view '(Record ((name String imm))))
  (define actual
    '(Record ((hidden (Owned Res) imm) (id Int imm) (name String imm))))
  (define proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,actual ,view)))
  (define value
    '(Rec ((hidden imm (OwnLeaf (resource 611)))
          (id imm 17)
          (name imm "A"))))
  (define core
    `(RecRewrite
      (Rec ((item imm (Discharge ,proof ,value))))
      ((item field ,view imm String (Proj field name)))))
  (define expected (entry-result-type 'String))
  (define initial `(cfg ,core () () () ()))
  (define-values (configs rules) (config-trace+rules initial))
  (define rows
    (for/list ([configuration (in-list configs)])
      (runtime-row configuration '() expected)))
  (define first-live
    (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
  (define rsd-index
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (eq? rule 'R-DischargeRemainder))
      index))
  (check-not-false first-live "Owned trace に runtime-row がある config がある")
  (check-not-false rsd-index "Owned の trace が RSD を通る")
  (for ([configuration (in-list (drop configs (or first-live 0)))]
        [row (in-list (drop rows (or first-live 0)))]
        [index (in-naturals (or first-live 0))])
    (check-not-false row)
    (check-true (config-ok? configuration '() expected row)
                (format "Owned config ~a: ~s; row=~s" index configuration row)))
  (define before-core (config-core (list-ref configs rsd-index)))
  (define before-rsd
    (find-term
     (lambda (term)
       (match term [`(Discharge (ProofRep (Reserved o-narrow) ,_) (Rec ,_)) #t]
         [_ #f]))
     before-core))
  (check-not-false before-rsd (format "RSD 前の config core: ~s" before-core))
  (define before-fields
    (match before-rsd [`(Discharge ,_ (Rec ,fields)) fields] [_ '()]))
  (check-not-false
   (find-term
    (lambda (term)
      (match term [`(OwnedLeaf ,_ (resource 611)) #t] [_ #f]))
    (third (assoc 'hidden before-fields)))
   "RSD 前の hidden は OwnLeaf 由来の OwnedLeaf")
  (define after-core (config-core (list-ref configs (add1 rsd-index))))
  (define after-record
    (find-term
     (lambda (term)
       (match term
         [`(Rec ,fields) (and (assoc 'id fields) (assoc 'name fields))]
         [_ #f]))
     after-core))
  (check-not-false after-record "Owned RSD 後に id と name が残る")
  (define after-fields (match after-record [`(Rec ,fields) fields] [_ '()]))
  (check-false (assoc 'hidden after-fields))
  (check-equal? (third (assoc 'id after-fields)) 17)
  (check-equal? (config-core (last configs)) '(Rec ((item imm "A"))))
  (check-not-false (member 'R-RecRewrite-Close rules)))

(test-case "借用余剰と NFn 返り値の借用余剰は config view で拒否する"
  (define view '(Record ((name String imm))))
  (define borrowed-wide
    '(Record ((hidden (Borrowed Int 0) imm) (name String imm))))
  (define borrowed-value
    '(Rec ((hidden imm (BorrowRef 1 () 0)) (name imm "A"))))
  (check-false (config-view-compatible? borrowed-wide view))
  (check-false
   (config-ok?
    `(cfg (Let (saved const ,view) ,borrowed-value saved)
          ((1 0 (declared Int))) ((1 Available)) () ())
    '() view '()))
  (check-false
   (config-view-compatible?
    `(NFn () ,borrowed-wide () () () User)
    `(NFn () ,view () () () User))))

(test-case "tag 差の逆方向は config view に通さない"
  (for ([pair (in-list
               '(((Record ((a Int imm opt))) (Record ((a Int imm))))
                 ((Record ((a Int imm))) (Record ((a Int mut))))
                 ((Union Bool (Union Int String)) (Union Int String))
                 ((Record ((a Int mut))) (Record ((a Bool mut))))))])
    (check-false (config-view-compatible? (first pair) (second pair)))))

(test-case "Surface の const は view に無い欄を引き続き拒否する"
  (define result
    (compile-source/string
     'src
     (string-append
      "type Named = { name: String }\n"
      "fn f(n: Named) -> Int {\n"
      "  const y: Named = n\n"
      "  return y.id\n"
      "}\nf({ name: \"A\" })")))
  (check-true (diagnostic? result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-RCD-004")))

(test-case "merge view の nested update・shape 再代入・即時 capture 呼び出しを trace で保つ"
  (for ([condition (in-list '("b" "g(b)"))])
    (define updated
      (check-source-trace
        (joined-view-source
        condition "String"
        (string-append
         "  value = { profile: { name: \"C\" } }\n"
         "  return value.profile.name\n"))
       #:require-rules '(R-DischargeRemainder)
       #:return-trace? #t))
    (when updated
      (check-rsd-step updated (compiled-type (first updated))
                      (compiled-callables (first updated)))
      (check-final-core updated "C"))

    (define reshaped
      (check-source-trace
        (joined-view-source
        condition "Bool"
        (string-append
         "  value = { profile: { name: \"C\" }, active: true }\n"
         "  return value.active\n"))
       #:require-rules '(R-DischargeRemainder)
       #:return-trace? #t))
    (when reshaped
      (check-rsd-step reshaped (compiled-type (first reshaped))
                      (compiled-callables (first reshaped)))
      (check-final-core reshaped '(Construct Bool true)))

    (define captured
      (check-source-trace
        (joined-view-source
        condition "String"
       (string-append
         "  let reader = fn() => value.profile.name\n"
         "  return reader()\n"))
       #:require-rules '(R-DischargeRemainder)
       #:return-trace? #t))
    (when captured
      (check-rsd-step captured (compiled-type (first captured))
                      (compiled-callables (first captured)))
      (check-final-core captured "A"))))

(test-case "同じ静的 J への分岐合流は変換を挿さず trace を保つ"
  (for ([condition (in-list '("b" "g(b)"))])
    (define prefix
      (string-append
       (if (string=? condition "g(b)")
           "fn g(value: Bool) -> Bool { return value }\n"
           "")
       "type Profile = { name: String }\n"
       "type View = { profile: Profile }\n"
       "fn f(b: Bool) -> String ! Mutation {\n"
       "  let mut value: View = { profile: { name: \"A\", id: 1 }, root: 0 }\n"
       "  if " condition " {\n"
       "    value = { profile: { name: \"B\" } }\n"
       "  } else {\n"
       "    value = { profile: { name: \"C\" } }\n"
       "  }\n"
       "  return value.profile.name\n"
       "}\nf(false)"))
    (define trace
      (check-source-trace prefix #:forbid-rules '(R-DischargeRemainder)
                          #:return-trace? #t))
    (when trace
      (check-equal? (count-form (compiled-core (first trace)) 'Reassign) 2)
      (check-true (positive? (count-form (compiled-core (first trace)) 'Eliminate)))
      (check-final-core trace "C"))))

(test-case "merge 後に RecRewrite する関数へ渡した入力を各 config で再型付けする"
  (for ([condition (in-list '("b" "g(b)"))])
    (define source
      (string-append
       (if (string=? condition "g(b)")
           "fn g(value: Bool) -> Bool { return value }\n"
           "")
       "type Profile = { name: String }\n"
       "type WideProfile = { name: String | Int }\n"
       "type View = { profile: Profile }\n"
       "type Widened = { profile: WideProfile }\n"
       "fn rewrite(p: View) -> Widened { return p }\n"
       "fn f(b: Bool) -> Widened ! Mutation {\n"
       "  let mut value: View = { profile: { name: \"A\", id: 1 }, root: 0 }\n"
       "  if " condition " {\n"
       "    value = { profile: { name: \"B\" }, active: true }\n"
       "  } else { () }\n"
       "  return rewrite(value)\n"
       "}\nf(false)"))
    (define trace
       (check-source-trace source
                          #:require-rules '(R-DischargeRemainder
                                            R-RecRewrite-Open
                                            R-RecRewrite-Close)
                          #:return-trace? #t))
    (when trace
      (check-true (positive? (count-form (compiled-core (first trace))
                                         'RecRewrite)))
      (check-rsd-step trace (compiled-type (first trace))
                      (compiled-callables (first trace))))))

(test-case "Option payload の広い Record を枝で取り出して RecRewrite する"
  (define prefix
    (string-append
     "type Profile = { name: String }\n"
     "type WideProfile = { name: String | Int }\n"
     "type View = { profile: Profile }\n"
     "type Widened = { profile: WideProfile }\n"
     "fn rewrite(p: View) -> Widened { return p }\n"
     "fn g() -> Option<View> ! Mutation {\n"
     "  let mut value: View = { profile: { name: \"A\", id: 1 }, root: 0 }\n"
     "  if false { value = { profile: { name: \"B\" }, active: true } } else { () }\n"
     "  return some(value)\n"
     "}\n"))
  (for ([scrutinee (in-list '(variable apply))])
    (define source
      (string-append
       prefix
       (if (eq? scrutinee 'variable)
           (string-append
            "fn f(option: Option<View>) -> Widened {\n"
            "  return when option {\n"
            "    some value => rewrite(value)\n"
            "    none => rewrite({ profile: { name: \"none\" } })\n"
            "  }\n}\nf(g())")
           (string-append
            "fn f() -> Widened ! Mutation {\n"
            "  return when g() {\n"
            "    some value => rewrite(value)\n"
            "    none => rewrite({ profile: { name: \"none\" } })\n"
            "  }\n}\nf()"))))
    (define trace
       (check-source-trace source
                          #:require-rules '(R-DischargeRemainder
                                            R-RecRewrite-Open
                                            R-RecRewrite-Close)
                          #:return-trace? #t))
    (when trace
      (check-true (positive? (count-form (compiled-core (first trace))
                                         'RecRewrite)))
      (check-rsd-step trace (compiled-type (first trace))
                      (compiled-callables (first trace))))))

(test-case "Union payload の広い Record を枝で取り出して RecRewrite する"
  (define prefix
    (string-append
     "type Profile = { name: String }\n"
     "type WideProfile = { name: String | Int }\n"
     "type View = { profile: Profile }\n"
     "type Choice = View | Bool\n"
     "type Widened = { profile: WideProfile }\n"
     "fn rewrite(p: View) -> Widened { return p }\n"
     "fn g() -> Choice ! Mutation {\n"
     "  let mut value: View = { profile: { name: \"A\", id: 1 }, root: 0 }\n"
     "  if false { value = { profile: { name: \"B\" }, active: true } } else { () }\n"
     "  return value\n"
     "}\n"))
  (for ([scrutinee (in-list '(variable apply))])
    (define source
      (string-append
       prefix
       (if (eq? scrutinee 'variable)
           (string-append
            "fn f(choice: Choice) -> Widened {\n"
            "  return when choice {\n"
            "    (value: View) => rewrite(value)\n"
            "    (flag: Bool) => rewrite({ profile: { name: \"none\" } })\n"
            "  }\n}\nf(g())")
           (string-append
            "fn f() -> Widened ! Mutation {\n"
            "  return when g() {\n"
            "    (value: View) => rewrite(value)\n"
            "    (flag: Bool) => rewrite({ profile: { name: \"none\" } })\n"
            "  }\n}\nf()"))))
    (define trace
       (check-source-trace source
                          #:require-rules '(R-DischargeRemainder
                                            R-RecRewrite-Open
                                            R-RecRewrite-Close)
                          #:return-trace? #t))
    (when trace
      (check-true (positive? (count-form (compiled-core (first trace))
                                         'RecRewrite)))
      (check-rsd-step trace (compiled-type (first trace))
                      (compiled-callables (first trace))))))

(test-case "RecRewrite 後も書換え欄と未書換え欄の nested width を読み取れる"
  (define source
    (string-append
     "type Name = { name: String }\n"
     "type WideName = { name: String | Int }\n"
     "type Flag = { flag: Bool }\n"
     "type Output = { profile: WideName, keep: Flag, convert: Int | String }\n"
     "type Input = { profile: Name, keep: Flag, convert: Int }\n"
     "fn rewrite(input: Input) -> Output { return input }\n"
     "fn f(b: Bool) -> Bool ! Mutation {\n"
     "  let mut value: Input = { profile: { name: \"A\", id: 1 }, keep: { flag: true, code: 9 }, convert: 1, root: 0 }\n"
     "  if b { value = { profile: { name: \"B\" }, keep: { flag: false }, convert: 2 } } else { () }\n"
     "  let result: Output = rewrite(value)\n"
     "  return when result.profile.name {\n"
     "    (name: String) => result.keep.flag\n"
     "    (id: Int) => false\n"
     "  }\n"
     "}\nf(false)"))
  (define trace
    (check-source-trace source
                        #:require-rules '(R-DischargeRemainder
                                          R-RecRewrite-Open
                                          R-RecRewrite-Close)
                        #:return-trace? #t))
  (when trace
    (define-values (_compiled configs rules) (apply values trace))
    (define close-indices
      (for/list ([rule (in-list rules)] [index (in-naturals)]
                 #:when (eq? rule 'R-RecRewrite-Close))
        index))
    (define close-index (and (pair? close-indices) (last close-indices)))
    (check-not-false close-index)
    (when close-index
      (define after (config-core (list-ref configs (add1 close-index))))
      (define output
        (find-term
         (lambda (term)
           (match term
             [`(Rec ,fields)
              (and (assoc 'profile fields) (assoc 'keep fields)
                   (assoc 'convert fields))]
             [_ #f]))
         after))
      (check-not-false output
                       (format "RecRewrite 後の Output Record が live: ~s" after))
      (when output
        (define fields (second output))
        (define rewritten
          (find-term
           (lambda (term)
             (match term [`(Rec ,row) (assoc 'id row)] [_ #f]))
           (third (assoc 'profile fields))))
        (define untouched
          (find-term
           (lambda (term)
             (match term [`(Rec ,row) (assoc 'code row)] [_ #f]))
           (third (assoc 'keep fields))))
        (check-not-false rewritten "書換え欄 profile の nested id が残る")
        (check-not-false untouched "未書換え欄 keep の nested code が残る")))))

(test-case "Union 部分集合と NFn 共変欄の RecRewrite 後を trace で検査する"
  (define union-source
    (string-append
     "type Input = { choice: Int | String, convert: Int }\n"
     "type Output = { choice: Bool | Int | String, convert: Int | String }\n"
     "fn widen(input: Input) -> Output { return input }\n"
     "widen({ choice: 1, convert: 2 })"))
  (define union-trace
    (check-source-trace union-source
                        #:require-rules '(R-RecRewrite-Open
                                          R-RecRewrite-Close)
                        #:return-trace? #t))
  (when union-trace
    (check-true (positive? (count-form (compiled-core (first union-trace))
                                       'RecRewrite))))

  (define function-source
    (string-append
     "type Name = { name: String }\n"
     "type WideName = { name: String, id: Int }\n"
     "type Input = { call: fn() -> WideName, convert: Int }\n"
     "type Output = { call: fn() -> Name, convert: Int | String }\n"
     "fn g() -> WideName { return { name: \"A\", id: 1 } }\n"
     "fn f(input: Input) -> String {\n"
     "  let output: Output = input\n"
     "  return output.call().name\n"
     "}\nf({ call: g, convert: 1 })"))
  (define function-trace
    (check-source-trace function-source
                        #:require-rules '(R-RecRewrite-Open
                                          R-RecRewrite-Close)
                        #:return-trace? #t))
  (when function-trace
    (check-true (positive? (count-form (compiled-core (first function-trace))
                                       'RecRewrite)))
    (check-final-core function-trace "A")))

(test-case "scalar Union の注入と消去を全 trace config で検査する"
  (for ([scrutinee (in-list '(variable apply))])
    (define source
      (if (eq? scrutinee 'variable)
          (string-append
           "fn g() -> Int | String { return 7 }\n"
           "fn f(value: Int | String) -> Int {\n"
           "  return when value {\n    (number: Int) => number\n    (text: String) => 0\n  }\n"
           "}\nf(g())")
          (string-append
           "fn g() -> Int | String { return 7 }\n"
           "fn f() -> Int {\n"
           "  return when g() {\n    (number: Int) => number\n    (text: String) => 0\n  }\n"
           "}\nf()")))
    (define trace (check-source-trace source #:return-trace? #t))
    (when trace
      (define compiled (first trace))
      (check-true (positive? (count-form (compiled-core compiled) 'UnionInject)))
      (check-true (positive? (count-form (compiled-core compiled) 'UnionEliminate)))
      (check-final-core trace 7))))

#lang racket

;; c3n2。Owned place から移した値が marker に保持され、消費後まで
;; 各構成の型と token 台帳が保たれることを一手ずつ確かめる。
(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../typing.rkt")

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (control configuration)
  (match configuration [`(cfg ,core ,_ ...) core]))

(define (heap configuration)
  (match configuration [`(cfg ,_ ,entries ,_ ...) entries]))

(define (tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,states ,_) states]))

(define (find-curry-value term)
  (match term
    [`(CurryVal ,_ ,_ ,_) term]
    [(? list? items)
     (for/or ([item (in-list items)]) (find-curry-value item))]
    [_ #f]))

(define (check-config-trace configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row
                     (format "config ~a の runtime row が無い: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "config ~a が不正: ~s" index configuration))))

(define (check-transit-prefix configs rules prefix)
  (define start
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (memq rule '(R-Move R-Forward)))
      index))
  (check-not-false start "R-Move も R-Forward も無い")
  (when (and start (<= (+ start (length prefix)) (length rules)))
    (check-equal? (take (drop rules start) (length prefix)) prefix))
  (and start (list-ref configs (add1 start))))

(define (check-terminal-cleanup terminal)
  (define held (collect-tokens (control terminal)))
  (for ([entry (in-list (tokens terminal))])
    (match entry
      [(list tk 'Available)
       (check-not-false (memq tk held)
                        (format "結果の値に無い token が Available: ~s" tk))]
      [_ (void)])))

(define (run-program core callables expected-prefix terminal-predicate
                     [places '()] [expected-transit-count 1])
  (define inferred (core-type-of core places callables))
  (check-true (and (list? inferred) (= (length inferred) 2))
              (format "source Core の型付けに失敗した: ~s; ~s"
                      inferred
                      (core-type-of/diagnostic core '() callables)))
  (if (and (list? inferred) (= (length inferred) 2))
      (let ([expected (first inferred)])
        (define-values (configs rules) (trace-g2 (inject-g2m core)))
        (check-config-trace configs callables expected)
        (define after-transit
          (check-transit-prefix configs rules expected-prefix))
        (when after-transit
          (check-equal? (length (transit-places (control after-transit)))
                        expected-transit-count
                        "最初の Move または Forward の移送 marker 数"))
        (define terminal (last configs))
        (check-true (terminal-predicate (control terminal))
                    (format "終端形が違う: ~s" (control terminal)))
        (check-terminal-cleanup terminal)
        (values configs rules expected after-transit))
      (values '() '() #f #f)))

(define (run-elaborated-source source)
  (match (elab source)
    [(list span-core type row callables)
     (define core (erase-core span-core))
     (check-equal? (core-type-of core '() callables) (list type row))
     (define-values (configs rules) (trace-g2 (inject-g2m core)))
     (check-config-trace configs callables type)
     (values configs rules type)]
    [other (fail (format "UCore の elaborate に失敗した: ~s" other))]))

(define int-function-type '(NFn (Int) Int () () () User))
(define int-callables `((identity ,int-function-type)))

(test-case "resource literal の Move は marker を作らない"
  (define core
    '(Scope ()
       (Let (p let (Owned Res)) (resource 7) (Drop (Move p)))))
  (define-values (configs _rules _expected _after)
    (run-program core '() '(R-Move R-Drop)
                 (lambda (c) (equal? c 'unit)) '() 0))
  (check-equal? (map second (tokens (last configs))) '(Dropped Dropped)))

(test-case "G1 の R-Move は marker を作らない"
  (define core '(Scope () (Let (p (Owned Int)) 17 (Drop (Move p)))))
  (let loop ([current (inject core)] [remaining 20] [seen-move? #f])
    (unless (zero? remaining)
      (match (apply-reduction-relation/tag-with-names -->g1/rules current)
        ['() (check-true seen-move? "G1 trace が R-Move に到達する")]
        [(list (list rule next))
         (define move? (string=? rule "R-Move"))
         (when move?
           (check-equal? (transit-places (control next)) '())
           (check-false seen-move? "G1 trace は R-Move を一度だけ通る"))
         (loop next (sub1 remaining) (or seen-move? move?))]
        [steps (fail (format "G1 に一意でない次状態がある: ~s" steps))]))))

(test-case "Owned Int を Move して Drop する"
  (define core
    '(Scope ()
       (Let (p let (Owned Int)) 17 (Drop (Move p)))))
  ;; Core の row は Drop の Own だけである。
  (define-values (configs rules _expected _after)
    (run-program core '() '(R-Move R-Drop) (lambda (c) (equal? c 'unit))))
  (check-not-false (member 'R-ScopeValue rules))
  (check-equal? (tokens (last configs)) '()))

(test-case "UCore の Lam は elaboration 後に値へ簡約する"
  (define-values (configs rules _type)
    (run-elaborated-source '(Fn ((x Int)) Int () x)))
  (check-not-false (member 'R-ScopeValue rules))
  (check-true (match (control (last configs)) [`(Lam ,_ ,_ ,_ ,_) #t] [_ #f])))

(test-case "UCore の PrimVal は elaboration 後に値へ簡約する"
  (define-values (configs rules _type)
    (run-elaborated-source 'add))
  (check-not-false (member 'R-ScopeValue rules))
  (check-true (match (control (last configs)) [`(PrimVal ,_ ,_) #t] [_ #f])))

(test-case "UCore の Curry は CurryVal へ簡約する"
  (define-values (configs rules _type)
    (run-elaborated-source '(Curry add 20)))
  (check-not-false (member 'R-CurryVal rules))
  (check-true (match (control (last configs)) [`(CurryVal ,_ ,_ ,_) #t] [_ #f])))

(test-case "UCore の Recur は RecurVal へ簡約する"
  (define-values (configs rules _type)
    (run-elaborated-source '(Recur loop ((x Int)) Int () x loop)))
  (check-not-false (member 'R-RecurBind rules))
  (check-true (match (control (last configs)) [`(RecurVal ,_ ,_ ,_ ,_) #t] [_ #f])))

(test-case "C4-001 の UCore Eliminate は移送 marker を外して枝を選ぶ"
  (define source
    '(Fn ((xs (Owned (List Int)))) Int (Own)
       (Eliminate (Move xs)
         ((nil () -> 0)
          (cons (head tail) -> head)))))
  (define-values (function function-type _function-row callables)
    (match (elab source)
      [(list span-core type row known-callables)
       (values (erase-core span-core) type row known-callables)]
      [other (fail (format "C4-001 UCore の elaborate に失敗した: ~s" other))]))
  (define control-term `(Scope (0) (Apply ,function (Move 0))))
  (define places '((0 (List Int))))
  (define typed (core-type-of control-term places callables))
  (check-true (and (list? typed) (= (length typed) 2))
              (format "C4-001 の実行項が型付けされない: ~s" typed))
  (define list-value
    '(Construct (List Int) cons 31 (Construct (List Int) nil)))
  (define start
    `(cfg ,control-term ((0 ,list-value (declared (Owned (List Int)))))
          ((0 Available)) () ()))
  (define-values (configs rules) (trace-g2 start))
  (check-config-trace configs callables (first typed))
  (check-not-false (member 'R-EliminateTransit rules))
  (check-not-false (member 'R-Eliminate rules))
  (check-equal? (control (last configs)) 31))

(test-case "Moved marker を Owned の q へ再束縛して Drop する"
  (define core
    '(Scope ()
       (Let (p let (Owned Int)) 17
         (Let (q let (Owned Int)) (Move p) (Drop (Move q))))))
  (define-values (configs rules _expected _after)
    (run-program core '() '(R-Move R-LetOwnedB)
                 (lambda (c) (equal? c 'unit))))
  (define second-let-index
    (for/first ([rule (in-list rules)] [index (in-naturals)]
                #:when (and (eq? rule 'R-LetOwnedB)
                            (positive? index)))
      index))
  (check-not-false second-let-index)
  (when second-let-index
    (define after (list-ref configs (add1 second-let-index)))
    (check-true
     (for/or ([entry (in-list (heap after))])
       (match entry
         [(list _ 17 '(declared (Owned Int))) #t]
         [_ #f]))
     "q の heap 値は marker を外した 17 で宣言型は Owned Int"))
  (check-equal? (tokens (last configs)) '()))

(test-case "Owned Lam の関数位置 marker を外して適用する"
  (define core
    '(Scope ()
       (Let (p let (Owned (NFn (Int) Int () () () User)))
            (Lam User identity (x) x)
         (Apply (Move p) 7))))
  (define-values (configs rules _expected _after)
    (run-program core int-callables
                 '(R-Move R-ApplyTransit R-Beta)
                 (lambda (c) (equal? c 7))))
  (void configs rules))

(test-case "Owned primitive の関数位置 marker を外して適用する"
  (define add '(PrimVal (Reserved o-add) add))
  (define core
    `(Scope ()
       (Let (p let (Owned (NFn (Int Int) Int () () ()
                               (Reserved o-add))))
            ,add
         (Apply (Move p) 7 8))))
  (define-values (_configs _rules _expected _after)
    (run-program core '() '(R-Move R-ApplyTransit R-Delta)
                 (lambda (c) (equal? c 15))))
  (void))

(test-case "Owned CurryVal の関数位置 marker を外して適用する"
  (define two-argument-type '(NFn (Int Int) Int () () () User))
  (define curried
    '(Curry (Lam User two-arguments (fixed next) fixed) 0))
  (define core
    `(Scope ()
       (Let (p let (Owned ,int-function-type)) ,curried
         (Apply (Move p) 23))))
  (define-values (_configs _rules _expected _after)
    (run-program core `((two-arguments ,two-argument-type))
                 '(R-Move R-ApplyTransit R-ApplyCurry R-Beta)
                 (lambda (c) (equal? c 0))))
  (void))

(test-case "Curry の関数欄で marker を保持し origin と二重移送を保つ"
  (define two-argument-type '(NFn (Int Int) Int () () () User))
  (define curried-lambda '(Lam User c3n-bin (x y) x))
  (define core
    `(Scope ()
       (Let (p let (Owned ,two-argument-type)) ,curried-lambda
         (Let (q let (Owned (NFn (Int) Int () () () User)))
              (Curry (Move p) 1)
           (Apply (Move q) 2)))))
  (define-values (configs rules _expected _after)
    (run-program core `((c3n-bin ,two-argument-type))
                 '(R-Move R-CurryTransit R-LetOwnedB R-Move
                           R-ApplyTransit R-ApplyCurry R-ApplyTransit R-Beta)
                 (lambda (c) (equal? c 1))))
  (define curry-index (index-of rules 'R-CurryTransit))
  (check-not-false curry-index)
  (when curry-index
    (define after-curry (list-ref configs (add1 curry-index)))
    (define curry-value (find-curry-value (control after-curry)))
    (check-not-false curry-value "CurryVal が marker を関数欄に保持する")
    (when curry-value
      (match curry-value
        [`(CurryVal ,_ (OwnedTransit ,place (Lam ,_ ,_ ,_ ,_)) ,_)
         (check-equal? place 0)]
        [_ (fail (format "CurryVal の関数欄が marker でない: ~s"
                         curry-value))])
      (check-equal? (term (verify-origins ,R0 ,curry-value)) 'ok)))
  (define q-move-index
    (and curry-index
         (for/first ([rule (in-list rules)] [index (in-naturals)]
                     #:when (and (> index curry-index) (eq? rule 'R-Move)))
           index)))
  (check-not-false q-move-index "q の Move がある")
  (when q-move-index
    (define after-q-move (list-ref configs (add1 q-move-index)))
    (check-equal? (sort (transit-places (control after-q-move)) <) '(0 1))))

(test-case "Owned RecurVal の関数位置 marker を外して適用する"
  (define recur
    '(Recur identity-recur loop (x) x loop))
  (define core
    `(Scope ()
       (Let (p let (Owned ,int-function-type)) ,recur
         (Apply (Move p) 23))))
  (define-values (_configs _rules _expected _after)
    (run-program core `((identity-recur ,int-function-type))
                 '(R-Move R-ApplyTransit R-RecurUnfold)
                 (lambda (c) (equal? c 23))))
  (void))

(test-case "Owned List の Eliminate marker を外して枝を選ぶ"
  (define list-type '(List Int))
  (define list-value '(Construct (List Int) cons 31
                                 (Construct (List Int) nil)))
  (define core
    `(Scope ()
       (Let (p let (Owned ,list-type)) ,list-value
         (Eliminate (Move p)
           ((nil () -> 0)
            (cons (head tail) -> head))))))
  (define-values (_configs rules _expected _after)
    (run-program core '() '(R-Move R-EliminateTransit)
                 (lambda (c) (equal? c 31))))
  (define transit-index (index-of rules 'R-EliminateTransit))
  (check-not-false transit-index))

(test-case "OwnLeaf の Owned Int producer は marker をそのまま運ぶ"
  (define core
    '(Scope ()
       (Let (p let (Owned Int)) 37
         (Construct (Option (Owned Int)) some (OwnLeaf (Move p))))))
  (define-values (configs rules _expected after)
    (run-program core '() '(R-Move R-OwnLeafTransit)
                 (lambda (c)
                   (match c
                     [`(Construct (Option (Owned Int)) some
                                  (OwnedTransit ,_ 37)) #t]
                     [_ #f]))))
  (define ownleaf-index (index-of rules 'R-OwnLeafTransit))
  (check-not-false ownleaf-index)
  (when ownleaf-index
    (check-equal? (tokens (list-ref configs ownleaf-index))
                  (tokens (list-ref configs (add1 ownleaf-index)))))
  (check-equal? (transit-places (control (last configs)))
                (transit-places (control after))))

(test-case "OwnLeaf の Owned NFn producer は marker をそのまま運ぶ"
  (define core
    '(Scope ()
       (Let (p let (Owned (NFn (Int) Int () () () User)))
            (Lam User identity (x) x)
         (Construct (Option (Owned (NFn (Int) Int () () () User))) some
                    (OwnLeaf (Move p))))))
  (define-values (_configs _rules _expected _after)
    (run-program core int-callables '(R-Move R-OwnLeafTransit)
                 (lambda (c)
                   (match c
                     [`(Construct (Option (Owned ,_)) some
                                  (OwnedTransit ,_ ,_)) #t]
                     [_ #f]))))
  (void))

(test-case "Forward の Owned place も marker で運ぶ"
  (define sink-type '(NFn ((Owned Int)) Unit () (Own) () User))
  (define owner-type `(NFn (,sink-type (Owned Int)) Unit () (Own) () User))
  (define sink
    '(Lam User sink (raw)
       (Handle (Return sink-boundary Unit) (answer -> answer)
         (Scope () (Let (received let (Owned Int)) raw
                     (Drop (Move received)))))))
  (define owner
    '(Lam User owner (h p)
       (Handle (Return owner-boundary Unit) (answer -> answer)
         (Scope ()
           (Let (x let (Owned Int)) p (Apply h (Forward x)))))))
  (define callables `((owner ,owner-type) (sink ,sink-type)))
  (define-values (configs rules _expected _after)
    (let* ([core `(Handle (Return forward-boundary Unit)
                          (answer -> answer)
                    (Scope (0) (Apply ,owner ,sink (Move 0))))]
           [typed (core-type-of core '((0 Int)) callables)])
      (check-true (and (list? typed) (= (length typed) 2))
                  (format "Forward fixture の型付けに失敗した: ~s" typed))
      (if (and (list? typed) (= (length typed) 2))
          (let ([start `(cfg ,core ((0 41 (declared (Owned Int))))
                              ((0 Available)) () ())])
            (define-values (trace trace-rules) (trace-g2 start))
            (check-config-trace trace callables (first typed))
            (define forward-index (index-of trace-rules 'R-Forward))
            (check-not-false forward-index)
            (when (and forward-index
                       (<= (+ forward-index 3) (length trace-rules)))
              (check-equal? (take (drop trace-rules forward-index) 3)
                            '(R-Forward R-Beta R-LetOwnedB)))
            (check-true ((lambda (c) (equal? c 'unit))
                         (control (last trace))))
            (check-terminal-cleanup (last trace))
            (values trace trace-rules (first typed) #f))
          (values '() '() #f #f))))
  (check-not-false (member 'R-Move rules)))

(test-case "ScopeAbort は marker 内部の OwnedLeaf を一度回収する"
  (define field-type '(Option (Owned Res)))
  (define record-type `(Record ((owned ,field-type imm))))
  (define record-value
    `(Rec ((owned imm (Construct ,field-type some
                                 (OwnLeaf (resource 29)))))))
  (define consumer-type
    `(NFn ((Owned ,record-type) Unit) Unit () () () User))
  (define consumer
    `(Lam User consumer (raw later)
       (Handle (Return consumer-boundary Unit) (return-value -> return-value)
         (Scope () (Let (received let (Owned ,record-type)) raw unit)))))
  (define callables `((consumer ,consumer-type)))
  (define core
    `(Handle (Return abort-boundary Unit) (answer -> answer)
       (Scope ()
         (Let (p let (Owned ,record-type)) ,record-value
           (Scope ()
             (Apply ,consumer (Move p)
                    (Perform (Return abort-boundary Unit) unit)))))))
  (define-values (configs rules _expected _after)
    (run-program core callables '(R-Move)
                 (lambda (c) (equal? c 'unit))))
  (check-not-false (member 'R-ScopeAbort rules))
  (define abort-index (index-of rules 'R-ScopeAbort))
  (check-not-false abort-index)
  (when abort-index
    (check-equal? (tokens (last configs)) '(((tok 0) Dropped)))))

(test-case "内部 OwnedLeaf を持つ Rec の移送後に token を回収する"
  (define field-type '(Option (Owned Res)))
  (define record-type `(Record ((owned ,field-type imm))))
  (define record-value
    `(Rec ((owned imm (Construct ,field-type some
                                 (OwnLeaf (resource 43)))))))
  (define core
    `(Scope ()
       (Let (p let (Owned ,record-type)) ,record-value
         (Drop (Move p)))))
  (define-values (configs _rules _expected _after)
    (run-program core '() '(R-Move R-Drop)
                 (lambda (c) (equal? c 'unit))))
  (check-equal? (map second (tokens (last configs))) '(Dropped)))

(test-case "Owned CurryVal が内部 OwnedLeaf を持つときも移送後に回収する"
  (define function-type
    '(NFn ((Owned Res) Int) Int () (Own) () User))
  (define curried
    '(Curry (Lam User consume-owned (owned number)
                (Handle (Return consume-owned Int) (answer -> answer)
                  (Scope ()
                    (Let (received let (Owned Res)) owned
                      (Let (discarded const Unit) (Drop (Move received))
                        number)))))
           (OwnLeaf (resource 47))))
  (define callable `((consume-owned ,function-type)))
  (define owned-function-type
    '(NFn (Int) Int () (Own) () (Derived User (Curry (OwnLeaf (resource 47))))))
  (define core
    `(Scope ()
       (Let (p let (Owned ,owned-function-type)) ,curried
         (Drop (Move p)))))
  (define-values (configs _rules _expected _after)
    (run-program core callable '(R-Move R-Drop)
                 (lambda (c) (equal? c 'unit))))
  (check-equal? (map second (tokens (last configs))) '(Dropped)))

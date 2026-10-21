#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../gen.rkt"
         "../elaborate.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../unsafe-gen.rkt"
         "../ptr-static.rkt"
         "../typing.rkt")

(define token '(tok 1))
(define leaf `(OwnedLeaf ,token (resource 1)))

;; G1/G2m の評価文脈の穴と、穴の外に残る子を同じ表で分類する。
;; pending-code の最後の要素は現行 scanner の穴の根に対する判定である。
(define position-table
  '((Apply function type-unreachable "Owned 関数の根は Move/CurryVal に限る")
    (Apply argument active-value "評価中の引数")
    (Apply later-argument pending-code "先行する引数の後" accept)
    (Let bound active-value "束縛値")
    (Let body pending-code "束縛値の後" reject)
    (Construct field active-value "評価中の構築子欄")
    (Construct later-field pending-code "完成した値の欄を leaf scanner が走査" accept)
    (Eliminate scrutinee type-unreachable "Option/Data の scrutinee")
    (Eliminate branch deferred-code "選択前の枝")
    (Perform payload active-value "escape する payload")
    (Handle body active-value "handler の処理対象")
    (Handle handler deferred-code "catch 前の節")
    (Scope body active-value "scope の制御項")
    (Recur body deferred-code "RecurVal に捕捉される本体")
    (Recur continuation pending-code "RecurBind 後の継続" reject)
    (Yield payload active-value "観測 payload")
    (Yield continuation pending-code "payload 評価後の継続" reject)
    (Suspend body pending-code "Suspend が直ちに制御へ移す本体" reject)
    (Drop argument active-value "Drop の引数")
    (Curry function type-unreachable "関数位置の Owned root 制約")
    (Curry argument active-value "固定引数")
    (Curry later-argument pending-code "関数評価中の固定引数" accept)
    (OwnLeaf payload active-value "producer の payload")
    (Rec field active-value "評価中の record 欄")
    (Rec later-field pending-code "完成した値の欄を leaf scanner が走査" accept)
    (Discharge inner type-unreachable "Proof が要求する Record 型")
    (UnionInject payload type-unreachable "Owned union member は拒否")
    (UnionEliminate scrutinee type-unreachable "Union の scrutinee")
    (UnionEliminate branch deferred-code "選択前の枝")
    (RecRewrite input type-unreachable "Record の入力")
    (RecRewrite entry deferred-code "Open 前の entry 本体")
    (RecRewriteOpen field active-value "現在の作業欄")
    (RecRewriteOpen later-field pending-code "先行する作業欄の後" accept)
    (Proj operand type-unreachable "Record 射影の入力")
    (ProjOpt operand type-unreachable "optional Record 射影の入力")
    (ReborrowAt operand type-unreachable
                "BorrowMut capability の入力")
    (ProjBorrowAt operand type-unreachable
                  "借用 Record の入力")
    (Read operand type-unreachable "Borrowed payload")
    (Assign target type-unreachable "BorrowedMut target")
    (Assign value pending-code "target 評価後の値" reject)
    (Reassign value pending-code "MutSlot target 評価後の値" reject)
    (RegionApp function type-unreachable "ForallRegion function")
    (AddressOf operand type-unreachable "place operand")
    (PtrOffset pointer type-unreachable "RawPtr operand")
    (PtrOffset offset pending-code "pointer 評価後の offset" reject)
    (RawLoad pointer type-unreachable "RawPtr operand")
    (RawStore pointer type-unreachable "RawPtr operand")
    (RawStore value pending-code "pointer 評価後の payload" reject)
    (FromRawPtr pointer type-unreachable "RawPtr operand")
    (Unsafe body active-value "Unsafe boundary の本体")))

(define (assoc-row form hole)
  (for/first ([row (in-list position-table)]
              #:when (and (eq? (first row) form)
                          (eq? (second row) hole)))
    row))

(struct row-case
  (leaf-cfg control-cfg nested-cfg places callables environment expected effect)
  #:transparent)

(define (config-core cfg)
  (match cfg [`(cfg ,core ,_ ...) core]))

(define (make-config core with-token?)
  `(cfg ,core () () ,(if with-token? `((,token Available)) '()) ()))

(define (make-row-case leaf-core control-core nested-core expected effect
                       [callables '()] [places '()] [environment '()])
  (row-case (make-config leaf-core #t)
            (make-config control-core #f)
            (and nested-core (make-config nested-core #t))
            places callables environment expected effect))

(define add '(PrimVal (Reserved o-add) add))
(define multiply '(PrimVal (Reserved o-mul) mul))
(define acquire '(PrimVal (Reserved o-acquire) acquire))
(define (with-leaf result)
  `(Let (unused const (Owned Res)) ,leaf ,result))

(define active-value-fixtures
  (list
   (list 'Apply 'argument `(Apply ,add ,leaf 1))
   (list 'Let 'bound `(Let (x const (Owned Res)) ,leaf unit))
   (list 'Construct 'field
         `(Construct (Option (Owned Res)) some ,leaf))
   (list 'Perform 'payload `(Perform (Return boundary (Owned Res)) ,leaf))
   (list 'Handle 'body
         `(Handle (Return boundary (Owned Res)) (answer -> answer) ,leaf))
   (list 'Scope 'body `(Scope () ,leaf))
   (list 'Yield 'payload `(Yield ,leaf unit))
   (list 'Drop 'argument `(Drop ,leaf))
   (list 'Curry 'argument `(Curry ,multiply ,leaf))
   (list 'OwnLeaf 'payload `(OwnLeaf ,leaf))
   (list 'Rec 'field `(Rec ((a imm ,leaf))))
   (list 'RecRewriteOpen 'field `(RecRewriteOpen ((a imm ,leaf))))
   (list 'Unsafe 'body `(Unsafe ,leaf))))

(define (deferred-core form child)
  (case form
    [(Handle)
     `(Handle (Return boundary Unit) (argument -> ,child) unit)]
    [(Recur)
     `(Recur loop-id loop () ,child loop)]
    [(Eliminate)
     `(Eliminate (Construct (Option Int) none)
                 ((none () -> unit) (some (x) -> ,child)))]
    [(UnionEliminate)
     `(UnionEliminate (UnionVal (Union Int String) String "s")
                      ((Int x -> ,child) (String s -> unit)))]
    [(RecRewrite)
     `(RecRewrite (Rec ((a imm (Absent Unit))))
                  ((a input Unit imm Unit ,child)))]
    [else (error 'deferred-core "unknown deferred position: ~s" form)]))

(define deferred-value-shapes
  (list `(Rec ((a imm ,leaf)))
        `(Construct (Option (Owned Res)) some ,leaf)
        `(UnionVal (Union Int (Owned Res)) (Owned Res) ,leaf)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
    (when (zero? fuel)
      (error 'trace-g2 "evaluation fuel exhausted: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "expected a unique successor: ~s" steps)])))

(define (step-g2 start)
  (match (raw-steps-g2/named start)
    [(list (list rule after)) (values rule after)]
    [steps (error 'step-g2 "expected one successor: ~s" steps)]))

(define (check-config-trace configs callables expected)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false row
                     (format "config ~a の runtime row が無い: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected row)
                (format "config ~a が不正: ~s" index configuration))))

(define (test-config-core cfg)
  (match cfg [`(cfg ,core ,_ ...) core]))

(define (replace-leaf core)
  (match core
    [`(OwnedLeaf ,_ ,_) 'unit]
    [(? list? children) (map replace-leaf children)]
    [_ core]))

(define (replace-leaf-with-transit core)
  (match core
    [`(OwnedLeaf ,_ ,_) '(OwnedTransit 90 7)]
    [(? list? children) (map replace-leaf-with-transit children)]
    [_ core]))

(define (token-occurrences core tk)
  (match core
    [`(OwnedLeaf ,found ,_) (if (equal? found tk) 1 0)]
    [(? list? children) (apply + (map (lambda (child) (token-occurrences child tk))
                                      children))]
    [_ 0]))

(define (replace-leaf-with-producer core)
  (match core
    [`(OwnedLeaf ,_ ,payload) `(OwnLeaf ,payload)]
    [(? list? children) (map replace-leaf-with-producer children)]
    [_ core]))

(define (set-token-state cfg tk new-state)
  (match cfg
    [`(cfg ,core ,heap ,places ,tokens ,events)
     `(cfg ,core ,heap ,places
           ,(for/list ([entry (in-list tokens)])
              (if (equal? (first entry) tk)
                  (list tk new-state)
                  entry))
           ,events)]))

(define pending-fixtures
  (list
   (list 'Apply 'later-argument
         `(Apply ,add 1 ,leaf)
         `(Apply ,add 1 2)
         `(Apply ,add 1 ,(with-leaf 2))
         'Int '())
   (list 'Curry 'later-argument
         `(Curry ,multiply ,leaf)
         `(Curry ,multiply 2)
         `(Curry ,multiply ,(with-leaf 2))
         #f '())
   (list 'Let 'body
         `(Let (x const Int) 1 ,leaf)
         '(Let (x const Int) 1 unit)
         `(Let (x const Int) 1 ,(with-leaf 'unit))
         'Unit '())
   (list 'Construct 'later-field
         `(Construct (List Int) cons 1 ,leaf)
         '(Construct (List Int) cons 1 (Construct (List Int) nil))
         `(Construct (List Int) cons 1
                     ,(with-leaf '(Construct (List Int) nil)))
         '(List Int) '())
   (list 'Rec 'later-field
         `(Rec ((a imm 1) (b imm ,leaf)))
         '(Rec ((a imm 1) (b imm unit)))
         `(Rec ((a imm 1) (b imm ,(with-leaf 'unit))))
         '(Record ((a Int imm) (b Unit imm))) '())
   (list 'Yield 'continuation
         `(Yield 1 ,leaf)
         '(Yield 1 unit)
         `(Yield 1 ,(with-leaf 'unit))
         'Unit '((Yield Int)))
   (list 'Suspend 'body
         `(Suspend ,leaf)
         '(Suspend 1)
         `(Suspend ,(with-leaf 1))
         'Int '(Suspend))
   (list 'RecRewriteOpen 'later-field
         `(RecRewriteOpen ((a imm 1) (b imm ,leaf)))
         '(RecRewriteOpen ((a imm 1) (b imm unit)))
         `(RecRewriteOpen ((a imm 1) (b imm ,(with-leaf 'unit))))
         '(Record ((a Int imm) (b Unit imm))) '())
   (list 'Recur 'continuation
         `(Recur loop-id loop () unit ,leaf)
         '(Recur loop-id loop () unit unit)
         `(Recur loop-id loop () unit ,(with-leaf 'unit))
         'Unit '() '((loop-id (NFn () Unit () () () User))))
   (list 'Reassign 'value
         `(Scope () (Let (x mut Int) 1
                      (Let (y const Unit) (Reassign x Int ,leaf) y)))
         '(Scope () (Let (x mut Int) 1
                      (Let (y const Unit) (Reassign x Int 2) y)))
         `(Scope () (Let (x mut Int) 1
                      (Let (y const Unit) (Reassign x Int ,(with-leaf 2)) y)))
         'Unit '(Mutation))
   ;; row-fixture は、型付き trace から作る control config を使う。
   (list 'PtrOffset 'offset #f #f #f 'Int '())
   (list 'Assign 'value
         `(Assign (BorrowMutRef 0 (b) 0) ,leaf)
         '(Assign (BorrowMutRef 0 (b) 0) 9)
         `(Assign (BorrowMutRef 0 (b) 0)
                  (Let (unused const (Owned Res))
                       (OwnedLeaf (tok 2) (resource 2))
                       9))
         'Unit '(Mutation))
   (list 'RawStore 'value
         `(Unsafe (RawStore (AddressOf (BorrowMutRef 0 (b) 0)) ,leaf))
         '(Unsafe (RawStore (AddressOf (BorrowMutRef 0 (b) 0)) 9))
         `(Unsafe (RawStore (AddressOf (BorrowMutRef 0 (b) 0))
                            ,(with-leaf 9)))
         'Unit '(Mutation))))

(define borrow-pending-rows
  '(((Assign value) (Mutation))
    ((PtrOffset offset) ())
    ((RawStore value) (Mutation))))

(define (make-borrowed-row-case leaf-core control-core nested-core expected effect)
  (define heap
    '((0 (Rec ((a imm 7)
               (b mut 8)
               (owned imm (OwnedLeaf (tok 0) (resource 9)))))
        (declared (Record ((a Int imm) (b Int mut)
                           (owned (Owned Res) imm)))))))
  (define states '((0 Available)))
  (define (configuration core tokens)
    `(cfg ,core ,heap ,states ,tokens ()))
  (define (available-leaf-tokens core)
    (match core
      [`(OwnedLeaf ,tk ,_) (list tk)]
      [(? list? children) (append-map available-leaf-tokens children)]
      [_ '()]))
  (define (tokens-for core)
    (append '(((tok 0) Available))
            (for/list ([tk (in-list (remove-duplicates
                                     (available-leaf-tokens core)))])
              `(,tk Available))))
  (row-case (configuration leaf-core (tokens-for leaf-core))
            (configuration control-core '(((tok 0) Available)))
            (configuration nested-core (tokens-for nested-core))
            '() '() '() expected effect))

(define ptr-offset-source
  '(Scope ()
     (Let (z let (Owned (List Int)))
       (Construct (List Int) cons 1000 (Construct (List Int) nil))
       (Eliminate (BorrowMut z)
         ((cons (h t) -> (Unsafe (RawLoad (PtrOffset (AddressOf h) 0))))
          (nil () -> 1000))))))

(define (ready-ptr-offset? core)
  (match core
    [`(PtrOffset (AddressOf (BorrowMutRef ,_ ,_ ,_)) ,_) #t]
    [(? list? children) (ormap ready-ptr-offset? children)]
    [_ #f]))

(define (replace-ready-ptr-offset core offset)
  (match core
    [`(PtrOffset (AddressOf (BorrowMutRef ,place ,path ,region)) ,_)
     `(PtrOffset (AddressOf (BorrowMutRef ,place ,path ,region)) ,offset)]
    [(? list? children) (map (lambda (child)
                               (replace-ready-ptr-offset child offset))
                             children)]
    [_ core]))

(define (replace-config-core configuration core [tokens #f])
  (match configuration
    [`(cfg ,_ ,heap ,states ,old-tokens ,events)
     `(cfg ,core ,heap ,states ,(or tokens old-tokens) ,events)]))

(define (make-ptr-offset-row-case)
  ;; PtrOffset は可変借用の Eliminate 枝が作った BorrowMutRef を使う。
  (match (prepare-unsafe-term ptr-offset-source)
    [(list 'ok start _sidecar)
     (define execution (bounded-trace-g2 start 100))
     (define base
       (for/first ([configuration (in-list (execution-configs execution))]
                   #:when (ready-ptr-offset? (config-core configuration)))
         configuration))
     (unless base
       (error 'make-ptr-offset-row-case "PtrOffset の実行 config がない"))
     (define fresh-token '(tok 10000))
     (define (token-table configuration)
       (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))
     (define (add-token configuration)
       (replace-config-core
        configuration (config-core configuration)
        (cons `(,fresh-token Available) (token-table configuration))))
     (define leaf-config
       (replace-config-core (add-token base)
                            (replace-ready-ptr-offset (config-core base)
                                                      `(OwnedLeaf ,fresh-token
                                                                  (resource 10000)))))
     (define nested-config
       (replace-config-core (add-token base)
                            (replace-ready-ptr-offset
                             (config-core base)
                             `(Let (unused const (Owned Res))
                                   (OwnedLeaf ,fresh-token (resource 10000))
                                   0))))
     (row-case leaf-config base nested-config '() '() '() 'Int '())]
    [other (error 'make-ptr-offset-row-case
                  "PtrOffset fixture を準備できない: ~s" other)]))

(define option-proof
  '(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped
              (Record ((kept Int imm) (owned (Option (Owned Res)) imm)))
              (Record ((kept Int imm))))))

(define type-unreachable-fixtures
  (list
   (list 'Apply 'function
         `(Apply ,leaf 1 2)
         '(Apply (PrimVal (Reserved o-add) add) 1 2) '() '() '())
   (list 'Curry 'function
         `(Curry ,leaf 1)
         '(Curry (PrimVal (Reserved o-mul) mul) 1) '() '() '())
   (list 'Discharge 'inner
         `(Discharge ,option-proof ,leaf)
         `(Discharge ,option-proof
                     (Rec ((kept imm 1)
                           (owned imm (Construct (Option (Owned Res)) none)))))
         '() '() '())
   (list 'UnionInject 'payload
         `(UnionInject (Union (Owned Res) Int) (Owned Res) ,leaf)
         '(UnionInject (Union Int Bool) Int 1) '() '() '())
   (list 'Eliminate 'scrutinee
         `(Eliminate ,leaf ((none () -> 0) (some (x) -> x)))
         '(Eliminate (Construct (Option Int) some 1)
                     ((none () -> 0) (some (x) -> x))) '() '() '())
   (list 'UnionEliminate 'scrutinee
         `(UnionEliminate ,leaf ((Bool b -> 0) (Int i -> i)))
         '(UnionEliminate (UnionInject (Union Int Bool) Int 1)
                          ((Bool b -> 0) (Int i -> i))) '() '() '())
   (list 'RecRewrite 'input
         `(RecRewrite ,leaf ((a x Int imm Int x)))
         '(RecRewrite (Rec ((a imm 1))) ((a x Int imm Int x))) '() '() '())
   (list 'Proj 'operand `(Proj ,leaf a)
         '(Proj (Rec ((a imm 1))) a) '() '() '())
   (list 'ProjOpt 'operand `(ProjOpt Int ,leaf a)
         '(ProjOpt Int (Rec ((a imm 1))) a)
         '() '() '())
   (list 'ReborrowAt 'operand
         `(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Scope () (Reborrow ,leaf))))
         '(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Scope () (Reborrow (Scope () (BorrowMut x)))))) '() '() '())
   (list 'ProjBorrowAt 'operand
         `(Scope (1) (ProjBorrow (Scope () ,leaf) a))
         '(Scope (1) (ProjBorrow (BorrowMut 1) a))
         '((1 (Record ((a Int imm) (b Bool mut))))) '() '())
   (list 'Read 'operand
         `(Scope (1) (Read ,leaf))
         '(Scope (1) (Read (Borrow 1))) '((1 Int)) '() '())
   (list 'Assign 'target
         `(Scope (1) (Assign ,leaf 1))
         '(Scope (1) (Assign (BorrowMut 1) 1)) '((1 Int)) '() '())
   (list 'RegionApp 'function
         `(RegionLam (a) (RegionApp ,leaf ((RParam a))))
         '(RegionLam (a) (RegionApp f ((RParam a)))) '() '()
         '((f (ForallRegion (a) (NFn () Int () () () User)) let)))
   (list 'AddressOf 'operand
         `(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (RawLoad (AddressOf ,leaf)))))
         '(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (RawLoad (AddressOf (BorrowMut x)))))) '() '() '())
   (list 'PtrOffset 'pointer
         `(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (RawLoad (PtrOffset ,leaf 1)))))
         '(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (RawLoad (PtrOffset (AddressOf (BorrowMut x)) 1)))))
         '() '() '())
   (list 'RawLoad 'pointer
         `(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (RawLoad ,leaf))))
         '(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (RawLoad (AddressOf (BorrowMut x)))))) '() '() '())
   (list 'RawStore 'pointer
         `(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Let (y let (Owned Res)) (resource 2)
                       (Unsafe (RawStore ,leaf (Read (Borrow y)))))))
         '(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Let (y let (Owned Res)) (resource 2)
                       (Unsafe (RawStore (AddressOf (BorrowMut x))
                                         (Read (Borrow y))))))) '() '() '())
   (list 'FromRawPtr 'pointer
         `(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (Read (FromRawPtr ,leaf 0)))))
         '(Scope () (Let (x let (Owned Res)) (resource 1)
                     (Unsafe (Read (FromRawPtr (AddressOf (BorrowMut x)) 0)))))
         '() '() '())))

(define (row-fixture form hole)
  (define entry
    (assoc (list form hole)
                (append
                 (for/list ([fixture (in-list pending-fixtures)])
                   (cons (list (first fixture) (second fixture)) fixture))
                 (for/list ([fixture (in-list type-unreachable-fixtures)])
                   (cons (list (first fixture) (second fixture)) fixture)))))
  (cond
    [(eq? (third (assoc-row form hole)) 'type-unreachable)
     (match (cdr entry)
       [(list _ _ leaf-core control-core places callables environment)
        (if (equal? (list form hole) '(FromRawPtr pointer))
            (match (prepare-unsafe-term control-core)
              [(list 'ok _ (? ptr-sidecar?))
               (make-row-case leaf-core control-core #f #f '()
                              callables places environment)]
              [_ #f])
            (let ([typed
                   (fixture-core-type control-core places callables environment)])
              (and (not (eq? typed 'ill-typed))
                   (make-row-case leaf-core control-core #f
                                  (first typed) (second typed)
                                  callables places environment))))]
       [_ #f])]
    [(equal? (list form hole) '(PtrOffset offset))
     (make-ptr-offset-row-case)]
    [(memq form '(Assign RawStore))
     (match (cdr entry)
       [(list _ _ leaf-core control-core nested-core expected effect _ ...)
        (make-borrowed-row-case leaf-core control-core nested-core expected effect)])]
    [else
     (match entry
    [(cons _ (list _ _ leaf-core control-core nested-core expected effect callables))
     (define type
       (if expected expected
           (first (core-type-of control-core '() callables))))
     (make-row-case leaf-core control-core nested-core type effect callables)]
    [(cons _ (list _ _ leaf-core control-core nested-core expected effect))
     (define type
       (if expected
           expected
           (first (core-type-of control-core '() '()))))
     (make-row-case leaf-core control-core nested-core type effect)]
    [_ #f])]))

(define (fixture-core-type core places callables environment)
  (define ir (build-region-ir core))
  (define annotated
    (with-handlers ([exn:fail?
                     (lambda (error)
                       (if (regexp-match? #rx"所有者を辿れない operand"
                                          (exn-message error))
                           (list 'region-rejected (exn-message error))
                           (raise error)))])
      (annotate-regions core ir)))
  (match annotated
    [`(region-rejected ,_) annotated]
    [_
     (define owners
       (for/hash ([entry (in-list places)])
         (values (first entry) (region-at ir '()))))
     (core-type-of annotated places callables environment
                   (region-ctx ir '() owners (hash)))]))

(define (case-core-type rc cfg)
  (fixture-core-type (config-core cfg)
                     (row-case-places rc)
                     (row-case-callables rc)
                     (row-case-environment rc)))

(define (case-config-ok? rc cfg)
  (define row
    (runtime-row cfg (row-case-callables rc) (row-case-expected rc)))
  (and row
       (equal? row (row-case-effect rc))
       (config-ok? cfg (row-case-callables rc)
                   (row-case-expected rc) row)))

(define (contains-borrow-value? value)
  (match value
    [(list (or 'BorrowRef 'BorrowMutRef) _ ...) #t]
    [(? list? children) (ormap contains-borrow-value? children)]
    [_ #f]))

(define (contains-form? term head)
  (match term
    [(? list? terms)
     (or (and (pair? terms) (eq? (first terms) head))
         (ormap (lambda (child) (contains-form? child head)) terms))]
    [_ #f]))

(test-case "c3m3: 位置表は四分類と pending の根判定を明示する"
  (check-true (andmap (lambda (row)
                        (and (memq (third row)
                                 '(active-value pending-code deferred-code
                                                 type-unreachable))
                             #t))
                      position-table))
    (check-true (andmap (lambda (row)
                        (if (eq? (third row) 'pending-code)
                            (and (= (length row) 5)
                                 (memq (fifth row) '(accept reject)))
                            (= (length row) 4)))
                      position-table)))

(test-case "c3m3: 型上到達不能な代表位置は OwnedLeaf だけを置くと拒否する"
  (for ([row (in-list position-table)]
        #:when (eq? (third row) 'type-unreachable))
    (define rc (row-fixture (first row) (second row)))
    (check-not-false rc (format "fixture ~s/~s" (first row) (second row)))
    (define label (format "~s/~s: ~a" (first row) (second row) (fourth row)))
    (if (equal? (list (first row) (second row)) '(FromRawPtr pointer))
        (let ([leaf-result (prepare-unsafe-term
                            (config-core (row-case-leaf-cfg rc)))]
              [control-result (prepare-unsafe-term
                               (config-core (row-case-control-cfg rc)))])
          (check-true (and (list? control-result)
                           (= (length control-result) 3)
                           (eq? (first control-result) 'ok)
                           (ptr-sidecar? (third control-result)))
                      label)
          (check-equal? leaf-result 'discard label))
        (let ([leaf-result (case-core-type rc (row-case-leaf-cfg rc))]
              [control-result (case-core-type rc (row-case-control-cfg rc))])
          (if (memq (first row) '(ReborrowAt ProjBorrowAt))
              (begin
                (check-eq? leaf-result 'ill-typed label)
                (let ([owned-place-core
                       (if (eq? (first row) 'ReborrowAt)
                           '(Scope ()
                              (Let (x let (Owned Res)) (resource 1)
                                (Scope () (Reborrow x))))
                           '(Let (x let (Owned (Record ((a Int imm)
                                                       (b Bool mut)))))
                              (Rec ((a imm 1)
                                    (b mut (Construct Bool true))))
                              (Scope () (ProjBorrow x a))))])
                  (check-eq? (fixture-core-type owned-place-core
                                               (row-case-places rc)
                                               (row-case-callables rc)
                                               (row-case-environment rc))
                             'ill-typed
                             (format "~a: Owned place を operand 根にした型検査"
                                     label))
                  (when (eq? (first row) 'ProjBorrowAt)
                    (check-not-eq?
                     (fixture-core-type
                      '(Let (x let (Owned (Record ((a Int imm)
                                                  (b Bool mut)))))
                         (Rec ((a imm 1)
                               (b mut (Construct Bool true))))
                         (Scope () (ProjBorrow (BorrowMut x) a)))
                      (row-case-places rc)
                      (row-case-callables rc)
                      (row-case-environment rc))
                     'ill-typed
                     (format "~a: Owned record の BorrowMut 対照" label)))))
              (check-eq? leaf-result 'ill-typed label))
          (check-not-eq? control-result 'ill-typed
                         (format "対照 ~a places=~s env=~s" label
                                 (row-case-places rc)
                                 (row-case-environment rc)))))))

(test-case "c3m3: pending-code は内側の active leaf と根判定を保つ"
  (for ([fixture (in-list pending-fixtures)])
    (define form (first fixture))
    (define hole (second fixture))
    (define row (assoc-row form hole))
    (define rc (row-fixture form hole))
    (define label
      (format "~s/~s: ~a" form hole (fourth row)))
    (check-true (case-config-ok? rc (row-case-control-cfg rc))
                (format "~a control: row=~s cfg=~s" label
                        (runtime-row (row-case-control-cfg rc)
                                     (row-case-callables rc)
                                     (row-case-expected rc))
                        (row-case-control-cfg rc)))
    (check-true (case-config-ok? rc (row-case-nested-cfg rc))
                (format "~a nested: row=~s cfg=~s" label
                        (and (row-case-nested-cfg rc)
                             (runtime-row (row-case-nested-cfg rc)
                                          (row-case-callables rc)
                                          (row-case-expected rc)))
                        (row-case-nested-cfg rc)))
    (check-equal? (control-leaf-positions-ok? (config-core
                                               (row-case-leaf-cfg rc)))
                  (eq? (fifth row) 'accept)
                  label)))

(test-case "c3m3: pending root-leaf の accept/reject 表を全行固定する"
  (for ([row (in-list position-table)]
        #:when (eq? (third row) 'pending-code))
    (define rc (row-fixture (first row) (second row)))
    (check-not-false rc (format "fixture ~s/~s" (first row) (second row)))
    (define label (format "~s/~s" (first row) (second row)))
    (check-equal? (control-leaf-positions-ok? (config-core (row-case-leaf-cfg rc)))
                  (eq? (fifth row) 'accept)
                  label)))

(test-case "c3n3: pending の借用値を含む構成は runtime-row が row を返す"
  (for ([row (in-list position-table)]
        #:when (eq? (third row) 'pending-code))
    (define key (list (first row) (second row)))
    (define rc (row-fixture (first row) (second row)))
    (check-not-false rc (format "fixture ~s/~s" (first row) (second row)))
    (define configs
      (filter values (list (row-case-control-cfg rc)
                           (row-case-nested-cfg rc))))
    (define contains-borrow?
      (ormap (lambda (cfg) (contains-borrow-value? (config-core cfg))) configs))
    (define expected-entry
      (assoc key borrow-pending-rows))
    (check-equal? contains-borrow? (and expected-entry #t)
                  (format "~s/~s borrow=~s"
                          (first row) (second row) contains-borrow?))
    (when expected-entry
      (for ([cfg (in-list configs)])
        (define actual
          (runtime-row cfg (row-case-callables rc) (row-case-expected rc)))
        (check-equal? actual (second expected-entry)
                      (format "~s/~s runtime-row" (first row) (second row)))
        (check-true (and actual
                         (config-ok? cfg (row-case-callables rc)
                                     (row-case-expected rc) actual))
                    (format "~s/~s config-ok?" (first row) (second row)))))))

(test-case "c3n3: 借用値を含む pending 構成の trace は row と構成を保つ"
  (for ([entry (in-list borrow-pending-rows)])
    (define key (first entry))
    (define rc (row-fixture (first key) (second key)))
    (check-not-false rc (format "fixture ~s" key))
    (define start (row-case-control-cfg rc))
    (define start-row
      (runtime-row start (row-case-callables rc) (row-case-expected rc)))
    (check-equal? start-row (second entry) (format "~s 起点 row" key))
    (define-values (configs _rules) (trace-g2 start))
    (check-equal? (raw-steps-g2/named (last configs)) '()
                  (format "~s trace は終端まで進む" key))
    (for ([cfg (in-list configs)] [index (in-naturals)])
      (define row
        (runtime-row cfg (row-case-callables rc) (row-case-expected rc)))
      (check-not-false row (format "~s config ~a の row" key index))
      (check-true (row-subset? row start-row)
                  (format "~s config ~a の row が増えない" key index))
      (check-true (config-ok? cfg (row-case-callables rc)
                              (row-case-expected rc) row)
                  (format "~s config ~a が不正: ~s" key index cfg)))))

(test-case "c3n3: source の Borrow と BorrowMut trace は materialize 後に row と構成を保つ"
  (for ([mutable? (in-list '(#f #t))])
    (define borrowed-type
      (if mutable? '(BorrowedMut Int 0) '(Borrowed Int 0)))
    (define borrow-form
      (if mutable? '(BorrowMut x) '(Borrow x)))
    (define source
      `(Scope ()
         (Let (x let (Owned Int)) 7
           (Scope ()
             (Let (b let ,borrowed-type) ,borrow-form (Read b))))))
    (define ir (build-region-ir source))
    (define rho (region->rho ir (region-at ir '(0 1 0 0))))
    (define (materialize-region term)
      (cond [(equal? term borrowed-type)
             (list (first borrowed-type) (second borrowed-type) rho)]
            [(pair? term)
             (cons (materialize-region (car term))
                   (materialize-region (cdr term)))]
            [else term]))
    (define typed-core (materialize-region source))
    (define mut-types (box (hash)))
    (check-equal?
     (first (type-of/raw typed-core '() '() '()
                          (region-ctx ir '() (hash) (hash))
                          #:mut-types mut-types))
     'ok
     (format "mutable?=~s region-aware source typing" mutable?))
    (define annotated (annotate-regions typed-core ir))
    (define start
      (inject-g2m (annotate-mut-binding-types annotated (unbox mut-types))))
    (define-values (configs rules) (trace-g2 start))
    (check-equal? (length configs) 8 (format "mutable?=~s config count" mutable?))
    (check-equal? rules
                  (if mutable?
                      '(R-LetOwnedB R-BorrowMut R-LetB R-ReadMut
                        R-ScopeValue R-ScopeValue R-ScopeValue)
                      '(R-LetOwnedB R-Borrow R-LetB R-Read
                        R-ScopeValue R-ScopeValue R-ScopeValue))
                  (format "mutable?=~s rules" mutable?))
    (check-true (ormap (lambda (cfg)
                         (contains-borrow-value? (config-core cfg)))
                       configs)
                (format "mutable?=~s BorrowRef in control" mutable?))
    (check-false (ormap (lambda (cfg)
                          (contains-borrow-value? (config-heap cfg)))
                        configs)
                 (format "mutable?=~s BorrowRef stays in control" mutable?))
    (for ([cfg (in-list configs)] [index (in-naturals)])
      (define row (runtime-row cfg '() 'Int))
      (check-not-false row (format "mutable?=~s config ~a row" mutable? index))
      (check-true (config-ok? cfg '() 'Int row)
                  (format "mutable?=~s config ~a config-ok?" mutable? index)))))

(test-case "c3n3: heap の BorrowRef trace は row と構成を保ち、Moved owner を拒否する"
  (define start
    '(cfg (Read (BorrowRef 2 () 0))
          ((2 7 (declared Int))
           (3 (BorrowRef 2 () 0) (declared (Borrowed Int 0))))
          ((2 Available) (3 Available)) () ()))
  (check-true (contains-borrow-value? (config-heap start)))
  (define start-row (runtime-row start '() 'Int))
  (check-equal? start-row '())
  (check-true (config-ok? start '() 'Int start-row))
  (define-values (configs rules) (trace-g2 start))
  (check-equal? rules '(R-Read))
  (check-config-trace configs '() 'Int)
  (define moved
    '(cfg (Read (BorrowRef 2 () 0))
          ((2 7 (declared Int))
           (3 (BorrowRef 2 () 0) (declared (Borrowed Int 0))))
          ((2 Moved) (3 Available)) () ()))
  (check-false (runtime-row moved '() 'Int))
  (check-false (config-ok? moved '() 'Int start-row)))

(test-case "c3m3: active-value の各位置は根 leaf を許す"
  (check-equal? (map (lambda (fixture) (take fixture 2)) active-value-fixtures)
                (for/list ([row (in-list position-table)]
                           #:when (eq? (third row) 'active-value))
                  (take row 2)))
  (for ([fixture (in-list active-value-fixtures)])
    (check-true (control-leaf-positions-ok? (third fixture))
                (format "~s/~s" (first fixture) (second fixture)))))

(test-case "c3n1: active と pending の位置表で marker の根判定を固定する"
  (for ([fixture (in-list active-value-fixtures)])
    (check-true
     (control-leaf-positions-ok? (replace-leaf-with-transit (third fixture)))
     (format "active ~s/~s" (first fixture) (second fixture))))
  (for ([fixture (in-list pending-fixtures)])
    (define row (assoc-row (first fixture) (second fixture)))
    (define rc (row-fixture (first fixture) (second fixture)))
    (define core
      (or (third fixture)
          (config-core (row-case-leaf-cfg rc))))
    (check-equal?
     (control-leaf-positions-ok?
      (replace-leaf-with-transit core))
     (eq? (fifth row) 'accept)
     (format "pending ~s/~s" (first fixture) (second fixture))))
  (for ([form (in-list '(Handle Recur Eliminate UnionEliminate RecRewrite))])
    (define child
      `(Drop (Rec ((a imm (OwnedTransit 90 7))))))
    (check-false (control-leaf-positions-ok? (deferred-core form child))
                 (format "deferred ~s の子全体" form))))

(test-case "c3m3: deferred-code は根 leaf を含む子を拒否する"
  (for ([form (in-list '(Handle Recur Eliminate UnionEliminate RecRewrite))])
    (define row
      (assoc-row form (case form
                        [(Handle) 'handler]
                        [(Recur) 'body]
                        [(Eliminate UnionEliminate) 'branch]
                        [(RecRewrite) 'entry])))
    (check-not-false row (format "position-table row for ~s" form))
    (check-false
     (control-leaf-positions-ok? (deferred-core form leaf))
     (format "~s root leaf: ~a" form (fourth row)))))

(test-case "c3m3: deferred-code の子全体を走査して値内部の leaf も拒否する"
  (for* ([form (in-list '(Handle Recur Eliminate RecRewrite))]
         [nested (in-list deferred-value-shapes)])
    (check-false (control-leaf-positions-ok?
                  (deferred-core form `(Drop ,nested)))
                 (format "~s nested value ~s" form nested)))
  (check-false
   (control-leaf-positions-ok?
    `(Handle (Return boundary Unit) (argument -> unit)
             (Eliminate (Construct (Option Int) none)
                        ((none () -> unit)
                         (some (x) -> (Drop ,leaf))))))
   "Handle 本体の内側の Eliminate 枝")
  (check-false
   (control-leaf-positions-ok?
   `(Let (x const Unit) unit
          (Handle (Return boundary Unit) (argument -> (Drop ,leaf)) unit)))
   "Let 本体の内側の handler 節"))

(test-case "c3m3: active-value の実 trace は全構成で通る"
  (define surface
    '(Let r (Apply acquire 13)
       (Let f (Fn ((p (Owned Res))) (Owned Res) (Own) (Move p))
         (Apply f (Move r)))))
  (match (elab surface)
    [(list core expected _row callables)
     (define executable (execution-core core callables))
     (define-values (configs rules)
       (trace-g2 (inject-g2m executable)))
     (check-not-false (member 'R-HandleValue rules))
     (check-config-trace configs callables expected)]
    [other (fail-check (format "Surface Handle を elaborate できない: ~s" other))])

  (define direct-handle
    '(Scope (0)
       (Handle (Return boundary (Owned Res)) (answer -> answer) (Move 0))))
  (define direct-handle-type (core-type-of direct-handle '((0 Res)) '()))
  (check-not-eq? direct-handle-type 'ill-typed)
  (define-values (handle-configs handle-rules)
    (trace-g2
     `(cfg ,direct-handle
           ((0 (resource 14) (declared (Owned Res))))
           ((0 Available)) () ())))
  (check-not-false (member 'R-Move handle-rules))
  (check-config-trace handle-configs '() (first direct-handle-type))

  (define unsafe-core '(Scope (0) (Unsafe (Move 0))))
  (define unsafe-type (core-type-of unsafe-core '((0 Res)) '()))
  (check-not-eq? unsafe-type 'ill-typed)
  (define-values (unsafe-configs unsafe-rules)
    (trace-g2
     `(cfg ,unsafe-core
           ((0 (resource 15) (declared (Owned Res))))
           ((0 Available)) () ())))
  (check-not-false (member 'R-UnsafeExit unsafe-rules))
  (check-config-trace unsafe-configs '() (first unsafe-type))

  (define list-owned '(List (Owned Res)))
  (define later
    `(Lam User later () (Construct ,list-owned nil)))
  (define later-type `(NFn () ,list-owned () () () User))
  (define later-callables `((later ,later-type)))
  (define construct-core
    `(Scope (0)
       (Construct ,list-owned cons (OwnLeaf (Move 0)) (Apply ,later))))
  (define-values (construct-configs construct-rules)
    (trace-g2
     `(cfg ,construct-core
           ((0 (resource 17) (declared (Owned Res))))
           ((0 Available)) () ())))
  (check-not-false (member 'R-Move construct-rules))
  (check-config-trace construct-configs later-callables list-owned)
  (check-true
   (for/or ([configuration (in-list construct-configs)])
     (match (test-config-core configuration)
       [`(Scope ,_ (Construct ,_ cons (OwnedLeaf ,_ ,_) (Apply ,_))) #t]
       [_ #f]))
   "Construct の先行欄は leaf 値、後続 Apply は pending-code"))

(test-case "c3m3: 選択された Eliminate 枝と UnionEliminate 枝の trace は保たれる"
  (define option-owned '(Option (Owned Res)))
  (define option-value
    `(Construct ,option-owned some (OwnLeaf (resource 30))))
  (define eliminate-core
    `(Scope ()
       (Eliminate ,option-value
         ((some (raw) ->
            (Scope ()
              (Let (owned let (Owned Res)) raw (Drop (Move owned)))))
          (none () -> unit)))))
  (define eliminate-start
    `(cfg ,eliminate-core () () () ()))
  (check-equal? (core-type-of eliminate-core '() '()) '(Unit (Own)))
  (define-values (eliminate-configs eliminate-rules)
    (trace-g2 eliminate-start))
  (check-not-false (member 'R-Eliminate eliminate-rules))
  (check-config-trace eliminate-configs '() 'Unit)
  (define eliminate-selected
    (list-ref eliminate-configs
              (add1 (index-of eliminate-rules 'R-Eliminate))))
  (check-true (control-leaf-positions-ok? (test-config-core eliminate-selected))
              "選択後の枝は制御位置になり scanner を通る")
  (check-true
   (for/or ([configuration (in-list eliminate-configs)])
     (= (length (collect-tokens (test-config-core configuration))) 1))
   "選択後は branch binder の Let が生成された leaf を active にする")

  (define union-type '(Union Int Bool))
  (define union-core
    `(Scope ()
       (UnionEliminate (UnionInject ,union-type Int 1)
         ((Int ignored -> ,option-value)
          (Bool flag -> (Construct ,option-owned none))))))
  (define union-start `(cfg ,union-core () () () ()))
  (check-equal?
   (core-type-of union-core '() '())
   (list option-owned '()))
  (define-values (union-configs union-rules) (trace-g2 union-start))
  (check-not-false (member 'R-UnionEliminate union-rules))
  (check-not-false (member 'R-OwnLeaf union-rules))
  (check-config-trace union-configs '() option-owned)
  (define union-selected
    (list-ref union-configs
              (add1 (index-of union-rules 'R-UnionEliminate))))
  (check-true (control-leaf-positions-ok? (test-config-core union-selected))
              "Union の選択後の枝は制御位置になり scanner を通る")
  (check-true
   (= (length (collect-tokens (test-config-core (last union-configs)))) 1)
   "選択後の枝で生成した leaf は active value に着地する"))

(test-case "c3m3: 遅延コードを捨てる五規則の token 漏れを拒否する"
  (define loop-type '(NFn () Unit () (Own) () User))
  (define loop-callables `((loop-id ,loop-type)))
  (define cases
    (list
     (list "Handle" '(tok 8)
           '(Handle (Return boundary Unit)
                    (x -> (Drop (OwnedLeaf (tok 8) (resource 8))))
                    unit)
           'Unit '() 'R-HandleValue 0)
     (list "Recur loop" '(tok 9)
           '(Recur loop-id loop ()
              (Drop (OwnedLeaf (tok 9) (resource 9))) loop)
           loop-type loop-callables 'R-RecurBind 1)
     (list "Recur unit" '(tok 10)
           '(Recur loop-id loop ()
              (Drop (OwnedLeaf (tok 10) (resource 10))) unit)
           'Unit loop-callables 'R-RecurBind 0)
     (list "Eliminate" '(tok 13)
           '(Eliminate (Construct (Option Int) none)
              ((none () -> unit)
               (some (x) -> (Drop (OwnedLeaf (tok 13) (resource 13))))))
           'Unit '() 'R-Eliminate 0)
     (list "UnionEliminate" '(tok 14)
           '(UnionEliminate (UnionVal (Union Int String) String "s")
              ((Int x -> (Drop (OwnedLeaf (tok 14) (resource 14))))
               (String s -> unit)))
           'Unit '() 'R-UnionEliminate 0)))
  (for ([case (in-list cases)])
    (match-define (list label tk core expected callables wanted-rule remaining) case)
    (define start `(cfg ,core () () ((,tk Available)) ()))
    (define start-row (runtime-row start callables expected))
    (check-not-false start-row (format "~a の初期 row" label))
    (check-false (control-leaf-positions-ok? core)
                 (format "~a の deferred-code" label))
    (check-false (config-ok? start callables expected start-row)
                 (format "~a の初期 token 化構成" label))
    (define-values (actual-rule after) (step-g2 start))
    (check-eq? actual-rule wanted-rule label)
    (check-equal? (token-occurrences (test-config-core after) tk) remaining label)
    (define after-row (runtime-row after callables expected))
    (check-not-false after-row (format "~a の遷移後 row" label))
    (when (equal? label "Recur loop")
      (check-true
       (match (test-config-core after)
         [`(RecurVal ,_ ,_ () ,_) #t]
         [_ #f])
       "R-RecurBind は token を含む body を RecurVal に捕捉する"))
    (check-false (config-ok? after callables expected after-row)
                 (format "~a の遷移後 token 漏れ" label))
    (define control
      (set-token-state
       (replace-config-core after
                            (replace-leaf-with-producer (test-config-core after)))
       tk 'Dropped))
    (define control-row (runtime-row control callables expected))
    (check-not-false control-row (format "~a の回収済み対照 row" label))
    (check-true (config-ok? control callables expected control-row)
                (format "~a の回収済み対照" label))))

(test-case "c3m3: Absent の RecRewrite entry 本体は Open 前から拒否する"
  (define option-owned '(Option (Owned Res)))
  (define rewrite
    `(RecRewrite
      (Rec ((a imm (Absent Int))))
      ((a input Int imm ,option-owned
          (Let (hidden const (Owned Res))
               (OwnedLeaf (tok 7) (resource 7))
               (Construct ,option-owned none))))))
  (define expected '(Record ((a (Option (Owned Res)) imm opt))))
  (define start `(cfg ,rewrite () () (((tok 7) Available)) ()))
  (check-not-eq? (core-type-of rewrite '() '()) 'ill-typed)
  (define start-row (runtime-row start '() expected))
  (check-not-false start-row)
  (check-false (config-ok? start '() expected start-row))
  (define-values (rule after) (step-g2 start))
  (check-eq? rule 'R-RecRewrite-Open)
  (check-equal? (token-occurrences (test-config-core after) '(tok 7)) 0)
  (define after-row (runtime-row after '() expected))
  (check-not-false after-row)
  (check-false (config-ok? after '() expected after-row))
  (define control-rewrite
    `(RecRewrite
      (Rec ((a imm (Absent Int))))
      ((a input Int imm ,option-owned (Construct ,option-owned none)))))
  (define control-start `(cfg ,control-rewrite () () () ()))
  (define-values (control-configs _control-rules) (trace-g2 control-start))
  (check-config-trace control-configs '() expected))

(test-case "c3m3: present と Absent の RecRewrite 欄は pending-code を保つ"
  (define option-owned '(Option (Owned Res)))
  (define rewrite
    `(RecRewrite
      (Rec ((a imm (Construct ,option-owned some (OwnLeaf (resource 7))))
           (b imm (Absent ,option-owned))))
      ((a input ,option-owned imm ,option-owned input)
       (b absent ,option-owned imm ,option-owned absent))))
  (define inferred (core-type-of rewrite '() '()))
  (check-not-eq? inferred 'ill-typed)
  (define expected (first inferred))
  (define-values (configs rules)
    (trace-g2 `(cfg ,rewrite () () () ())))
  (check-not-false (member 'R-RecRewrite-Open rules))
  (check-not-false (member 'R-RecRewrite-Close rules))
  (check-config-trace configs '() expected)
  (check-true
   (for/or ([configuration (in-list configs)])
     (match (test-config-core configuration)
       [`(RecRewriteOpen ,_) #t]
       [_ #f]))
   "present entry は作業欄の pending-code に残る"))

(test-case "c3m3: Return の Owned payload と Recur の Owned 引数は active 位置へ移る"
  (define return-core
    '(Scope (0)
       (Drop
        (Handle (Return boundary (Owned Res))
          (answer -> answer)
          (Perform (Return boundary (Owned Res)) (Move 0))))))
  (define return-type (core-type-of return-core '((0 Res)) '()))
  (check-not-eq? return-type 'ill-typed)
  (define-values (return-configs return-rules)
    (trace-g2
     `(cfg ,return-core
           ((0 (resource 50) (declared (Owned Res))))
           ((0 Available)) () ())))
  (check-not-false (member 'R-HandleReturn return-rules))
  (check-config-trace return-configs '() (first return-type))

  (define recur-type '(NFn ((Owned Res)) Unit () (Own) () User))
  (define recur-callables `((owned-recur ,recur-type)))
  (define recur-core
    '(Recur owned-recur loop (raw)
       (Scope ()
         (Let (owned let (Owned Res)) raw (Drop (Move owned))))
       (Apply loop (Apply (PrimVal (Reserved o-acquire) acquire) 51))))
  (check-equal? (core-type-of recur-core '() recur-callables) '(Unit (Own)))
  (define-values (recur-configs recur-rules)
    (trace-g2 `(cfg ,recur-core () () () ())))
  (check-not-false (member 'R-RecurBind recur-rules))
  (check-not-false (member 'R-RecurUnfold recur-rules))
  (check-config-trace recur-configs recur-callables 'Unit))

(test-case "c3m3: pending-code の Let、Apply、Yield は一度だけ評価され escape で回収する"
  (define let-start
    '(cfg (Let (unused const Unit) unit
               (Drop (OwnedLeaf (tok 40) (resource 40))))
          () () (((tok 40) Available)) ()))
  (check-true (control-leaf-positions-ok? (config-core let-start)))
  (define-values (let-configs let-rules) (trace-g2 let-start))
  (check-not-false (member 'R-Drop let-rules))
  (check-config-trace let-configs '() 'Unit)
  (check-equal? (token-occurrences (config-core (first let-configs)) '(tok 40)) 1)
  (check-equal? (map second (match (last let-configs)
                             [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))
                '(Dropped))

  (define consume-type '(NFn (Unit (Owned Res)) Unit () (Own) () User))
  (define consume-callables `((consume ,consume-type)))
  (define consume-lam
    '(Lam User consume (plain raw)
       (Handle (Return consumer-boundary Unit)
         (return-value -> return-value)
         (Scope ()
           (Let (owned let (Owned Res)) raw (Drop (Move owned)))))))
  (define apply-core
    `(Apply ,consume-lam unit
            (Apply (PrimVal (Reserved o-acquire) acquire) 41)))
  (check-equal? (core-type-of apply-core '() consume-callables) '(Unit (Own)))
  (define-values (apply-configs apply-rules)
    (trace-g2 `(cfg ,apply-core () () () ())))
  (check-not-false (member 'R-Delta apply-rules))
  (check-not-false (member 'R-Beta apply-rules))
  (check-equal? (count (lambda (rule) (eq? rule 'R-Delta)) apply-rules) 1)
  (check-equal? (count (lambda (rule) (eq? rule 'R-Beta)) apply-rules) 1)
  (check-config-trace apply-configs consume-callables 'Unit)
  (define applied-body
    (list-ref apply-configs (add1 (index-of apply-rules 'R-Beta))))
  (check-true
   (match (config-core applied-body)
     [`(Handle ,_ ,_ (Scope ()
                     (Let (owned let (Owned Res))
                          (OwnedLeaf ,tk (resource 41)) ,_)))
      (and (= (token-occurrences (config-core applied-body) tk) 1)
           (control-leaf-positions-ok? (config-core applied-body)))]
     [_ #f])
   "R-Beta 後に後続引数の leaf が body の active Let へ一度だけ移る")
  (check-true
   (for/or ([configuration (in-list apply-configs)])
     (match (config-core configuration)
       [`(Apply ,_ unit (OwnedLeaf ,_ ,_)) #t]
       [_ #f]))
   "後続 Apply 引数の root leaf が一度だけ beta で active body へ移る")

  (define yield-core
    '(Yield unit (Drop (Apply (PrimVal (Reserved o-acquire) acquire) 42))))
  (define yield-type (core-type-of yield-core '() '()))
  (check-not-eq? yield-type 'ill-typed)
  (define-values (yield-configs yield-rules)
    (trace-g2 `(cfg ,yield-core () () () ())))
  (check-not-false (member 'R-Yield yield-rules))
  (check-equal? (count (lambda (rule) (eq? rule 'R-Delta)) yield-rules) 1)
  (check-config-trace yield-configs '() (first yield-type))
  (define produced
    (list-ref yield-configs (add1 (index-of yield-rules 'R-Delta))))
  (check-true (control-leaf-positions-ok? (config-core produced)))
  (check-equal? (length (collect-tokens (config-core produced))) 1)
  (check-equal?
   (map second (match (last yield-configs)
                 [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))
   '(Dropped))

  (define escape-core
    `(Scope ()
       (Yield unit
         (Apply ,consume-lam
                (Perform (Return escape-boundary Unit) unit)
                (OwnedLeaf (tok 43) (resource 43))))))
  (define escape-start
    `(cfg ,escape-core () () (((tok 43) Available)) ()))
  (define-values (escape-configs escape-rules) (trace-g2 escape-start))
  (check-not-false (member 'R-Yield escape-rules))
  (check-not-false (member 'R-ScopeAbort escape-rules))
  (check-config-trace escape-configs consume-callables 'Unit)
  (check-equal? (map second (match (last escape-configs)
                             [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))
                '(Dropped)))

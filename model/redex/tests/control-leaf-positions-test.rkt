#lang racket

(require rackunit
         "../lang.rkt"
         "../gen.rkt"
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
    (ReborrowAt operand type-unreachable "借用 capability の入力")
    (ProjBorrowAt operand type-unreachable "借用 Record の入力")
    (Read operand type-unreachable "Borrowed payload")
    (Assign target type-unreachable "BorrowedMut target")
    (Assign value pending-code "target 評価後の値" reject known-row)
    (Reassign value pending-code "MutSlot target 評価後の値" reject)
    (RegionApp function type-unreachable "ForallRegion function")
    (AddressOf operand type-unreachable "place operand")
    (PtrOffset pointer type-unreachable "RawPtr operand")
    (PtrOffset offset pending-code "pointer 評価後の offset" reject known-row)
    (RawLoad pointer type-unreachable "RawPtr operand")
    (RawStore pointer type-unreachable "RawPtr operand")
    (RawStore value pending-code "pointer 評価後の payload" reject known-row)
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
(define (with-leaf result)
  `(Let (unused const (Owned Res)) ,leaf ,result))

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
                      (Let (y const Unit) (Reassign x ,leaf) y)))
         '(Scope () (Let (x mut Int) 1
                      (Let (y const Unit) (Reassign x 2) y)))
         `(Scope () (Let (x mut Int) 1
                      (Let (y const Unit) (Reassign x ,(with-leaf 2)) y)))
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

(define (make-borrowed-row-case leaf-core control-core nested-core expected effect)
  (define heap
    '((0 (Rec ((a imm 7)
               (b mut 8)
               (owned imm (OwnedLeaf (tok 0) (resource 9))))))))
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
                     (Scope () (Reborrow (BorrowMut x))))) '() '() '())
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
    [(cons _ (list _ _ leaf-core control-core nested-core expected effect
                   callables places environment))
     (define typed (fixture-core-type control-core places callables environment))
     (and (not (eq? typed 'ill-typed))
          (make-row-case leaf-core control-core nested-core expected effect
                         callables places environment))]
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
    [(cons _ (list _ _ leaf-core control-core places callables environment))
     (define typed (fixture-core-type control-core places callables environment))
     (and (not (eq? typed 'ill-typed))
          (make-row-case leaf-core control-core #f (first typed) (second typed)
                         callables places environment))]
    [_ #f])]))

(define (fixture-core-type core places callables environment)
  (with-handlers ([exn:fail? (lambda (_) 'ill-typed)])
   (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
   (core-type-of annotated places callables environment
                 (region-ctx ir '() owners (hash)))))

(define (case-core-type rc cfg)
  (fixture-core-type (config-core cfg)
                     (row-case-places rc)
                     (row-case-callables rc)
                     (row-case-environment rc)))

(define (case-config-ok? rc cfg [known-row? #f])
  (define row
    (if known-row?
        (row-case-effect rc)
        (runtime-row cfg (row-case-callables rc) (row-case-expected rc))))
  (and row
       (equal? row (row-case-effect rc))
       (config-ok? cfg (row-case-callables rc)
                   (row-case-expected rc) row)))

(define (contains-borrow-value? value)
  (match value
    [(list (or 'BorrowRef 'BorrowMutRef) _ ...) #t]
    [(? list? children) (ormap contains-borrow-value? children)]
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
                            (and (memq (fifth row) '(accept reject))
                                 (or (= (length row) 5)
                                     (and (= (length row) 6)
                                          (eq? (sixth row) 'known-row))))
                            (= (length row) 4)))
                      position-table)))

(test-case "c3m3: 型上到達不能な代表位置は OwnedLeaf だけを置くと拒否する"
  (for ([row (in-list position-table)]
        #:when (eq? (third row) 'type-unreachable))
    (define rc (row-fixture (first row) (second row)))
    (check-not-false rc (format "fixture ~s/~s" (first row) (second row)))
    (define label (format "~s/~s" (first row) (second row)))
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
        (begin
          (check-eq? (case-core-type rc (row-case-leaf-cfg rc)) 'ill-typed label)
          (check-not-eq? (case-core-type rc (row-case-control-cfg rc)) 'ill-typed
                         (format "対照 ~a places=~s env=~s" label
                                 (row-case-places rc)
                                 (row-case-environment rc)))))))

(test-case "c3m3: pending-code は内側の active leaf と現行の根判定を保つ"
  (for ([fixture (in-list pending-fixtures)])
    (define form (first fixture))
    (define hole (second fixture))
    (define row (assoc-row form hole))
    (define known-row? (and (= (length row) 6)
                            (eq? (sixth row) 'known-row)))
    (define rc (row-fixture form hole))
    (define label
      (format "~s/~s: ~a~a" form hole (fourth row)
              (if known-row?
                  " [known-row: BorrowMutRef の既知 row を config-ok? へ渡す]"
                  "")))
    (check-true (case-config-ok? rc (row-case-control-cfg rc) known-row?)
                (format "~a control: row=~s cfg=~s" label
                        (runtime-row (row-case-control-cfg rc)
                                     (row-case-callables rc)
                                     (row-case-expected rc))
                        (row-case-control-cfg rc)))
    (check-true (case-config-ok? rc (row-case-nested-cfg rc) known-row?)
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

(test-case "c3m3: pending の借用値と known-row の印が一致する"
  (for ([row (in-list position-table)]
        #:when (eq? (third row) 'pending-code))
    (define rc (row-fixture (first row) (second row)))
    (check-not-false rc (format "fixture ~s/~s" (first row) (second row)))
    (define configs
      (filter values (list (row-case-control-cfg rc)
                           (row-case-nested-cfg rc))))
    (define contains-borrow?
      (ormap (lambda (cfg) (contains-borrow-value? (config-core cfg))) configs))
    (define exception?
      (and (= (length row) 6)
           (eq? (sixth row) 'known-row)))
    (check-equal? contains-borrow? (and exception? #t)
                  (format "~s/~s exception=~s borrow=~s"
                          (first row) (second row)
                          (and exception? (sixth row)) contains-borrow?))
    (when exception?
      (for ([cfg (in-list configs)])
        (check-false (runtime-row cfg (row-case-callables rc)
                                  (row-case-expected rc))
                     (format "~s/~s known-row must bypass runtime-row"
                             (first row) (second row)))))))

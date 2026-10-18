#lang racket

(require rackunit
         "../compat.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../ownership.rkt"
         "../traits.rkt"
         "../validators.rkt"
         "../typing.rkt"
         "../borrow.rkt"
         "../region.rkt"
         "../type-equiv.rkt"
         "../diagnostic.rkt")

(define (typed core places callables [environment '()])
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define owners
    (for/hash ([entry (in-list places)])
      (values (first entry) (region-at ir '()))))
  (type-of/raw annotated places callables environment
               (region-ctx ir '() owners (hash))))

(define (typing-key result)
  (match result
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (borrowed-record-callables narrow)
  (define g-type `(NFn (,narrow) Unit () () () User))
  (values `((g ,g-type)) `((g ,g-type))))

(define borrow-place '((1 Res)))

(define (always-compatible _actual _expected) #t)

(define borrow-wide
  '(Record ((hidden (Borrowed Int ρ) imm) (name String imm))))
(define borrow-narrow '(Record ((name String imm))))
(define borrow-value
  '(Rec ((hidden imm (BorrowRef 1 () ρ)) (name imm "A"))))

(test-case "借用を含む型は borrow-free? が偽になる"
  (check-false (borrow-free? '(Borrowed Int ρ)))
  (check-false (borrow-free? '(BorrowedMut Int ρ)))
  (check-false (borrow-free? '(Record ((name String imm)
                                      (b (Borrowed Int ρ) imm)))))
  (check-true (borrow-free? '(Record ((name String imm) (id Int imm)))))
  (for ([type (in-list '((Owned (Borrowed Int ρ))
                         (Option (Borrowed Int ρ))
                         (List (Borrowed Int ρ))
                         (Result Int (Borrowed Int ρ))
                         (Untrusted (Borrowed Int ρ))
                         (Refined (Borrowed Int ρ) (Prop P))
                         (Union Int (Borrowed Int ρ))
                         (Intersection Int (Borrowed Int ρ))
                         (ForallRegion (r) (Borrowed Int (RParam r)))))])
    (check-false (borrow-free? type)))
  (check-true (borrow-free? '(NFn () (Borrowed Int ρ) () () () User)))
  (check-true (borrow-free? '(RawPtr (Borrowed Int ρ) Const NonNull
                                     (Align 4) (AddrSpace native)
                                     (Prov owned))))
  (check-false (borrow-free? '(SomeFutureType Int))))

(test-case "再帰する Data の schema を visited で一度だけ辿る"
  (define (no-fail reason kind key)
    (error 'borrow-hiding-test "~s ~s ~s" reason kind key))
  (define ledger
    (make-trait-ledger
     canonical-trait-env
     #:data '((Nat () ((zero ()) (succ ((Data Nat ())))))
              (BorrowBox () ((box ((ForallRegion (r)
                                    (Borrowed Int (RParam r)))
                                   (Data BorrowBox ()))))))
     #:fail no-fail))
  (call-with-trait-ledger
   ledger
   (lambda ()
     (check-true (borrow-free? '(Data Nat ())))
     (check-false (borrow-free? '(Data BorrowBox ()))
                  "Data schema の借用を見落とさない")
     (check-false (borrow-free? '(Data Missing ()))))))

(test-case "最上位の借用残余を RSD の義務として返す"
  (check-equal? (borrow-hiding-kind borrow-wide borrow-narrow compat?)
                `(drop-obligation ,borrow-wide ,borrow-narrow)))

(test-case "mut から imm の共通欄の入れ子も借用残余を落とす"
  (define actual
    '(Record ((inner
                     (Record ((name String imm)
                              (b (Borrowed Int ρ) imm)))
                     mut))))
  (define expected
    '(Record ((inner (Record ((name String imm))) imm))))
  (define shape (remainder-removal-shape actual expected))
  (check-equal? shape
                '((inner nested #f ((b drop #f)))))
  (check-equal? (remainder-target-type actual expected) expected)
  (check-true (rsd-proof-pair-ok? actual expected compat?)))

(test-case "Owned と借用の余剰を一つの shape で取り除く"
  (define actual
    '(Record ((name String imm)
              (owned (Owned Res) imm)
              (hidden (Borrowed Int ρ) imm))))
  (define expected '(Record ((name String imm))))
  (check-equal? (remainder-removal-shape actual expected)
                '((owned drop #f) (hidden drop #f)))
  (check-equal?
   (strip-remainder
    actual expected
    '(Rec ((name imm "A")
           (owned imm 7)
           (hidden imm (BorrowRef 1 () ρ)))))
   (list '(Rec ((name imm "A")))
         '(7 (BorrowRef 1 () ρ)))))

(test-case "RSD は借用残余を値から実際に取り除く"
  (check-equal? (remainder-removal-shape borrow-wide borrow-narrow)
                '((hidden drop #f)))
  (check-equal?
   (strip-remainder borrow-wide borrow-narrow borrow-value)
   (list '(Rec ((name imm "A"))) '((BorrowRef 1 () ρ)))))

(test-case "Union と Owned の payload 内側の隠れる借用は拒否する"
  (define wide '(Record ((name String imm) (b (Borrowed Int ρ) imm))))
  (define narrow '(Record ((name String imm))))
  (define wide2 '(Record ((name String imm) (b (Borrowed Bool ρ) imm))))
  (define narrow2 '(Record ((name String imm) (id Int imm))))
  (check-equal?
   (borrow-hiding-kind `(Union ,wide ,wide2) `(Union ,narrow ,narrow2)
                       always-compatible)
   'reject)
  (check-equal?
   (borrow-hiding-kind `(Owned ,wide) `(Owned ,narrow) always-compatible)
   'reject))

(test-case "Union 値の Owned root への持ち上げは借用検査を通る"
  (define union-type '(Union Int String))
  (check-equal?
   (borrow-hiding-kind union-type `(Owned ,union-type) compat?)
   'ok)
  (define owned-union `(Owned ,union-type))
  (define (check-lift bound callables environment)
    (typed `(Let (value let ,owned-union) ,bound (Move value))
           '() callables environment))
  (check-equal?
   (typing-key (check-lift 'source '() `((source ,union-type))))
   'ok
   "変数から Owned Union へ持ち上げる")
  (define g-type `(NFn () ,union-type () () () User))
  (check-equal?
   (typing-key (check-lift '(Apply g) `((g ,g-type)) `((g ,g-type))))
   'ok
   "呼び出し結果から Owned Union へ持ち上げる"))

(test-case "NFn と wrapper の内側の隠れる借用は互換時も拒否する"
  (define wide '(Record ((name String imm) (b (Borrowed Int ρ) imm))))
  (define narrow '(Record ((name String imm))))
  (define pairs
    (list (list `(NFn () ,wide () () () User)
                `(NFn () ,narrow () () () User))
          (list `(NFn (,narrow) Int () () () User)
                `(NFn (,wide) Int () () () User))
          (list `(Untrusted ,wide) `(Untrusted ,narrow))
          (list `(Refined ,wide (Prop P))
                `(Refined ,narrow (Prop P)))))
  (for ([pair (in-list pairs)])
    (check-true (compat? (first pair) (second pair)))
    (check-equal? (borrow-hiding-kind (first pair) (second pair)
                                      compat?)
                  'reject)))

(test-case "Borrowed<Record> の capability view は許可する"
  (check-equal? (borrow-hiding-kind `(Borrowed ,borrow-wide ρ)
                                    `(Borrowed ,borrow-narrow ρ)
                                    compat?)
                'ok))

(test-case "RSD の後にも NFn 返り値に借用が隠れる Proof を拒否する"
  (define wide-nfn `(NFn () ,borrow-wide () () () User))
  (define narrow-nfn `(NFn () ,borrow-narrow () () () User))
  (define actual `(Record ((name String imm) (f ,wide-nfn imm))))
  (define expected `(Record ((name String imm) (f ,narrow-nfn imm))))
  (check-true (compat? actual expected))
  (check-equal? (remainder-target-type actual expected) actual)
  (check-equal? (borrow-hiding-kind actual expected compat?) 'reject)
  (check-false (rsd-proof-pair-ok? actual expected compat?)))

(define borrow-wide-at-rp
  '(Record ((hidden (Borrowed Res (RVar 0)) imm) (name String imm))))
(define borrow-narrow-at-rp '(Record ((name String imm))))
(define borrow-wide-value
  '(Rec ((hidden imm borrow) (name imm "A"))))
(define borrow-rsd-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,borrow-wide-at-rp
                                     ,borrow-narrow-at-rp)))

(define borrow-wide-at-region-0
  '(Record ((hidden (Borrowed Res 0) imm) (name String imm))))
(define borrow-narrow-at-region-0 '(Record ((name String imm))))

(test-case "Scope の結果で余剰借用を隠す Core は E-BOR-027"
  (define-values (callables environment)
    (borrowed-record-callables borrow-narrow-at-rp))
  (define result
    (typed `(Apply g
                   (Scope (1)
                     (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
                       ,borrow-wide-value)))
           borrow-place callables environment))
  (check-equal?
   (typing-key result)
   'borrow-hidden-by-narrowing))

(test-case "分岐の各出口で借用を隠すと E-BOR-027"
  (define-values (g-callables g-environment)
    (borrowed-record-callables borrow-narrow-at-rp))
  (define test-type '(NFn (Unit) (Option Unit) () () () User))
  (define callables (append g-callables `((test ,test-type))))
  (define environment (append g-environment `((flag (Option Unit))
                                               (test ,test-type))))
  (for ([scrutinee (in-list '(flag (Apply test unit)))])
    (define core
      `(Eliminate ,scrutinee
         ((none () -> (Apply g
                             (Scope (1)
                               (Let (borrow let (Borrowed Res (RVar 0)))
                                    (Borrow 1) ,borrow-wide-value))))
          (some (value) -> unit))))
    (check-equal? (typing-key (typed core borrow-place callables environment))
                  'borrow-hidden-by-narrowing)))

(test-case "捕捉する閉包への仮引数で借用を隠すと E-BOR-027"
  (define outer-type
    `(NFn (,borrow-narrow-at-rp)
          (NFn () ,borrow-narrow-at-rp () () () User)
          () () () User))
  (define inner-type `(NFn () ,borrow-narrow-at-rp () () () User))
  (define core
    `(Apply (Lam User outer (value) (Lam User inner () value))
            (Scope (1)
              (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
                ,borrow-wide-value))))
  (check-equal?
   (typing-key (typed core borrow-place
                       `((outer ,outer-type) (inner ,inner-type))))
   'borrow-hidden-by-narrowing))

(test-case "Recur の back-edge で借用を隠すと E-BOR-027"
  (define recur-type `(NFn (,borrow-narrow-at-rp) Unit () (Partial) () User))
  (define core
    `(Scope (1)
       (Recur loop-id loop (value)
         (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
           (Apply loop ,borrow-wide-value))
         unit)))
  (check-equal? (typing-key (typed core borrow-place `((loop-id ,recur-type))))
                'borrow-hidden-by-narrowing))

(test-case "Untrusted と Refined payload の狭窄で借用を隠すと E-BOR-027"
  (for ([wrap (in-list '(untrusted refined))])
    (define expected
      (if (eq? wrap 'untrusted)
          `(Untrusted ,borrow-narrow-at-region-0)
          `(Refined ,borrow-narrow-at-region-0 (Prop P))))
    (define function-type `(NFn (,expected) Unit () () () User))
    (define payload-type
      (if (eq? wrap 'untrusted)
          `(Untrusted ,borrow-wide-at-region-0)
          `(Refined ,borrow-wide-at-region-0 (Prop P))))
    (check-equal?
     (typing-key (typed '(Apply consume wrapped) '()
                        `((consume ,function-type))
                        `((consume ,function-type) (wrapped ,payload-type))))
     'borrow-hidden-by-narrowing)))

(test-case "ProjOpt term と非 Owned place の隠れた借用は E-BOR-027"
  (define term
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (ProjOpt ,borrow-narrow-at-rp
                  (Rec ((nested imm ,borrow-wide-value))) nested))))
  (check-equal? (typing-key (typed term borrow-place '()))
                'borrow-hidden-by-narrowing)
  (define outer-wide
    `(Record ((field ,borrow-wide-at-region-0 imm))))
  ;; ProjOpt place は任意の place 表を根にでき、Owned root には限定されない。
  (check-equal?
   (typing-key
    (type-of/raw `(ProjOpt ,borrow-narrow-at-region-0 2 field)
                  `((2 ,outer-wide)) '() '()
                  (empty-region-ctx)))
   'borrow-hidden-by-narrowing))

(test-case "NFn の返り値と反変引数で借用を隠す Core は E-BOR-027"
  (define narrow '(Record ((name String imm))))
  (define wide-r
    '(Record ((hidden (Borrowed Int (RParam r)) imm) (name String imm))))
  (define nfn-return-wide `(NFn () ,wide-r () () () User))
  (define nfn-return-narrow `(NFn () ,narrow () () () User))
  (define nfn-arg-narrow `(NFn (,narrow) Unit () () () User))
  (define nfn-arg-wide `(NFn (,wide-r) Unit () () () User))
  (define (run expected actual)
    (define consume-type
      `(ForallRegion (r) (NFn (,expected) Unit () () () User)))
    (define actual-type `(ForallRegion (r) ,actual))
    (define core
      `(RegionLam (a)
         (Apply (RegionApp consume ((RParam a)))
                (RegionApp f ((RParam a))))))
    (typed core '() `((consume ,consume-type) (f ,actual-type))
           `((consume ,consume-type) (f ,actual-type))))
  (check-equal? (typing-key (run nfn-return-narrow nfn-return-wide))
                'borrow-hidden-by-narrowing)
  (check-equal? (typing-key (run nfn-arg-wide nfn-arg-narrow))
                'borrow-hidden-by-narrowing))

(test-case "Union view と Owned payload は既存の type-mismatch のまま"
  (define narrow '(Record ((name String imm))))
  (define wide '(Record ((hidden (Borrowed Int 0) imm) (name String imm))))
  (define union-narrow (normalize-type `(Union Bool ,narrow)))
  (define union-wide (normalize-type `(Union Bool ,wide)))
  (check-equal?
   (typing-key
    (typed '(Apply consume value) '()
           `((consume (NFn (,union-narrow) Unit () () () User)))
           `((consume (NFn (,union-narrow) Unit () () () User))
             (value ,union-wide))))
   'type-mismatch)
  (define owned-narrow `(Owned ,narrow))
  (define owned-wide `(Owned ,wide))
  (check-equal?
   (typing-key
    (typed '(Apply consume (Move value)) '()
           `((consume (NFn (,owned-narrow) Unit () () () User)))
           `((consume (NFn (,owned-narrow) Unit () () () User))
             (value ,owned-wide))))
   'type-mismatch))

(test-case "UnionInject の payload を RSD で除去すれば Core は受理する"
  (define union-type (normalize-type `(Union Bool ,borrow-narrow-at-rp)))
  (define core
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (UnionInject ,union-type ,borrow-narrow-at-rp
                      (Discharge ,borrow-rsd-proof ,borrow-wide-value)))))
  (check-equal? (typing-key (typed core borrow-place '())) 'ok))

(define owned-wide-type
  '(Record ((kept Int imm) (owned (Option (Owned Res)) imm))))
(define owned-narrow-type '(Record ((kept Int imm))))
(define owned-source-type `(NFn (Unit) ,owned-wide-type () (Own) () User))
(define owned-wide-value '(Apply owned-source unit))
(define owned-rsd-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,owned-wide-type ,owned-narrow-type)))

(test-case "const は直接と Let 包みの RSD 後の借用・Owned を受理する"
  (define borrowed-cases
    (list
     (list 'borrowed
           borrow-narrow-at-rp borrow-wide-value borrow-rsd-proof
           `(Scope (1)
              (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
                (Let (x const ,borrow-narrow-at-rp)
                     (Discharge ,borrow-rsd-proof ,borrow-wide-value) x)))
           `(Scope (1)
              (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
                (Let (x const ,borrow-narrow-at-rp)
                     (Let (tmp let ,borrow-wide-at-rp) ,borrow-wide-value
                       (Discharge ,borrow-rsd-proof tmp)) x))))
     (list 'owned
           owned-narrow-type owned-wide-value owned-rsd-proof
           `(Let (x const ,owned-narrow-type)
                 (Discharge ,owned-rsd-proof ,owned-wide-value) x)
           `(Let (x const ,owned-narrow-type)
                 (Let (tmp let ,owned-wide-type) ,owned-wide-value
                   (Discharge ,owned-rsd-proof (Move tmp))) x))))
  (for ([test (in-list borrowed-cases)])
    (define (type-case core)
      (if (eq? (first test) 'borrowed)
          (typed core borrow-place '())
          (typed core '() `((owned-source ,owned-source-type))
                 `((owned-source ,owned-source-type)))))
    (check-equal? (typing-key (type-case (fifth test))) 'ok
                  (format "~a: 直接 Discharge" (first test)))
    (check-equal? (typing-key (type-case (sixth test))) 'ok
                  (format "~a: Let 包みの Discharge" (first test)))))

(test-case "Discharge 無しの const 最上位残余は借用・Owned とも E-RCD-005"
  (define borrowed
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (Let (x const ,borrow-narrow-at-rp) ,borrow-wide-value x))))
  (check-equal? (typing-key (typed borrowed borrow-place '()))
                'const-record-residual)
  (check-equal?
   (typing-key
    (typed `(Let (x const ,owned-narrow-type) ,owned-wide-value x) '()
           `((owned-source ,owned-source-type))
           `((owned-source ,owned-source-type))))
   'const-record-residual))

(test-case "const の共通 imm 欄にある借用残余は RSD で落とせる"
  (define actual
    '(Record ((nested (Record ((hidden (Borrowed Res (RVar 0)) imm)
                               (name String imm))) imm))))
  (define expected
    '(Record ((nested (Record ((name String imm))) imm))))
  (define value
    '(Rec ((nested imm
                 (Rec ((hidden imm borrow) (name imm "A")))))))
  (define proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,actual ,expected)))
  (define core
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (Let (x const ,expected)
              (Discharge ,proof ,value) x))))
  (check-equal? (typing-key (typed core borrow-place '())) 'ok))

(test-case "let は最上位の借用残余を文脈型に残す"
  (define core
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (Let (wide let ,borrow-narrow-at-rp) ,borrow-wide-value
           (Proj wide hidden)))))
  (check-equal? (typing-key (typed core borrow-place '())) 'ok))

(test-case "mut の借用 view は既存 key、Reassign wide RHS は E-VAR-013"
  (define mut-core
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (Let (x mut ,borrow-wide-at-rp) ,borrow-wide-value unit))))
  (check-equal? (typing-key (typed mut-core borrow-place '()))
                'mut-binding-unsupported-type)
  (define reassign-core
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (Let (x mut ,borrow-narrow-at-rp)
              (Rec ((name imm "A")))
           (Reassign x ,borrow-narrow-at-rp ,borrow-wide-value)))))
  (check-equal? (typing-key (typed reassign-core borrow-place '()))
                'reassign-type-mismatch))

(test-case "Assign と RawStore は隠れた借用を Discharge 無しで格納しない"
  (define wide
    '(Record ((hidden (Borrowed Res (RVar 0)) imm) (name String imm))))
  (define narrow '(Record ((name String imm))))
  (define value '(Rec ((hidden imm borrow) (name imm "A"))))
  (define assign
    `(Scope (1 2)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (Assign (BorrowMut 2) ,value))))
  (check-equal?
   (typing-key (typed assign `((1 Res) (2 ,narrow)) '()))
   'borrow-hidden-by-narrowing)
  (define pointer
    `(RawPtr ,narrow Mut NonNull (Align 1) (AddrSpace native) (Prov owned)))
  (define raw-store
    `(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (Unsafe (RawStore ptr ,value)))))
  (check-equal?
   (typing-key (typed raw-store '((1 Res)) '()
                       `((ptr ,pointer))))
   'borrow-hidden-by-narrowing))

(test-case "Curry の固定引数も借用を隠さない"
  (define narrow '(Record ((name String imm))))
  (define wide '(Record ((hidden (Borrowed Int 0) imm) (name String imm))))
  (define function-type `(NFn (,narrow) Unit () () () User))
  (define environment `((f ,function-type) (value ,wide)))
  (check-equal?
   (typing-key
    (typed '(Curry f value) '() `((f ,function-type)) environment))
   'borrow-hidden-by-narrowing))

(test-case "RegionLam は外側の借用の capture を拒否し自身の RParam は保つ"
  (define capture-core
    '(Scope (1)
       (Let (borrow let (Borrowed Res (RVar 0))) (Borrow 1)
         (RegionLam (a) borrow))))
  (check-equal? (typing-key (typed capture-core borrow-place '()))
                'borrow-hidden-by-narrowing)
  (define polymorphic
    '(RegionLam (a) (Lam User g (x) 1)))
  (define callables
    '((g (ForallRegion (a)
          (NFn ((Borrowed Int (RParam a))) Int () () () User)))))
  (check-equal? (typing-key (typed polymorphic '() callables)) 'ok))

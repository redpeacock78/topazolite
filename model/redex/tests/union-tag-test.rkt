#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../annotate.rkt"
         "../borrow.rkt"
         "../compat.rkt"
         "../erase.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../span-core.rkt"
         "../type-shape.rkt"
         "../type-equiv.rkt"
         "../typing.rkt"
         "../uniquify.rkt")

(define U '(Union Int (Union String Bool)))
(define U1 '(Union Int Bool))
(define U2 '(Union String Bool))
(define IS '(Union Int String))
(define nfn-u1 `(NFn (,U1) Int () () () User))
(define nfn-u `(NFn (,U) Int () () () User))

(define inject-int `(UnionInject ,IS Int 1))
(define elim-is
  `(UnionEliminate ,inject-int ((Int i -> i) (String s -> 0))))

(define (if-term then else)
  `(Eliminate (Construct Bool true)
              ((true () -> ,then) (false () -> ,else))))

(define plain-record-join-term
  (if-term '(Rec ((a imm 1)))
           '(Rec ((a imm (Construct Bool true))))))
(define record-imm-join-term
  (if-term `(Rec ((a imm (UnionInject ,U1 Int 1)) (b imm 2)))
           `(Rec ((a imm (UnionInject ,U2 String "s")) (c imm 3)))))
(define record-mut-join-term
  (if-term `(Rec ((a mut (UnionInject ,U1 Int 1))))
           `(Rec ((a mut (UnionInject ,U2 String "s"))))))

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment)
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define-syntax-rule (tagged body ...)
  (parameterize ([current-union-tag-mode #t]) body ...))

(define (type-of core [environment '()])
  (match (type-of/raw core '() '() environment)
    [(list 'ok (list type _row)) type]
    [other other]))

(define (tc? actual expected)
  (tag-compat? actual expected '() equal?))

(test-case "G2 と G2m は UnionInject と UnionEliminate を受理する"
  (check-true (redex-match? G2 c inject-int))
  (check-true (redex-match? G2 c elim-is))
  (check-true (redex-match? G2m c elim-is)))

(test-case "UnionVal は G2m の値であり、G2 と G2+ は受理しない"
  (define tagged `(UnionVal ,IS Int 1))
  (check-true (redex-match? G2m v tagged))
  (check-false (redex-match? G2 c tagged))
  (check-false (redex-match? G2+ c tagged)))

(test-case "G2m の評価文脈は inject と eliminate の穴を受理する"
  (check-true
   (redex-match? G2m F (term (UnionInject (Union Int String) Int hole))))
  (check-true
   (redex-match? G2m E (term (UnionInject (Union Int String) Int hole))))
  (check-true
   (redex-match? G2m G (term (UnionInject (Union Int String) Int hole))))
  (check-true
   (redex-match? G2m F (term (UnionEliminate hole ((Int i -> i))))))
  (check-true
   (redex-match? G2m E (term (UnionEliminate hole ((Int i -> i))))))
  (check-true
   (redex-match? G2m G (term (UnionEliminate hole ((Int i -> i)))))))

(test-case "fseg は (Payload) を受理する"
  (check-true (redex-match? G2m fp '(a (Payload) 0))))

(test-case "spanful Union Core は G2+ に属し erase と uniquify を保つ"
  (define raw
    '(Let (x Int) 0
       (UnionEliminate (UnionInject (Union Int String) Int 1)
         ((Int x -> x) (String y -> x)))))
  (define spanful (annotate-core raw))
  (check-true (redex-match? G2+ c spanful))
  (check-equal? (erase-core spanful) raw)
  (define branch
    (first (list-ref (peel-node (list-ref (peel-node spanful) 3)) 2)))
  (check-true (span-ok? (branch-span branch)))
  (check-true (span-ok? (ubr-span branch)))
  (check-equal? (erase-core (peel-ubr branch)) '(Int x -> x))
  (define renamed (erase-core (uniquify-binders spanful)))
  (match renamed
    [`(Let (,outer Int) 0
       (UnionEliminate ,_
         ((Int ,inner -> ,inner-body)
          (String ,other -> ,other-body))))
     (check-not-equal? outer inner)
     (check-not-equal? inner other)
     (check-equal? inner inner-body)
     (check-equal? outer other-body)]
    [_ (fail (format "unexpected uniquified core: ~s" renamed))]))

(test-case "core-types-normal? は inject の型を正規化し ubr の型を走査する"
  (check-true (core-types-normal? inject-int))
  (check-true (core-types-normal? elim-is))
  (check-true
   (core-types-normal?
    '(UnionInject (Union (Union Int Bool) String) Int 1)))
  (check-false
   (core-types-normal?
    '(UnionEliminate 1 (((Union (Union Int Bool) String) x -> x))))))

(test-case "構造的な走査は ubr の本体を子として扱い束縛を閉じる"
  (check-equal? (core-children elim-is) (list inject-int 'i 0))
  (check-equal? (core-with-children elim-is (list inject-int 'i 0)) elim-is)
  (check-true (set-empty? (core-free-vars elim-is))))

(test-case "erase-core と inject-g2m は Union Core の形を保つ"
  (check-equal? (erase-core elim-is) elim-is)
  (match (inject-g2m elim-is)
    [`(cfg (Scope () ,core) () () () ())
     (check-equal? core elim-is)]
    [other (fail (format "unexpected injected config: ~s" other))]))

(test-case "tag mode の既定は #f で、新しい構成子を E-TYP-001 で拒否する"
  (check-false (current-union-tag-mode))
  (check-equal? (key-of inject-int) 'ill-typed)
  (check-equal? (key-of elim-is) 'ill-typed))

(test-case "tag 保存互換：Union は既に tag を持つ部分集合だけを渡す"
  (check-true (tc? U1 U))
  (check-true (tc? 'Never U))
  (check-false (tc? 'Int U))
  (check-false (tc? U 'Int))
  (check-false (tc? U U1)))

(test-case "tag 保存互換：record の imm 欄と関数の変性"
  (check-true (tc? `(Record ((a ,U1 imm))) `(Record ((a ,U imm)))))
  (check-false (tc? '(Record ((a Int imm))) `(Record ((a ,U imm)))))
  (check-false (tc? '(NFn (Int) Int () () () User) nfn-u)))

(test-case "tag 保存互換：借用と Untrusted、Refined の payload"
  (check-true (tc? `(Borrowed ,U1 0) `(Borrowed ,U 0)))
  (check-false (tc? `(BorrowedMut ,U1 0) `(BorrowedMut ,U 0)))
  (check-true (tc? `(Untrusted ,U1) `(Untrusted ,U)))
  (check-false (tc? `(Untrusted Int) `(Untrusted ,U)))
  (check-true (tc? `(Refined ,U1 (Prop p)) `(Refined ,U (Prop p)))))

(test-case "tag の狭まり：Union と Record の構造を保つ"
  (check-true (tag-narrowing? U1 U))
  (check-true (tag-narrowing? 'Never U))
  (check-false (tag-narrowing? 'Int U))
  (check-false (tag-narrowing? 'Int 'Bool))
  (check-true
   (tag-narrowing? `(Record ((a ,U1 mut))) `(Record ((a ,U mut)))))
  (check-false
   (tag-narrowing? `(Record ((a ,U1 mut) (b Int imm)))
                   `(Record ((a ,U mut)))))
  (check-false
   (tag-narrowing? `(Record ((a ,U1 imm))) `(Record ((a ,U mut)))))
  (check-false
   (tag-narrowing? `(Record ((a ,U1 imm opt))) `(Record ((a ,U imm))))))

(test-case "tag の狭まり：NFn、借用、data 型の内側は緩めない"
  (check-false (tag-narrowing? nfn-u1 nfn-u))
  (check-false
   (tag-narrowing? `(Record ((f ,nfn-u1 mut))) `(Record ((f ,nfn-u mut)))))
  (check-false (tag-narrowing? `(Owned ,nfn-u1) `(Owned ,nfn-u)))
  (check-false
   (tag-narrowing? `(Owned (Record ((f (Option ,U1) mut))))
                   `(Owned (Record ((f (Option ,U) mut))))))
  (check-false (tag-narrowing? `(Borrowed ,U1 0) `(Borrowed ,U 0)))
  (check-false
   (tag-narrowing? `(Data Box (,U1)) `(Data Box (,U)))))

(test-case "tag 保存互換：mut 欄と Owned payload は tag の狭まりを求める"
  (check-true (tc? `(Record ((a ,U1 mut))) `(Record ((a ,U mut)))))
  (check-false (tc? '(Record ((a Int mut))) '(Record ((a Bool mut)))))
  (check-true (tc? `(Owned ,U1) `(Owned ,U)))
  (check-false (tc? `(Owned ,nfn-u1) `(Owned ,nfn-u))))

(test-case "UnionInject：成分の inject と正規化"
  (tagged
   (check-equal? (type-of inject-int) (normalize-type IS))
   (check-equal? (type-of '(UnionInject (Union Int (Union Int String)) Int 1))
                 (normalize-type IS))
   (check-equal? (key-of `(UnionInject ,IS Bool (Construct Bool true)))
                 'union-inject-not-member)
   (check-equal? (key-of '(UnionInject Int Int 1)) 'union-inject-not-member)
   (check-not-equal? (key-of `(UnionInject ,IS Int (Construct Bool true))) 'ok)
   (check-equal?
    (type-of '(UnionInject (Union (Option Int) String) (Option Int)
                           (Construct (Option Int) some 1)))
    '(Union (Option Int) String))))

(test-case "UnionEliminate：synth、check、枝検査"
  (tagged
   (check-equal? (type-of elim-is) 'Int)
   (check-equal? (key-of '(UnionEliminate 1 ((Int i -> i)))) 'non-union-eliminate)
   (check-equal? (key-of `(UnionEliminate ,inject-int ((Int i -> i))))
                 'non-exhaustive-union-eliminate)
   (check-equal? (key-of `(UnionEliminate ,inject-int
                            ((Int i -> i) (Int j -> j) (String s -> 0))))
                 'non-exhaustive-union-eliminate)
   (check-equal? (key-of `(UnionEliminate ,inject-int
                            ((Int i -> i) (String s -> (Construct Bool true)))))
                         'type-mismatch)
   (check-equal?
    (type-of '(Let (y const Int)
                (UnionEliminate (UnionInject (Union Int String) Int 1)
                  ((Int i -> i) (String s -> 0)))
                y))
    'Int)
   (check-equal?
    (type-of `(UnionEliminate ,inject-int
                ((Int i -> (Perform (Return boundary Int) 1))
                 (String s -> 0))))
    'Int)))

(test-case "UnionEliminate：余った枝も型付けする"
  (tagged
   (check-equal? (type-of `(UnionEliminate ,inject-int
                             ((Int i -> i) (String s -> 0) (Bool b -> 0))))
                 'Int)
   (check-equal? (key-of `(UnionEliminate ,inject-int
                            ((Int i -> i) (String s -> 0) (Bool b -> (Read b)))))
                 'read-non-borrow)))

(test-case "Owned を直接の成分に持つ Union は入れ子でも拒否する"
  (tagged
   (check-equal? (key-of `(UnionInject (Union Int (Union String (Owned Res))) Int 1))
                 'owned-union-member)
   (check-equal?
    (key-of '(Let (x const (Union Int (Owned Res)))
               (UnionInject (Union Int (Owned Res)) Int 1)
               x))
    'owned-union-member)))

(test-case "Data 型の引数にある Owned 成分の Union も well-formedness 検査が見つける"
  (check-true
   (owned-union-member? '(Data Phantom ((Union Int (Owned Res)))))))

(test-case "Owned を直接の成分に持つ Union は tag mode が無効でも拒否する"
  (check-false (current-union-tag-mode))
  (check-equal? (key-of '(Let (x const (Union Int (Owned Res))) 1 x))
                'owned-union-member)
  (check-equal?
   (key-of '(Let (x const (Union Int (Union String (Owned Res)))) 1 x))
   'owned-union-member))

(test-case "tag mode の check 境界は tag の無い値を Union の位置へ入れない"
  (tagged
   (check-not-equal?
    (key-of `(UnionInject (Union (Record ((a ,IS imm))) Bool)
                          (Record ((a ,IS imm)))
                          (Rec ((a imm 1)))))
    'ok)
   (check-not-equal?
    (key-of `(Let (y const ,IS)
                  (UnionEliminate ,inject-int ((Int i -> i) (String s -> 0)))
                  y))
    'ok)))

(test-case "tag 保存の上界"
  (check-equal? (tag-upper-bound 'Never U1) (normalize-type U1))
  (check-equal? (tag-upper-bound U1 'Never) (normalize-type U1))
  (check-equal? (tag-upper-bound U1 U2) (normalize-type U))
  (check-false (tag-upper-bound U1 'Int))
  (check-false (tag-upper-bound 'Int 'Bool))
  (check-equal? (tag-upper-bound 'Int 'Int) 'Int)
  (check-equal?
   (tag-upper-bound `(Record ((a ,U1 imm) (b Int imm)))
                    `(Record ((a ,U2 imm) (c Int imm))))
   (normalize-type `(Record ((a ,U imm)))))
  (check-equal?
   (tag-upper-bound `(Record ((a ,U1 mut))) `(Record ((a ,U2 mut))))
   (normalize-type `(Record ((a ,U mut))))))

(test-case "synth 合流は tag 保存の上界を使い tag の無い値から Union を作らない"
  (check-equal? (type-of plain-record-join-term)
                (normalize-type '(Record ((a (Union Int Bool) imm)))))
  (tagged
   (check-equal? (key-of plain-record-join-term) 'unmergeable-branch-records)
   (check-equal? (type-of record-imm-join-term)
                 (normalize-type `(Record ((a ,U imm)))))
   (check-equal? (type-of record-mut-join-term)
                 (normalize-type `(Record ((a ,U mut)))))))

(test-case "UnionEliminate の synth は枝の tag 保存の上界を使う"
  (define core
    `(UnionEliminate ,inject-int
       ((Int i -> (UnionInject ,U1 Int 1))
        (String s -> (UnionInject ,U2 String "s")))))
  (tagged
   (check-equal? (type-of core) (normalize-type U))))

(test-case "tag mode の値を渡す境界は暗黙の tag 無し widening を拒否する"
  (define rec-term
    `(Let (r const (Record ((a ,IS imm))))
          (Rec ((a imm 1)))
          (Proj r a)))
  (define assign-term
    `(Let (m mut ,IS) ,inject-int
          (Assign (BorrowMut m) 1)))
  (define bare-let
    `(Let (x const ,IS) 1
          (UnionEliminate x ((Int i -> 0) (String s -> 0)))))
  (define rec-union
    '(Union (Record ((a Int imm) (b Int imm)))
            (Record ((a Int imm) (c Bool imm)))))
  (define union-to-rec
    `(Let (u const ,rec-union)
          (UnionInject ,rec-union
                       (Record ((a Int imm) (b Int imm)))
                       (Rec ((a imm 1) (b imm 2))))
          (Let (r const (Record ((a Int imm)))) u (Proj r a))))
  (check-equal? (type-of rec-term) IS)
  (tagged
   (check-not-equal? (key-of rec-term) 'ok)
   (check-not-equal? (key-of assign-term) 'ok)
   (check-not-equal? (key-of bare-let) 'ok)
   (check-not-equal? (key-of union-to-rec) 'ok)))

(test-case "Reassign は tag の狭まりを受け入れ、Owned 欄の損失を拒否する"
  (define wide-union (normalize-type U))
  (define narrow-reassign
    `(Let (x mut ,wide-union)
          (UnionInject ,U1 Int 1)
          (Reassign x (UnionInject ,U1 Int 2))))
  (define owned-loss-environment
    '((slot (Record ((y Int imm))) mut)
      (source (Record ((x (Owned Res) imm) (y Int imm))) const)))
  (tagged
   (check-equal? (key-of narrow-reassign) 'ok)
   (check-equal? (key-of '(Reassign slot source) owned-loss-environment)
                 'reassign-type-mismatch)))

(define borrowed-union-core
  '(Scope (1)
     (UnionEliminate (Borrow 1)
                     ((Int i -> (Let (value const Int) (Read i) unit))
                      (String s -> (Let (value const String) (Read s) unit))))))
(define borrowed-union-ir (build-region-ir borrowed-union-core))
(define borrowed-union-Λ
  (region-ctx borrowed-union-ir '()
              (hash 1 (region-at borrowed-union-ir '()))
              (hash)))

(test-case "借用した Union の枝は成分の共有借用を渡す"
  (define result
    (tagged
     (type-of/raw (annotate-regions borrowed-union-core borrowed-union-ir)
                  (list (list 1 IS)) '() '() borrowed-union-Λ)))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

(define borrowed-mut-union-core
  '(Scope (1)
     (UnionEliminate (BorrowMut 1)
                     ((Int i -> (Assign i 7))
                      (String s -> (Assign s "s"))))))
(define borrowed-mut-union-ir (build-region-ir borrowed-mut-union-core))
(define borrowed-mut-union-Λ
  (region-ctx borrowed-mut-union-ir '()
              (hash 1 (region-at borrowed-mut-union-ir '()))
              (hash)))

(test-case "借用した Union の枝は成分の可変借用を渡す"
  (define result
    (tagged
     (type-of/raw (annotate-regions borrowed-mut-union-core
                                    borrowed-mut-union-ir)
                  (list (list 1 IS)) '() '() borrowed-mut-union-Λ)))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

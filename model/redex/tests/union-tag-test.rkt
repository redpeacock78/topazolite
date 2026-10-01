#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../annotate.rkt"
         "../compat.rkt"
         "../erase.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../span-core.rkt"
         "../type-shape.rkt"
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

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment)
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

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

(test-case "core-types-normal? は inject と ubr の型を走査する"
  (check-true (core-types-normal? inject-int))
  (check-true (core-types-normal? elim-is))
  (check-false
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

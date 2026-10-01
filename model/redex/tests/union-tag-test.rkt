#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../annotate.rkt"
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

(define inject-int `(UnionInject ,IS Int 1))
(define elim-is
  `(UnionEliminate ,inject-int ((Int i -> i) (String s -> 0))))

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment)
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

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

#lang racket

(require rackunit racket/match redex/reduction-semantics
         "../lang.rkt" "../typing.rkt" "../borrow.rkt" "../region.rkt")

;; SCP-001。宣言 row に Mutation が無い関数の本体で再代入すると落ちる。
;; P1c2a が入れた undeclared-function-effect の検査がそのまま働くことを固定する。
;; callables の綴りは tests/typing-test.rkt:11-17 の callable-types に倣う。
(define callable-types
  '((loop-id (NFn (Int) Int () () () User))
    (mut-loop-id (NFn (Int) Int () (Mutation) () User))))

(define (key-of core)
  (match (type-of/raw core '() callable-types '() (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

;; 本体で再代入するが loop-id の宣言 row は空である。
(check-equal?
 (key-of (term (Recur loop-id loop (x)
                      (Let (m mut Int) x
                           (Let (u const Unit) (Reassign m 2) m))
                      (Apply loop 1))))
 'undeclared-function-effect)

;; 宣言 row に Mutation があれば同じ本体が通る。
(check-equal?
 (key-of (term (Recur mut-loop-id loop (x)
                      (Let (m mut Int) x
                           (Let (u const Unit) (Reassign m 2) m))
                      (Apply loop 1))))
 'ok)

;; P2f。Apply の εin/εout 合成を、構文の違う同値な effect label も含めて固定する。
(define (row-of core callables)
  (match (type-of/raw core '() callables '() (empty-region-ctx))
    [(list 'ok (list _ row)) row]
    [other (error 'row-of "expected a successful typing result: ~s" other)]))

(define (nfn latent-in latent-out)
  `(NFn (Int) Int ,latent-in ,latent-out () User))

(define (one-fn name latent-in latent-out)
  `((,name ,(nfn latent-in latent-out))))

(define (identity-fn name)
  `(Lam User ,name (x) x))

(define equivalent-effect-type-a
  '(NFn () Int () ((Yield Int) (Return b Int)) () User))

(define equivalent-effect-type-b
  '(NFn () Int () ((Return b Int) (Yield Int)) () User))

(test-case "εin consumes a matching argument effect"
  (check-equal?
   (row-of `(Apply ,(identity-fn 'f) (Perform (Return b Int) 1))
           (one-fn 'f '((Return b Int)) '()))
   '()))

(test-case "effects outside εin remain at the call site"
  (check-equal?
   (row-of `(Apply ,(identity-fn 'f) (Perform (Return b Int) 1))
           (one-fn 'f '((Return a Int)) '()))
   '((Return b Int))))

(test-case "εout is added even when arguments are pure"
  (check-equal?
   (row-of `(Apply ,(identity-fn 'f) 1)
           (one-fn 'f '() '((Yield Int))))
   '((Yield Int))))

(test-case "εin consumes an effect label equivalent by type"
  (check-equal?
   (row-of `(Apply ,(identity-fn 'f)
                   (Perform (Return b ,equivalent-effect-type-b)
                            (Lam User effect-value () 1)))
           (append (one-fn 'f `((Return b ,equivalent-effect-type-a)) '())
                   `((effect-value ,equivalent-effect-type-b))))
   '()))

(test-case "outer effect union deduplicates equivalent labels"
  (define function-type (nfn '() '()))
  (define function-expression
    `(Handle (Return boundary ,function-type)
             (result -> (Perform (Return c ,equivalent-effect-type-a)
                                 (Lam User effect-value () 1)))
             (Perform (Return boundary ,function-type)
                      (Lam User f (x) x))))
  (check-equal?
   (row-of `(Apply ,function-expression
                   (Perform (Return c ,equivalent-effect-type-b)
                            (Lam User effect-value () 1)))
           (append (one-fn 'f '() '())
                   `((effect-value ,equivalent-effect-type-b))))
   `((Return c ,equivalent-effect-type-a))))

(test-case "row-subset? accepts equivalent declared and body labels"
  (define signature
    `(NFn () Unit () ((Return b ,equivalent-effect-type-a)) () User))
  (check-equal?
   (core-type-of
    `(Lam User f ()
         (Perform (Return b ,equivalent-effect-type-b)
                  (Lam User effect-value () 1)))
    '()
    `((f ,signature)
      (effect-value ,equivalent-effect-type-b)))
   (list signature '())))

(test-case "Handle removes a handled label equivalent by type"
  (check-equal?
   (row-of
    `(Handle (Return boundary ,equivalent-effect-type-a)
             (result -> result)
             (Perform (Return boundary ,equivalent-effect-type-b)
                      (Lam User effect-value () 1)))
    `((effect-value ,equivalent-effect-type-b)))
   '()))

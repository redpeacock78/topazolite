#lang racket

;; SUR-012。期待の関数型から省略した仮引数型を補う。

(require racket/match
         rackunit
         "../diagnostic.rkt"
         "../elaborate.rkt")

(define (code-of term)
  (match (elab term)
    [`(err ,d) (diagnostic-id d)]
    [_ 'ok]))

(define (found-of term)
  (match (elab term)
    [`(err ,d) (diagnostic-found d)]
    [other (error 'found-of "失敗しなかった: ~s" other)]))

(define (type-of term)
  (match (elab term)
    [(list _ type _ _) type]
    [other (error 'type-of "成功しなかった: ~s" other)]))

(define (tree-contains? tree wanted)
  (or (equal? tree wanted)
      (and (pair? tree)
           (or (tree-contains? (car tree) wanted)
               (tree-contains? (cdr tree) wanted)))))

(define (diagnostic-of term)
  (match (elab term)
    [`(err ,d) d]
    [other (error 'diagnostic-of "失敗しなかった: ~s" other)]))

(define e-typ-025 (diagnostic-code-of 'elaborate 'parameter-type-not-inferable))
(define e-type-mismatch (diagnostic-code-of 'elaborate 'type-mismatch))
(define e-duplicate-parameter (diagnostic-code-of 'elaborate 'duplicate-parameter))

(test-case "SUR-012: 期待の関数型から仮引数型を補う"
  (check-equal?
   (code-of '(Fn () (NFn (Int) Int () ()) ()
                 (Fn ((x #:infer)) #:infer () x)))
   'ok))

(test-case "SUR-012: 補った仮引数型で本体を検査する"
  (check-equal?
   (code-of '(Fn () (NFn (Int) Bool () ()) ()
                 (Fn ((x #:infer)) #:infer () x)))
   e-type-mismatch))

(test-case "SUR-012: 明示と省略の混在"
  (check-equal?
   (code-of '(Fn () (NFn (Int Bool) Bool () ()) ()
                 (Fn ((x Int) (b #:infer)) #:infer () b)))
   'ok))

(test-case "SUR-012: 明示した戻り型と省略した仮引数型"
  (check-equal?
   (code-of '(Fn () (NFn (Int) Int () ()) ()
                 (Fn ((x #:infer)) Int () x)))
   'ok))

(test-case "SUR-012: 明示した仮引数型は期待型より広くてよい（反変）"
  (check-equal?
   (code-of '(Fn () (NFn (Int Bool) Int () ()) ()
                 (Fn ((x (Union Int String)) (b #:infer)) #:infer () 1)))
   'ok))

(test-case "SUR-012: 期待型が Owned 関数型でも仮引数型を補う"
  (check-equal?
   (code-of '(Fn ((p (Owned Res)))
                 (Owned (NFn (Int) (Owned Res) (Own) ()))
                 (Own)
                 (Fn ((x #:infer)) #:infer (Own) (Move p))))
   'ok))

(test-case "SUR-012: 合成位置の仮引数省略 Fn は E-TYP-025"
  (check-equal? (code-of '(Fn ((x #:infer)) #:infer () x)) e-typ-025)
  (check-equal? (found-of '(Fn ((x #:infer)) #:infer () x))
                'no-expected-function)
  (check-equal? (code-of '(Fn ((x #:infer)) Int () x)) e-typ-025))

(test-case "SUR-012: 期待型が関数型でなければ E-TYP-025"
  (define t '(Fn () Int () (Fn ((x #:infer)) #:infer () x)))
  (check-equal? (code-of t) e-typ-025)
  (check-equal? (found-of t) 'no-expected-function))

(test-case "SUR-012: 期待型が関数型の Union なら E-TYP-025"
  (define t '(Fn () (Union (NFn (Int) Int () ())
                           (NFn (Bool) Bool () ())) ()
                 (Fn ((x #:infer)) #:infer () x)))
  (check-equal? (code-of t) e-typ-025)
  (check-equal? (found-of t) 'no-expected-function))

(test-case "SUR-012: 仮引数の数が期待型と異なれば E-TYP-025"
  (define t '(Fn () (NFn (Int Int) Int () ()) ()
                 (Fn ((x #:infer)) #:infer () x)))
  (check-equal? (code-of t) e-typ-025)
  (check-equal? (found-of t) 'arity-mismatch))

(test-case "SUR-012: 仮引数の重複は期待型の有無によらず先に報告する"
  (check-equal? (code-of '(Fn ((x #:infer) (x Int)) #:infer () x))
                e-duplicate-parameter)
  (check-equal? (code-of '(Fn () (NFn (Int) Int () ()) ()
                              (Fn ((x #:infer) (x Int)) #:infer () x)))
                e-duplicate-parameter))

(test-case "SUR-012: E-TYP-025 の primary span は最初の省略 binder の span"
  (define infer-span '(#:span src 11 12))
  (define term
    `(Fn (#:span src 0 30)
         (((#:bind x ,infer-span) (#:infer ,infer-span))
          ((#:bind y (#:span src 15 16))
           (#:infer (#:span src 15 16))))
         (#:infer (#:span src 20 21))
         (#:ef () (#:span src 21 22))
         (#:var x (#:span src 23 24))))
  (define d (diagnostic-of term))
  (check-equal? (diagnostic-id d) e-typ-025)
  (check-equal? (diagnostic-primary-span d) infer-span))

(test-case "SUR-012: 出力の Typed Core と Φ に #:infer が現れない"
  (define r (elab '(Fn () (NFn (Int Bool) Bool () ()) ()
                       (Fn ((x Int) (b #:infer)) #:infer () b))))
  (check-false (tree-contains? r '#:infer)))

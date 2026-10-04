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

(define (record-field-mode tree wanted)
  (match tree
    [`(Rec ,_ (,fields ...))
     (for/or ([field (in-list fields)])
       (match field
         [`((#:lbl ,label ,_) ,mode ,_)
          (and (eq? label wanted) mode)]
         [`(,label ,mode ,_)
          (and (eq? label wanted) mode)]
         [_ #f]))]
    [(? pair?)
     (or (record-field-mode (car tree) wanted)
         (record-field-mode (cdr tree) wanted))]
    [_ #f]))

(define (diagnostic-of term)
  (match (elab term)
    [`(err ,d) d]
    [other (error 'diagnostic-of "失敗しなかった: ~s" other)]))

(define e-typ-025 (diagnostic-code-of 'elaborate 'parameter-type-not-inferable))
(define e-type-mismatch (diagnostic-code-of 'elaborate 'type-mismatch))
(define e-duplicate-parameter (diagnostic-code-of 'elaborate 'duplicate-parameter))
(define e-owned-record-field (diagnostic-code-of 'elaborate 'owned-record-field))

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

;; P2m2c で function value の再構成を入れたら正例へ戻す（spec §5.1 (c)）。
(test-case "P2m2c: 関数値の Union 引数を反変に再構成する"
  (check-equal?
   (code-of '(Fn () (NFn (Int Bool) Int () ()) ()
                 (Fn ((x (Union Int String)) (b #:infer)) #:infer () 1)))
   e-type-mismatch))

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

(test-case "SUR-012: E-Let-Fn-Check は宣言型で仮引数型を補う"
  (define t '(Let (f const (NFn (Int) Int () ()))
                  (Fn ((x #:infer)) #:infer () x)
                  (Apply f 1)))
  (check-equal? (code-of t) 'ok)
  (check-equal? (type-of t) 'Int))

(test-case "SUR-012: 宣言型が関数型でない束縛は E-TYP-025"
  (define t '(Let (f const Int) (Fn ((x #:infer)) #:infer () x) f))
  (check-equal? (code-of t) e-typ-025)
  (check-equal? (found-of t) 'no-expected-function))

;; P2m2c で function return の再構成を入れたら正例へ戻す（spec §5.1 (c)）。
(test-case "P2m2c: 関数値の戻り値へ Union injection を再構成する"
  (check-equal?
   (code-of '(Let (f const (NFn (Int) (Union Int String) () ()))
                  (Fn ((x Int)) #:infer () 1)
                  (Apply f 1)))
   e-type-mismatch))

(test-case "SUR-012: E-Rec-Check は欄の期待型で仮引数型を補う"
  (check-equal?
   (code-of '(Fn () (Record ((print (NFn (Int) Int () ()) imm))) ()
                 (Rec ((print imm (Fn ((x #:infer)) #:infer () x))))))
   'ok))

(test-case "SUR-012: E-Rec-Check は imm の欄を mut の期待へ写さない"
  (check-equal?
   (code-of '(Fn () (Record ((a Int mut))) () (Rec ((a imm 1)))))
   e-type-mismatch))

(test-case "SUR-012: E-Rec-Check は入力 record の mut を Core に保つ"
  (match (elab '(Fn () (Record ((a Int imm))) () (Rec ((a mut 1)))))
    [(list core _ _ _)
     (check-equal? (record-field-mode core 'a) 'mut)]
    [other (error 'record-field-mode "elaboration failed: ~s" other)]))

(test-case "SUR-012: label の集合が異なる record 式は合成へ退避する"
  (check-equal?
   (code-of '(Fn () (Record ((a Int imm))) ()
                 (Rec ((a imm 1) (b imm 2)))))
   'ok)
  (check-equal?
   (code-of '(Fn () (Record ((a (NFn (Int) Int () ()) imm))) ()
                 (Rec ((a imm (Fn ((x #:infer)) #:infer () x)) (b imm 2)))))
   e-typ-025))

(test-case "SUR-012: E-Rec-Check は Owned の欄を拒否する"
  (check-equal?
   (code-of '(Fn ((o (Owned Res))) (Record ((a (Owned Res) imm))) ()
                 (Rec ((a imm (Move o))))))
   e-owned-record-field))

(test-case "SUR-012: 期待型が Owned<Record> なら合成へ退避する"
  (check-equal?
   (code-of '(Fn () (Owned (Record ((a (NFn (Int) Int () ()) imm)))) ()
                 (Rec ((a imm (Fn ((x #:infer)) #:infer () x))))))
   e-typ-025))

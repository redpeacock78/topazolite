#lang racket

(require rackunit
         redex/reduction-semantics
         (prefix-in ty: "../typing.rkt")
         (prefix-in el: "../elaborate.rkt")
         "../lang.rkt"
         "../ucore.rkt"
         "../span-core.rkt")

;; P1c2b spec 4.1。bmode の mut が 4 層すべてで合う。
(test-case "bmode の mut が 4 層で合う"
  (check-true (redex-match? G2 bmode (term mut)))
  (check-true (redex-match? G2m bmode (term mut)))
  (check-true (redex-match? UCore bmode (term mut)))
  (check-true (redex-match? G2+ bmode (term mut)))
  ;; UCore+ は UCore の bmode をそのまま継ぐ。
  (check-true (redex-match? UCore+ bmode (term mut))))

;; 既存の 2 つが消えていないことも同時に見る。
(test-case "const と let は残る"
  (for ([mode (in-list '(const let))])
    (check-true (redex-match? G2 bmode mode) (format "~s" mode))
    (check-true (redex-match? G2m bmode mode) (format "~s" mode))
    (check-true (redex-match? UCore bmode mode) (format "~s" mode))
    (check-true (redex-match? G2+ bmode mode) (format "~s" mode))))

;; mut を宣言した Let が項として合う。
(test-case "mut の Let が項として合う"
  (check-true (redex-match? G2 c (term (Let (x mut Int) 1 x))))
  (check-true (redex-match? G2m c (term (Let (x mut Int) 1 x)))))

;; P1c2b spec 6.1。環境 entry は 2 要素と 3 要素の両方を許す。
(test-case "valid-environment? が 2 要素と 3 要素を受理する"
  (check-true (ty:valid-environment? '((x Int))))
  (check-true (ty:valid-environment? '((x Int mut))))
  (check-true (ty:valid-environment? '((x Int mut) (y Int))))
  ;; 4 要素は拒む。
  (check-false (ty:valid-environment? '((x Int mut extra))))
  ;; 1 要素も拒む。
  (check-false (ty:valid-environment? '((x)))))

;; extend は modes を省略すると 2 要素を作る。
(test-case "extend の modes は省略できる"
  (check-equal? (ty:environment-extend '() '(x) '(Int)) '((x Int)))
  (check-equal? (ty:environment-extend '() '(x) '(Int) '(mut)) '((x Int mut))))

;; lookup は 3 要素 entry からも型を取れる。
(test-case "lookup が 3 要素 entry から型を取る"
  (check-equal? (ty:environment-lookup '((x Int mut)) 'x) 'Int)
  (check-equal? (ty:environment-lookup '((x Int)) 'x) 'Int)
  (check-false (ty:environment-lookup '((x Int mut)) 'y)))

;; binding-mode-of は 3 要素 entry の mode を返す。
(test-case "binding-mode-of が mode を返す"
  (check-equal? (ty:binding-mode-of '((x Int mut)) 'x) 'mut)
  (check-false (ty:binding-mode-of '((x Int)) 'x))
  (check-false (ty:binding-mode-of '((x Int mut)) 'y)))

;; spec 6.3。3 要素 entry を混ぜても recur の対は同じものが取れる。
(test-case "recur-frame-for は 3 要素 entry に影響されない"
  (define env2 '((f (NFn () Int () ())) (x Int)))
  (define env3 '((f (NFn () Int () ())) (x Int mut)))
  (check-equal? (ty:environment-lookup env2 'f)
               (ty:environment-lookup env3 'f)))

(define rec2 '(Rec ((a imm 1) (b imm unit))))

;; P1c2b。mut は let と同じく残余 field を binding 型へ戻す（spec 7.3）。
(check-equal?
 (ty:core-type-of `(Let (x mut (Record ((a Int imm)))) ,rec2 (Proj x b)) '() '())
 '(Unit ()))
;; 非 record の T では const や let と差が出ない。
(check-equal? (ty:core-type-of '(Let (x mut Int) 1 x) '() '()) '(Int ()))
;; 非互換 field は let と同じく拒否する。
(check-equal?
 (ty:core-type-of `(Let (x mut (Record ((a Bool imm)))) ,rec2 x) '() '())
 'ill-typed)

;; elaborate 側も同じ扱いである（spec 7.4）。
(define (elab-type term) (match (el:elab term) [(list _ type _ _) type]))
(check-equal?
 (elab-type `(Let (x mut (Record ((a Int imm)))) ,rec2 x))
 '(Record ((a Int imm) (b Unit imm))))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../annotate.rkt"
         "../classify.rkt"
         "../compat.rkt"
         "../lowering.rkt"
         "../typing.rkt")

;; span.md §7.3: 判定に span を使わない項面の関数は、投影を通してから既存の
;; 走査へ渡す。ここで固定するのは「spanful な項の判定が spanless 版と一致する」
;; ことである。
;; ill-typed 側の一致では契約を固定できない。投影が入っていない実装でも
;; redex-match? が落ちて 'ill-typed になり、同じ値が返るためである。
;; そのため各 test-case は well-typed な項の型が一致することを見る。

(define callable-types
  (term ((identity-id (NFn (Int) Int () ()))
         (binary-id (NFn (Int Int) Int () ())))))

(test-case "span.md §7.3: core-type-of は spanful な c を投影して受理する"
  (define prim '(PrimVal (Reserved o-lt) lt))
  (check-equal? (core-type-of (annotate-core prim) '() '())
                '((NFn (Int Int) Bool () ()) ()))
  (check-equal? (core-type-of (annotate-core prim) '() '())
                (core-type-of prim '() '()))
  ;; #:bind と Lam の span を含む項。
  (define lam '(Lam User identity-id (x) x))
  (check-equal? (core-type-of (annotate-core lam) '() callable-types)
                '((NFn (Int) Int () ()) ()))
  ;; #:lit と Apply の span を含む項。
  (define applied `(Apply (Lam User binary-id (x y) x) 1 2))
  (check-equal? (core-type-of (annotate-core applied) '() callable-types)
                '(Int ()))
  ;; #:ty と #:bind を持つ Let。
  (define bound '(Let (n Int) 1 n))
  (check-equal? (core-type-of (annotate-core bound) '() '())
                (core-type-of bound '() '()))
  (check-equal? (core-type-of (annotate-core bound) '() '())
                '(Int ())))

(test-case "span.md §7.3: core-check-row と core-check も spanful な c を受ける"
  (define prim '(PrimVal (Reserved o-lt) lt))
  (define signature '(NFn (Int Int) Bool () ()))
  (check-equal? (core-check-row (annotate-core prim) '() '() signature)
                '())
  (check-true (core-check (annotate-core prim) '() '() signature '())))

;; 分類の 3 判定のうち no-recursion? は Recur の有無だけを見るため、spanful でも
;; 偶然一致しうる。投影の有無を分けるのは structural? と guarded? であり、
;; どちらも Eliminate と Apply の内側まで構造を照合する。
(define structural-callables
  '((list-loop-id (NFn ((List Int)) Int () ()))))

(define structural-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> (Apply loop tail))))
          (Apply loop (Construct (List Int) nil))))

(test-case "span.md §7.3: classify は spanful な c を投影して分類する"
  (check-equal? (classify (annotate-core structural-loop) '() structural-callables)
                '(Finite structural))
  (check-equal? (classify (annotate-core structural-loop) '() structural-callables)
                (classify structural-loop '() structural-callables))
  (check-equal? (classify (annotate-core '(Apply (PrimVal (Reserved o-add) add) 1 2))
                          '() '())
                '(Finite no-recursion)))

;; span.md §7 の lowering 行は「出力に span を残さない」である。写しが spanless
;; 版と一致することでこれを固定する。PR の符号化そのものは lowering-test.rkt が
;; 固定しているため、ここでは書き下さない。
(test-case "span.md §7: lower は spanful な core を投影して写す"
  (define core '(Apply (PrimVal (Reserved o-add) add) 1 2))
  (define-values (spanless-status spanless-result) (lower core 'racket-cs))
  (define-values (spanful-status spanful-result)
    (lower (annotate-core core) 'racket-cs))
  (check-eq? spanless-status 'ok)
  (check-eq? spanful-status 'ok)
  (check-equal? spanful-result spanless-result))

(test-case "span.md §7: lower-value も spanful な値を投影して写す"
  (define value '(PrimVal (Reserved o-add) add))
  (define-values (spanless-status spanless-result) (lower-value value 'racket-cs))
  (define-values (spanful-status spanful-result)
    (lower-value (annotate-core value) 'racket-cs))
  (check-eq? spanless-status 'ok)
  (check-eq? spanful-status 'ok)
  (check-equal? spanful-result spanless-result))

;; span.md §7.3: 型の位置の包みは、境界検査より前に compat? 自身が落とす。
(define wrapped-int '(#:ty Int (#:span #:synthetic 0 0)))

(test-case "span.md §7.3: compat? は型の位置の包みを自身の error で落とす"
  (check-exn #rx"^compat\\?"
             (lambda () (compat? wrapped-int 'Int)))
  (check-exn #rx"^compat\\?"
             (lambda () (compat? 'Int wrapped-int)))
  ;; Never は全型と互換だが、短絡より前に包みを落とす。
  (check-exn #rx"^compat\\?"
             (lambda () (compat? 'Never wrapped-int)))
  (check-exn #rx"^compat\\?"
             (lambda ()
               (compat? `(Record ((a ,wrapped-int imm)))
                        '(Record ((a Int imm)))))))

(test-case "span.md §7.3: compat? の義務も型面の fail-closed を保つ"
  ;; 義務の側は proposition-equiv? 経由で normalize-proposition が落とす。
  (check-exn #rx"^normalize-proposition"
             (lambda ()
               (compat? `(NFn () Int () (,wrapped-int))
                        `(NFn () Int () (,wrapped-int))))))

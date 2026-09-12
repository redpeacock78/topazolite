#lang racket

(require rackunit
         racket/match
         "../typing.rkt"
         "../elaborate.rkt"
         "../diagnostic.rkt"
         "../borrow.rkt"
         "../region.rkt")

;; SCP-001。let binding は既定で immutable であり、再代入には mut を要求する。
;; 呼出し口は owned-narrowing-test.rkt:39-49 と同じ 3 つである。

;; 失敗した判定の key を取り出す。type-of/raw の失敗は
;; (list 'fail key node details ...) の形である。
(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

;; 診断 code を取り出す。core-type-of/diagnostic は Diagnostic を返す。
(define (code-of core [environment '()])
  (diagnostic-id
   (core-type-of/diagnostic core '() '() environment (empty-region-ctx))))

;; 成功した判定は (list type row) を返す。
(define (type-row-of core [environment '()])
  (core-type-of core '() '() environment (empty-region-ctx)))

;; elaborate 側の code。owned-narrowing-test.rkt:24-27 と同じ形である。
(define (elaborate-code-of source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define ok-core '(Let (x mut Int) 1 (Reassign x 2)))

;; mut binding への再代入を受理し、Unit を返す。
(check-equal? (first (type-row-of ok-core)) 'Unit)

;; 再代入は Mutation を立てる。
(check-not-false (memq 'Mutation (second (type-row-of ok-core))))

;; const と let の binding へは再代入できない。
(for ([mode (in-list '(const let))])
  (check-equal? (key-of `(Let (x ,mode Int) 1 (Reassign x 2)))
                'immutable-binding
                (format "mode ~a" mode)))

;; 2 要素 entry（束縛様相を持たない環境）へも再代入できない。
(check-equal? (key-of '(Reassign x 2) '((x Int)))
              'immutable-binding)

;; 値の型は type-equiv? で見る。Int の slot へ unit は入らない。
(check-equal? (key-of '(Let (x mut Int) 1 (Reassign x unit)))
              'reassign-type-mismatch)

;; mut binding の型に Owned は置けない。Owned の値は Fn 引数型から作る。
(check-equal?
 (key-of '(Let (x mut (Owned Res)) (Move s) 1)
         '((s (Owned Res))))
 'mut-binding-unsupported-type)

;; 借用も同じ key で落ちる。
(check-equal?
 (key-of '(Let (x mut (Borrowed Int 0)) (Borrow s) 1)
         '((s Int)))
 'mut-binding-unsupported-type)

;; 3 つの key の typing 側の code。
(check-equal? (code-of '(Let (x const Int) 1 (Reassign x 2))) "E-VAR-008")
(check-equal? (code-of '(Let (x mut (Owned Res)) (Move s) 1)
                       '((s (Owned Res))))
              "E-VAR-009")
(check-equal? (code-of '(Let (x mut Int) 1 (Reassign x unit))) "E-VAR-010")
(let ([diagnostic
       (core-type-of/diagnostic '(Let (x mut Int) 1 (Reassign x unit))
                                '() '())])
  (check-equal? (diagnostic-expected diagnostic) 'Int)
  (check-equal? (diagnostic-found diagnostic) 'Unit))

;; elaborate 側も同じ 3 つの key を出す。code は別の 3 本である。
(check-equal? (elaborate-code-of '(Let (x const Int) 1 (Reassign x 2)))
              "E-VAR-011")
(check-equal?
 (elaborate-code-of '(Let (x mut (Owned Res)) (Move s) 1))
 "E-VAR-012")
(check-equal? (elaborate-code-of '(Let (x mut Int) 1 (Reassign x unit)))
              "E-VAR-013")

;; registry の版と 6 本の対応。
(check-equal? diagnostic-registry-version 13)
(check-equal? (diagnostic-code-of 'typing 'immutable-binding) "E-VAR-008")
(check-equal? (diagnostic-code-of 'typing 'mut-binding-unsupported-type)
              "E-VAR-009")
(check-equal? (diagnostic-code-of 'typing 'reassign-type-mismatch)
              "E-VAR-010")
(check-equal? (diagnostic-code-of 'elaborate 'immutable-binding) "E-VAR-011")
(check-equal? (diagnostic-code-of 'elaborate 'mut-binding-unsupported-type)
              "E-VAR-012")
(check-equal? (diagnostic-code-of 'elaborate 'reassign-type-mismatch)
              "E-VAR-013")

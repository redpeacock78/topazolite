#lang racket

(require rackunit
         "../diagnostic.rkt"
         "../elaborate.rkt")

;; 失敗値から Diagnostic を取り出す。
(define (elab-diagnostic term)
  (match (elab term)
    [`(err ,d) d]
    [other (error 'elab-diagnostic "失敗しなかった: ~s" other)]))

(test-case
 "失敗値の中身が schema を満たす Diagnostic である"
 (define d (elab-diagnostic 'no-such-variable))
 (check-pred diagnostic? d)
 (check-true (diagnostic-valid? d))
 (check-equal? (diagnostic-schema-errors d) '())
 (check-equal? (diagnostic-id d)
               (diagnostic-code-of 'elaborate 'unbound-variable))
 (check-equal? (diagnostic-message d) (diagnostic-title d)))

(test-case
 "details が 1 件なら found にその値が入り expected は #f である"
 (define d (elab-diagnostic 'no-such-variable))
 (check-equal? (diagnostic-found d) 'no-such-variable)
 (check-false (diagnostic-expected d)))

(test-case
 "判断を下した Let 節点の span を取り details は expected と found へ入る"
 (define let-span '(#:span src 0 20))
 (define lit-span '(#:span src 12 13))
 (define term
   `(Let ,let-span ((#:bind x ,let-span) let (#:ty Bool ,let-span))
         (#:lit 1 ,lit-span)
         (#:var x ,let-span)))
 (define d (elab-diagnostic term))
 (check-equal? (diagnostic-id d)
               (diagnostic-code-of 'elaborate 'type-mismatch))
 ;; 束縛式の span ではない。
 (check-equal? (diagnostic-primary-span d) let-span)
 ;; expected は宣言した型、found は棄却された実測型である。
 (check-equal? (diagnostic-expected d) 'Bool)
 (check-equal? (diagnostic-found d) 'Int))

(test-case
 "invalid-obligation は最近傍の包みの span を取る"
 (define ty-span '(#:span src 4 40))
 ;; NFn の obligations に、判定表が引き当てない (Prop id) を置く。
 (define term
   `(Let (#:span src 0 60)
         ((#:bind f (#:span src 4 5)) let
          (#:ty (NFn (Int) Int () ((Prop no-such-validator))) ,ty-span))
         (#:lit 1 (#:span src 44 45))
         (#:var f (#:span src 50 51))))
 (define d (elab-diagnostic term))
 (check-equal? (diagnostic-id d)
               (diagnostic-code-of 'elaborate 'invalid-obligation))
 (check-equal? (diagnostic-primary-span d) ty-span)
 (check-equal? (diagnostic-found d) '(Prop no-such-validator)))

(test-case
 "invalid-proposition も同じ最近傍の包みの span を取る"
 (define ty-span '(#:span src 4 30))
 ;; Refined の proposition に同じ値を置く。
 (define term
   `(Let (#:span src 0 40)
         ((#:bind x (#:span src 4 5)) let
          (#:ty (Refined Int (Prop no-such-validator)) ,ty-span))
         (#:lit 1 (#:span src 34 35))
         (#:var x (#:span src 36 37))))
 (define d (elab-diagnostic term))
 (check-equal? (diagnostic-id d)
               (diagnostic-code-of 'elaborate 'invalid-proposition))
 (check-equal? (diagnostic-primary-span d) ty-span)
 (check-equal? (diagnostic-found d) '(Prop no-such-validator)))

;; [REQ: DIA-003] Phase 0 の producer は長さ 1 の source-chain を出す（spec §15）
(test-case
 "elaborate の source-chain は長さ 1 で sourceId が kind を決める"
 (define let-span '(#:span src 0 20))
 (define lit-span '(#:span src 12 13))
 (define spanful
   `(Let ,let-span ((#:bind x ,let-span) let (#:ty Bool ,let-span))
         (#:lit 1 ,lit-span)
         (#:var x ,let-span)))
 (define d (elab-diagnostic spanful))
 (check-equal? (diagnostic-source-chain d)
               (list (list 'surface 'verbatim let-span)))
 (define s (elab-diagnostic 'no-such-variable))
 (check-equal? (diagnostic-primary-span s) '(#:span #:synthetic 0 0))
 (check-equal? (diagnostic-source-chain s)
               (list (list 'surface 'synthetic-span
                           '(#:span #:synthetic 0 0)))))

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

;; elaborate の例外表 5 key について expected と found の分配を固定する。
;; typing 側の typing-span-test.rkt の distribution-table と同型である。
;; 期待値は現行実装の観測値であり、producer の引数順を変えても変わらない。
(define elaborate-distribution-table
  (list
   (list 'type-mismatch
         `(Let (#:span src 0 20)
               ((#:bind x (#:span src 4 5)) let (#:ty Bool (#:span src 8 12)))
               (#:lit 1 (#:span src 14 15))
               (#:var x (#:span src 16 17)))
         'Bool 'Int)
   (list 'arity-mismatch
         '(Apply (Fn ((x Int)) Int () x) 1 2)
         1 2)
   (list 'constructor-type-mismatch
         '(Fn () (List Int) () (Construct bogus))
         '(List Int) 'bogus)
   (list 'undeclared-function-effect
         '(Fn () Unit () (Yield 1 unit))
         '() '((Yield Int)))
   (list 'undeclared-recur-effect
         '(Recur loop ((xs (List Int))) Unit ()
                 (Yield 1 (Apply loop (Construct nil (Types Int))))
                 (Apply loop (Construct nil (Types Int))))
         '() '((Yield Int)))))

(test-case
 "elaborate の例外表 5 key の expected と found の分配"
 (for ([entry (in-list elaborate-distribution-table)])
   (match-define (list key term expected found) entry)
   (define d (elab-diagnostic term))
   ;; 意図した key へ到達したことを先に確かめる。
   ;; 別の key の Diagnostic が返ると expected/found の照合が無意味になる。
   (check-equal? (diagnostic-id d) (diagnostic-code-of 'elaborate key))
   (check-equal? (diagnostic-expected d) expected)
   (check-equal? (diagnostic-found d) found)
   (check-not-equal? expected found
                     (format "~a の expected と found は異なる" key))))

;; 例外表の allowlist の外にある key は、details が 2 件でも
;; expected/actual の対として扱わない。
;; allowlist を外して素の 2 要素照合へ畳むと、Box が expected へ入り
;; この試験が落ちる。
(test-case
 "表に無い key の details 2 件は found の list へ入る"
 (define d
   (elab-diagnostic
    '(LetType Box (TypeMake List) (Fn ((x Box)) Int () x))))
 (check-equal? (diagnostic-id d)
               (diagnostic-code-of 'elaborate 'unsaturated-type))
 (check-false (diagnostic-expected d))
 ;; 第 1 要素は型構成子の名前、第 2 要素はその kind である。
 ;; どちらも「期待した型」ではない。
 (check-equal? (diagnostic-found d) '(Box (Type -> Type))))

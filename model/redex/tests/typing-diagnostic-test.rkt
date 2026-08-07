#lang racket

(require rackunit
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../typing.rkt")

;; [REQ: DIA-001] typing の Diagnostic 生成（diagnostic.md §7、§12）

(define empty '())

(test-case "成功する入力では core-type-of と同じ値を返す"
  (check-equal?
   (core-type-of/diagnostic (term (PrimVal (Reserved o-lt) lt)) empty empty)
   (term ((NFn (Int Int) Bool () ()) ())))
  ;; 成功値は list であり struct ではないため diagnostic? で判別できる。
  (check-false
   (diagnostic? (core-type-of/diagnostic (term (PrimVal (Reserved o-lt) lt))
                                         empty
                                         empty))))

(test-case "失敗する入力では E-TYP-001 の Diagnostic を返す"
  (define d (core-type-of/diagnostic (term x) empty empty))
  (check-true (diagnostic? d))
  (check-equal? (diagnostic-id d) (diagnostic-code-of 'typing 'ill-typed))
  (check-true (diagnostic-valid? d))
  ;; E-TYP-001 は粗い受け皿であり、expected と found を埋めない（spec §12）。
  (check-false (diagnostic-expected d))
  (check-false (diagnostic-found d)))

(test-case "primary-span は入力 Core 項の根から取る"
  ;; 根は #:var なので span は第 3 要素にある。
  (define d (core-type-of/diagnostic '(#:var x (#:span src 5 9)) empty empty))
  (check-equal? (diagnostic-primary-span d) '(#:span src 5 9)))

(test-case "失敗の原因が内側にあっても primary-span は根を指す"
  ;; y が未束縛なので型検査は失敗する。infer は棄却した部分項を持たないため、
  ;; 根の span を使う（spec §12 と §13）。内側の span を返す実装ならここで落ちる。
  (define core
    '(Apply (#:span src 0 20)
            (PrimVal (#:span src 1 4) (Reserved o-add) add)
            (#:var y (#:span src 10 11))
            (#:lit 2 (#:span src 12 13))))
  (define d (core-type-of/diagnostic core empty empty))
  (check-true (diagnostic? d))
  (check-equal? (diagnostic-primary-span d) '(#:span src 0 20)))

(test-case "spanless な入力では synthetic fallback を使う"
  ;; annotate-core は根へ (#:span #:synthetic 0 0) を割り当てるため、
  ;; fallback との区別が付かない。spanless な項で検査する。
  (define d (core-type-of/diagnostic (term x) empty empty))
  (check-equal? (diagnostic-primary-span d) '(#:span #:synthetic 0 0)))

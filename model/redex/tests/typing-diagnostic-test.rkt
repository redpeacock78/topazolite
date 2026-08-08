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

(test-case "未束縛変数は E-VAR-006 の Diagnostic を返す"
  (define d (core-type-of/diagnostic (term x) empty empty))
  (check-true (diagnostic? d))
  (check-equal? (diagnostic-id d) (diagnostic-code-of 'typing 'unbound-variable))
  (check-true (diagnostic-valid? d))
  ;; この診断では expected と found を埋めない。
  (check-false (diagnostic-expected d))
  (check-false (diagnostic-found d)))

(test-case "棄却節点が根なら primary-span は根を指す"
  ;; 根は #:var なので span は第 3 要素にある。
  (define d (core-type-of/diagnostic '(#:var x (#:span src 5 9)) empty empty))
  (check-equal? (diagnostic-primary-span d) '(#:span src 5 9)))

(test-case "失敗の原因が内側なら primary-span は内側を指す"
  ;; y が未束縛なので型検査は失敗する。fail が運ぶ棄却節点の span を使う。
  (define core
    '(Apply (#:span src 0 20)
            (PrimVal (#:span src 1 4) (Reserved o-add) add)
            (#:var y (#:span src 10 11))
            (#:lit 2 (#:span src 12 13))))
  (define d (core-type-of/diagnostic core empty empty))
  (check-true (diagnostic? d))
  (check-equal? (diagnostic-primary-span d) '(#:span src 10 11)))

(test-case "spanless な入力では synthetic fallback を使う"
  ;; annotate-core は根へ (#:span #:synthetic 0 0) を割り当てるため、
  ;; fallback との区別が付かない。spanless な項で検査する。
  (define d (core-type-of/diagnostic (term x) empty empty))
  (check-equal? (diagnostic-primary-span d) '(#:span #:synthetic 0 0)))

(test-case "入口検査の失敗は細分類した Diagnostic を返す"
  (define d (core-type-of/diagnostic '(NotACoreForm) empty empty))
  (check-equal? (diagnostic-id d) "E-SYN-004")
  (check-eq? (diagnostic-category d) 'SYN))

(test-case "不正な callable 表は typing の入口 key になる"
  (define d (core-type-of/diagnostic 1 empty 'not-a-table))
  (check-equal? (diagnostic-id d) "E-TYP-018")
  (check-equal? (diagnostic-found d) 'not-a-table))

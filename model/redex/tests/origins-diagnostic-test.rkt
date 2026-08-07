#lang racket

(require rackunit
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../origins.rkt")

;; [REQ: DIA-001] origins の Diagnostic 生成（diagnostic.md §7、§12）

(test-case "origin が正しい項では 'ok を返す"
  (check-equal?
   (verify-origins/diagnostic R0 `(Apply (PrimVal (Reserved o-add) add) 1 2))
   'ok)
  (check-equal?
   (verify-initial-origins/diagnostic R0 `(Apply (PrimVal (Reserved o-add) add) 1 2))
   'ok))

(test-case "偽装した origin では E-ORG-001 の Diagnostic を返す"
  (define subject `(PrimVal (#:span src 4 7) (Reserved o-add) sub))
  (define d (verify-origins/diagnostic R0 subject))
  (check-true (diagnostic? d))
  (check-equal? (diagnostic-id d) (diagnostic-code-of 'origins 'forged))
  (check-true (diagnostic-valid? d))
  (check-equal? (diagnostic-primary-span d) '(#:span src 4 7))
  ;; found には棄却の対象になった部分項をそのまま入れる（spec §12）。
  (check-equal? (diagnostic-found d) subject)
  (check-false (diagnostic-expected d)))

(test-case "primary-span は根ではなく偽装した部分項を指す"
  ;; typing と違い origins は棄却した部分項を持っているため、根へ丸めない。
  ;; 根の span を返す実装ならここで落ちる。
  (define subject `(PrimVal (#:span src 10 13) (Reserved o-add) sub))
  (define core
    `(Apply (#:span src 0 20)
            ,subject
            (#:lit 1 (#:span src 14 15))
            (#:lit 2 (#:span src 16 17))))
  (define d (verify-origins/diagnostic R0 core))
  (check-equal? (diagnostic-primary-span d) '(#:span src 10 13))
  (check-equal? (diagnostic-found d) subject))

(test-case "spanless な部分項では synthetic fallback を使う"
  (define d (verify-origins/diagnostic R0 `(PrimVal (Reserved o-add) sub)))
  (check-equal? (diagnostic-primary-span d) '(#:span #:synthetic 0 0))
  (check-equal? (diagnostic-found d) `(PrimVal (Reserved o-add) sub)))

(test-case "初期成果物の層の違反も同じ E-ORG-001 になる"
  ;; initial-layer-violation の経路である。verify-origins では 'ok になる。
  (define subject `(UVal (#:span src 3 8) (#:lit 1 (#:span src 5 6))))
  (check-equal? (verify-origins/diagnostic R0 subject) 'ok)
  (define d (verify-initial-origins/diagnostic R0 subject))
  (check-true (diagnostic? d))
  (check-equal? (diagnostic-id d) (diagnostic-code-of 'origins 'forged))
  (check-equal? (diagnostic-primary-span d) '(#:span src 3 8))
  (check-equal? (diagnostic-found d) subject))

(test-case "metafunction 側の返り値は変わらない"
  ;; adapter を足しても既存の 74 箇所の assertion が指す形は保つ。
  (define subject `(PrimVal (Reserved o-add) sub))
  (check-equal? (term (verify-origins ,R0 ,subject)) `(forged ,subject))
  (check-equal? (term (verify-initial-origins ,R0 ,subject)) `(forged ,subject)))

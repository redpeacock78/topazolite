#lang racket

(require rackunit
         redex/reduction-semantics
         "../span-core.rkt")

(test-case "CanonicalSpan は sourceId と 2 つの非負 byte offset を持つ"
  (check-true (redex-match? Span s (term (#:span main.tz 0 0))))
  (check-true (redex-match? Span s (term (#:span main.tz 3 17))))
  (check-true (redex-match? Span s (term (#:span #:synthetic 0 0)))))

(test-case "byte offset は非負の整数に限る"
  (check-false (redex-match? Span s (term (#:span main.tz -1 3))))
  (check-false (redex-match? Span s (term (#:span main.tz 0 1.5))))
  (check-false (redex-match? Span s (term (#:span main.tz 0)))))

(test-case "sourceId は記号か予約 keyword に限る"
  (check-false (redex-match? Span s (term (#:span "main.tz" 0 3))))
  (check-false (redex-match? Span s (term (#:span 7 0 3))))
  ;; 予約でない keyword は sourceId にならない。
  (check-false (redex-match? Span s (term (#:span #:other 0 3)))))

(test-case "span-ok? は startByte <= endByte を要求する"
  (check-true (span-ok? (term (#:span main.tz 3 17))))
  ;; 空 span は許す。
  (check-true (span-ok? (term (#:span main.tz 5 5))))
  (check-false (span-ok? (term (#:span main.tz 17 3))))
  ;; 文法に合わない項は span-ok? も偽である。
  (check-false (span-ok? (term (#:span main.tz -1 3))))
  (check-false (span-ok? (term (Apply 1 2)))))

(test-case "span-of は節点の形ごとに span の位置を選ぶ"
  ;; #:var と #:lit は span が第 3 要素、それ以外の節点は第 2 要素である。
  (check-equal? (span-of '(#:var x (#:span src 5 9))) '(#:span src 5 9))
  (check-equal? (span-of '(#:lit 1 (#:span src 5 9))) '(#:span src 5 9))
  (check-equal? (span-of '(Apply (#:span src 0 20) (#:var f (#:span src 1 2))))
                '(#:span src 0 20))
  ;; G2+ の Core 節点にも同じ 2 つの形が当てはまる。
  (check-equal? (span-of '(PrimVal (#:span src 3 7) (Reserved o-add) add))
                '(#:span src 3 7))
  (check-exn exn:fail? (lambda () (span-of '(Apply 1 2)))))

(test-case "entry-span は span を取れないときだけ synthetic へ落ちる"
  (check-equal? (entry-span '(Apply (#:span src 0 20) (#:var f (#:span src 1 2))))
                '(#:span src 0 20))
  ;; spanless な項では span-of が error を出すため fallback を使う。
  (check-equal? (entry-span '(Apply 1 2)) '(#:span #:synthetic 0 0))
  ;; 文法に合う形でも startByte > endByte なら span-ok? が偽になり fallback へ落ちる。
  (check-equal? (entry-span '(Apply (#:span src 20 0) 1))
                '(#:span #:synthetic 0 0)))

(check-equal? (peel-node '(Drop (#:span src 3 7) 1)) '(Drop 1))
(check-equal? (peel-node '(#:var x (#:span src 0 1))) 'x)
(check-equal? (peel-node '(Drop 1)) '(Drop 1))
(check-equal? (peel-ty '(#:ty Int (#:span src 0 3))) 'Int)
(check-equal? (peel-bind '(#:bind x (#:span src 0 1))) 'x)
(check-equal? (peel-lbl '(#:lbl a (#:span src 0 1))) 'a)
(check-equal? (peel-ef '(#:ef (Own) (#:span src 0 3))) '(Own))
(check-equal? (branch-span '((#:span src 1 9) K () -> 1)) '(#:span src 1 9))
(check-equal? (peel-branch '((#:span src 1 9) K () -> 1)) '(K () -> 1))
(check-equal? (wrapper-span '(#:ty Int (#:span src 0 3))) '(#:span src 0 3))

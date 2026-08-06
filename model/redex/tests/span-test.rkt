#lang racket

(require rackunit
         redex/reduction-semantics
         "../span.rkt")

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

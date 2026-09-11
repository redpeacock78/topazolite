#lang racket

(require rackunit
         redex/reduction-semantics
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

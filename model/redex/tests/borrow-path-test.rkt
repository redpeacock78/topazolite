#lang racket

(require rackunit
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../borrow.rkt")

;; 借用の値は root place と field path の対を持つ。
;; 空の列が root を指す。root を表す特別な記号は無い。
(check-true (redex-match? G2m v (term (BorrowRef 1 () (RVar 0)))))
(check-true (redex-match? G2m v (term (BorrowRef 1 (a b) (RVar 0)))))
(check-true (redex-match? G2m v (term (BorrowMutRef 1 (a) (RVar 0)))))
;; 旧い 2 引数の形はもう値でない。
(check-false (redex-match? G2m v (term (BorrowRef 1 (RVar 0)))))

;; 接頭辞の関係。
(check-true (path-prefix? '() '()))
(check-true (path-prefix? '() '(a b)))
(check-true (path-prefix? '(a) '(a b)))
(check-false (path-prefix? '(a b) '(a)))
(check-false (path-prefix? '(a) '(b)))

;; 重なりの規則。root が同じで一方が他方の接頭辞のときだけ重なる。
(check-true (capability-overlap? 1 '() 1 '(a)))
(check-true (capability-overlap? 1 '(a) 1 '(a b)))
(check-true (capability-overlap? 1 '(a) 1 '(a)))
;; 兄弟 field は重ならない。
(check-false (capability-overlap? 1 '(a) 1 '(b)))
;; root が違えば path によらず重ならない。
(check-false (capability-overlap? 1 '() 2 '()))
(check-false (capability-overlap? 1 '(a) 2 '(a)))

;; spec §10 の不変性。両方が空の path のとき、判定は designator の一致に一致する。
;; G5b までの要求はすべてこの形なので、既存の受理と拒否が変わらない。
(check-true (capability-overlap? 1 '() 1 '()))
(check-false (capability-overlap? 1 '() 2 '()))

#lang racket/base

(require rackunit
         "../search.rkt"
         "../traits.rkt")

(test-case "COH-001: 正典の系譜表は検査を通る"
  (check-true (scope-genealogy-ok?)))

(test-case "COH-001: scope-ancestors は自身から根までを返す"
  (check-equal? (scope-ancestors 'root) '(root))
  (check-equal? (scope-ancestors 's-kernel) '(s-kernel root))
  (check-equal? (scope-ancestors 's-user) '(s-user root)))

(test-case "COH-001: 表に無い scope は親を持たないものとして扱う"
  ;; 呼び出し側が組み立てた scope 識別子は表に無いことがある。
  (check-equal? (scope-ancestors 'deep) '(deep)))

(test-case "COH-001: 可視性は祖先到達で決まる"
  ;; root は常に可視である。子は自身を含む系譜からだけ可視になる。
  (check-true (scope-visible? 'root '(root)))
  (check-false (scope-visible? 's-kernel '(root)))
  (check-false (scope-visible? 's-user '(root)))
  (check-true (scope-visible? 's-user '(root s-user)))
  (check-true (scope-visible? 'root '(s-user)))
  (check-false (scope-visible? 'deep '(root))))

(test-case "COH-001: 壊れた系譜表は拒否される"
  ;; 親が表に無い。
  (check-false (scope-genealogy-ok? '((root #f) (s-a unknown-parent))
                                    '() '()))
  ;; 根がない。
  (check-false (scope-genealogy-ok? '((s-a s-b) (s-b s-a)) '() '()))
  ;; 根が二つある。
  (check-false (scope-genealogy-ok? '((root #f) (other #f)) '() '()))
  ;; sid が重複する。
  (check-false (scope-genealogy-ok? '((root #f) (root #f)) '() '()))
  ;; 循環がある。
  (check-false (scope-genealogy-ok? '((root #f) (s-a s-b) (s-b s-a))
                                    '() '())))

(test-case "COH-001: 表に無い scope を使う trait 行と impl 行は拒否される"
  (check-false
   (scope-genealogy-ok? '((root #f))
                        (list (list 'o-t 'T 's-missing '()))
                        '()))
  (check-false
   (scope-genealogy-ok? '((root #f))
                        '()
                        (list (list 'o-i 'i 'impl 'T 'Int 's-missing)))))

(test-case "COH-001: 出力 trait の生成 scope が不可視なら合成候補は立たない"
  ;; SizableTaggable の生成 scope は s-kernel である。成分は Sizable Int
  ;; （対象型 scope root）と Taggable Int（対象型 scope s-user）であり、
  ;; (root s-user) からはどちらも可視かつ coherent になる。動いているのは
  ;; 出力 trait の生成 scope の可視性だけである。
  (define goal (make-goal '(Implements Int SizableTaggable)))
  (check-equal? (length (project-goal Γ-pc0 '(root s-user) goal)) 0)
  ;; 成分が両方とも可視であることを、成分ごとの goal で確かめる。
  (check-equal? (length (project-goal Γ-pc0 '(root s-user)
                                      (make-goal '(Implements Int Sizable))))
                1)
  (check-equal? (length (project-goal Γ-pc0 '(root s-user)
                                      (make-goal '(Implements Int Taggable))))
                1)
  ;; 生成 scope を含む系譜からは合成候補が立つ。連言項が落としているのが
  ;; 出力 scope であることの対照である。
  (check-equal? (length (project-goal Γ-pc0 '(root s-kernel s-user) goal)) 1))

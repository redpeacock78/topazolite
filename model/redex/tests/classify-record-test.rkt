#lang racket
(require rackunit "../classify.rkt")

(define structural-callables
  '((list-loop-id (NFn ((List Int)) Int () ()))))

; bmode 付き Let（3 要素 binding）が再帰呼び出しを包んでも structural を保つ。
; walker の bmode Let 分岐が無いと (Let (r const Int) ...) が fallthrough し Unknown になる。
(define let-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Let (r const Int) (Apply loop tail) r))))
          (Apply loop (Construct (List Int) nil))))
(check-equal? (classify let-loop '() structural-callables) '(Finite structural))

; Rec は record リテラルであり productivity guard ではない（設計文書 §9.3 で codex 確定）。
; よって Rec／Proj で再帰呼び出しを包んでも productivity は変わらず、構造再帰として (Finite structural)。
; walker に Rec／Proj 分岐が無いと fallthrough し Unknown へ誤分類する。
(define rec-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Proj (Rec ((r imm (Apply loop tail)))) r))))
          (Apply loop (Construct (List Int) nil))))
(check-equal? (classify rec-loop '() structural-callables) '(Finite structural))

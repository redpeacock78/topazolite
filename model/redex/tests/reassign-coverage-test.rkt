#lang racket

(require rackunit
         "../borrow-oracle.rkt"
         "../classify.rkt"
         "../lowering.rkt"
         "../diagnostic.rkt")

;; spec §6.7。classify は Reassign の節を持たない。既定節へ落ちるため
;; Reassign の内側の自己呼出しは構造的下降として見えず Unknown になる。
;; Assign も同じ扱いである。
(define mut-callables '((mut-loop-id (NFn (Int) Int () ()))))

(check-equal?
 (classify '(Recur mut-loop-id loop (n)
                   (Reassign x (Apply loop n))
                   (Apply loop 1))
           '() mut-callables)
 'Unknown)

;; spec §9.8。backend-matrix の対応表に Reassign は無い。lower の入口が
;; unknown-core-form（E-LOW-003）で閉じることを固定する。
;; PR 側へ降ろすときはここが最初に落ちる。
(define-values (status result) (lower '(Reassign x 1) 'racket-cs))
(check-eq? status 'capability)
(check-equal? (diagnostic-id result) "E-LOW-003")

;; spec §4.6。R-LetMutB は H/Ω に place を加える置換規則として記録し、
;; R-Reassign は H を書き換えても非置換規則として記録する。
(test-case "mut slot の H 更新と oracle の規則分類が一致する"
  (define let-pre
    '(cfg (Scope () (Let (x mut Int) 1 x)) () () () ()))
  (define let-post
    '(cfg (Scope (0) (MutSlot 0)) ((0 1)) ((0 Available)) () ()))
  (define let-provenance
    (provenance-extend (empty-provenance) 'R-LetMutB let-pre let-post))
  (check-true (provenance? let-provenance))
  (check-equal? (resolve-designator let-provenance 'x) '(0))
  (define reassign-pre
    '(cfg (Reassign (MutSlot 0) 2)
          ((0 1)) ((0 Available)) () ()))
  (define reassign-post
    '(cfg unit ((0 2)) ((0 Available)) () ()))
  (check-equal? (rule-bucket 'R-Reassign) 'non-substituting)
  (check-true
   (provenance?
    (provenance-extend (empty-provenance)
                       'R-Reassign reassign-pre reassign-post))))

#lang racket
(require rackunit racket/list "../search.rkt" "../origins.rkt")

(define PT  '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define PT2 '(ProofRep (Reserved o-type-narrative-b) TypeNarrativeCap))
(define cT  '(Candidate (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
                        typeNarrativeCap root default ()))
(define cT2 '(Candidate (ProofRep (Reserved o-type-narrative-b) TypeNarrativeCap)
                        other root default ()))
(define goalT (make-goal 'TypeNarrativeCap))

;; PSR-001（順序非依存）: 候補環境を並べ替えても SR は不変。
(test-case "resolve-candidates は順序非依存"
  (define base (list cT cT2))
  (define srs (map (lambda (p) (resolve-candidates goalT p)) (permutations base)))
  (check-true (>= (length srs) 2))                 ; 実際に複数順列を通した
  (check-true (apply equal? srs)))

;; PSR-001（二軸独立）: χ の class 軸と resolve-candidates の SR 軸は独立。
;; 同じ (goal, Σ) で χ を変えても SR は不変、χ を固定して Σ を変えても class は不変。
(test-case "class と SR は互いを導出しない"
  (define chiF (make-classifier (list (cons goalT 'Finite))))
  (define chiU (make-classifier (list (cons goalT 'Unknown))))
  (define sigma (list cT))
  (define finite-view  (list (chiF goalT Γ-pc0) (resolve-candidates goalT sigma)))
  (define unknown-view (list (chiU goalT Γ-pc0) (resolve-candidates goalT sigma)))
  (check-not-equal? (first finite-view) (first unknown-view))  ; class は Finite/Unknown で異なる
  (check-equal? (second finite-view) (second unknown-view))    ; SR は χ 非依存で同一
  (check-equal? (chiF goalT Γ-pc0) (chiF goalT '()))           ; χ 固定なら Σ 差でも class 不変
  ; SR 軸は Σ に追従する（χ ではなく Σ が SR を動かす）
  (check-not-equal? (resolve-candidates goalT sigma)
                    (resolve-candidates goalT '())))

;; wf-Σ の要求: valid な Σ は true、forge origin・命題不一致を含む Σ は wf-Σ? が false。
(test-case "wf-Σ? は不整合な Σ を弾く"
  (check-true (wf-Σ? (list cT) goalT))                              ; valid Σ
  (check-false (wf-Σ?                                               ; forge origin を含む
                (list cT '(Candidate (ProofRep (Reserved o-bogus) TypeNarrativeCap)
                                     x root default ()))
                goalT))
  (check-false (wf-Σ?                                               ; 命題不一致を含む
                (list cT '(Candidate (ProofRep (Reserved o-any) ValidNarrativeTrait)
                                     y root default ()))
                goalT))
  (check-false (scope-visible? 'deep '(root))))                     ; 不可視 scope（補助）

;; PSR-003 artifact 境界: 手書き artifact が Unknown を Finite と偽っても、
;; trusted な χ が Unknown を返すため discharge? は充足を認めない。
(test-case "artifact 境界で Unknown 拒否が保たれる"
  (define chiU (make-classifier (list (cons goalT 'Unknown))))
  (check-false (discharge? Γ-pc0 chiU default-oracle goalT))
  ; 既定の Γ_pc⁰ からの再導出は決定的で、同じ判定を返す
  (check-equal? (discharge? Γ-pc0 default-classifier default-oracle goalT)
                (discharge? Γ-pc0 default-classifier default-oracle goalT)))

#lang racket

(require racket/set
         rackunit
         redex/reduction-semantics
         "../machine.rkt")

(provide rule-correspondence
         target-rule-names)

;; spec §5.4 の対応表の源側。値は写し先の規則名で、#f は目標側に規則を持たない
;; ことを表す。4 組が 1 本へ畳まれ R-Discharge が消えるので、値の相異なる集合は
;; 20 本になる。この表と machine.rkt の実物がずれたら下の検査が落ちる。
(define rule-correspondence
  '((R-Delta        . R-PR-Prim)
    (R-Beta         . R-PR-App)
    (R-CurryVal     . R-PR-Curry)
    (R-ApplyCurry   . R-PR-Curry)
    (R-Let          . R-PR-Let)
    (R-LetB         . R-PR-Let)
    (R-LetOwned     . R-PR-LetOwned)
    (R-LetOwnedB    . R-PR-LetOwned)
    (R-Eliminate    . R-PR-Match)
    (R-Proj         . R-PR-Proj)
    (R-Discharge    . #f)
    (R-RecurBind    . R-PR-Letrec)
    (R-RecurUnfold  . R-PR-Letrec)
    (R-Move         . R-PR-Move)
    (R-MoveError    . R-PR-MoveError)
    (R-Drop         . R-PR-Drop)
    (R-Yield        . R-PR-Yield)
    (R-Suspend      . R-PR-Suspend)
    (R-ScopeValue   . R-PR-ScopeValue)
    (R-ScopeAbort   . R-PR-ScopeAbort)
    (R-ScopeError   . R-PR-ScopeError)
    (R-HandleValue  . R-PR-InstallValue)
    (R-HandleReturn . R-PR-InstallEffect)
    (R-HandleSkip   . R-PR-InstallSkip)
    (R-HandleError  . R-PR-InstallError)))

(define target-rule-names
  (list->set (filter values (map cdr rule-correspondence))))

(define g1-rule-names
  (list->set (reduction-relation->rule-names -->g1/rules)))

(define g2-rule-names
  (list->set (reduction-relation->rule-names -->g2/rules)))

(test-case
 "-->g1/rules declares 21 rules"
 (check-equal? (set-count g1-rule-names) 21))

(test-case
 "-->g2/rules adds exactly four names to -->g1/rules"
 ;; 同名の上書きは名前集合を増やさない。増えるのは 4 本だけである。
 (check-equal? (set-subtract g2-rule-names g1-rule-names)
               (set 'R-Proj 'R-Discharge 'R-LetB 'R-LetOwnedB))
 (check-equal? (set-subtract g1-rule-names g2-rule-names) (set))
 (check-equal? (set-count g2-rule-names) 25))

(test-case
 "the correspondence table covers exactly the source rule names"
 (check-equal? (list->set (map car rule-correspondence)) g2-rule-names)
 (check-equal? (length rule-correspondence) 25))

(test-case
 "the target side has 20 rules"
 (check-equal? (set-count target-rule-names) 20))

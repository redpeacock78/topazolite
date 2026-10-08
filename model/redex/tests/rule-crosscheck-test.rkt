#lang racket

(require racket/set
         rackunit
         redex/reduction-semantics
         "../machine.rkt")

;; [REQ: BAK-001] 源と目標の規則名の対応（backend-matrix.md §4）

(provide rule-correspondence
         target-support-rule-names
         target-rule-names)

;; backend-matrix.md §4 の対応表の源側。値は写し先の規則名で、
;; #f は目標側に規則を持たないことを表す。
;; Curry、Recur、Let、LetOwned、RecRewrite の 5 組は目標側でそれぞれ 1 本へ畳む。
;; R-Discharge と R-DischargeRemainder には一対一の写し先がない。
;; R-OwnLeaf、各借用 Eliminate、R-RetireValue、R-RetireError、R-RetirePerform、
;; G2m 固有規則は目標側になく、raw pointer の 7 規則も対象外である。
;; この表と machine.rkt の実物がずれたら下の検査が落ちる。
(define rule-correspondence
  '((R-Delta        . R-PR-Prim)
    (R-Beta         . R-PR-App)
    (R-CurryVal     . R-PR-Curry)
    (R-ApplyCurry   . R-PR-Curry)
    (R-Let          . R-PR-Let)
    (R-LetB         . R-PR-Let)
    (R-LetIdentity  . R-PR-Let)
    (R-LetIdentityB . R-PR-Let)
    (R-LetOwned     . R-PR-LetOwned)
    (R-LetOwnedB    . R-PR-LetOwned)
    (R-LetMutB      . #f)
    (R-Eliminate    . R-PR-Match)
    (R-EliminateRef . #f)
    (R-EliminateMutRef . #f)
    (R-UnionInject . #f)
    (R-UnionEliminate . #f)
    (R-UnionEliminateRef . #f)
    (R-UnionEliminateMutRef . #f)
    (R-RecRewrite-Open . R-PR-RecRewrite)
    (R-RecRewrite-Close . R-PR-RecRewrite)
    (R-Proj         . R-PR-Proj)
    (R-ProjOpt      . R-PR-ProjOpt)
    (R-ProjPlace    . R-PR-ProjPlace)
    (R-ProjOptPlace . R-PR-ProjOptPlace)
    (R-Discharge    . #f)
    (R-DischargeRemainder . #f)
    (R-RegionApp    . #f)
    (R-Borrow       . #f)
    (R-BorrowError  . #f)
    (R-BorrowMut    . #f)
    (R-BorrowMutError . #f)
    (R-Reborrow     . #f)
    (R-ProjBorrow   . #f)
    (R-ProjBorrowMut . #f)
    (R-Read         . #f)
    (R-ReadMut      . #f)
    (R-Assign       . #f)
    (R-ReadMutSlot  . #f)
    (R-Reassign     . #f)
    (R-AddressOf    . #f)
    (R-PtrOffset    . #f)
    (R-RawLoad      . #f)
    (R-RawStore     . #f)
    (R-FromRawPtrConst . #f)
    (R-FromRawPtrMut . #f)
    (R-UnsafeExit   . #f)
    (R-RecurBind    . R-PR-Letrec)
    (R-RecurUnfold  . R-PR-Letrec)
    (R-Move         . R-PR-Move)
    (R-MoveError    . R-PR-MoveError)
    (R-OwnLeaf      . #f)
    (R-Drop         . R-PR-Drop)
    (R-Yield        . R-PR-Yield)
    (R-RetireValue  . #f)
    (R-RetireError  . #f)
    (R-RetirePerform . #f)
    (R-Suspend      . R-PR-Suspend)
    (R-ScopeValue   . R-PR-ScopeValue)
    (R-ScopeAbort   . R-PR-ScopeAbort)
    (R-ScopeError   . R-PR-ScopeError)
    (R-HandleValue  . R-PR-InstallValue)
    (R-HandleReturn . R-PR-InstallEffect)
    (R-HandleSkip   . R-PR-InstallSkip)
    (R-HandleError  . R-PR-InstallError)))

(define target-support-rule-names (set 'R-PR-RecRemove))

(define target-rule-names
  (set-union (list->set (filter values (map cdr rule-correspondence)))
             target-support-rule-names))

(define g1-rule-names
  (list->set (reduction-relation->rule-names -->g1/rules)))

(define g2-rule-names
  (list->set (reduction-relation->rule-names -->g2/rules)))

(test-case
 "-->g1/rules declares 26 rules"
 (check-equal? (set-count g1-rule-names) 26))

(test-case
 "-->g2/rules adds exactly thirty-eight names to -->g1/rules"
 ;; R-LetIdentity は G1 と G2 の双方に属するため、差分には含めない。
 (check-equal? (set-subtract g2-rule-names g1-rule-names)
               (set 'R-Proj 'R-ProjOpt 'R-ProjPlace 'R-ProjOptPlace
                    'R-Discharge 'R-DischargeRemainder 'R-LetB
                    'R-LetIdentityB 'R-LetOwnedB
                    'R-LetMutB
                    'R-Borrow 'R-BorrowError 'R-BorrowMut
                    'R-BorrowMutError 'R-Reborrow
                    'R-ProjBorrow 'R-ProjBorrowMut
                    'R-UnionInject 'R-UnionEliminate
                    'R-RecRewrite-Open 'R-RecRewrite-Close
                    'R-UnionEliminateRef 'R-UnionEliminateMutRef
                    'R-Read 'R-ReadMut 'R-Assign 'R-ReadMutSlot 'R-Reassign
                    'R-RegionApp
                    'R-EliminateRef 'R-EliminateMutRef 'R-AddressOf 'R-PtrOffset
                    'R-RawLoad 'R-RawStore 'R-FromRawPtrConst
                    'R-FromRawPtrMut 'R-UnsafeExit))
 (check-equal? (set-subtract g1-rule-names g2-rule-names) (set))
 (check-equal? (set-count g2-rule-names) 64))

(test-case
 "the correspondence table covers exactly the source rule names"
 (check-equal? (list->set (map car rule-correspondence)) g2-rule-names)
 (check-equal? (length rule-correspondence) 64))

(test-case
 "the target side has 25 rules, including one support rule"
 (check-equal? target-support-rule-names (set 'R-PR-RecRemove))
 (check-equal? (set-count target-rule-names) 25))

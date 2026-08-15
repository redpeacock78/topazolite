#lang racket

(require rackunit
         racket/set
         "../typing.rkt"
         "../region.rkt")

;; spec §3.1: typing の走査が張る point の集合と region.rkt の core-points が
;; 張る集合は一致しなければならない。片方だけが節点を数えると、
;; region-at ir point が定義域外で error になる。
;; この Core は型検査が最後まで走る。
;; with-typing は最初の fail で脱出するため、途中で落ちる Core では
;; 走査が全 point を訪れず、集合の一致が空虚に成立しうる。
;; 構築子は schema.rkt の綴り、すなわち some と none である。
;; Let の束縛子は G2 の形であり bmode を伴う。
(define core
  '(Scope ()
     (Let (x const Int) 1
       (Eliminate (Construct (Option Int) some 2)
         ((some (y) -> y)
          (none () -> x))))))

;; 走査が途中で止まっていないことを先に固定する。
;; これが 'ill-typed なら下の集合の一致は空虚である。
;; core-type-of は型だけでなく effect row も返すため、Int と空 row の対になる。
;; Task 1 は Λ の threading だけを変え、既存の返り値契約は変えない。
(check-equal? (core-type-of core '() '()) '(Int ()))

(check-equal? (list->set (typing-visited-points core '() '()))
              (list->set (core-points core)))

;; Discharge は連ねてよい。base へ一度に跳ぶ実装は inner の中間 point を
;; 落とすため、2 層の型検査成功と point 集合の一致を別に固定する。
(define cap-proof
  '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define nested-discharge
  `(Discharge ,cap-proof
     (Discharge ,cap-proof
       (Apply (Lam User cap-id (x) x) 1))))
(define nested-callables
  '((cap-id (NFn (Int) Int () (TypeNarrativeCap TypeNarrativeCap)))))
(check-equal? (core-type-of nested-discharge '() nested-callables)
              '(Int ()))
(check-equal? (list->set
              (typing-visited-points nested-discharge '() nested-callables))
             (list->set (core-points nested-discharge)))

#lang racket
(require rackunit "../typing.rkt" "../search.rkt")

(define left '(Record ((a Int imm) (b String imm))))
(define right '(Record ((a Int imm) (c Bool imm))))
(define mutability-clash '(Record ((a Int mut))))
(define disjoint '(Record ((z Int imm))))

;; RFN-002: merge は共通の field だけを残し、残った field ごとに常在性
;; witness を立てる。
(let-values ([(merged witnesses) (merge-record-types (list left right))])
  (check-equal? merged '(Record ((a Int imm))))
  (check-equal? (map (lambda (binding) (entry-phi (second binding)))
                     witnesses)
                '((Presence a)))
  (check-equal? (map (lambda (binding) (entry-origin (second binding)))
                     witnesses)
                '((Reserved o-merge)))
  ;; W は候補文脈として整合である。
  (check-true (wf-context? witnesses)))

;; 可変性が食い違う field は落ちず、imm へ降格して残る。
(let-values ([(merged witnesses)
              (merge-record-types (list left mutability-clash))])
  (check-equal? merged '(Record ((a Int imm))))
  (check-equal? (map (lambda (binding) (entry-phi (second binding)))
                     witnesses)
                '((Presence a))))

;; 交差が空なら W も空である。共通 label を持たない枝で観測する。
(let-values ([(merged witnesses)
              (merge-record-types (list left disjoint))])
  (check-equal? merged '(Record ()))
  (check-equal? witnesses '()))

;; 単一枝の merge は field をすべて残す。
(let-values ([(merged witnesses) (merge-record-types (list left))])
  (check-equal? merged left)
  (check-equal? (map (lambda (binding) (entry-phi (second binding)))
                     witnesses)
                '((Presence a) (Presence b))))

;; RFN-002: 局所検査。merge が立てた W だけで常在性の義務を充足する。
(check-true
 (merge-witnesses-dischargeable? (list left right) '((Presence a))))
(check-false
 (merge-witnesses-dischargeable? (list left right) '((Presence b))))
(check-false
 (merge-witnesses-dischargeable? (list left right) '((Presence c))))
(check-true
 (merge-witnesses-dischargeable? (list left) '((Presence a) (Presence b))))
;; 義務が空なら常に充足する。
(check-true (merge-witnesses-dischargeable? (list left right) '()))

;; RFN-002: W は型にも成果物にも載らない。merge の結果型は G2c までと同じ。
(check-equal?
 (core-type-of
  '(Eliminate (Construct Bool true)
     ((true () -> (Rec ((a imm 1) (b imm unit))))
      (false () -> (Rec ((a imm 2) (c imm unit))))))
  '() '())
 '((Record ((a Int imm))) ()))

;; RFN-002: 別の merge の witness では充足できない。同じラベルでも merge が
;; 違えば別の W である。
(check-false
 (merge-witnesses-dischargeable?
  (list '(Record ((x Int imm))) '(Record ((x Int imm))))
  '((Presence a))))

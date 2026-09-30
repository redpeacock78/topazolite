#lang racket

(require rackunit "../rows.rkt" "../compat.rkt")

(define r1 '((a Int imm) (b Bool mut)))
(define r2 '((c String imm)))
(define r3 '((b Bool mut) (a Int imm)))  ; r1 と順序違い
(define ro '((a Int imm) (b Bool mut opt)))

(check-equal? (field-presence '(a Int imm)) 'req)
(check-equal? (field-presence '(b Bool mut opt)) 'opt)
(check-true (field-optional? '(b Bool mut opt)))
(check-false (field-optional? '(a Int imm)))
(check-equal? (field-with-type '(b Bool mut opt) 'Int) '(b Int mut opt))
(check-equal? (field-row-map-type ro (lambda (type) `(List ,type)))
              '((a (List Int) imm) (b (List Bool) mut opt)))
(check-false (field-row-map-type ro (lambda (_) #f)))

(check-equal? (field-row-lookup r1 'a) '(Int imm))
(check-equal? (field-row-lookup r1 'z) #f)

(check-equal? (field-row-⊕ r1 r2) '((a Int imm) (b Bool mut) (c String imm)))
(check-equal? (field-row-⊕ r1 '((a Int imm))) #f)  ; ラベル重複

(check-equal? (field-row-residual r1 '((a Int imm))) '((b Bool mut)))
(check-equal? (field-row-residual r1 r1) '())

(check-true  (field-row-equiv? r1 r3 equal?))            ; 順序独立
(check-false (field-row-equiv? '((a Int imm)) '((a Int imm opt)) equal?))
(check-true  (field-row-equiv? '((a Int imm opt)) '((a Int imm opt)) equal?))
(check-false (field-row-equiv? r1 '((a Int mut)) equal?))  ; 可変性不一致
(check-false (field-row-equiv? r1 '((a Bool imm) (b Bool mut)) equal?))  ; 型不一致

; intersection: 共通ラベルで型一致かつ可変性一致の field のみ残す
(check-equal? (field-row-intersection r1 '((a Int imm) (c String imm)) equal?)
              '((a Int imm)))
(check-equal? (field-row-intersection '((a Int imm) (b Int imm opt))
                                      '((a Int imm opt) (b Int imm opt))
                                      equal?)
              '((b Int imm opt)))
(check-equal? (field-row-intersection r1 '((a Int mut)) equal?) '())  ; 可変性違いは残さない

(check-true  (field-row-unique? r1))
(check-false (field-row-unique? '((a Int imm) (a Bool mut))))

; G2c 回帰: NFn 分岐の変更が record width subsumption を変えない
(check-true  (compat? '(Record ((a Int imm) (b Bool mut))) '(Record ((a Int imm)))))
(check-false (compat? '(Record ((a Int imm))) '(Record ((a Int imm) (b Bool mut)))))

#lang racket

(require rackunit "../type-equiv.rkt")

; definitional equality はラベル集合・field 型・可変性の完全一致（順序独立）
(check-true  (type-equiv? '(Record ((a Int imm) (b Bool mut)))
                          '(Record ((b Bool mut) (a Int imm)))))
(check-false (type-equiv? '(Record ((a Int imm))) '(Record ((a Int mut)))))
(check-false (type-equiv? '(Record ((a Int imm))) '(Record ((a Bool imm)))))
(check-false (type-equiv? '(Record ((a Int imm))) '(Record ((a Int imm opt)))))
(check-true  (type-equiv? '(Record ((a Int imm opt) (b Bool mut)))
                           '(Record ((b Bool mut) (a Int imm opt)))))
(check-equal? (normalize-type '(Record ((b Bool mut) (a Int imm opt))))
              '(Record ((a Int imm opt) (b Bool mut))))
(check-false (equal? (canonical-proposition-key '(FieldType a (Record ((x Int imm)))))
                     (canonical-proposition-key '(FieldType a (Record ((x Int imm opt)))))))
(check-false (proposition-equiv? '(FieldType a (Record ((x Int imm))))
                                 '(FieldType a (Record ((x Int imm opt))))))
(check-false (type-equiv? '(Refined (Record ((x Int imm))) ())
                          '(Refined (Record ((x Int imm opt))) ())))
; width 差は型同値ではない（それは compat? の subsumption）
(check-false (type-equiv? '(Record ((a Int imm) (b Bool imm))) '(Record ((a Int imm)))))
; ネストした Record も再帰一致
(check-true  (type-equiv? '(Record ((a (Record ((x Int imm))) imm)))
                          '(Record ((a (Record ((x Int imm))) imm)))))

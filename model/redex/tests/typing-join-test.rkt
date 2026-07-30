#lang racket/base

(require racket/list
         rackunit
         "../search.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define int-branch '(Record ((a Int imm))))
(define string-branch '(Record ((a String imm))))
(define joined-type (normalize-type '(Union Int String)))

(define (witness-propositions witnesses)
  (map (lambda (binding) (entry-phi (cadr binding))) witnesses))

(test-case "join-types unions distinct types deterministically"
  (check-equal? (join-types 'Int 'String) joined-type)
  (check-equal? (join-types 'String 'Int) joined-type))

(test-case "join-types collapses equivalent types"
  (check-equal? (join-types 'Int 'Int) 'Int)
  (check-equal?
   (join-types '(Record ((a Int imm) (z Int imm)))
               '(Record ((z Int imm) (a Int imm))))
   '(Record ((a Int imm) (z Int imm)))))

(test-case "merge-field joins only immutable field types"
  (check-equal?
   (merge-field '(a Int imm) '(a String imm))
   `(a ,joined-type imm))
  (check-equal?
   (merge-field '(a Int mut) '(a Int mut))
   '(a Int mut))
  (check-false
   (merge-field '(a Int mut) '(a String mut)))
  (check-false
   (merge-field '(a Int imm) '(a String mut))))

(test-case "merge joins colliding immutable fields and emits local witnesses"
  (let-values ([(merged witnesses)
                (merge-record-types (list int-branch string-branch))])
    (check-equal? merged `(Record ((a ,joined-type imm))))
    (check-equal? (map car witnesses)
                  '(presence-a field-type-a-0 field-type-a-1))
    (check-equal? (witness-propositions witnesses)
                  '((Presence a)
                    (FieldType a Int)
                    (FieldType a String)))
    (check-false (check-duplicates (map car witnesses)))
    (check-true (wf-context? witnesses))))

(test-case "merge drops mutable conflicts and mutability mismatches"
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((a Int mut)))
                       '(Record ((a String mut)))))])
    (check-equal? merged '(Record ()))
    (check-equal? witnesses '()))
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((a Int imm)))
                       '(Record ((a Int mut)))))])
    (check-equal? merged '(Record ()))
    (check-equal? witnesses '())))

(test-case "merge keeps equivalent mutable fields"
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((a Int mut)))
                       '(Record ((a Int mut)))))])
    (check-equal? merged '(Record ((a Int mut))))
    (check-equal? (witness-propositions witnesses)
                  '((Presence a)))))

(test-case "fields missing from a branch do not survive merge"
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((a Int imm)))
                       '(Record ((b String imm)))))])
    (check-equal? merged '(Record ()))
    (check-equal? witnesses '())))

(test-case "merge and witness order are independent of branch order"
  (define-values (left-type left-witnesses)
    (merge-record-types (list int-branch string-branch)))
  (define-values (right-type right-witnesses)
    (merge-record-types (list string-branch int-branch)))
  (check-equal? left-type right-type)
  (check-equal? left-witnesses right-witnesses))

(test-case "duplicate branch types do not duplicate FieldType witnesses"
  (define-values (_merged witnesses)
    (merge-record-types (list int-branch string-branch int-branch)))
  (check-equal? (witness-propositions witnesses)
                '((Presence a)
                  (FieldType a Int)
                  (FieldType a String))))

(test-case "FieldType witnesses describe branch types, not Union members"
  (define union-type (normalize-type '(Union Int Bool)))
  (define-values (_merged witnesses)
    (merge-record-types
     (list int-branch
           `(Record ((a ,union-type imm))))))
  (check-equal? (witness-propositions witnesses)
                `((Presence a)
                  (FieldType a ,union-type)
                  (FieldType a Int))))

(test-case "join witnesses discharge only their recorded field types"
  (define types (list int-branch string-branch))
  (check-true
   (merge-witnesses-dischargeable?
    types
    '((Presence a) (FieldType a Int) (FieldType a String))))
  (check-false
   (merge-witnesses-dischargeable?
    types
    '((FieldType a Bool))))
  ;; join 型そのものは branch 型 witness ではない。
  (check-false
   (merge-witnesses-dischargeable?
    types
    `((FieldType a ,joined-type)))))

(test-case "witness binding names follow the declared scheme"
  (check-equal? (presence-binding-name 'a) 'presence-a)
  (check-equal? (field-type-binding-name 'a 0) 'field-type-a-0))

#lang racket/base

(require racket/list
         rackunit
         "../search.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define u1 (normalize-type '(Union Int Bool)))
(define u2 (normalize-type '(Union String Bool)))
(define tagged-int-branch `(Record ((a ,u1 imm))))
(define tagged-string-branch `(Record ((a ,u2 imm))))
(define tagged-joined-type (normalize-type `(Union ,u1 ,u2)))
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

(test-case "ROW-005: merge-field は異型を可変性を保ったまま join する"
  ;; tag の無い field の型差から Union を合成しない。
  (check-false (merge-field '(a Int imm) '(a String imm)))
  (check-equal?
   (merge-field '(a Int mut) '(a Int mut))
   '(a Int mut))
  (check-false (merge-field '(a Int mut) '(a String mut)))
  ;; 可変性が食い違えば、同型でも imm になる。
  (check-equal?
   (merge-field '(a Int imm) '(a Int mut))
   '(a Int imm))
  (check-false (merge-field '(a Int imm) '(a String mut))))

(test-case "merge joins colliding immutable fields and emits local witnesses"
  (let-values ([(merged witnesses)
   (merge-record-types (list tagged-int-branch tagged-string-branch))])
    (check-equal? merged `(Record ((a ,tagged-joined-type imm))))
    (check-equal? (map car witnesses)
                  '(presence-a field-type-a-0 field-type-a-1))
    (check-equal? (witness-propositions witnesses)
                  `((Presence a)
                    (FieldType a ,u1)
                    (FieldType a ,u2)))
    (check-false (check-duplicates (map car witnesses)))
    (check-true (wf-context? witnesses))))

(test-case "ROW-005: 異型 mut は mut のまま残り、可変性不一致だけが降格する"
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list `(Record ((a ,u1 mut)))
                       `(Record ((a ,u2 mut)))))])
    (check-equal? merged `(Record ((a ,tagged-joined-type mut))))
    (check-equal? (witness-propositions witnesses)
                  `((Presence a)
                    (FieldType a ,u1)
                    (FieldType a ,u2))))
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((a Int imm)))
                       '(Record ((a Int mut)))))])
    (check-equal? merged '(Record ((a Int imm))))
    (check-equal? (witness-propositions witnesses)
                  '((Presence a)))))

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
   (merge-record-types (list tagged-int-branch tagged-string-branch)))
  (define-values (right-type right-witnesses)
    (merge-record-types (list tagged-string-branch tagged-int-branch)))
  (check-equal? left-type right-type)
  (check-equal? left-witnesses right-witnesses))

(test-case "duplicate branch types do not duplicate FieldType witnesses"
  (define-values (merged witnesses)
    (merge-record-types
     (list tagged-int-branch tagged-string-branch tagged-int-branch)))
  (check-equal? merged `(Record ((a ,tagged-joined-type imm))))
  (check-equal? (witness-propositions witnesses)
                `((Presence a)
                  (FieldType a ,u1)
                  (FieldType a ,u2))))

(test-case "FieldType witnesses describe branch types, not Union members"
  (define-values (merged witnesses)
    (merge-record-types
     (list tagged-int-branch tagged-string-branch)))
  (check-equal? merged `(Record ((a ,tagged-joined-type imm))))
  (check-equal? (witness-propositions witnesses)
                `((Presence a)
                  (FieldType a ,u1)
                  (FieldType a ,u2))))

(test-case "join witnesses discharge only their recorded field types"
  (define types (list tagged-int-branch tagged-string-branch))
  (check-true
   (merge-witnesses-dischargeable?
    types
    `((Presence a) (FieldType a ,u1) (FieldType a ,u2))))
  (check-false
   (merge-witnesses-dischargeable?
    types
    '((FieldType a Bool))))
  ;; 合流型そのものは branch 型 witness ではない。
  (check-false
   (merge-witnesses-dischargeable?
    types
    `((FieldType a ,tagged-joined-type)))))

(test-case "witness binding names follow the declared scheme"
  (check-equal? (presence-binding-name 'a) 'presence-a)
  (check-equal? (field-type-binding-name 'a 0) 'field-type-a-0))

(test-case "ROW-005: join できない field は merge 全体を fail-closed にする"
  ;; (Intersection Int Bool) は Record でない交差であり normalize-type が #f を
  ;; 返す。脱落ではなく失敗であることを、返り値の形で観測する。
  (let-values ([(merged witnesses)
                (merge-record-types
                 (list '(Record ((a (Intersection Int Bool) imm)))
                       '(Record ((a Int imm)))))])
    (check-false merged)
    (check-equal? witnesses '())))

(test-case "tag mode: row merge は既存 Union の tag 保存上界を使う"
  (define u1 '(Union Int Bool))
  (define u2 '(Union String Bool))
  (define merged-union (normalize-type `(Union ,u1 ,u2)))
  (parameterize ([current-union-tag-mode #t])
    (check-equal? (merge-field `(a ,u1 imm) `(a ,u2 imm))
                  `(a ,merged-union imm))
    (check-equal? (merge-field `(a ,u1 mut) `(a ,u2 mut))
                  `(a ,merged-union mut))
    (let-values ([(merged witnesses)
                  (merge-record-types
                   (list `(Record ((a ,u1 imm) (left Int imm)))
                         `(Record ((a ,u2 imm) (right Int imm)))))])
      (check-equal? merged `(Record ((a ,merged-union imm))))
      (check-equal? (witness-propositions witnesses)
                    `((Presence a)
                      (FieldType a ,(normalize-type u1))
                      (FieldType a ,(normalize-type u2)))))))

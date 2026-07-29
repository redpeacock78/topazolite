#lang racket/base
(require rackunit "../type-equiv.rkt")

(test-case "union flattens, sorts, dedups, and right-associates"
  (check-equal? (normalize-type '(Union String Int))
                (normalize-type '(Union Int String)))
  (check-equal? (normalize-type '(Union Int Int)) 'Int)
  (check-equal? (normalize-type '(Union Int (Union String Bool)))
                (normalize-type '(Union (Union Int String) Bool))))

(test-case "union dedup compares against the whole retained set, not neighbours"
  ;; A ≡ A' だが外部表現順では A < B < A' になる。
  ;; 隣接比較だけでは A' が残ってしまう。
  (define A  '(Record ((a Int imm) (z Int imm))))
  (define B  '(Record ((m Int imm))))
  (define A2 '(Record ((z Int imm) (a Int imm))))
  (define lhs (normalize-type `(Union ,A (Union ,B ,A2))))
  (define rhs (normalize-type `(Union ,A2 (Union ,B ,A))))
  (check-equal? lhs rhs)
  (check-equal? (length (union-members lhs)) 2))

(test-case "normalize-type is idempotent"
  (for ([t (list '(Union String Int)
                 '(Union Int (Union String Bool))
                 '(Intersection (Record ((a Int imm))) (Record ((b Int imm)))))])
    (define n (normalize-type t))
    (check-equal? (normalize-type n) n)
    (check-true (type-normal? n))))

(test-case "normalization recurses through Untrusted"
  (check-equal? (normalize-type '(Untrusted (Union String Int)))
                (normalize-type '(Untrusted (Union Int String))))
  (check-equal?
   (canonical-proposition-key
    '(Implements (Untrusted (Record ((a Int imm) (z Int imm)))) P))
   (canonical-proposition-key
    '(Implements (Untrusted (Record ((z Int imm) (a Int imm)))) P))))

(test-case "intersection is erased by row composition"
  (check-equal? (normalize-type '(Intersection (Record ((a Int imm)))
                                               (Record ((b Int imm)))))
                '(Record ((a Int imm) (b Int imm)))))

(test-case "colliding intersection fails to normalize"
  (check-false (normalize-type '(Intersection (Record ((a Int imm)))
                                              (Record ((a Bool imm))))))
  (check-false (normalize-type '(Intersection Int String))))

(test-case "canonical-proposition-key quotients type-equiv?"
  ;; effect row の順序と重複、Record の field 順序をまたいで同じ鍵になる。
  (define p1 '(Implements (NFn (Int) Unit (Suspend Partial) ()) Printable))
  (define p2 '(Implements (NFn (Int) Unit (Partial Suspend) ()) Printable))
  (check-equal? (canonical-proposition-key p1) (canonical-proposition-key p2))
  (define q1 '(FieldType f (Record ((a Int imm) (z Int imm)))))
  (define q2 '(FieldType f (Record ((z Int imm) (a Int imm)))))
  (check-equal? (canonical-proposition-key q1) (canonical-proposition-key q2))
  (check-not-equal? (canonical-proposition-key p1)
                    (canonical-proposition-key '(Implements Int Printable))))

(test-case "RequiresBoth is canonicalized by trait-name order"
  (check-equal? (canonical-proposition-key '(RequiresBoth Sizable Printable))
                (canonical-proposition-key '(RequiresBoth Printable Sizable))))

(test-case "type-equiv? uses Union and proposition canonicalization"
  (check-true (type-equiv? '(Union Int String) '(Union String Int)))
  (check-true
   (type-equiv? '(Proof (RequiresBoth Sizable Printable))
                '(Proof (RequiresBoth Printable Sizable))))
  (check-true
   (type-equiv? '(Refined Int (FieldType f (Record ((a Int imm) (z Int imm)))))
                '(Refined Int (FieldType f (Record ((z Int imm) (a Int imm)))))))
  (check-true
   (type-equiv? '(NFn () Unit () ((RequiresBoth Sizable Printable)))
                '(NFn () Unit () ((RequiresBoth Printable Sizable)))))
  (check-false
   (type-equiv? '(NFn () Unit () (ValidNarrativeTrait TypeNarrativeCap))
                '(NFn () Unit () (TypeNarrativeCap ValidNarrativeTrait)))))

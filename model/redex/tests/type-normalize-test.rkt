#lang racket/base
(require rackunit
         "../type-equiv.rkt"
         "../type-shape.rkt")

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

(test-case "union equivalence is set equality, not multiset"
  ;; CMP-001 は重複が正規形を分けないと述べる。type-equiv? も同じ扱いにする。
  (check-true
   (type-equiv? '(Union Int (Union Int String)) '(Union Int String)))
  ;; 片方だけが Union でも、包含が破れるので非同値になる。
  (check-false (type-equiv? '(Union Int String) 'Int)))

(test-case "canonicalization falls back to syntax when no key exists"
  ;; Intersection の被演算子が Record でないと正規化に失敗し、鍵は #f になる。
  ;; 鍵の #f どうしを一致とみなすと別命題が同値になり、不一致とみなすと反射律が
  ;; 壊れる。どちらも起きないことを固定する。
  (define bad '(Implements (Intersection Int String) P))
  (define other '(Implements (Intersection Bool Unit) Q))
  (check-false (canonical-proposition-key bad))
  (check-false (type-equiv? `(Proof ,bad) `(Proof ,other)))
  (check-true (type-equiv? `(Proof ,bad) `(Proof ,bad)))
  (check-false
   (type-equiv? `(NFn () Unit () (,bad)) `(NFn () Unit () (,other))))
  (check-true
   (type-equiv? `(NFn () Unit () (,bad)) `(NFn () Unit () (,bad))))
  (check-false (type-equiv? `(Refined Int ,bad) `(Refined Int ,other)))
  (check-true (type-equiv? `(Refined Int ,bad) `(Refined Int ,bad))))

(test-case "core-types-normal? rejects a non-normal type hidden in an annotation"
  (check-false
   (core-types-normal? '(Let (x (Union String Int)) 1 x)))
  (check-true
   (core-types-normal? '(Let (x Int) 1 x)))
  (check-false
   (core-types-normal? '(Let (x let (Union String Int)) 1 x)))
  (check-true
   (core-types-normal? '(Let (x let Int) 1 x))))

(test-case "core-types-normal? rejects a residual Intersection"
  (check-false
   (core-types-normal?
    '(Let (x (Intersection (Record ((a Int imm)))
                           (Record ((b Int imm)))))
       1
       x))))

(test-case "proposition-types-normal? recurses into embedded types"
  (check-false
   (proposition-types-normal? '(Implements (Union String Int) Printable)))
  (check-true
   (proposition-types-normal? '(Implements Int Printable))))

(test-case "effect-row-normal? recurses into embedded types"
  (check-false (effect-row-normal? '((Return boundary (Union String Int)))))
  (check-true (effect-row-normal? '((Return boundary Int)))))

(test-case "type-shape-ok? recurses into composite and proposition types"
  (define duplicate-row '(Record ((a Int imm) (a Bool imm))))
  (check-false (type-shape-ok? `(Union Int ,duplicate-row)))
  (check-false (type-shape-ok? `(Intersection Int ,duplicate-row)))
  (check-true (type-shape-ok? '(Union Int (Record ((a Int imm))))))
  (check-false (type-shape-ok? `(Proof (FieldType f ,duplicate-row))))
  (check-false (type-shape-ok? `(Refined Int (FieldType f ,duplicate-row))))
  (check-false (type-shape-ok? `(NFn () Unit () ((FieldType f ,duplicate-row))))))

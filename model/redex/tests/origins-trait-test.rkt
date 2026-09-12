#lang racket/base

(require rackunit
         racket/list
         redex/reduction-semantics
         "../lang.rkt"
         "../origins.rkt"
         "../span-core.rkt"
         "../traits.rkt"
         "../type-shape.rkt")

(define (trait-constant-name row)
  (string->symbol (format "~a-trait" (trait-name row))))

(define (verify-initial core)
  (term (verify-initial-origins ,R0 ,core)))

(test-case "the trait tables contribute R0 entries"
  ;; NAR-003: trait の第 1 欄は表の鍵であり R0 の ID ではない。R0 に
  ;; 現れると、それが新しい trusted root になる。
  (for ([row (in-list trait-table)])
    (check-false (assoc (trait-origin row) R0)
                 (format "~s" (trait-name row))))
  (for ([row (in-list impl-table)])
    (check-equal? (assoc (impl-oid row) R0)
                  (list (impl-oid row)
                        (list 'prim (impl-name row)))))
  (for ([row (in-list intersect-table)])
    (check-equal? (assoc (intersect-oid row) R0)
                  (list (intersect-oid row)
                        (list 'prim (intersect-name row))))))

(test-case "the trait tables contribute Γ0 entries"
  (for ([row (in-list impl-table)])
    (define trait-row (trait-row-by-name (impl-trait-name row)))
    (define requirements
      (instantiate-requirements
       (trait-template trait-row)
       (impl-target-type row)))
    (check-equal?
     (assoc (impl-name row) Γ0)
     (list (impl-name row)
           (list `(NFn ((Record ,requirements))
                       (Proof (Implements ,(impl-target-type row)
                                          ,(impl-trait-name row)))
                       () ())
                 `(PrimVal (Reserved ,(impl-oid row)) ,(impl-name row))))))
  (for ([row (in-list intersect-table)])
    (check-equal?
     (assoc (intersect-name row) Γ0)
     (list (intersect-name row)
           (list `(NFn ((Proof (ValidNarrativeTrait ,(intersect-left row)))
                        (Proof (ValidNarrativeTrait ,(intersect-right row))))
                       (Proof (RequiresBoth ,(intersect-left row)
                                            ,(intersect-right row)))
                       () ())
                 `(PrimVal (Reserved ,(intersect-oid row))
                           ,(intersect-name row)))))))

(test-case "R0 and Γ0 keys stay unique after appending trait rows"
  (check-equal? (length (map car R0))
                (length (remove-duplicates (map car R0))))
  (check-equal? (length (map car Γ0))
                (length (remove-duplicates (map car Γ0)))))

(test-case "Γ0 holds the sole source of trait validity proofs"
  (for ([row (in-list trait-table)])
    (define name (trait-constant-name row))
    (define proposition `(ValidNarrativeTrait ,(trait-name row)))
    (check-equal?
     (assoc name Γ0)
     (list name
           (list `(Proof ,proposition)
                 `(ProofRep ,(trait-derived-origin row) ,proposition)))
     (format "~s" (trait-name row)))))

(test-case "proof-issuer-ok? accepts trait-table issuers"
  (check-true
   (proof-issuer-ok? R0
                     '(Derived (Reserved o-language-narrative)
                               (Trait Printable))
                     '(ValidNarrativeTrait Printable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-impl-printable-int)
                     '(Implements Int Printable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-derive-sizable-int)
                     '(Implements Int Sizable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-intersect-print-size)
                     '(RequiresBoth Printable Sizable))))

(test-case "proof-issuer-ok? rejects mismatched trait issuers"
  (check-false
   (proof-issuer-ok? R0 '(Reserved o-impl-taggable-bool)
                     '(Implements Int Printable)))
  (check-false
   (proof-issuer-ok? R0 '(Reserved o-impl-printable-int)
                     '(Implements Bool Printable)))
  (check-false
   (proof-issuer-ok? R0 '(Reserved o-trait-printable)
                     '(ValidNarrativeTrait Sizable))))

(test-case "proof-issuer-ok? compares trait propositions canonically"
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-impl-printable-int)
                     '(Implements (Union Int Int) Printable)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-intersect-print-size)
                     '(RequiresBoth Sizable Printable))))

(test-case "FieldType is local-only"
  (define witness
    '(ProofRep (Reserved o-merge) (FieldType f Int)))
  (check-true
   (proof-issuer-ok? R0 '(Reserved o-merge) '(FieldType f Int)))
  (check-equal? (verify-initial witness) `(forged ,witness)))

(test-case "trait-global-bindings derives one entry per impl row and intersect row"
  (define bindings (trait-global-bindings))
  (check-equal? (length bindings)
                (+ (length impl-table) (length intersect-table)))
  (for ([row (in-list impl-table)])
    (define trait-row (trait-row-by-name (impl-trait-name row)))
    (check-equal?
     (assoc (impl-name row) bindings)
     (list (impl-name row)
           (list `(Implements ,(impl-target-type row)
                              ,(impl-trait-name row))
                 `(Reserved ,(impl-oid row))
                 (impl-name row)
                 'root
                 'default
                 (list (trait-origin trait-row) (impl-oid row))))))
  ;; TRT-005: intersect 行は RequiresBoth 候補を供給する。
  (for ([row (in-list intersect-table)])
    (check-equal?
     (assoc (intersect-name row) bindings)
     (list (intersect-name row)
           (list `(RequiresBoth ,(intersect-left row)
                                ,(intersect-right row))
                 `(Reserved ,(intersect-oid row))
                 (intersect-name row)
                 'root
                 'default
                 (list (intersect-oid row)))))))

(test-case "trait-derived Γ0 values pass initial origin verification"
  (define names
    (append (map trait-constant-name trait-table)
            (map impl-name impl-table)
            (map intersect-name intersect-table)))
  (for ([name (in-list names)])
    (define value (second (second (assoc name Γ0))))
    (check-equal? (verify-initial value) 'ok (format "~s" name))))

;; NAR-003: step は Trait の形を受理する。
(test-case "NAR-003: step が Trait の形を受理する"
  (check-true (redex-match? G1 step '(Trait Printable)))
  (check-true
   (redex-match? G1 O '(Derived (Reserved o-language-narrative)
                                (Trait Printable))))
  ;; 既存の 5 形は変わらない。
  (check-true (redex-match? G1 step '(Policy ownership)))
  (check-true (redex-match? G1 step '(Expand nm)))
  ;; G1+（span-core）でも同じ形が通る。両方の文法を触るため、片方の
  ;; 取りこぼしをこの 1 本で落とす。
  (check-true (redex-match? G1+ step '(Trait Printable)))
  (check-true
   (redex-match? G1+ O '(Derived (Reserved o-language-narrative)
                                 (Trait Printable)))))

;; NAR-003: 継承していない origin を持つ trait Proof は拒否される。
(test-case "NAR-003: 偽造した trait Proof の origin を拒否する"
  ;; User origin。
  (check-false
   (proof-issuer-ok? R0 'User '(ValidNarrativeTrait Printable)))
  ;; 親が違う予約 Narrative。
  (check-false
   (proof-issuer-ok? R0
                     '(Derived (Reserved o-type-narrative) (Trait Printable))
                     '(ValidNarrativeTrait Printable)))
  ;; step の trait 名が命題の trait 名と食い違う。
  (check-false
   (proof-issuer-ok? R0
                     '(Derived (Reserved o-language-narrative) (Trait Sizable))
                     '(ValidNarrativeTrait Printable)))
  ;; 表に無い trait 名。
  (check-false
   (proof-issuer-ok? R0
                     '(Derived (Reserved o-language-narrative) (Trait Bogus))
                     '(ValidNarrativeTrait Bogus)))
  ;; 予約 Narrative が別の値へ束縛された R0 では通らない。
  (define rebound
    (cons '(o-language-narrative somethingElse)
          (filter (lambda (entry)
                    (not (eq? (car entry) 'o-language-narrative)))
                  R0)))
  (check-false
   (proof-issuer-ok? rebound
                     '(Derived (Reserved o-language-narrative)
                               (Trait Printable))
                     '(ValidNarrativeTrait Printable))))

;; NAR-003: 正典の表は全行が R0 の実値照合を通る。上の負例と対にして、
;; 検査が実質何も見ない形で通る退化を防ぐ。
(test-case "NAR-003: 正典の trait 表は全行が trait-origin-ok? を通る"
  (for ([row (in-list trait-table)])
    (check-true (trait-origin-ok? R0 row) (format "~s" (trait-name row)))))

;; NAR-003: 型の正規形の走査が新しい step を辿れる。walk-step は閉世界で
;; あり、節が無ければ error で止まる。
(test-case "NAR-003: core-types-normal? が Trait step を辿る"
  (check-true
   (core-types-normal?
    '(ProofRep (Derived (Reserved o-language-narrative) (Trait Printable))
               (ValidNarrativeTrait Printable)))))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt")

;; unsafe.md §3.1。6 引数すべてを型成分として持つ。
(test-case "RawPtr の 6 引数（unsafe.md §3.1）"
  (for ([type (in-list
               (term ((RawPtr Int Const NonNull (Align 4)
                              (AddrSpace native) (Prov owned))
                      (RawPtr Int Mut Nullable (Align 16)
                              (AddrSpace wasm-linear) (Prov foreign))
                      (RawPtr (RawPtr Int Const NonNull (Align 1)
                                      (AddrSpace ffi) (Prov unknown))
                              Mut NonNull (Align 8)
                              (AddrSpace js-buffer) (Prov unknown)))))])
    (check-true (redex-match? G1 τ type))))

;; 引数の数と綴りが合わない形は τ ではない。
(test-case "RawPtr の不整形（unsafe.md §3.1）"
  (for ([bad (in-list
              (term ((RawPtr Int Const NonNull (Align 4)
                             (AddrSpace native))
                     (RawPtr Int mut NonNull (Align 4)
                             (AddrSpace native) (Prov owned))
                     (RawPtr Int Const NonNull 4
                             (AddrSpace native) (Prov owned))
                     (RawPtr Int Const NonNull (Align 4)
                             native (Prov owned)))))])
    (check-false (redex-match? G1 τ bad))))

;; 5 つの新しい非終端が独立に照合する。
(test-case "pointer の成分の非終端（unsafe.md §3.1）"
  (check-true (redex-match? G1 ptrmut (term Const)))
  (check-true (redex-match? G1 ptrmut (term Mut)))
  (check-false (redex-match? G1 ptrmut (term mut)))
  (check-true (redex-match? G1 nul (term NonNull)))
  (check-true (redex-match? G1 nul (term Nullable)))
  (check-true (redex-match? G1 align (term (Align 0))))
  (check-false (redex-match? G1 align (term (Align -1))))
  (check-true (redex-match? G1 as (term (AddrSpace native))))
  (check-true (redex-match? G1 prov (term (Prov owned)))))

;; unsafe.md §4.1。Unsafe は ℓ の要素であり、ε に載る。
(test-case "Unsafe の Effect label（unsafe.md §4.1）"
  (check-true (redex-match? G1 ℓ (term Unsafe)))
  (check-true (redex-match? G1 ε (term (Unsafe))))
  (check-true (redex-match? G1 ε (term ((Return b Int) Unsafe)))))

;; ptrmut を非終端にしても record の可変性の literal は壊れない。
(test-case "m の literal が保たれる（unsafe.md §3.1）"
  (check-true (redex-match? G2 m (term imm)))
  (check-true (redex-match? G2 m (term mut)))
  (check-false (redex-match? G2 m (term Mut)))
  (check-true (redex-match? G2 r (term ((a Int mut))))))

;; unsafe.md §4.2。6 つの操作が c として照合する。
(test-case "pointer 操作の構文（unsafe.md §4.2）"
  (for ([core (in-list
               (term ((AddressOf x)
                      (PtrOffset x 1)
                      (RawLoad x)
                      (RawStore x 1)
                      (FromRawPtr x 0)
                      (FromRawPtr x (RVar 0))
                      (FromRawPtr x (RParam rp))
                      (Unsafe (RawLoad x)))))])
    (check-true (redex-match? G2 c core) (format "G2: ~s" core))
    (check-true (redex-match? G2m c core) (format "G2m: ~s" core))))

;; unsafe.md §5.1。PtrProp は φ の構成子であり、Proof と Refined に載る。
(test-case "PtrProp の構文（unsafe.md §5.1）"
  (define proposition (term (PtrProp NonNull Int)))
  (check-true (redex-match? G2 φ proposition))
  (check-true (redex-match? G2m φ proposition))
  (check-true (redex-match? G2 τ (term (Proof (PtrProp Aligned Int)))))
  (check-true (redex-match? G2 Q (term ((PtrProp NonNull Int)
                                        (PtrProp Aligned Int))))))

;; unsafe.md §4.3。PtrVal は place と field path と可変性と provenance を持つ。
(test-case "PtrVal の構文（unsafe.md §4.3）"
  (check-true (redex-match? G2m v (term (PtrVal 0 () Mut (Prov owned)))))
  (check-true (redex-match? G2m v (term (PtrVal 3 (a 1) Const (Prov owned)))))
  (check-false (redex-match? G2m v (term (PtrVal 0 () (Prov owned)))))
  (check-false (redex-match? G2m v (term (PtrVal 0 () mut (Prov owned)))))
  (check-false (redex-match? G2 v (term (PtrVal 0 () Mut (Prov owned))))))

;; unsafe.md §6.3。3 つの評価文脈すべてに枠がある。
(test-case "評価文脈の枠（unsafe.md §6.3）"
  (for ([ctx (in-list '(F E G))])
    (for ([frame (in-list
                  (term ((Unsafe hole)
                         (AddressOf hole)
                         (PtrOffset hole 1)
                         (PtrOffset (PtrVal 0 () Mut (Prov owned)) hole)
                         (RawLoad hole)
                         (RawStore hole 1)
                         (RawStore (PtrVal 0 () Mut (Prov owned)) hole)
                         (FromRawPtr hole 0))))])
      (check-true
       (case ctx
         [(F) (redex-match? G2m F frame)]
         [(E) (redex-match? G2m E frame)]
         [(G) (redex-match? G2m G frame)])
       (format "~a: ~s" ctx frame)))))

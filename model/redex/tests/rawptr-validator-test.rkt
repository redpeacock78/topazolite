#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../validators.rkt"
         "../search.rkt")

;; unsafe.md §3.1。address space は 4 つに限る。
(test-case "address space の許可集合（unsafe.md §3.1）"
  (for ([space (in-list '(native wasm-linear js-buffer ffi))])
    (check-true (addr-space-ok? `(AddrSpace ,space))))
  (check-false (addr-space-ok? '(AddrSpace gpu)))
  (check-false (addr-space-ok? '(AddrSpace)))
  (check-false (addr-space-ok? 'native))
  (check-false (addr-space-ok? '(Prov owned))))

;; unsafe.md §3.1。provenance は 3 つに限る。
(test-case "provenance の許可集合（unsafe.md §3.1）"
  (for ([p (in-list '(foreign owned unknown))])
    (check-true (prov-ok? `(Prov ,p))))
  (check-false (prov-ok? '(Prov native)))
  (check-false (prov-ok? '(AddrSpace native)))
  (check-false (prov-ok? 'owned)))

;; unsafe.md §5.1。PtrProp の識別子は 10 個に限る。
(test-case "PtrProp の識別子の許可集合（unsafe.md §5.1）"
  (for ([id (in-list '(NonNull Aligned InBounds Initialized AliveAllocation
                       Readable Writable AbiMatched LifetimeValid
                       OwnershipTransferred))])
    (check-true (ptr-prop-id-ok? id))
    ;; 文法の ptr-prop-id と許可集合が乖離しないことを見る。
    (check-true (redex-match? G2 φ (term (PtrProp ,id Int)))))
  (check-false (ptr-prop-id-ok? 'Bogus))
  (check-false (ptr-prop-id-ok? 'nonnull))
  (check-false (ptr-prop-id-ok? '(PtrProp NonNull Int))))

;; unsafe.md §3.1。RawPtr の 5 成分をまとめて検査する。
(test-case "raw-ptr-components-ok? が 5 成分を閉じる（unsafe.md §3.1）"
  (define (ptr ptrmut nul align as prov)
    `(RawPtr Int ,ptrmut ,nul ,align ,as ,prov))
  (check-true (raw-ptr-components-ok?
               (ptr 'Const 'NonNull '(Align 4)
                    '(AddrSpace native) '(Prov owned))))
  ;; 文法の RawPtr と validator の成分集合が乖離しないことを見る。
  (check-true
   (redex-match? G2 τ
                 (term (RawPtr Int Const NonNull (Align 1)
                                (AddrSpace native) (Prov owned)))))
  (check-true (raw-ptr-components-ok?
               (ptr 'Mut 'Nullable '(Align 1)
                    '(AddrSpace ffi) '(Prov unknown))))
  ;; 成分ごとの負例。文法の literal と綴りが違うものは落ちる。
  (check-false (raw-ptr-components-ok?
                (ptr 'mut 'NonNull '(Align 4)
                     '(AddrSpace native) '(Prov owned))))
  (check-false (raw-ptr-components-ok?
                (ptr 'Const 'nonnull '(Align 4)
                     '(AddrSpace native) '(Prov owned))))
  (check-false (raw-ptr-components-ok?
                (ptr 'Const 'NonNull '(Align -1)
                     '(AddrSpace native) '(Prov owned))))
  (check-false (raw-ptr-components-ok?
                (ptr 'Const 'NonNull '(Align 0)
                     '(AddrSpace native) '(Prov owned))))
  (check-false (raw-ptr-components-ok?
                (ptr 'Const 'NonNull 'Align
                     '(AddrSpace native) '(Prov owned))))
  (check-false (raw-ptr-components-ok?
                (ptr 'Const 'NonNull '(Align 4)
                     '(AddrSpace gpu) '(Prov owned))))
  (check-false (raw-ptr-components-ok?
                (ptr 'Const 'NonNull '(Align 4)
                     '(AddrSpace native) '(Prov native))))
  ;; RawPtr 以外の型は落ちる。
  (check-false (raw-ptr-components-ok? 'Int))
  (check-false (raw-ptr-components-ok? '(Owned Res))))

;; unsafe.md §5.1。許可集合の中の PtrProp だけが Finite に写る。
(test-case "既定 χ が PtrProp を Finite に写す（unsafe.md §5.1）"
  (check-eq? (default-classifier (make-goal '(PtrProp NonNull Int)) Γ-pc0)
             'Finite)
  (check-eq? (default-classifier (make-goal '(PtrProp Aligned Int)) Γ-pc0)
             'Finite)
  (check-eq? (default-classifier (make-goal '(PtrProp Bogus Int)) Γ-pc0)
             'Unknown))

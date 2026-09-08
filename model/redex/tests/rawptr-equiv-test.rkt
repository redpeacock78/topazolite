#lang racket

(require rackunit
         "../type-equiv.rkt")

(define (ptr payload [ptrmut 'Const])
  `(RawPtr ,payload ,ptrmut NonNull (Align 4)
           (AddrSpace native) (Prov owned)))

(define unsorted '(Record ((b Int imm) (a Int imm))))
(define sorted '(Record ((a Int imm) (b Int imm))))

;; unsafe.md §4.4。payload を正規化する。
(test-case "normalize-type が RawPtr の payload を正規化する（unsafe.md §4.4）"
  (check-equal? (normalize-type (ptr unsorted)) (ptr sorted))
  (check-false (type-normal? (ptr unsorted)))
  (check-true (type-normal? (ptr sorted))))

;; unsafe.md §4.4。正準鍵も payload を通す。canonical-type-key は provide に
;; 無いため、live な経路である canonical-proposition-key から確かめる。
;; payload を ForallRegion にすると、normalize が束縛子を書き換えず
;; canonical-key/normal だけが添字へ置き換えるので、RawPtr の節が無いと落ちる。
(test-case "canonical-key/normal が RawPtr の payload を通す（unsafe.md §4.4）"
  (define forall-a '(ForallRegion (a) (NFn ((Borrowed Int (RParam a))) Int () ())))
  (define forall-b '(ForallRegion (b) (NFn ((Borrowed Int (RParam b))) Int () ())))
  (check-equal? (canonical-proposition-key `(PtrProp NonNull ,(ptr forall-a)))
                (canonical-proposition-key `(PtrProp NonNull ,(ptr forall-b)))))

;; unsafe.md §4.4。同値は payload を type-equiv? で、残る 5 成分を equal? で
;; 比べる。address space が違えば同値ではない（unsafe.md §3.2）。
(test-case "type-equiv? が RawPtr を比べる（unsafe.md §4.4）"
  (check-true (type-equiv? (ptr sorted) (ptr sorted)))
  (check-true (type-equiv? (ptr '(Union Int Bool)) (ptr '(Union Bool Int))))
  (check-false (type-equiv? (ptr 'Int 'Const) (ptr 'Int 'Mut)))
  (check-false
   (type-equiv?
    '(RawPtr Int Const NonNull (Align 4) (AddrSpace native) (Prov owned))
    '(RawPtr Int Const NonNull (Align 4) (AddrSpace js-buffer) (Prov owned))))
  (check-false
   (type-equiv?
    '(RawPtr Int Const NonNull (Align 4) (AddrSpace native) (Prov owned))
    '(RawPtr Int Const NonNull (Align 8) (AddrSpace native) (Prov owned))))
  (check-false
   (type-equiv?
    '(RawPtr Int Const NonNull (Align 4) (AddrSpace native) (Prov owned))
    '(RawPtr Int Const Nullable (Align 4) (AddrSpace native) (Prov owned))))
  (check-false
   (type-equiv?
    '(RawPtr Int Const NonNull (Align 4) (AddrSpace native) (Prov owned))
    '(RawPtr Int Const NonNull (Align 4) (AddrSpace native) (Prov foreign))))
  (check-false (type-equiv? (ptr 'Int) '(Borrowed Int 0))))

;; unsafe.md §4.4。PtrProp は φ の構成子なので命題側も正規化する。
(test-case "PtrProp の正規化と正準鍵（unsafe.md §4.4）"
  (check-equal? (normalize-proposition `(PtrProp NonNull ,unsorted))
                `(PtrProp NonNull ,sorted))
  (check-equal? (canonical-proposition-key `(PtrProp NonNull ,unsorted))
                (canonical-proposition-key `(PtrProp NonNull ,sorted)))
  (check-true (proposition-equiv? `(PtrProp NonNull ,unsorted)
                                  `(PtrProp NonNull ,sorted)))
  (check-false (proposition-equiv? '(PtrProp NonNull Int)
                                   '(PtrProp Aligned Int)))
  ;; Proof と Refined の内側でも同じ正規化が働く。
  (check-equal? (normalize-type `(Proof (PtrProp NonNull ,unsorted)))
                `(Proof (PtrProp NonNull ,sorted)))
  (check-true (type-equiv? `(Proof (PtrProp NonNull ,unsorted))
                            `(Proof (PtrProp NonNull ,sorted)))))

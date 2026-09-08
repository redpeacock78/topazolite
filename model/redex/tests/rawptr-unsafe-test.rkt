#lang racket

(require rackunit
         "../region.rkt"
         "../borrow.rkt"
         "../validators.rkt"
         "../typing.rkt")

(define ptr
  '(RawPtr Int Mut NonNull (Align 1) (AddrSpace native) (Prov owned)))

(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (check-core core)
  (define ir (build-region-ir core))
  (type-of/raw core '() '() '() (Λ-of ir)))

(define (key-of result)
  (match result
    [(list 'fail key _ ...) key]
    [_ #f]))

;; unsafe.md §4.3。判定は fail-closed である。基底型も明示しなければ
;; すべての (Unsafe c) が落ちる。
(test-case "漏出なしを返す基底型（unsafe.md §4.3）"
  (for ([type (in-list (list 'Int 'Bool 'Unit 'String 'Never 'Res
                             '(TypeInfo Type)
                             '(Proof ValidNarrativeTrait)))])
    (check-false (leaks-rawptr? type) (format "~a" type))))

(test-case "RawPtr そのものは漏出ありである（unsafe.md §4.3）"
  (check-true (leaks-rawptr? ptr)))

(test-case "成分へ降りる構成子（unsafe.md §4.3）"
  (check-true (leaks-rawptr? `(List ,ptr)))
  (check-true (leaks-rawptr? `(Option ,ptr)))
  (check-true (leaks-rawptr? `(Result Int ,ptr)))
  ;; (Owned (RawPtr ...)) は type-shape-ok? が落とす形だが、leaks-rawptr? は
  ;; 型形状の検査とは独立の走査であり、節の網羅を保つため明示する。
  (check-true (leaks-rawptr? `(Owned ,ptr)))
  (check-true (leaks-rawptr? `(Borrowed ,ptr (RVar 0))))
  (check-true (leaks-rawptr? `(BorrowedMut ,ptr (RVar 0))))
  (check-true (leaks-rawptr? `(Untrusted ,ptr)))
  (check-true (leaks-rawptr? `(Refined ,ptr (Prop ValidPort))))
  (check-true (leaks-rawptr? `(Union Int ,ptr)))
  (check-true (leaks-rawptr? `(Intersection Int ,ptr)))
  (check-true (leaks-rawptr? `(ForallRegion (rp) ,ptr)))
  (check-true (leaks-rawptr? `(Record ((f0 ,ptr imm)))))
  (check-false (leaks-rawptr? '(Record ((f0 Int imm))))))

;; NFn を辿るのは、RawPtr を包んだ関数値が境界の外へ出ると呼び出し側が
;; pointer を取り出せるためである。
(test-case "NFn の引数型と返り値型と ε を辿る（unsafe.md §4.3）"
  (check-true (leaks-rawptr? `(NFn (,ptr) Int () ())))
  (check-true (leaks-rawptr? `(NFn (Int) ,ptr () ())))
  (check-true (leaks-rawptr? `(NFn (Int) Int ((Yield ,ptr)) ())))
  (check-true (leaks-rawptr? `(NFn (Int) Int ((Return b ,ptr)) ())))
  (check-false (leaks-rawptr? '(NFn (Int) Int (Own Unsafe) ()))))

;; φ と Q は命題の対象を運ぶだけであり、pointer 値の持ち出し経路ではない。
;; copy-out-scan も Refined の φ と NFn の Q へ降りない形が先例である。
(test-case "Refined の φ と NFn の Q へは降りない（unsafe.md §4.3）"
  (check-false (leaks-rawptr? `(Refined Int (PtrProp NonNull ,ptr))))
  (check-false (leaks-rawptr? `(NFn (Int) Int () ((PtrProp NonNull ,ptr))))))

(test-case "未知の型構成子は fail-closed で落ちる（unsafe.md §4.3）"
  (check-true (leaks-rawptr? '(FutureType Int)))
  (check-true (leaks-rawptr? 'NotAType)))

;; unsafe.md §4.1。(Unsafe c) は ε から Unsafe だけを除く。
(test-case "Unsafe は ε から Unsafe だけを除く（unsafe.md §4.1）"
  (define core
    `(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Unsafe (RawLoad (AddressOf (BorrowMut x)))))))
  (match (check-core core)
    [(list 'ok (list type row))
     (check-equal? type 'Res)
     (check-false (memq 'Unsafe row))]
    [other (fail (format "受理されなかった: ~s" other))]))

;; unsafe.md §4.1。内側の他の Effect は残る。
(test-case "Unsafe の内側の他の Effect は残る（unsafe.md §4.1）"
  (define core
    `(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Unsafe (Move x)))))
  (match (check-core core)
    [(list 'ok (list _type row))
     (check-equal? row '(Own))]
    [other (fail (format "受理されなかった: ~s" other))]))

;; unsafe.md §4.3。境界の外へ pointer を出す項は落ちる。
(test-case "Unsafe から RawPtr が出る項は落ちる（unsafe.md §4.3）"
  (check-equal?
   (key-of (check-core
            `(Scope ()
               (Let (x let (Owned Res)) (resource 1)
                 (Unsafe (AddressOf (BorrowMut x)))))))
   'rawptr-escapes-unsafe))

;; Unsafe の外へ出る Yield の payload も row に RawPtr を運ぶため、型だけで
;; なく effect row を検査する。
(test-case "Unsafe の Yield effect row から RawPtr が出る項は落ちる（unsafe.md §4.3）"
  (check-equal?
   (key-of
    (check-core
     '(Scope ()
        (Let (x let (Owned Res)) (resource 1)
          (Unsafe
           (Let (p const (RawPtr Res Mut NonNull (Align 1)
                                  (AddrSpace native) (Prov owned)))
                (AddressOf (BorrowMut x))
                (Yield p unit)))))))
   'rawptr-escapes-unsafe))

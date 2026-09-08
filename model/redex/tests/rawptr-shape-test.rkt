#lang racket

(require rackunit
         "../type-shape.rkt")

;; unsafe.md §4.4。RawPtr の payload を辿る。
(test-case "type-shape-ok? が RawPtr の payload を辿る（unsafe.md §4.4）"
  (define (ptr payload)
    `(RawPtr ,payload Const NonNull (Align 4)
             (AddrSpace native) (Prov owned)))
  (check-true (type-shape-ok? (ptr 'Int)))
  (check-true (type-shape-ok? (ptr '(Record ((a Int imm) (b Int imm))))))
  ;; record の label が重複する payload は落ちる。
  (check-false (type-shape-ok? (ptr '(Record ((a Int imm) (a Int imm))))))
  ;; 借用の payload を Owned で包めない既存の判断は変わらない。
  (check-false (type-shape-ok? (ptr '(Borrowed (Owned Res) 0))))
  ;; unsafe.md §3.1。payload 以外の 5 成分も raw-ptr-components-ok? で閉じる。
  (check-false (type-shape-ok? '(RawPtr Int mut NonNull (Align 4)
                                        (AddrSpace native) (Prov owned))))
  (check-false (type-shape-ok? '(RawPtr Int Const Maybe (Align 4)
                                        (AddrSpace native) (Prov owned))))
  (check-false (type-shape-ok? '(RawPtr Int Const NonNull (Align -1)
                                        (AddrSpace native) (Prov owned))))
  (check-false (type-shape-ok? '(RawPtr Int Const NonNull (Align 0)
                                        (AddrSpace native) (Prov owned))))
  (check-false (type-shape-ok? '(RawPtr Int Const NonNull (Align 4)
                                        (AddrSpace gpu) (Prov owned))))
  (check-false (type-shape-ok? '(RawPtr Int Const NonNull (Align 4)
                                        (AddrSpace native) (Prov native)))))

;; unsafe.md §3.4。Owned の直下に RawPtr を置けない。
(test-case "Owned の直下の RawPtr（unsafe.md §3.4）"
  (define p '(RawPtr Int Const NonNull (Align 4)
                     (AddrSpace native) (Prov owned)))
  (check-false (type-shape-ok? `(Owned ,p)))
  ;; Owned を経由しない構造の欄には置ける。
  (check-true (type-shape-ok? `(Record ((ptr ,p imm)))))
  (check-true (type-shape-ok? `(Option ,p))))

;; unsafe.md §4.4。PtrProp の識別子と型を検査する。
(test-case "proposition-shape-ok? が PtrProp を検査する（unsafe.md §4.4）"
  (check-true (proposition-shape-ok? '(PtrProp NonNull Int)))
  (check-false (proposition-shape-ok? '(PtrProp Bogus Int)))
  (check-false (proposition-shape-ok?
                '(PtrProp NonNull (Record ((a Int imm) (a Int imm))))))
  ;; Proof と Refined の内側でも同じ判定が働く。
  (check-false (type-shape-ok? '(Proof (PtrProp Bogus Int))))
  (check-false (type-shape-ok? '(Refined Int (PtrProp Bogus Int))))
  (check-true (type-shape-ok? '(Refined Int (PtrProp NonNull Int))))
  ;; Q（NFn の obligations）の内側でも同じ判定が働く。
  (check-false (type-shape-ok? '(NFn () Int () ((PtrProp Bogus Int)))))
  (check-true (type-shape-ok? '(NFn () Int () ((PtrProp NonNull Int))))))

;; unsafe.md §4.4。core-types-normal? が新しい 7 形を辿る。
(test-case "core-types-normal? が pointer 操作を辿る（unsafe.md §4.4）"
  (for ([core (in-list '((AddressOf x)
                         (RawLoad x)
                         (Unsafe x)
                         (PtrOffset x 1)
                         (RawStore x 1)
                         (FromRawPtr x 0)
                         (PtrVal 0 () Mut (Prov owned))))])
    (check-true (core-types-normal? core) (format "~s" core)))
  ;; 内側の正規形でない型注釈を見落とさない。
  (check-false
   (core-types-normal?
    '(Unsafe (Let (y const (Record ((b Int imm) (a Int imm)))) 1 y))))
  (check-false
   (core-types-normal?
    '(RawStore x (Let (y const (Record ((b Int imm) (a Int imm)))) 1 y)))))

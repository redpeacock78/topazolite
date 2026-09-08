#lang racket

(require rackunit
         "../validators.rkt"
         "../type-shape.rkt")

;; unsafe.md §6.5。ForallRegion の本体の Owned を見落とさない。
(test-case "owned-free? が ForallRegion の本体を辿る（unsafe.md §6.5）"
  (check-false (owned-free? '(ForallRegion (rp) (Owned Res))))
  (check-true (owned-free? '(ForallRegion (rp) Int)))
  ;; type-shape-ok? 経由でも Owned を Untrusted で隠せない。
  (check-false (type-shape-ok? '(Untrusted (ForallRegion (rp) (Owned Res)))))
  (check-false (type-shape-ok?
                '(Refined (ForallRegion (rp) (Owned Res))
                          (Implements Int SomeTrait)))))

;; unsafe.md §6.5。借用は Owned ではないので #t を返し、payload へ降りない。
(test-case "owned-free? が借用を通す（unsafe.md §6.5）"
  (check-true (owned-free? '(Borrowed (Owned Res) 0)))
  (check-true (owned-free? '(BorrowedMut (Owned Res) 0)))
  ;; 所有値を含む構造の借用は意図された用法である。
  ;; ここで確かめるのは owned-free? の側だけである。type-shape-ok? は
  ;; 既存の (Borrowed (Owned _) _) の節（type-shape.rkt:48 以降）で #f を
  ;; 返し、Untrusted の節がその結果を and で受けるため #f のままになる。
  ;; spec §6.5 の「既存の受理を保つ」は owned-free? の意味である。
  (check-false (type-shape-ok? '(Untrusted (Borrowed (Owned Res) 0)))))

;; unsafe.md §6.5。RawPtr も Owned ではない。
(test-case "owned-free? が RawPtr を通す（unsafe.md §6.5）"
  (check-true (owned-free? '(RawPtr Int Const NonNull (Align 4)
                                    (AddrSpace native) (Prov owned))))
  (check-true (owned-free? '(RawPtr (Owned Res) Const NonNull (Align 4)
                                    (AddrSpace native) (Prov owned)))))

;; unsafe.md §6.5。基底型と既知の構成子は #t、未知の構成子は #f。
(test-case "owned-free? の fail-closed（unsafe.md §6.5）"
  (for ([type (in-list '(Int Bool Unit String Never Res
                         (TypeInfo Type) (Proof ValidNarrativeTrait)))])
    (check-true (owned-free? type) (format "~s" type)))
  (check-false (owned-free? '(SomeFutureType Int)))
  (check-false (owned-free? '(Owned Res))))

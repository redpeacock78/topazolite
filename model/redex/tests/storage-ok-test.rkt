#lang racket

;; [REQ: REC-001] 可変記憶域に置く型は、到達する callable がすべて Partial を持つ。

(require rackunit
         "../type-shape.rkt")

(define pure-fn '(NFn (Int) Int () () () User))
(define partial-fn '(NFn (Int) Int () (Partial) () User))
(define yield-fn '(NFn (Int) Int () ((Yield Int)) () User))

;; 辿る構成子ごとに、純粋な NFn を置くと拒否し、Partial の NFn を置くと受理する。
(define (wraps fn)
  (list fn
        `(Record ((f ,fn imm) (n Int mut)))
        `(Union Int ,fn)
        `(Union ,fn Int)
        `(List ,fn)
        `(Option ,fn)
        `(Result Int ,fn)
        `(Result ,fn Int)
        `(Owned ,fn)
        `(Borrowed ,fn r1)
        `(BorrowedMut ,fn r1)
        `(Untrusted ,fn)
        `(Refined ,fn (Prop p))
        `(ForallRegion (r1) ,fn)
        `(RawPtr ,fn Mut NonNull (Align 4) (AddrSpace native) (Prov owned))))

(test-case "REC-001: value path の純粋な NFn は拒否する"
  (for ([τ (in-list (wraps pure-fn))])
    (check-false (storage-ok? τ) (format "~s" τ))))

(test-case "REC-001: value path の NFn がすべて Partial なら受理する"
  (for ([τ (in-list (wraps partial-fn))])
    (check-true (storage-ok? τ) (format "~s" τ))))

(test-case "REC-001: Yield だけの row は Partial の代わりにならない"
  (check-false (storage-ok? yield-fn)))

(test-case "REC-001: Union の一成分でも純粋な NFn なら拒否する"
  (check-false (storage-ok? `(Union ,partial-fn ,pure-fn))))

(test-case "REC-001: NFn の仮引数型と戻り型と Q へは降りない"
  (check-true (storage-ok? `(NFn (,pure-fn) Int () (Partial) () User)))
  (check-true (storage-ok? `(NFn (Int) ,pure-fn () (Partial) () User)))
  (check-true (storage-ok? `(NFn (Int) Int () (Partial)
                                ((FieldType f ,pure-fn)) User))))

(test-case "REC-001: callable を運ばない型は受理する"
  (for ([τ (in-list '(Int Bool Unit String Never Res
                      (TypeInfo Type)
                      (Proof (Prop p))
                      (Record ((a Int mut)))))])
    (check-true (storage-ok? τ) (format "~s" τ))))

(test-case "REC-001: 知らない形の型は拒否する"
  (check-false (storage-ok? '(Mystery Int))))

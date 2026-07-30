#lang racket/base
(require rackunit "../compat.rkt" "../type-equiv.rkt")

(test-case "compat? is reflexive on unions"
  (define u '(Union Int String))
  (check-true (compat? u u)))

(test-case "each sub member must be compatible with some sup member"
  (check-true (compat? 'Int '(Union Int String)))
  ;; Union は二項なので、3 要素は右結合の入れ子で書く。
  (check-true (compat? '(Union Int String) '(Union Int (Union String Bool))))
  (check-false (compat? '(Union Int Bool) '(Union Int String)))
  (check-false (compat? '(Union Int String) 'Int)))

(test-case "union compat does not depend on member order"
  (check-true (compat? '(Union String Int) '(Union Int String)))
  (check-true (compat? '(Union Int String) '(Union String Int))))

(test-case "obligation subsumption compares by canonical key"
  ;; 同値だが表記の違う命題は包含関係を満たす。obligations-subset? は非公開なので
  ;; 公開 API の compat? を通して観測する。
  (define (nfn q) `(NFn () Unit () ,q))
  (check-true (compat?
               (nfn '((Implements (Record ((a Int imm) (z Int imm))) Printable)))
               (nfn '((Implements (Record ((z Int imm) (a Int imm))) Printable)))))
  ;; 正規化できない命題は正準鍵が #f になる。#f どうしを一致とみなしてはならない。
  (check-false (compat?
                (nfn '((Implements (Intersection Int String) Printable)))
                (nfn '((Implements (Intersection Bool Unit) Sizable)))))
  (check-true (compat?
               (nfn '((Implements (Intersection Int String) Printable)))
               (nfn '((Implements (Intersection Int String) Printable))))))

(test-case "type-equiv? implies compat? on Refined propositions"
  ;; φ の表記だけが違う二つの Refined は type-equiv? で同値である。
  ;; compat? が構文比較のままだと非互換になり、VAR-002 性質2 が破れる。
  ;; properties-variance-test.rkt の生成器は Refined を作らないので、
  ;; この反例は性質テストでは観測できない。
  (define left
    '(Refined Int (Implements (Record ((a Int imm) (z Int imm))) Printable)))
  (define right
    '(Refined Int (Implements (Record ((z Int imm) (a Int imm))) Printable)))
  (check-true (type-equiv? left right))
  (check-true (compat? left right))
  (check-true (compat? right left))
  ;; φ が別命題なら非互換のまま。
  (check-false (compat? left '(Refined Int (Implements Int Printable)))))

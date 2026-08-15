#lang racket

(require rackunit
         redex/reduction-semantics
         "../compat.rkt"
         "../diagnostic.rkt"
         "../lang.rkt"
         "../type-equiv.rkt"
         "../type-shape.rkt"
         "../typing.rkt")

;; 文法。
(check-true (redex-match? G2m τ (term (Borrowed Int 0))))
(check-true (redex-match? G2m τ (term (BorrowedMut Int 0))))

;; normalize-type: payload を再帰で正規化し、ρ はそのまま残す。
(check-equal? (normalize-type '(Borrowed (Record ((b Int imm) (a Int imm))) 3))
              '(Borrowed (Record ((a Int imm) (b Int imm))) 3))

;; canonical-key/normal: レコードの行の順序違いが同値になる。
;; 節を足し忘れると末尾の [_ type] fallback が拾い、この 2 つが不等になる。
(check-true (type-equiv? '(Borrowed (Record ((b Int imm) (a Int imm))) 0)
                         '(Borrowed (Record ((a Int imm) (b Int imm))) 0)))
(check-true (type-equiv? '(BorrowedMut (Record ((b Int imm) (a Int imm))) 0)
                         '(BorrowedMut (Record ((a Int imm) (b Int imm))) 0)))

;; ρ が違えば別の型である。
(check-false (type-equiv? '(Borrowed Int 0) '(Borrowed Int 1)))
(check-false (type-equiv? '(Borrowed Int 0) '(BorrowedMut Int 0)))

;; compat?: 構成子が一致し payload が互換で ρ が equal? のときに限り真。
(check-true (compat? '(Borrowed Int 0) '(Borrowed Int 0) '()))
(check-false (compat? '(Borrowed Int 0) '(Borrowed Int 1) '()))
(check-false (compat? '(BorrowedMut Int 0) '(Borrowed Int 0) '()))
(check-false (compat? '(Borrowed Int 0) '(BorrowedMut Int 0) '()))

;; type-shape-ok?: payload が直接 Owned のとき偽。
(check-false (type-shape-ok? '(Borrowed (Owned Int) 0)))
(check-false (type-shape-ok? '(BorrowedMut (Owned Int) 0)))

;; 再帰的な owned-free? は採らない。所有値を含む構造の借用は意図された用法である。
(check-true (type-shape-ok? '(Borrowed (Record ((f (Owned Int) imm))) 0)))
(check-true (type-shape-ok? '(Borrowed (List (Owned Int)) 0)))

;; Union の要素の畳み込みが両構成子を区別する。
;; 鍵の実装（type-equiv.rkt の private な external-key）は観測しない。
;; 公開されている sort-then-dedup の結果の要素数で契約を固定する。
;; 2 要素が残るのは、両者が同じ要素へ畳まれないことを意味する。
(check-equal? (length (sort-then-dedup (list '(Borrowed Int 0)
                                             '(BorrowedMut Int 0))))
              2)
(check-equal? (length (sort-then-dedup (list '(Borrowed Int 0)
                                             '(Borrowed Int 1))))
              2)

;; 負の対照。同一の型は 1 要素へ畳まれる。
;; これが無いと、上の 2 本は「畳み込みが常に働かない」場合にも通ってしまう。
(check-equal? (length (sort-then-dedup (list '(Borrowed Int 0)
                                             '(Borrowed Int 0))))
              1)

;; 同じ契約を normalize-type の側からも固定する。
(check-true (type-equiv? (normalize-type '(Union (Borrowed Int 0)
                                                 (BorrowedMut Int 0)))
                         '(Union (Borrowed Int 0) (BorrowedMut Int 0))))
(check-equal? (normalize-type '(Union (Borrowed Int 0) (Borrowed Int 0)))
              '(Borrowed Int 0))

;; borrowed-owned-payload が返り、non-normal-type が返らないことを固定する。
;; 束縛子は G2 の形であり bmode を伴う。bmode を落とすと G2 の Core にならず、
;; 入口検査が先に落ちて E-BOR-001 へ届かない。
(define bad-core '(Let (x const (Borrowed (Owned Int) 0)) 1 x))
(define diag (core-type-of/diagnostic bad-core '() '()))
(check-equal? (diagnostic-id diag) "E-BOR-001")
;; 汎用の key へ先に落ちていないことを、code の比較で固定する。
;; diagnostic-code-of は code 文字列そのものを返すため、重ねて包まない。
(check-not-equal? (diagnostic-id diag)
                  (diagnostic-code-of 'typing 'non-normal-type))

;; Proj は Record を要求する。Eliminate は data 型を要求する。
;; Move と Drop は所有を要求する（段 8 で Ψ の判定も加わる）。
;; いずれも Borrowed には当たらず、payload を露出できない。
(define env '((b (Borrowed (Record ((f Int imm))) 0))))

(check-equal? (core-type-of '(Proj b f) '() '() env) 'ill-typed)
(check-equal? (core-type-of '(Eliminate b ((Some (y) -> y))) '() '() env) 'ill-typed)
(check-equal? (core-type-of '(Move b) '() '() env) 'ill-typed)
(check-equal? (core-type-of '(Drop b) '() '() env) 'ill-typed)

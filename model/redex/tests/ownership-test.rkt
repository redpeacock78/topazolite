#lang racket/base

(require rackunit
         "../ownership.rkt")

;; 互換性述語の身代わり。ownership.rkt は候補選択にしか使わないため、
;; 単体テストでは「常に互換」と「型が完全一致するときだけ互換」の 2 種で足りる。
(define (always-compatible actual expected) #t)

(define owned '(Owned Res))

(test-case "最上位の record で余剰 Owned 欄が落ちると拒否する"
  (check-false
   (owned-narrowing-ok? `(Record ((x ,owned imm) (y Int imm)))
                        '(Record ((y Int imm)))
                        always-compatible)))

(test-case "余剰欄が Int だけの width narrowing は通す"
  (check-true
   (owned-narrowing-ok? '(Record ((x Int imm) (y Int imm)))
                        '(Record ((y Int imm)))
                        always-compatible)))

(test-case "入れ子の record の内側で落ちる場合も拒否する"
  (check-false
   (owned-narrowing-ok?
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) imm)))
    '(Record ((a (Record ((y Int imm))) imm)))
    always-compatible)))

(test-case "Borrowed の payload では打ち切る"
  (check-true
   (owned-narrowing-ok?
    `(Borrowed (Record ((x ,owned imm) (y Int imm))) 0)
    '(Borrowed (Record ((y Int imm))) 0)
    always-compatible)))

(test-case "Untrusted と Refined の payload を辿る"
  (check-false
   (owned-narrowing-ok?
    `(Untrusted (Record ((x ,owned imm) (y Int imm))))
    '(Untrusted (Record ((y Int imm))))
    always-compatible))
  (check-false
   (owned-narrowing-ok?
    `(Refined (Record ((x ,owned imm) (y Int imm))) (Prop p))
    '(Refined (Record ((y Int imm))) (Prop p))
    always-compatible)))

(test-case "NFn の返り値は共変に辿る"
  (check-false
   (owned-narrowing-ok?
    `(NFn (Int) (Record ((x ,owned imm) (y Int imm))) () ())
    '(NFn (Int) (Record ((y Int imm))) () ())
    always-compatible)))

(test-case "NFn の引数は反変に辿る"
  (check-false
   (owned-narrowing-ok?
    `(NFn ((Record ((y Int imm)))) Int () ())
    `(NFn ((Record ((x ,owned imm) (y Int imm)))) Int () ())
    always-compatible)))

;; Union は (Union 左 右) の 2 項形である。union-members が左右へ潜って
;; 要素列へ平坦化する。3 要素は右結合で (Union A (Union B C)) と書く。
(test-case "Union は安全な互換候補が一つあれば通す"
  ;; expected の第 1 候補は余剰 Owned を落とすが、第 2 候補は落とさない。
  (check-true
   (owned-narrowing-ok?
    `(Record ((x ,owned imm) (y Int imm)))
    `(Union (Record ((y Int imm)))
            (Record ((x ,owned imm) (y Int imm))))
    always-compatible)))

(test-case "Union は安全な候補が一つも無ければ拒否する"
  (check-false
   (owned-narrowing-ok?
    `(Record ((x ,owned imm) (y Int imm)))
    '(Union (Record ((y Int imm))) (Record ((z Int imm))))
    always-compatible)))

(test-case "Union の候補選択は互換性述語で絞る"
  ;; 安全な候補が互換でないなら、残る候補は安全でないので拒否になる。
  (define (only-narrow-compatible actual expected)
    (equal? expected '(Record ((y Int imm)))))
  (check-false
   (owned-narrowing-ok?
    `(Record ((x ,owned imm) (y Int imm)))
    `(Union (Record ((y Int imm)))
            (Record ((x ,owned imm) (y Int imm))))
    only-narrow-compatible)))

(test-case "actual 側が Union なら全 member が安全な候補を持つことを要求する"
  (check-false
   (owned-narrowing-ok?
    `(Union (Record ((y Int imm)))
            (Record ((x ,owned imm) (y Int imm))))
    '(Record ((y Int imm)))
    always-compatible)))

(test-case "mut 欄は辿らない"
  ;; compat? が mut を type-equiv? で閉じるため、narrowing は起きない。
  (check-true
   (owned-narrowing-ok?
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) mut)))
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) mut)))
    always-compatible)))

(test-case "Never と型が合わない組は検査対象なしとして通す"
  (check-true (owned-narrowing-ok? 'Never '(Record ((y Int imm)))
                                   always-compatible))
  (check-true (owned-narrowing-ok? 'Int 'Int always-compatible)))

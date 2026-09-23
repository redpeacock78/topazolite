#lang racket/base

(require rackunit
         "../ownership.rkt")

;; 互換性述語の身代わり。ownership.rkt は候補選択にしか使わないため、
;; 単体テストでは「常に互換」と「型が完全一致するときだけ互換」の 2 種で足りる。
(define (always-compatible actual expected) #t)

(define owned '(Owned Res))

(test-case "最上位の record で余剰 Owned 欄が落ちると義務を返す"
  (check-equal?
   (owned-narrowing-kind `(Record ((x ,owned imm) (y Int imm)))
                         '(Record ((y Int imm)))
                         always-compatible)
   `(drop-obligation (Record ((x ,owned imm) (y Int imm)))
                     (Record ((y Int imm))))))

(test-case "余剰欄が Int だけの width narrowing は通す"
  (check-equal?
   (owned-narrowing-kind '(Record ((x Int imm) (y Int imm)))
                         '(Record ((y Int imm)))
                         always-compatible)
   'ok))

(test-case "入れ子の record の内側で落ちると拒否する"
  (check-equal?
   (owned-narrowing-kind
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) imm)))
    '(Record ((a (Record ((y Int imm))) imm)))
    always-compatible)
   'reject))

(test-case "Borrowed の payload では打ち切る"
  (check-equal?
   (owned-narrowing-kind
    `(Borrowed (Record ((x ,owned imm) (y Int imm))) 0)
    '(Borrowed (Record ((y Int imm))) 0)
    always-compatible)
   'ok))

(test-case "Untrusted と Refined の payload を辿る"
  (check-equal?
   (owned-narrowing-kind
    `(Untrusted (Record ((x ,owned imm) (y Int imm))))
    '(Untrusted (Record ((y Int imm))))
    always-compatible)
   'reject)
  (check-equal?
   (owned-narrowing-kind
    `(Refined (Record ((x ,owned imm) (y Int imm))) (Prop p))
    '(Refined (Record ((y Int imm))) (Prop p))
    always-compatible)
   'reject))

(test-case "NFn の返り値は共変に辿る"
  (check-equal?
   (owned-narrowing-kind
    `(NFn (Int) (Record ((x ,owned imm) (y Int imm))) () () () User)
    '(NFn (Int) (Record ((y Int imm))) () () () User)
    always-compatible)
   'reject))

(test-case "NFn の引数は反変に辿る"
  (check-equal?
   (owned-narrowing-kind
    `(NFn ((Record ((y Int imm)))) Int () () () User)
    `(NFn ((Record ((x ,owned imm) (y Int imm)))) Int () () () User)
    always-compatible)
   'reject))

;; Union は (Union 左 右) の 2 項形である。union-members が左右へ潜って
;; 要素列へ平坦化する。3 要素は右結合で (Union A (Union B C)) と書く。
(test-case "Union は安全な互換候補が一つあれば通す"
  ;; expected の第 1 候補は余剰 Owned を落とすが、第 2 候補は落とさない。
  (check-equal?
   (owned-narrowing-kind
    `(Record ((x ,owned imm) (y Int imm)))
    `(Union (Record ((y Int imm)))
            (Record ((x ,owned imm) (y Int imm))))
    always-compatible)
   'ok))

(test-case "Union は安全な候補が一つも無ければ拒否する"
  (check-equal?
   (owned-narrowing-kind
    `(Record ((x ,owned imm) (y Int imm)))
    '(Union (Record ((y Int imm))) (Record ((z Int imm))))
    always-compatible)
   'reject))

(test-case "Union の候補選択は互換性述語で絞る"
  ;; 安全な候補が互換でないなら、残る候補は安全でないので拒否になる。
  (define (only-narrow-compatible actual expected)
    (equal? expected '(Record ((y Int imm)))))
  (check-equal?
   (owned-narrowing-kind
    `(Record ((x ,owned imm) (y Int imm)))
    `(Union (Record ((y Int imm)))
            (Record ((x ,owned imm) (y Int imm))))
    only-narrow-compatible)
   'reject))

(test-case "actual 側が Union なら全 member が安全な候補を持つことを要求する"
  (check-equal?
   (owned-narrowing-kind
    `(Union (Record ((y Int imm)))
            (Record ((x ,owned imm) (y Int imm))))
    '(Record ((y Int imm)))
    always-compatible)
   'reject))

(test-case "mut 欄は辿らない"
  ;; compat? が mut を type-equiv? で閉じるため、narrowing は起きない。
  ;; mut 欄を辿る実装ならここが 'reject になる。
  (check-equal?
   (owned-narrowing-kind
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) mut)))
    '(Record ((a (Record ((y Int imm))) mut)))
    always-compatible)
   'ok))

(test-case "Never と型が合わない組は検査対象なしとして通す"
  (check-equal? (owned-narrowing-kind 'Never '(Record ((y Int imm)))
                                      always-compatible)
                'ok)
  (check-equal? (owned-narrowing-kind 'Int 'Int always-compatible)
                'ok))

(test-case "check-narrowing-return は 3 つの kind だけを通す"
  (define a '(Record ((x (Owned Res) imm))))
  (define e '(Record ()))
  (check-true  (check-narrowing-return (list a e values) (list 'ok)))
  (check-true  (check-narrowing-return (list a e values) (list 'reject)))
  (check-true  (check-narrowing-return (list a e values)
                                       (list `(drop-obligation ,a ,e))))
  (check-false (check-narrowing-return (list a e values) (list #t)))
  (check-false (check-narrowing-return (list a e values)
                                       (list `(drop-obligation ,e ,a))))
  (check-false (check-narrowing-return (list a e values)
                                       (list '(drop-obligation Nope Nope))))
  (check-false (check-narrowing-return (list a e) (list 'ok))))

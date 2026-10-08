#lang racket/base

(require rackunit
         racket/list
         racket/match
         "../compat.rkt"
         "../ownership.rkt"
         "row005-property-support.rkt")

;; 互換性述語の身代わり。ownership.rkt は候補選択にしか使わないため、
;; 単体テストでは「常に互換」と「型が完全一致するときだけ互換」の 2 種で足りる。
(define (always-compatible actual expected) #t)

(define owned '(Owned Res))

(define nested-two-wide
  `(Record ((a (Record ((x ,owned imm) (y Int imm))) imm))))
(define nested-two-narrow
  '(Record ((a (Record ((y Int imm))) imm))))
(define nested-three-wide
  `(Record ((a (Record ((b (Record ((x ,owned imm) (y Int imm))) imm)
                       (z Int imm))) imm))))
(define nested-three-narrow
  '(Record ((a (Record ((b (Record ((y Int imm))) imm)
                       (z Int imm))) imm))))
(define nested-required-optional-wide
  `(Record ((a (Record ((x ,owned imm) (y Int imm))) imm))))
(define nested-required-optional-narrow
  '(Record ((a (Record ((y Int imm))) imm opt))))

(define (shape-by-label shape)
  (and shape
       (sort
        (for/list ([entry (in-list shape)])
          (match entry
            [(list label 'drop optional?) (list label 'drop optional?)]
            [(list label 'nested optional? child)
             (list label 'nested optional? (shape-by-label child))]))
        symbol<? #:key first)))

(define (check-target-layout actual target shape)
  (match* (actual target)
    [(`(Record ,actual-row) `(Record ,target-row))
     (define dropped
       (for/list ([entry (in-list shape)]
                  #:when (eq? (second entry) 'drop))
         (first entry)))
     (define retained
       (filter (lambda (field) (not (memq (first field) dropped))) actual-row))
     (check-equal? (map first target-row) (map first retained))
     (for ([target-field (in-list target-row)]
           [actual-field (in-list retained)])
       (check-equal? (third target-field) (third actual-field))
       (check-equal? (length target-field) (length actual-field))
       (check-equal? (if (= (length target-field) 4) (fourth target-field) #f)
                     (if (= (length actual-field) 4) (fourth actual-field) #f))
       (define nested
         (for/first ([entry (in-list shape)]
                     #:when (and (eq? (first entry) (first target-field))
                                 (eq? (second entry) 'nested)))
           entry))
       (when nested
         (check-target-layout (second actual-field) (second target-field)
                              (fourth nested))))]
    [(_ _) (void)]))

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

(test-case "imm Record の共通欄の 2 段と 3 段の Owned 損失は最上位の義務になる"
  (check-equal?
   (owned-narrowing-kind nested-two-wide nested-two-narrow
                         always-compatible)
   `(drop-obligation ,nested-two-wide ,nested-two-narrow))
  (check-equal?
   (owned-narrowing-kind nested-three-wide nested-three-narrow
                         always-compatible)
   `(drop-obligation ,nested-three-wide ,nested-three-narrow)))

(test-case "最上位と入れ子の Owned 損失は一つの最上位義務になる"
  (define actual
    `(Record ((outer ,owned imm)
              (a (Record ((x ,owned imm) (y Int imm))) imm))))
  (define expected
    '(Record ((a (Record ((y Int imm))) imm))))
  (check-equal?
   (owned-narrowing-kind actual expected
                         always-compatible)
   `(drop-obligation ,actual ,expected)))

(test-case "入れ子義務は imm Record の共通欄の鎖だけを通る"
  (define (nested-union-compatible? actual expected)
    (or (equal? actual expected)
        (and (equal? actual `(Record ((x ,owned imm) (y Int imm))))
             (equal? expected '(Record ((y Int imm)))))))
  (define union-wide
    `(Record ((f (Union (Record ((x ,owned imm) (y Int imm))) Bool) imm))))
  (define union-narrow
    '(Record ((f (Union (Record ((y Int imm))) Bool) imm))))
  (define owned-wide
    `(Record ((f (Owned (Record ((x ,owned imm) (y Int imm)))) imm))))
  (define owned-narrow
    `(Record ((f (Owned (Record ((y Int imm)))) imm))))
  (define untrusted-wide
    `(Record ((f (Untrusted (Record ((x ,owned imm) (y Int imm)))) imm))))
  (define untrusted-narrow
    '(Record ((f (Untrusted (Record ((y Int imm)))) imm))))
  (define refined-wide
    `(Record ((f (Refined (Record ((x ,owned imm) (y Int imm)))
                         (Prop p)) imm))))
  (define refined-narrow
    '(Record ((f (Refined (Record ((y Int imm))) (Prop p)) imm))))
  (check-equal? (owned-narrowing-kind union-wide union-narrow
                                      nested-union-compatible?)
                'reject)
  (check-equal? (owned-narrowing-kind owned-wide owned-narrow
                                      always-compatible)
                'reject)
  (check-equal? (owned-narrowing-kind untrusted-wide untrusted-narrow
                                      always-compatible)
                'reject)
  (check-equal? (owned-narrowing-kind refined-wide refined-narrow
                                      always-compatible)
                'reject))

(test-case "入れ子義務の shape は型対を保ち、除去欄を列挙する"
  (check-equal? (remainder-removal-shape nested-two-wide nested-two-narrow)
                '((a nested #f ((x drop #f)))))
  (check-equal? (remainder-removal-shape nested-three-wide nested-three-narrow)
                '((a nested #f ((b nested #f ((x drop #f)))))))
  (check-equal?
   (owned-narrowing-kind nested-required-optional-wide
                         nested-required-optional-narrow
                         always-compatible)
   `(drop-obligation ,nested-required-optional-wide
                     ,nested-required-optional-narrow))
  (check-equal?
   (remainder-removal-shape nested-required-optional-wide
                            nested-required-optional-narrow)
   '((a nested #f ((x drop #f))))))

(test-case "optional な入れ子欄の shape は実際の optional 属性を保持する"
  (define actual
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) imm opt))))
  (define expected
    '(Record ((a (Record ((y Int imm))) imm opt))))
  (check-equal?
   (remainder-removal-shape actual expected)
   '((a nested #t ((x drop #f)))))
  (check-equal?
   (owned-narrowing-kind actual expected always-compatible)
   `(drop-obligation ,actual ,expected)))

(test-case "remainder-target-type は shape の欄だけを actual から取り除く"
  (define actual
    `(Record ((outer ,owned imm)
              (a (Record ((x ,owned imm opt)
                          (kept Int imm)
                          (tail Int imm opt))) imm opt)
              (tail Int imm))))
  (define expected
    '(Record ((a (Record ((kept Int imm))) imm opt)
              (tail Int imm))))
  (check-equal?
   (remainder-target-type actual expected)
   '(Record ((a (Record ((kept Int imm) (tail Int imm opt))) imm opt)
             (tail Int imm))))
  (define optional-removal-actual
    `(Record ((kept Int imm) (drop ,owned imm opt))))
  (define optional-removal-expected '(Record ((kept Int imm))))
  (check-equal?
   (remainder-target-type optional-removal-actual optional-removal-expected)
   '(Record ((kept Int imm))))
  (define owned-free-actual '(Record ((extra Int imm) (kept Int imm))))
  (check-equal?
   (remainder-target-type owned-free-actual '(Record ((kept Int imm))))
   owned-free-actual)
  (check-false (remainder-target-type actual 'Int)))

(test-case "有限な全 drop-obligation 対で target は互換かつ shape と layout を保つ"
  (define obligation-pairs
    (for*/list ([actual (in-list R)]
                [expected (in-list R)]
                #:when (eq? (case-class actual expected) 'drop-obligation))
      (list actual expected)))
  (check-equal? (length obligation-pairs) 11)
  (for ([pair (in-list obligation-pairs)])
    (define actual (first pair))
    (define expected (second pair))
    (define target (remainder-target-type actual expected))
    (check-not-false target)
    (check-equal? (owned-narrowing-kind target expected compat?) 'ok)
    (check-true (compat? target expected))
    (check-equal? (shape-by-label (remainder-removal-shape actual target))
                  (shape-by-label (remainder-removal-shape actual expected)))
    (check-target-layout actual target
                         (remainder-removal-shape actual expected))))

(test-case "必須 actual 欄を optional expected 欄へ対応させても必須を保つ"
  (define top-actual `(Record ((drop ,owned imm) (kept Int imm))))
  (define top-expected '(Record ((kept Int imm opt))))
  (define top-target (remainder-target-type top-actual top-expected))
  (check-equal? top-target '(Record ((kept Int imm))))
  (check-true (compat? top-target top-expected))
  (define nested-actual
    `(Record ((box (Record ((drop ,owned imm) (kept Int imm))) imm))))
  (define nested-expected
    '(Record ((box (Record ((kept Int imm opt))) imm))))
  (define nested-target
    (remainder-target-type nested-actual nested-expected))
  (check-equal? nested-target
                '(Record ((box (Record ((kept Int imm))) imm))))
  (check-true (compat? nested-target nested-expected)))

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

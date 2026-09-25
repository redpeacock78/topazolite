#lang racket

;; BIT-003。型位置の | と & を Core の Union と Intersection へ落とす部分の回帰である。

(require rackunit
         racket/match
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../traits.rkt")

(define (lower str)
  (lower-surface (parse (lex/string 'src str)) canonical-trait-env))
(define (code str)
  (define r (lower str))
  (and (diagnostic? r) (diagnostic-id r)))
(define (primary str)
  (diagnostic-primary-span (lower str)))
(define (sp lo hi) `(#:span src ,lo ,hi))
(define (compile str) (compile-source/string 'src str))

(define (derive-size src)
  (match (lowered-term (lower src))
    [`(Let ,_ ,_
           (Apply ,_ ,_ (Rec ,_ (((#:lbl size ,_) imm
                                  (Fn ,_ ,_ ,_ ,_ (#:lit ,n ,_))))))
           ,_)
     n]
    [other (fail-check (format "unexpected derive term ~s" other))]))

(test-case
 "BIT-003: 別名を注釈で使うと、Union は正規化した注釈になる"
 ;; 型別名は Core の項を作らないので、注釈で使う形でだけ検査する。
 (define r (compile "type Identifier = String | Int\nlet x: Identifier = 1\nx"))
 (check-true (compiled? r) (format "compile failed: ~s" r))
 (check-equal? (compiled-type r) '(Union Int String)))

(test-case
 "BIT-003: Record の Intersection は一つの Record に正規化される"
 (define r (compile (string-append
                     "fn bool(x: Bool) -> Bool { x }\n"
                     "let r: { a: Int } & { b: Bool } = { a: 1, b: bool(true) }\nr")))
 (check-true (compiled? r) (format "compile failed: ~s" r))
 (check-equal? (compiled-type r) '(Record ((a Int imm) (b Bool imm)))))

(test-case
 "BIT-003: Union の注釈は elaborate と typing を通る"
 (check-true (compiled? (compile "let x: Int | String = 1\nx"))))

(test-case
 "BIT-003: 正規化できない & は E-SUR-020 で、失敗した TInter を指す"
 ;; 別名定義。"type T = " は 9 byte である。
 (check-equal? (code "type T = Int & { a: Int }\n0") "E-SUR-020")
 (check-equal? (primary "type T = Int & { a: Int }\n0") (sp 9 25))
 ;; let の注釈。同じ label を両辺が持つ。
 (check-equal? (code "let x: { a: Int } & { a: Bool } = 0\nx") "E-SUR-020")
 (check-equal? (primary "let x: { a: Int } & { a: Bool } = 0\nx") (sp 7 31))
 ;; 関数の注釈。Union は Record に正規化されない。括弧は span を広げない。
 (define fn-src "fn(x: ({ a: Int } | { b: Int }) & { c: Int }) -> Int { 0 }")
 (check-equal? (code fn-src) "E-SUR-020")
 (check-equal? (primary fn-src) (sp 7 44))
 ;; trait template。
 (check-equal? (code "trait P { f: Int & { a: Int } }\n0") "E-SUR-020")
 (check-equal? (primary "trait P { f: Int & { a: Int } }\n0") (sp 13 29))
 ;; derive の対象型。
 (check-equal? (code "derive Sizable for Int & { a: Int }\n0") "E-SUR-020")
 (check-equal? (primary "derive Sizable for Int & { a: Int }\n0") (sp 19 35))
 ;; impl の対象型。本体の注釈も同じ型なので、primary span は検査しない。
 (check-equal?
  (code "impl Sizable for Int & { a: Int } { size: fn(x: Int & { a: Int }) -> Int { 0 } }\n0")
  "E-SUR-020"))

(test-case
 "BIT-003: 入れ子の & では最も内側の失敗した節点を指す"
 ;; "let x: (" は 8 byte である。
 (define src "let x: ({ a: Int } & { a: Bool }) & { c: Int } = 0\nx")
 (check-equal? (code src) "E-SUR-020")
 (check-equal? (primary src) (sp 8 32)))

(test-case
 "BIT-003: Self を含む & は trait 宣言の時点では検査しない"
 (check-true (lowered? (lower "trait P { f: Self & { required: Int } }\n0"))))

(test-case
 "BIT-003: Self を含む & は impl の対象型で具体化して正規化する"
 (define src (string-append "fn bool(x: Bool) -> Bool { x }\n"
                            "trait P { f: Self & { required: Int } }\n"
                            "impl P for { own: Bool } { f: { own: bool(true), required: 1 } }\n0"))
 (define low (lower src))
 (check-true (lowered? low) (format "lower failed: ~s" low))
 (define trait-row (findf (λ (r) (eq? (second r) 'P)) (lowered-trait-rows low)))
 (define impl-row (first (lowered-impl-rows low)))
 (check-equal? (instantiate-requirements (trait-template trait-row)
                                         (impl-target-type impl-row))
               '((f (Record ((own Bool imm) (required Int imm))) imm)))
 (check-true (compiled? (compile src)) (format "compile failed: ~s" (compile src))))

(test-case
 "BIT-003: 具体化した要求型が正規化できない impl は E-SUR-020 で、対象型を指す"
 ;; 1 行目は 39 byte と改行なので、2 行目は 40 から始まる。
 ;; "impl " の後の P は 45 から 46、" for " の後の Int は 51 から 54 である。
 (define src "trait P { f: Self & { required: Int } }\nimpl P for Int { f: 1 }\n0")
 (define d (lower src))
 (check-equal? (diagnostic-id d) "E-SUR-020")
 (check-equal? (diagnostic-primary-span d) (sp 51 54))
 (check-equal? (diagnostic-related d)
               (list (list 'trait-requirement (sp 45 46)
                           "trait P の要求 f を正規化できない"))))

(test-case
 "BIT-003: 生成規則の無い derive は E-SUR-020 より先に E-SUR-019 になる"
 (check-equal?
  (code "trait P { f: Self & { required: Int } }\nderive P for Int\n0")
  "E-SUR-019"))

(test-case
 "BIT-003: label の Self は型の Self ではないので、宣言の時点で検査する"
 ;; span は "trait P { f: " の後の 13 から、左 operand 13 byte、" & " 3 byte、右 operand 14 byte を足した 43 まで。
 (define src "trait P { f: { Self: Int } & { Self: Bool } }\n0")
 (define d (lower src))
 (check-equal? (diagnostic-id d) "E-SUR-020")
 (check-equal? (diagnostic-primary-span d) (sp 13 43))
 (check-equal? (diagnostic-related d) '()))

(test-case
 "BIT-003: Self を含む Union の要求型は具体化した後に正規化される"
 ;; 置き換えただけの (Union Bool (Union Bool String)) は正規形でなく、
 ;; 正規化しないと check-env! の内部検査で落ちる。
 (define src "trait Q { f: Bool | Self }\nimpl Q for Bool | String { f: true }\n0")
 (define low (lower src))
 (check-true (lowered? low) (format "lower failed: ~s" low))
 (define trait-row (findf (λ (r) (eq? (second r) 'Q)) (lowered-trait-rows low)))
 (check-equal? (instantiate-requirements (trait-template trait-row)
                                         (impl-target-type (first (lowered-impl-rows low))))
               '((f (Union Bool String) imm))))

(test-case
 "BIT-003: operand の中の誤りが E-SUR-020 より先に出る"
 (check-equal? (code "let x: { a: Unknown } & { b: Int } = 0\nx") "E-SUR-008"))

(test-case
 "BIT-003: Sizable の Union は正規化した成分の葉の数の和である"
 (check-equal? (derive-size "derive Sizable for Int | String\n0") 2)
 ;; 正規化で重複が除かれ Bool になる。
 ;; Int の既定 derive 行と重複しない Bool を使い、Union の重複除去を検査する。
 (check-equal? (derive-size "derive Sizable for Bool | Bool\n0") 1)
 (check-equal? (derive-size "derive Sizable for { a: Int } & { b: Bool }\n0") 2))

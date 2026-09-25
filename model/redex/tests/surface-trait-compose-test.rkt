#lang racket

;; SUR-009。trait と型の名前空間、および trait 合成の lowering の回帰である。

(require rackunit
         racket/match
         redex/reduction-semantics
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../traits.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../origins.rkt"
         "../search.rkt")

(define (parse-src str) (parse (lex/string 'src str)))
(define (lower str [base canonical-trait-env]) (lower-surface (parse-src str) base))
(define (code str [base canonical-trait-env])
  (define r (lower str base))
  (and (diagnostic? r) (diagnostic-id r)))

;; 基底に行を足した環境である。基底の構築が失敗するのは試験の誤りである。
(define (base+ #:trait [trait-rows '()] #:intersect [intersect-rows '()])
  (make-trait-env
   #:trait (append (trait-env-trait-rows canonical-trait-env) trait-rows)
   #:impl (trait-env-impl-rows canonical-trait-env)
   #:intersect (append (trait-env-intersect-rows canonical-trait-env) intersect-rows)
   #:scope (trait-env-scope-rows canonical-trait-env)
   #:fail (λ (r k key) (error 'test "bad base ~s ~s ~s" r k key))))

(define rw-src "trait Readable { }\ntrait Writable { }\n")

(define (implements? src goal)
  (define r (compile-source/string 'src src))
  (unless (compiled? r) (fail-check (format "compile failed: ~s" r)))
  (call-with-trait-ledger
   (compiled-ledger r)
   (λ () (not (null? (project-goal (current-Γ-pc0) '(root) (make-goal goal)))))))

;; str の中で n 番目（0 始まり）に現れる sub の span である。
(define (nth-span str sub [n 0])
  (define p (list-ref (regexp-match-positions* (regexp-quote sub) str) n))
  `(#:span src ,(car p) ,(cdr p)))

(define (check-diagnostic str id sub n [related '()])
  (define d (lower str))
  (check-true (diagnostic? d) (format "~s が Diagnostic になる" str))
  (check-equal? (diagnostic-id d) id)
  (check-equal? (diagnostic-primary-span d) (nth-span str sub n))
  (check-equal? (diagnostic-related d) related))

(test-case
 "SUR-009: trait 名を型の位置で使うと E-SUR-021 になる"
 (for ([c (in-list
           (list (list "trait R { }\n{ let x: R = 1\n x }" "R" 1)
                 (list "type N = Printable\n0" "Printable" 0)
                 (list "type N = Printable | Sizable\n0" "Printable" 0)
                 (list "type N = Int & Printable\n0" "Printable" 0)
                 (list "type N = { a: Printable }\n0" "Printable" 0)
                 (list "trait Q { f: Printable }\n0" "Printable" 0)
                 (list "trait R { }\nimpl R for Printable { }\n0" "Printable" 0)))])
   (check-diagnostic (first c) "E-SUR-021" (second c) (third c))))

(test-case
 "SUR-009: 未知の名前が trait 名より左にあれば E-SUR-008 になる"
 (check-diagnostic "type N = Foo & Printable\n0" "E-SUR-008" "Foo" 0))

(test-case
 "SUR-009: 型と trait の名前の衝突は宣言の順によらず型の側で E-SUR-023 になる"
 (define a "trait Foo { }\ntype Foo = Int\n0")
 (check-diagnostic a "E-SUR-023" "Foo" 1
                   (list (list 'trait-declaration (nth-span a "Foo" 0) "trait Foo の宣言")))
 (define b "type Foo = Int\ntrait Foo { }\n0")
 (check-diagnostic b "E-SUR-023" "Foo" 0
                   (list (list 'trait-declaration (nth-span b "Foo" 1) "trait Foo の宣言"))))

(test-case
 "SUR-009: 基底の trait 名の型と基本型名の trait は related を持たない E-SUR-023 になる"
 (check-diagnostic "type Printable = Int\n0" "E-SUR-023" "Printable" 0)
 (check-diagnostic "trait Int { }\n0" "E-SUR-023" "Int" 0))

(test-case
 "SUR-009: 二項の合成は合成 trait 行と intersect 行を 1 つずつ作る"
 (define low (lower (string-append rw-src "type RW = Readable & Writable\n0")))
 (check-true (lowered? low))
 (check-equal? (lowered-intersect-rows low)
               '((o-intersect-user-1 intersect-user-1 Readable Writable RW)))
 (check-equal? (last (lowered-trait-rows low)) '(o-trait-user-RW RW root ())))

(test-case
 "SUR-009: 合成 trait の Implements は成分の impl から解ける"
 (check-true
  (implements? (string-append rw-src
                              "type RW = Readable & Writable\n"
                              "impl Readable for Bool { }\nimpl Writable for Bool { }\n0")
               '(Implements Bool RW))))

(test-case
 "SUR-009: 三項の合成は隠れた出力を内側に持つ入れ子になる"
 (define src (string-append rw-src "trait Extra { }\n"
                            "type RWX = Readable & Writable & Extra\n"))
 (define low (lower (string-append src "0")))
 (check-equal? (lowered-intersect-rows low)
               '((o-intersect-user-1 intersect-user-1 Readable Writable %compose-1)
                 (o-intersect-user-2 intersect-user-2 %compose-1 Extra RWX)))
 (check-true
  (implements? (string-append src
                              "impl Readable for Bool { }\nimpl Writable for Bool { }\n"
                              "impl Extra for Bool { }\n0")
               '(Implements Bool RWX))))

(test-case
 "SUR-009: 内側の鍵に名前を付けた宣言が後にあれば、その名前を出力にする"
 (define low (lower "trait A { }\ntrait B { }\ntrait C { }\ntype X = A & B & C\ntype AB = A & B\n0"))
 (check-equal? (lowered-intersect-rows low)
               '((o-intersect-user-1 intersect-user-1 A B AB)
                 (o-intersect-user-2 intersect-user-2 AB C X))))

(test-case
 "SUR-009: 同じ鍵の宣言は先の宣言の別名になり、impl は E-SUR-018 になる"
 (define src (string-append rw-src "type RW = Readable & Writable\ntype WR = Writable & Readable\n"))
 (define low (lower (string-append src "0")))
 (check-equal? (length (lowered-intersect-rows low)) 1)
 (check-equal? (code (string-append src "impl WR for Bool { }\n0")) "E-SUR-018"))

(test-case
 "SUR-009: 基底と同じ鍵の合成は行を作らず、基底の台帳を使い回す"
 (for ([src (in-list (list "type PS = Printable & Sizable\n0"
                           "type PST = Printable & Sizable & Taggable\n0"))])
   (define low (lower src))
   (check-equal? (lowered-trait-rows low) '())
   (check-equal? (lowered-intersect-rows low) '())
   (define r (compile-source/string 'src src))
   (check-eq? (compiled-ledger r) canonical-trait-ledger)))

(test-case
 "SUR-009: 括弧で右に寄せた三項は基底と別の鍵になり、行を 1 つ作る"
 (define low (lower "type P_ST = Printable & (Sizable & Taggable)\n0"))
 (check-equal? (lowered-intersect-rows low)
               '((o-intersect-user-1 intersect-user-1 Printable SizableTaggable P_ST))))

(define (operands str l-sub l-n r-sub r-n)
  (list (list 'composition-left (nth-span str l-sub l-n) (format "`&` の左辺 ~a" l-sub))
        (list 'composition-right (nth-span str r-sub r-n) (format "`&` の右辺 ~a" r-sub))))

(test-case
 "SUR-009: 同じ鍵の trait を並べると E-SUR-022 になる"
 (define a "type D = Printable & Printable\n0")
 (define d (lower a))
 (check-equal? (diagnostic-id d) "E-SUR-022")
 (check-equal? (diagnostic-primary-span d)
               (nth-span a "Printable & Printable"))
 (check-equal? (diagnostic-related d) (operands a "Printable" 0 "Printable" 1))
 (check-equal?
  (code "type A = Printable & Sizable\ntype B = Sizable & Printable\ntype C = A & B\n0")
  "E-SUR-022"))

(test-case
 "SUR-009: label が衝突する trait を並べると E-SUR-022 になる"
 (check-equal? (code "trait Q { size: Int }\ntype D = Q & Sizable\n0") "E-SUR-022"))

(test-case
 "SUR-009: 合成宣言の循環は循環を閉じた葉で E-SUR-010 になる"
 (check-diagnostic "type A = B & Printable\ntype B = A & Sizable\n0"
                   "E-SUR-010" "A" 1))

(test-case
 "SUR-009: 合成宣言の名前を型の位置で使うと E-SUR-021 になる"
 (check-diagnostic "type PS = Printable & Sizable\n{ let x: PS = 1\n x }"
                   "E-SUR-021" "PS" 1))

(test-case
 "SUR-009: 合成 trait 行の origin id が基底と衝突すると宣言の span で E-SUR-016 になる"
 (define src (string-append rw-src "type RW = Readable & Writable\n0"))
 (define d (lower src (base+ #:trait '((o-trait-user-RW Legacy root ())))))
 (check-equal? (diagnostic-id d) "E-SUR-016")
 (check-equal? (diagnostic-primary-span d)
               (nth-span src "type RW = Readable & Writable")))

(test-case
 "SUR-009: intersect 行の番号は基底の o-intersect-user- の最大の次になる"
 (define base
   (base+ #:trait '((o-trait-user-A A root ((a Int imm)))
                    (o-trait-user-B B root ((b Int imm)))
                    (o-trait-user-AB AB root ((a Int imm) (b Int imm))))
          #:intersect '((o-intersect-user-3 intersect-user-3 A B AB))))
 (check-equal? (map first (lowered-intersect-rows (lower "type SA = Sizable & A\n0" base)))
               '(o-intersect-user-4)))

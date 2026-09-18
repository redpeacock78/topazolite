#lang racket

(require rackunit
         "../lexer.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../diagnostic.rkt")

;; parse を通してから落とす。span を手で組むより、実際に走る経路と同じ形で
;; 回帰できる。
(define (low str) (lower-surface (parse (lex/string 'src str))))
(define (code str)
  (define r (low str))
  (and (diagnostic? r) (diagnostic-id r)))

(test-case
 "前方参照を許す"
 ;; spec §6。1 度目で全宣言を読み終えてから展開するので、宣言の並び順に
 ;; 依らない。
 (check-false (diagnostic? (low "type A = { a: B, b: B }\ntype B = Int\n1")))
 (check-false (diagnostic? (low "type B = Int\ntype A = { a: B, b: B }\n1"))))

(test-case
 "表に無い非原始型の名前は E-SUR-008 である"
 (check-equal? (code "type A = B\n1") "E-SUR-008"))

(test-case
 "原始型の名前は表を引かずに通る"
 (check-false (diagnostic? (low "type A = Int\n1")))
 (check-false (diagnostic? (low "type A = { a: Bool, b: String, c: Unit }\n1"))))

(test-case
 "同じ名前の宣言が 2 つあれば E-SUR-009 である"
 (check-equal? (code "type A = Int\ntype A = Bool\n1") "E-SUR-009")
 ;; primary span は 2 つ目の SName である
 (check-equal? (diagnostic-primary-span (low "type A = Int\ntype A = Bool\n1"))
               '(#:span src 18 19)))

(test-case
 "原始型の名前を別名にすると E-SUR-011 である"
 (check-equal? (code "type Int = Bool\n1") "E-SUR-011")
 (check-equal? (code "type String = Int\n1") "E-SUR-011")
 ;; spec §6.1。原始型の検査が重複の検査より先なので、2 回書いても
 ;; E-SUR-011 が 1 つ目の宣言で出る。
 (check-equal? (code "type Int = Bool\ntype Int = Unit\n1") "E-SUR-011")
 (check-equal? (diagnostic-primary-span (low "type Int = Bool\ntype Int = Unit\n1"))
               '(#:span src 5 8)))

(test-case
 "自分自身を参照する別名は E-SUR-010 である"
 (check-equal? (code "type A = A\n1") "E-SUR-010")
 ;; primary span は定義の中の参照であり、宣言している SName ではない
 (check-equal? (diagnostic-primary-span (low "type A = A\n1"))
               '(#:span src 9 10)))

(test-case
 "2 つの宣言をまたぐ循環は E-SUR-010 である"
 (check-equal? (code "type A = { a: B }\ntype B = { b: A }\n1") "E-SUR-010"))

(test-case
 "共有は循環ではない"
 ;; spec §6。展開中の別名を stack で持ち、終わったら降ろす。
 ;; 「一度でも展開した名前の集合」で判定すると、この例を誤って拒む。
 (check-false (diagnostic? (low "type B = Int\ntype A = { a: B, b: B }\n1"))))

(test-case
 "record 型の重複した label は E-SUR-007 である"
 (check-equal? (code "type A = { a: Int, a: Bool }\n1") "E-SUR-007")
 ;; primary span は 2 つ目の TField の slabel である
 (check-equal? (diagnostic-primary-span (low "type A = { a: Int, a: Bool }\n1"))
               '(#:span src 19 20))
 ;; spec §6.1。3 つ以上あっても最初の 2 度目だけを返す
 (check-equal? (diagnostic-primary-span
                (low "type A = { a: Int, a: Bool, a: Unit }\n1"))
               '(#:span src 19 20)))

(test-case
 "診断は 1 件だけ返る"
 ;; spec §6.1。名前の誤りがあれば 2 度目の走査へ入らない。
 (define r (low "type Int = Bool\ntype A = C\n1"))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-id r) "E-SUR-011"))

;; 多段の展開である。parser は Fn の本体を必ず SBlock にするので、
;; Surface の項を手で組む。
(define s0 '(#:span src 0 1))
(define (prog items e) `(SProgram ,s0 ,items ,e))
(define (decl name ty) `(STypeDecl ,s0 (SName ,s0 ,name) ,ty))
(define (fn-of ty) `(SFn ,s0 ((SParam ,s0 (SName ,s0 x) ,ty)) ,ty (SVar ,s0 x)))
(define (param-type items ty)
  (define r (lower-surface (prog items (fn-of ty))))
  (second (second (first (third r)))))

(test-case
 "別名は不動点まで展開する"
 (check-equal? (param-type (list (decl 'A `(TName ,s0 B))
                                 (decl 'B `(TName ,s0 Int)))
                           `(TName ,s0 A))
               'Int))

(test-case
 "record 型の別名は Record の行になり、欄の可変性は imm である"
 (check-equal? (param-type (list (decl 'A `(TRec ,s0 ((TField ,s0 (SLabel ,s0 a)
                                                              (TName ,s0 Int))))))
                           `(TName ,s0 A))
               '(Record ((a Int imm)))))

(test-case
 "関数型は効果行と義務が空の NFn になる"
 (check-equal? (param-type '() `(TFn ,s0 ((TName ,s0 Int)) (TName ,s0 Bool)))
               '(NFn (Int) Bool () ())))

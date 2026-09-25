#lang racket

;; SUR-007。Surface の原文から Typed Core までの経路の回帰である。

(require rackunit
         "../driver.rkt"
         "../diagnostic.rkt")

(define (c str) (compile-source/string 'src str))
;; 相は Diagnostic の欄ではなく registry が持つ。code から行を引いて読む。
(define (phase-of d)
  (diagnostic-code-phase (diagnostic-code-row (diagnostic-id d))))

(define (code str)
  (define r (c str))
  (and (diagnostic? r) (diagnostic-id r)))

(test-case
 "整数だけの入力が型付きの成果物になる"
 (define r (c "1"))
 (check-true (compiled? r))
 (check-equal? (compiled-type r) 'Int)
 (check-equal? (compiled-row r) '()))

(test-case
 "関数宣言と適用が型付きの成果物になる"
 (define r (c "fn f(a: Int) -> Int { a }\nf(1)"))
 (check-true (compiled? r))
 (check-equal? (compiled-type r) 'Int))

(test-case
 "record リテラルと射影が型付きの成果物になる"
 (check-true (compiled? (c "{ a: 1 }")))
 (check-true (compiled? (c "{ let x = 1\n x }"))))

(test-case
 "const と let の束縛が型付きの成果物になる"
 (check-true (compiled? (c "type A = Int\nconst x: A = 1\nx")))
 (check-true (compiled? (c "{ let x = 1\n x }"))))

(test-case
 "lexer の診断がそのまま返る"
 (define r (compile-source 'src (bytes 97 255 98)))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-id r) "E-SUR-001")
 (check-equal? (phase-of r) 'surface))

(test-case
 "parser の診断がそのまま返る"
 (check-equal? (code "if cond { 1 }") "E-SUR-005")
 (check-equal? (code "") "E-SUR-006")
 (check-equal? (code "f(") "E-SUR-006"))

(test-case
 "型別名の診断がそのまま返る"
 (check-equal? (code "const x: Missing = 1\nx") "E-SUR-008"))

(test-case
 "elab の失敗は裸の Diagnostic であり err の包みが残らない"
 (define r (c "x"))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-id r) "E-VAR-002")
 (check-equal? (phase-of r) 'elaborate))

(test-case
 "展開表は elab へ素通しで渡る"
 (define bare (c "x"))
 (define s (diagnostic-primary-span bare))
 ;; frame は (nm s_call s_result) の 3 要素である（diagnostic.rkt:617）。
 (define frame (list (list 'm s s)))
 (define r (compile-source/string 'src "x" #:expansion-context (hash s frame)))
 (check-true (diagnostic? r))
 (check-equal? (diagnostic-expansion-trace r) frame)
 (check-equal? (diagnostic-expansion-trace bare) '()))

;; spec §10。成果物の core の節点が持つ span が、すべて入力の source-id を
;; 指し、親の span に包含されることを確かめる。個々の構成子を並べず走査で
;; 確かめるのは、lowering と elaboration の両方が節点を生成するためである。
(define (span-term? x)
  (and (list? x) (= (length x) 4) (eq? (first x) '#:span)))

(define (node-term? x)
  (and (list? x) (>= (length x) 2) (symbol? (first x))
       (span-term? (second x))))

(define (all-nodes x)
  (cond
    [(node-term? x) (cons x (append-map all-nodes (cddr x)))]
    [(list? x) (append-map all-nodes x)]
    [else '()]))

(define (span-within? inner outer)
  (and (eq? (second inner) (second outer))
       (>= (third inner) (third outer))
       (<= (fourth inner) (fourth outer))))

(define (containment-violations t)
  (for*/list ([n (in-list (all-nodes t))]
              [c (in-list (append-map all-nodes (cddr n)))]
              #:unless (span-within? (second c) (second n)))
    (list (first n) (second n) (first c) (second c))))

(define (foreign-source-ids t)
  (for/list ([n (in-list (all-nodes t))]
             #:unless (eq? (second (second n)) 'src))
    (list (first n) (second n))))

(test-case
 "成果物の span は入力の source-id を指し親に包含される"
 (for ([str (in-list (list "1"
                           "{ a: 1 }"
                           "fn f(a: Int) -> Int { a }\nf(1)"
                           "type A = Int\nconst x: A = 1\nx"
                           "{ let x = 1\n x }"))])
   (define r (c str))
   (check-true (compiled? r) (format "~s が受理される" str))
   (check-equal? (foreign-source-ids (compiled-core r)) '()
                 (format "~s の source-id" str))
   (check-equal? (containment-violations (compiled-core r)) '()
                 (format "~s の span 包含" str))))

(test-case
 "多 field 射影は選んだ欄だけの record 型になる"
 (check-equal? (compiled-type (c "{ let r = { a: 1, b: () }\n r.{a} }"))
               '(Record ((a Int imm)))))

(test-case
 "射影のあとも元の record を使える"
 (check-equal? (compiled-type (c "{ let r = { a: 1, b: 2 }\n let q = r.{a}\n r.b }"))
               'Int))

(test-case
 "mut で束縛した欄も射影の結果では imm になる"
 (check-equal? (compiled-type (c "{ let mut r = { a: 1 }\n r.{a} }"))
               '(Record ((a Int imm)))))

(test-case
 "true と false が合成位置でも Bool として型付けされる"
 (for ([src (list "true"
                  "false"
                  "const x: Bool = true\nx"
                  "{ let x = true\n x }"
                  "{ b: true }.b"
                  "fn f(a: Bool) -> Bool { a }\nf(false)")])
   (define r (c src))
   (check-true (compiled? r) src)
   (when (compiled? r)
     (check-equal? (compiled-type r) 'Bool src))))

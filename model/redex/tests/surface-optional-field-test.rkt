#lang racket

;; ADT-001。P2l3 spec §9 と §12。Surface の optional の欄の end-to-end である。

(require rackunit
         racket/match
         "../driver.rkt"
         "../diagnostic.rkt"
         "../erase.rkt"
         "../machine.rkt")

(define (compile str) (compile-source/string 'src str))
(define (compile-code str)
  (define r (compile str))
  (and (diagnostic? r) (diagnostic-id r)))
(define (type-of str) (compiled-type (compile str)))
(define (run-value str)
  (match (run-g2 (inject-g2m (erase-core (compiled-core (compile str)))) 10000)
    [`(cfg ,value () () () ()) value]
    [other (fail-check (format "終端の値を期待したが ~s" other))]))

(define person-type "{ name: Int, age?: Int }")

(test-case "ADT-001。省略した欄の p.age は none を返す"
  (define src (format "const p: ~a = { name: 1 }\np.age" person-type))
  (check-equal? (type-of src) '(Option Int))
  (check-equal? (run-value src) '(Construct (Option Int) none)))

(test-case "ADT-001。書いた欄の p.age は some を返す"
  (define src (format "const p: ~a = { name: 1, age: 2 }\np.age" person-type))
  (check-equal? (type-of src) '(Option Int))
  (check-equal? (run-value src) '(Construct (Option Int) some 2)))

(test-case "ADT-001。p.age は Option<Int> の注釈で受けられる"
  (check-false
   (compile-code
    (format "const p: ~a = { name: 1 }\nconst a: Option<Int> = p.age\n0" person-type))))

(test-case "ADT-001。p.{age} の欄の型は Option<Int> である"
  (check-equal?
   (type-of (format "const p: ~a = { name: 1 }\np.{age}" person-type))
   '(Record ((age (Option Int) imm)))))

(test-case "ADT-001。required の欄の省略は拒否する"
  (check-equal? (compile-code "const p: { name: Int, age: Int } = { age: 1 }\n0")
                "E-TYP-012"))

(test-case "ADT-001。関数の引数の型の optional の欄"
  (define src
    (string-append "fn age_of(p: { name: Int, age?: Int }) -> Option<Int> { p.age }\n"
                   "age_of({ name: 1 })"))
  (check-equal? (type-of src) '(Option Int))
  (check-equal? (run-value src) '(Construct (Option Int) none)))

(test-case "ADT-001。data 型の constructor の引数に optional の欄を宣言できる"
  (define src
    (string-append "type P =\n  | p<{ name: Int, age?: Int }>\n"
                   "const x: P = p({ name: 1 })\n0"))
  (check-false (compile-code src))
  (check-equal? (run-value src) 0))

(test-case "ADT-001。trait の宣言の optional の欄"
  (check-false (compile-code "trait T { a?: Int }\n0")))

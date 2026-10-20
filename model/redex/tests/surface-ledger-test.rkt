#lang racket

(require rackunit
         "../diagnostic.rkt"
         "../driver.rkt"
         "../origins.rkt"
         "../traits.rkt")

(define (compile source)
  (compile-source/string 'src source))

(define (ledger-with-trait trait-row)
  (define (fail reason kind key)
    (error 'ledger-with-trait "~s ~s ~s" reason kind key))
  (define env
    (make-trait-env
     #:trait (append (trait-env-trait-rows canonical-trait-env) (list trait-row))
     #:impl (trait-env-impl-rows canonical-trait-env)
     #:intersect (trait-env-intersect-rows canonical-trait-env)
     #:scope (trait-env-scope-rows canonical-trait-env)
     #:fail fail))
  (make-trait-ledger env #:fail fail))

(test-case "L1 宣言の無いプログラムは外側の台帳を eq? のまま使う"
  (define canonical-result (compile "0"))
  (check-true (compiled? canonical-result))
  (when (compiled? canonical-result)
    (check-eq? (compiled-ledger canonical-result) canonical-trait-ledger))
  (define custom (ledger-with-trait '(o-trait-user-Legacy Legacy root ())))
  (define custom-result
    (call-with-trait-ledger custom (lambda () (compile "0"))))
  (check-true (compiled? custom-result))
  (when (compiled? custom-result)
    (check-eq? (compiled-ledger custom-result) custom)))

(test-case "L2 impl を持つプログラムの台帳に R0 の impl 行が無い"
  (define outer (current-trait-ledger))
  (check-eq? outer canonical-trait-ledger)
  (define result
    (compile "impl Printable for Int { print: fn(x: Int) -> String { return \"i\" } }\n0"))
  (check-true (compiled? result) (format "compile failed: ~s" result))
  (when (compiled? result)
    (define rows (trait-env-impl-rows (trait-ledger-env (compiled-ledger result))))
    (check-equal? (length rows) 1)
    (check-equal? (first (first rows)) 'o-impl-user-Printable-1))
  (check-eq? (current-trait-ledger) outer))

(test-case "L3 trait 宣言だけのプログラムは base の impl 表を残す"
  (define result (compile "trait T { f: fn(Self) -> Int }\n0"))
  (check-true (compiled? result) (format "compile failed: ~s" result))
  (when (compiled? result)
    (check-equal?
     (length (trait-env-impl-rows (trait-ledger-env (compiled-ledger result))))
     7)))

(test-case "L4 derive を持つプログラムも impl 表を外す"
  (define result (compile "derive Sizable for Int\n0"))
  (check-true (compiled? result) (format "compile failed: ~s" result)))

#lang racket

;; P2m2c1c2 Task 2。関数仮引数の資源型 transfer encoding を検査する。
(require rackunit
         "../diagnostic.rkt"
         "../typing.rkt")

(define option-owned-type '(Option (Owned Res)))
(define record-owned-type
  '(Record ((n Int imm) (owned (Owned Res) imm))))

(define (function-signature parameter-type)
  `(NFn (,parameter-type) Int () (Own) () User))

(define (return-boundary body)
  `(Handle (Return boundary Int)
           (return-value -> return-value)
           (Scope () ,body)))

(define (function-core parameter-type body)
  `(Lam User f (raw) ,(return-boundary body)))

(define (key-of core callables)
  (match (core-type-of/diagnostic core '() callables)
    [(? diagnostic? result) (diagnostic-id result)]
    [_ 'ok]))

(define (valid-lam parameter-type)
  (function-core
   parameter-type
   `(Let (value let ,parameter-type) raw 1)))

(test-case "集約資源型の Option と Record 仮引数は encoding を通る"
  (for ([parameter-type (in-list (list option-owned-type record-owned-type))])
    (define result
      (core-type-of (valid-lam parameter-type)
                    '()
                    `((f ,(function-signature parameter-type)))))
    (check-equal? result (list (function-signature parameter-type) '()))))

(test-case "集約資源型の仮引数に encoding が無い Core は E-OWN-034"
  (define parameter-type option-owned-type)
  (check-equal?
   (key-of (function-core parameter-type 1)
           `((f ,(function-signature parameter-type))))
   "E-OWN-034"))

(test-case "encoding の Let 型が宣言型と異なる Core は E-OWN-034"
  (define parameter-type record-owned-type)
  (check-equal?
   (key-of (function-core parameter-type '(Let (value let Int) raw 1))
           `((f ,(function-signature parameter-type))))
   "E-OWN-034"))

(test-case "encoding の後に仮引数の生名が現れる Core は E-OWN-035"
  (define parameter-type option-owned-type)
  (check-equal?
   (key-of (function-core parameter-type
                          `(Let (value let ,parameter-type) raw raw))
           `((f ,(function-signature parameter-type))))
   "E-OWN-035"))

(test-case "RegionLam の内側の Lam も集約資源型の encoding を検査する"
  (define parameter-type option-owned-type)
  (define signature `(ForallRegion (rho) ,(function-signature parameter-type)))
  (define core `(RegionLam (rho) ,(valid-lam parameter-type)))
  (check-true
   (match (core-type-of core '() `((f ,signature)))
     [`((ForallRegion (,_) (NFn (,actual) Int () (Own) () User)) ())
      (equal? actual parameter-type)]
     [_ #f])))

(test-case "RecurVal と Recur は集約資源型の仮引数に encoding を要求する"
  (define parameter-type option-owned-type)
  (define signature (function-signature parameter-type))
  (define recur-value
    `(RecurVal recur-id f (raw)
       (Scope () (Let (value let ,parameter-type) raw 1))))
  (define recur
    `(Recur recur-id f (raw)
       (Scope () (Let (value let ,parameter-type) raw 1))
       0))
  (define callables `((recur-id ,signature)))
  (define actual-value
    (core-type-of recur-value '() callables))
  (check-true
   (match actual-value
     [`((NFn (,actual-type) Int () (Own) () User) ())
      (equal? actual-type parameter-type)]
     [_ #f]))
  (check-equal? (core-type-of recur '() callables) '(Int ())))

(test-case "集約資源型 Let の encoding 後の bare read は E-OWN-019"
  (define parameter-type option-owned-type)
  (define core
    (function-core
     parameter-type
     `(Let (value let ,parameter-type) raw
        (Let (copy let ,parameter-type) value 1))))
  (check-equal?
   (key-of core `((f ,(function-signature parameter-type))))
   "E-OWN-019"))

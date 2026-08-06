#lang racket

(require rackunit
         redex/reduction-semantics
         "../annotate.rkt"
         "../erase.rkt"
         "../origins.rkt"
         "../span-core.rkt")

(define (verify core) (term (verify-origins ,R0 ,core)))
(define (verify-initial core) (term (verify-initial-origins ,R0 ,core)))

(test-case "spanful な項が G2+ の c として受理される"
  (define core `(Apply (PrimVal (Reserved o-add) add) 1 2))
  (check-true (and (redex-match? G2+ c (annotate-core core)) #t)))

(test-case "spanful な origin 付き値は spanless と同じ判定になる"
  (define core `(Apply (PrimVal (Reserved o-add) add) 1 2))
  (check-equal? (verify (annotate-core core)) 'ok)
  (check-equal? (verify core) 'ok)
  (define type-rep `(TypeRep (Reserved o-int) Int Type))
  (check-equal? (verify (annotate-core type-rep)) 'ok)
  (define lam `(Lam User c-main (x) x))
  (check-equal? (verify (annotate-core lam)) 'ok))

(test-case "spanful な CurryVal は origin が spanless でも受理される"
  (define curried
    `(CurryVal (Derived (Reserved o-add) (Curry 1))
               (PrimVal (Reserved o-add) add)
               1))
  (check-equal? (verify curried) 'ok)
  (check-equal? (verify (annotate-core curried)) 'ok))

(test-case "偽装した origin は spanful でも forged になり span を保つ"
  (define core `(PrimVal (Reserved o-add) sub))
  (define spanful (annotate-core core))
  (define result (verify spanful))
  (check-equal? (first result) 'forged)
  (check-equal? (erase-core (second result)) core)
  (check-true (and (redex-match? G2+ v (second result)) #t))
  (check-equal? (verify core) `(forged ,core)))

(test-case "spanful な RVal と UVal は層ごとに判定が分かれる"
  (define rval
    `(RVal (ProofRep (Reserved o-valid-port) (Prop ValidPort)) 8080))
  (check-equal? (verify (annotate-core rval)) 'ok)
  (check-equal? (first (verify-initial (annotate-core rval))) 'forged)
  (check-equal? (first (verify-initial `(UVal 7))) 'forged))

(test-case "core でも spanful core でもない引数は error になる"
  (check-exn exn:fail? (λ () (verify `(Apply))))
  (check-exn exn:fail? (λ () (verify-initial `(#:span #:synthetic 0 0)))))

(test-case "annotate-core は semantic origin を包まない"
  (define (metadata-free? value)
    (cond
      [(and (pair? value) (keyword? (car value)))
       #f]
      [(list? value) (for/and ([element (in-list value)])
                       (metadata-free? element))]
      [else #t]))
  (define curried
    (annotate-core
     `(CurryVal (Derived (Reserved o-add) (Curry 1))
                (PrimVal (Reserved o-add) add)
                1)))
  ;; O は spanless である。annotate-core が O を包まないことを producer 側で
  ;; 固定する。文法の (Curry any) は spanful な O も受理するため、この不変は
  ;; 文法ではなくここで守る。
  (check-true (metadata-free? (third curried)))
  (check-equal? (third curried) `(Derived (Reserved o-add) (Curry 1))))

(test-case "spanful な O も受理され erase 後に spanless 版と一致する"
  (define spanless
    `(CurryVal (Derived (Reserved o-add) (Curry 1))
               (PrimVal (Reserved o-add) add)
               1))
  (define spanful-origin
    `(CurryVal (#:span #:synthetic 0 0)
               (Derived (Reserved o-add) (Curry (#:lit 1 (#:span #:synthetic 0 1))))
               (PrimVal (#:span #:synthetic 1 1) (Reserved o-add) add)
               (#:lit 1 (#:span #:synthetic 2 2))))
  ;; 文法は O の内側を any で受けるため通る。投影の上では区別できないので
  ;; 判定は spanless 版と同じになる。
  (check-equal? (verify spanful-origin) (verify spanless))
  (check-equal? (erase-core spanful-origin) spanless))

(test-case "origin-of は spanless な ov だけを受ける"
  (define type-rep `(TypeRep (Reserved o-int) Int Type))
  (check-equal? (term (origin-of ,type-rep)) `(Reserved o-int))
  (check-exn exn:fail?
             (λ () (term (origin-of ,(annotate-core type-rep))))))

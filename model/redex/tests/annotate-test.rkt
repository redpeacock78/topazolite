#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../span.rkt"
         "../erase.rkt"
         "../annotate.rkt")

(define g1-terms
  (term ((Apply 1 2)
         (Let (x Int) 1 x)
         (Construct (Option Int) some 1)
         (Eliminate (Construct (Option Int) some 1) ((some (x) -> x)))
         (Perform (Return b Int) 1)
         (Handle (Return b Int) (x -> x) 1)
         (Scope () 1)
         (Recur recur-id f (x) x (Apply f 0))
         (Yield 1 2)
         (Suspend 1)
         (Move x)
         (Drop 1)
         (Curry 1 2)
         (Lam User lam-id (x) x)
         (PrimVal User lt)
         (CurryVal User 1 2)
         (RecurVal recur-id f (x) x)
         (TypeRep User Int Type)
         (ProofRep User ValidNarrativeTrait)
         (resource 0)
         1
         unit
         "s"
         x)))

(test-case "annotate-core は G1 の全 production を spanful へ持ち上げる"
  (for ([core (in-list g1-terms)])
    (define lifted (annotate-core core))
    (check-true (or (and (redex-match? G1+ c lifted) #t)
                    (and (redex-match? G1+ v lifted) #t))
                (format "~a -> ~a" core lifted))))

(test-case "annotate-core と erase-core は往復する"
  (for ([core (in-list g1-terms)])
    (check-equal? (erase-core (annotate-core core)) core (format "~a" core))))

(test-case "annotate-core は決定的である"
  (for ([core (in-list g1-terms)])
    (check-equal? (annotate-core core) (annotate-core core))))

(test-case "annotate-core は未対応の production を素通ししない"
  (check-exn exn:fail? (λ () (annotate-core (term (NoSuchForm 1 2))))))

(test-case "生成 span は #:synthetic の空 span であり前順に番号が付く"
  (check-equal? (annotate-core (term 1))
                (term (#:lit 1 (#:span #:synthetic 0 0))))
  (check-equal? (annotate-core (term (Apply 1 2)))
                (term (Apply (#:span #:synthetic 0 0)
                             (#:lit 1 (#:span #:synthetic 1 1))
                             (#:lit 2 (#:span #:synthetic 2 2)))))
  ;; 生成 span はすべて span-ok? を満たす。
  (define (spans t)
    (cond [(and (list? t) (= 4 (length t)) (eq? (car t) '#:span)) (list t)]
          [(list? t) (append-map spans t)]
          [else '()]))
  (for ([core (in-list g1-terms)])
    (define found (spans (annotate-core core)))
    (check-true (pair? found) (format "~a" core))
    (for ([sp (in-list found)])
      (check-true (span-ok? sp) (format "~a" sp))
      (check-equal? (cadr sp) '#:synthetic))))

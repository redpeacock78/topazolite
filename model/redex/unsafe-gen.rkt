#lang racket

(require racket/match
         "borrow.rkt"
         "machine.rkt"
         "ptr-static.rkt"
         "region.rkt"
         "typing.rkt")

;; unsafe.md §5.4。G2 core を直に作る。elaborate も surface 構文も通さない。
;; 生成域は raw 操作の 5 形と、それが意味を持つのに必要な最小の周辺だけである。
(provide gen-unsafe-term
         prepare-unsafe-term)

(define binder-counter (box 0))

(define (fresh-binder! prefix)
  (define n (unbox binder-counter))
  (set-box! binder-counter (add1 n))
  (string->symbol (format "~a~a" prefix n)))

(define (gen-literal) (+ 1000 (random 1000)))
(define (pick choices) (list-ref choices (random (length choices))))

(define (in-scope body-maker)
  (define x (fresh-binder! 'x))
  `(Scope ()
     (Let (,x let (Owned Res)) (resource 1) ,(body-maker x))))

(define (gen-unsafe-outside x)
  (define choices
    (list
     (lambda () `(RawLoad (AddressOf (BorrowMut ,x))))
     (lambda () `(RawStore (AddressOf (BorrowMut ,x)) ,(gen-literal)))
     (lambda () `(PtrOffset (AddressOf (BorrowMut ,x)) 1))
     (lambda ()
       (define p (fresh-binder! 'p))
       (define q (fresh-binder! 'q))
       `(Let (,p const (RawPtr Res Mut NonNull (Align 1)
                              (AddrSpace native) (Prov owned)))
             (AddressOf (BorrowMut ,x))
             (Let (,q let Res)
                  (Unsafe (RawLoad ,p))
                  (RawLoad ,p))))))
  ((pick choices)))

(define (gen-unsafe-body depth x)
  (if (zero? depth)
      (gen-literal)
      (let ([choices
             (list
              (lambda () `(Unsafe (RawLoad (AddressOf (BorrowMut ,x)))))
              (lambda () `(Unsafe (RawStore (AddressOf (BorrowMut ,x))
                                             ,(gen-literal))))
              (lambda () `(Unsafe (RawLoad
                                    (PtrOffset (AddressOf (BorrowMut ,x)) 1))))
              (lambda () `(Unsafe
                            (Read (FromRawPtr (AddressOf (BorrowMut ,x)) 0))))
              (lambda () `(Unsafe (AddressOf (BorrowMut ,x))))
              (lambda () `(Unsafe (Yield ,(gen-literal)
                                         ,(gen-unsafe-body (sub1 depth) x))))
              (lambda () (gen-unsafe-outside x)))])
        ((pick choices)))))

(define (gen-unsafe-term depth)
  (set-box! binder-counter 0)
  (in-scope (lambda (x) (gen-unsafe-body depth x))))

(define (prepare-unsafe-term core)
  (define ir (build-region-ir core))
  (define result
    (with-handlers ([exn:fail? (lambda (_e) 'discard)])
      (type-of/raw*+ptr core '() '() '() (region-ctx ir '() (hash) (hash)))))
  (match result
    [(list 'ok (list _τ _ε sidecar))
     (list 'ok (inject-g2 core) sidecar)]
    [_ 'discard]))

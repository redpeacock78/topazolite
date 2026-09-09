#lang racket

(require racket/match
         "borrow.rkt"
         "borrow-gen.rkt"
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
  (define y (fresh-binder! 'y))
  `(Scope ()
     (Let (,x let (Owned Res)) (resource 1)
       (Let (,y let (Owned Res)) (resource 2)
         ,(body-maker x y)))))

(define (gen-unsafe-outside x y)
  (define choices
    (list
     (lambda () `(RawLoad (AddressOf (BorrowMut ,x))))
     (lambda () `(RawStore (AddressOf (BorrowMut ,x))
                           (Read (Borrow ,y))))
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

(define (gen-unsafe-body depth x y [include-outside? #t])
  (if (zero? depth)
      (gen-literal)
      (let ([choices
             (append
              (list
               (lambda () `(Unsafe (RawLoad (AddressOf (BorrowMut ,x)))))
               (lambda () `(Unsafe (RawStore (AddressOf (BorrowMut ,x))
                                              (Read (Borrow ,y)))))
               (lambda () `(Unsafe (RawLoad
                                     (PtrOffset (AddressOf (BorrowMut ,x)) 1))))
               (lambda () `(Unsafe
                             (Read (FromRawPtr (AddressOf (BorrowMut ,x)) 0))))
               (lambda () `(Unsafe (AddressOf (BorrowMut ,x))))
               (lambda () `(Unsafe (Yield ,(gen-literal)
                                          ,(gen-unsafe-body (sub1 depth)
                                                            x y #f)))))
              (if include-outside?
                  (list (lambda () (gen-unsafe-outside x y)))
                  '()))])
        ((pick choices)))))

(define (gen-unsafe-term depth)
  (set-box! binder-counter 0)
  (in-scope (lambda (x y) (gen-unsafe-body depth x y))))

;; FromRawPtr の ρ は Core の子ではないため、既存の
;; fill-region-placeholders では生成した placeholder を埋められない。
;; 同じ point 規約でその節点自身の lexical region を書き込む。
(define (fill-unsafe-regions core ir)
  (let walk ([t core] [point '()])
    (match t
      [`(FromRawPtr ,operand ,_rho)
       `(FromRawPtr
         ,(walk operand (append point '(0)))
         ,(region->rho ir (region-at ir point)))]
      [`(Let (,x ,bmode ,τ) ,bound ,body)
       `(Let (,x ,bmode ,τ)
             ,(walk bound (append point '(0)))
             ,(walk body (append point '(1))))]
      [(? list?)
       (core-with-children
        t
        (for/list ([child (in-list (core-children t))]
                   [i (in-naturals)])
          (walk child (append point (list i)))))]
      [_ t])))

(define (prepare-unsafe-term core)
  (define ir (build-region-ir core))
  (define filled (fill-region-placeholders core ir))
  (define region-filled (fill-unsafe-regions filled ir))
  ;; 機械は surface の BorrowMut ではなく、region と owner を注釈した
  ;; BorrowMutAt を還元する。型検査と同じ注釈済み core を両方へ渡す。
  (define annotated
    (with-handlers ([exn:fail? (lambda (_e) #f)])
      (annotate-regions region-filled ir)))
  (define result
    (if annotated
        (with-handlers ([exn:fail? (lambda (_e) 'discard)])
          (type-of/raw*+ptr annotated '() '() '()
                              (region-ctx ir '() (hash) (hash))))
        'discard))
  (match result
    [(list 'ok (list _τ _ε sidecar))
     (list 'ok (inject-g2m annotated) sidecar)]
    [_ 'discard]))

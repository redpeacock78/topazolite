#lang racket/base

;; P2l1 spec §4。data 型の宣言の索引と、その読み出し口。
;; 型を見る下位の module が origins.rkt を require できないため、ここを葉にする。
(require racket/list
         racket/match
         (only-in redex/reduction-semantics caching-enabled?))

(provide (struct-out data-index)
         empty-data-index
         current-data-index
         data-decl
         data-constructor
         data-schema
         data-field-types
         build-data-index)

(module+ data-env-internal
  (provide data-index-parameter))

(struct data-index (decls constructors) #:transparent)

(define empty-data-index (data-index (hash) (hash)))
(define data-index-parameter (make-parameter empty-data-index))

(define (current-data-index)
  (define index (data-index-parameter))
  (unless (or (eq? index empty-data-index) (not (caching-enabled?)))
    (error 'current-data-index "custom data index read with Redex caching enabled"))
  index)

(define (data-decl T)
  (hash-ref (data-index-decls (current-data-index)) T #f))

(define (data-constructor K)
  (hash-ref (data-index-constructors (current-data-index)) K #f))

(define (substitute-params term parameters arguments)
  (match term
    [`(Param ,X)
     (define position (index-of parameters X eq?))
     (if position (list-ref arguments position) term)]
    [(? pair? items) (map (λ (item) (substitute-params item parameters arguments)) items)]
    [_ term]))

(define (data-schema T arguments)
  (match (data-decl T)
    [`(,T (,parameters ...) (,constructors ...))
     (and (= (length parameters) (length arguments))
          (for/list ([constructor (in-list constructors)])
            (list (first constructor)
                  (map (λ (type) (substitute-params type parameters arguments))
                       (second constructor)))))]
    [_ #f]))

(define (data-field-types T arguments)
  (append-map second (or (data-schema T arguments) '())))

(define (build-data-index declarations)
  (if (null? declarations)
      empty-data-index
      (data-index
       (for/hash ([declaration (in-list declarations)])
         (values (first declaration) declaration))
       (for/fold ([index (hash)]) ([declaration (in-list declarations)])
         (for/fold ([index index])
                   ([constructor (in-list (third declaration))]
                    [position (in-naturals)])
           (hash-set index (first constructor)
                     (list (first declaration) position)))))))

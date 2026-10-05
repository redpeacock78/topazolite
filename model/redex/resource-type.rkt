#lang racket/base

(require racket/list
         racket/match
         racket/set
         "data-env.rkt")

(provide resource-type?
         runtime-resource-type?
         owned-type?)

;; 型付けと実行時が共有する資源型の構成子表。
;; schema が無い Data の扱いだけは各入口の契約に応じて呼び分ける。
(define (resource-type/missing type on-missing-schema)
  (let walk ([type type] [visited (set)])
    (match type
      ['Int #f] ['Bool #f] ['Unit #f] ['String #f] ['Never #f] ['Res #f]
      [`(TypeInfo ,_) #f]
      [`(Proof ,_) #f]
      [`(Owned ,_) #t]
      [`(Borrowed ,_ ,_) #f]
      [`(BorrowedMut ,_ ,_) #f]
      [`(RawPtr ,_ ,_ ,_ ,_ ,_ ,_) #f]
      [`(NFn ,_ ...) #f]
      [`(List ,element) (walk element visited)]
      [`(Option ,element) (walk element visited)]
      [`(Result ,ok-type ,error-type)
       (or (walk ok-type visited) (walk error-type visited))]
      [`(Untrusted ,payload) (walk payload visited)]
      [`(Refined ,payload ,_) (walk payload visited)]
      [`(Record ,row)
       (for/or ([field (in-list row)]) (walk (second field) visited))]
      [`(Union ,left ,right)
       (or (walk left visited) (walk right visited))]
      [`(Intersection ,left ,right)
       (or (walk left visited) (walk right visited))]
      [`(ForallRegion (,_ ...) ,body) (walk body visited)]
      [`(Data ,name (,arguments ...))
       (define key (cons name arguments))
       (define schema (data-schema name arguments))
       (cond
         [(not schema) (on-missing-schema name arguments)]
         [(set-member? visited key) #f]
         [else
          (for/or ([field (in-list (data-field-types name arguments))])
            (walk field (set-add visited key)))])]
      [_ #t])))

(define (resource-type? type)
  (resource-type/missing type (lambda (_name _arguments) #t)))

(define (runtime-resource-type? type)
  (resource-type/missing
   type
   (lambda (name arguments)
     (error 'runtime-resource-type?
            "schema の無い Data を実行の台帳の外で見た: ~s ~s"
            name arguments))))

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

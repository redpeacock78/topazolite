#lang racket

(require rackunit
         racket/match
         racket/runtime-path
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../lexer.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../parser.rkt"
         "../surface-lower.rkt"
         "../traits.rkt")

(define-runtime-path surface-lower-module "../surface-lower.rkt")

(define (lower source)
  (lower-surface (parse (lex/string 'src source)) canonical-trait-env))

(define impl-source
  (string-append
   "type User = { name: String }\n"
   "impl Printable for User { print: fn(u: User) -> String { return u.name } }\n"
   "0"))

(define (impl-record low)
  (match (lowered-term low)
    [`(Let ,_ ((#:bind %impl-rec-Printable-1 ,_) const (#:ty ,_ ,_))
           (Rec ,_ ,_)
           (Let ,_ ((#:bind %impl-Printable-1 ,_) const)
                (Apply ,_ (#:var impl-user-Printable-1 ,_)
                       (#:var %impl-rec-Printable-1 ,_))
                ,_))
     #t]
    [_ #f]))

(define (collect-forms tree predicate)
  (append (if (predicate tree) (list tree) '())
          (if (pair? tree)
              (append-map (λ (part) (collect-forms part predicate)) tree)
              '())))

(define (impl-apply-arguments tree primitive)
  (collect-forms
   tree
   (λ (node)
     (match node
       [`(Apply ,_ (#:var ,(== primitive) ,_) ,_) #t]
       [_ #f]))))

(define (run-value result)
  (call-with-trait-ledger
   (compiled-ledger result)
   (λ ()
     (match (run-g2 (inject-g2m (erase-core (compiled-execution-core result))) 10000)
       [`(cfg ,value () () () ()) value]
       [other (fail-check (format "終端状態を期待したが ~s" other))]))))

(test-case "B1 impl は要求型を注釈した record Let から同じ値で Proof を作る"
  (define low (lower impl-source))
  (check-true (lowered? low))
  (when (lowered? low)
    (check-true (impl-record low))
    (define row (first (lowered-impl-rows low)))
    (check-equal?
     (match (lowered-term low)
       [`(Let ,_ ((#:bind %impl-rec-Printable-1 ,_) const (#:ty ,type ,_))
              ,_ ,_)
        (lift-template-type type)]
       [_ #f])
     `(Record ,(instantiate-requirements
                (trait-template (trait-row-by-name 'Printable canonical-trait-env))
                (impl-target-type row))))))

(test-case "B2 record 式は一度だけ評価され primitive へ変数で渡る"
  (define low (lower impl-source))
  (check-true (lowered? low))
  (when (lowered? low)
    (define term (lowered-term low))
    (check-equal? (length (collect-forms term
                                         (λ (node)
                                           (match node [`(Rec ,_ ,_) #t] [_ #f]))))
                  1)
    (check-equal? (length (impl-apply-arguments term 'impl-user-Printable-1)) 1)
    (check-match (fourth (first (impl-apply-arguments term 'impl-user-Printable-1)))
                 `(#:var %impl-rec-Printable-1 ,_))))

(test-case "B3 derive も size record を束縛してから primitive へ渡る"
  (define low (lower "derive Sizable for Bool\n0"))
  (check-true (lowered? low))
  (when (lowered? low)
    (check-true
     (match (lowered-term low)
       [`(Let ,_ ((#:bind %derive-rec-Sizable-1 ,_) const)
              (Rec ,_ (((#:lbl size ,_) imm
                        (Fn ,_ ,_ ,_ ,_ (#:lit 1 ,_)))))
              (Let ,_ ((#:bind %derive-Sizable-1 ,_) const)
                   (Apply ,_ (#:var derive-user-Sizable-1 ,_)
                          (#:var %derive-rec-Sizable-1 ,_))
                   ,_))
        #t]
       [_ #f]))))

(test-case "B4 provider 表は origin から record の束縛名を引く"
  (define low (lower impl-source))
  (check-true (lowered? low))
  (when (lowered? low)
    (define accessor
      (with-handlers ([exn:fail? (λ (_) #f)])
        (dynamic-require surface-lower-module 'lowered-providers)))
    (check-true (procedure? accessor))
    (when accessor
      (check-equal? (hash-ref (accessor low) 'o-impl-user-Printable-1 #f)
                    '%impl-rec-Printable-1))))

(test-case "B5 provider 化後も既存の impl と derive は同じ値を返す"
  (for ([source (in-list
                 (list
                  (string-append
                   "trait Showable { show: fn(Self) -> String }\n"
                   "impl Showable for Int { show: fn(x: Int) -> String { return \"i\" } }\n"
                   "0")
                  "derive Sizable for Bool\n0"))])
    (define result (compile-source/string 'src source))
    (check-true (compiled? result) (format "compile failed: ~s" result))
    (when (compiled? result)
      (check-equal? (run-value result) 0))))

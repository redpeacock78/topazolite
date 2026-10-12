#lang racket

;; [REQ: OWN-006] c3n2。Owned と宣言された place の値を 9 の供給元と 9 の消費位置の組で Move し、
;; 直接の Owned の Let と OWN-006 の仮引数の経路の両方で、正規形までの全構成が有効であることを組ごとに固定する。
(require rackunit
         racket/match
         "../gen.rkt"
         "../machine.rkt"
         "../typing.rkt"
         "../type-equiv.rkt")

(define curry-source-type '(NFn ((Owned Res)) Unit () (Own) () User))
(define curry-source
  '(Lam User c3n-curry-source (curry-raw)
     (Handle (Return c3n-curry-boundary Unit)
       (curry-answer -> curry-answer)
       (Scope ()
         (Let (curry-owned let (Owned Res)) curry-raw
           (Drop (Move curry-owned)))))))
(define curry-source-expression
  `(Curry ,curry-source (OwnLeaf (resource 39))))

(define suppliers
  (list
   (list 'lam '(NFn () Unit () () () User) '(Lam User lifted-lam () unit))
   (list 'resource 'Res '(resource 29))
   (list 'int 'Int 17)
   (list 'record '(Record ((a Int imm))) '(Rec ((a imm 17))))
   (list 'eliminate-record
         '(Record ((a Int imm)))
         '(Eliminate (Construct Bool true)
             ((true () -> (Rec ((a imm 17))))
              (false () -> (Rec ((a imm 18)))))))
   (list 'list '(List Int) '(Construct (List Int) nil))
   (list 'inner-owned-leaf
         '(Record ((owned (Option (Owned Res)) imm)))
         '(Rec ((owned imm
                 (Construct (Option (Owned Res)) some
                   (OwnLeaf (resource 29)))))))
   (list 'curryval '(NFn () Unit () (Own) () User)
         curry-source-expression)
   (list 'union (normalize-type '(Union Int Bool))
         `(UnionInject ,(normalize-type '(Union Int Bool)) Int 17))))

(define consumer-names
  '(drop rebind scope-result apply-callee construct yield perform apply-arg return))

(define (consumer name tau)
  (case name
    [(drop) (values '(Drop (Move owner)) 'Unit '(Own) '())]
    [(rebind)
     (values `(Let (rebound let (Owned ,tau)) (Move owner) (Drop (Move rebound)))
             'Unit '(Own) '())]
    [(scope-result) (values '(Move owner) `(Owned ,tau) '() '())]
    [(apply-callee)
     (values `(Apply (Move owner)) 'Unit '(Own) '())]
    [(construct)
     (values `(Construct (Option (Owned ,tau)) some (OwnLeaf (Move owner)))
             `(Option (Owned ,tau)) '() '())]
    [(yield)
     (values `(Yield (OwnLeaf (Move owner)) unit) 'Unit
             `((Yield (Owned ,tau))) '())]
    [(perform)
     (values `(Perform (Return c3n-boundary (Owned ,tau)) (Move owner))
             'Never `((Return c3n-boundary (Owned ,tau))) '())]
    [(apply-arg)
     (define raw 'owned-raw)
     (define return-clause '(return-value -> return-value))
     (define ftype `(NFn ((Owned ,tau)) Unit () (Own) () User))
     (define fun
       `(Lam User sink (,raw)
          (Handle (Return sink-boundary Unit)
            ,return-clause
            (Scope ()
              (Let (received let (Owned ,tau)) ,raw
                (Drop (Move received)))))))
     (values `(Apply ,fun (Move owner)) 'Unit '(Own) `((sink ,ftype)))]
    [(return)
     (values `(Handle (Return c3n-boundary (Owned ,tau))
                      (answer -> answer)
                      (Perform (Return c3n-boundary (Owned ,tau))
                               (Move owner)))
             `(Owned ,tau) '() '())]))

(define (trace start)
  (let loop ([current start] [configs (list start)] [fuel 80])
    (when (zero? fuel)
      (error 'trace "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next)) (loop next (cons next configs) (sub1 fuel))]
      [steps (error 'trace "一意な次状態を期待した: ~s" steps)])))

(define (classify core callables)
  (define static (core-type-of core '() callables))
  (cond
    [(eq? static 'ill-typed) 'S]
    [else
     (define expected (first static))
     (if (for/and ([configuration (in-list (trace (inject-g2m core)))])
           (define row (runtime-row configuration callables expected))
           (and row (config-ok? configuration callables expected row)))
         'V
         'I)]))

(define (supplier-callables name)
  (append (if (eq? name 'lam) '((lifted-lam (NFn () Unit () () () User))) '())
          (if (eq? name 'curryval)
              (list (list 'c3n-curry-source curry-source-type))
              '())))

(define (direct-row supplier)
  (match-define (list name tau init) supplier)
  (cons name
        (for/list ([consumer-name (in-list consumer-names)])
          (define-values (body _expected _row extra) (consumer consumer-name tau))
          (classify `(Scope () (Let (owner let (Owned ,tau)) ,init ,body))
                    (append extra (supplier-callables name))))))

(define (formal-row supplier)
  (match-define (list name tau init) supplier)
  (cons name
        (for/list ([consumer-name (in-list consumer-names)])
          (define-values (body expected row extra) (consumer consumer-name tau))
          (define formal-effects (if (member 'Own row) row (cons 'Own row)))
          (define formal-type
            `(NFn ((Owned ,tau)) ,expected () ,formal-effects () User))
          (define formal-lam
            `(Lam User formal-provider (formal-raw)
               (Handle (Return formal-boundary ,expected)
                 (formal-answer -> formal-answer)
                 (Scope ()
                   (Let (owner let (Owned ,tau)) formal-raw ,body)))))
          (classify `(Scope ()
                       (Let (formal-source let (Owned ,tau)) ,init
                         (Apply ,formal-lam (Move formal-source))))
                    (append extra (supplier-callables name)
                            (list (list 'formal-provider formal-type)))))))

(define expected-rows
  '((lam              V V V V V V V V V)
    (resource         V V V S V V V V V)
    (int              V V V S V V V V V)
    (record           V V V S V V V V V)
    (eliminate-record V V V S V V V V V)
    (list             V V V S V V V V V)
    (inner-owned-leaf V V V S V V V V V)
    (curryval         V V V V V V V V V)
    (union            V V V S V V V V V)))

(test-case "直接の Owned の Let から Move した 81 組を組ごとに分類する"
  (check-equal? (map direct-row suppliers) expected-rows))

(test-case "Owned の仮引数の経路で Move した 81 組を組ごとに分類する"
  (check-equal? (map formal-row suppliers) expected-rows))

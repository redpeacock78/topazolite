#lang racket

;; P2m2c1c2 Task 2。関数仮引数の資源型 transfer encoding を検査する。
(require rackunit
         "../diagnostic.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
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

(define (key-of core callables [environment '()])
  (match (core-type-of/diagnostic core '() callables environment)
    [(? diagnostic? result) (diagnostic-id result)]
    [_ 'ok]))

(define (valid-lam parameter-type)
  (function-core
   parameter-type
   `(Let (value let ,parameter-type) raw 1)))

(define (test-ledger-fail reason kind key)
  (error 'test-ledger-fail "~s ~s ~s" reason kind key))
(define branch-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((Mixed () ((pack (Int (Option (Owned Res)) Int))))
            (Duo () ((pair ((Option (Owned Res)) (Option (Owned Res))))))
            (OwnedBox () ((box ((Owned Res)))))
            (OwnedOrInt () ((boxed ((Owned Res))) (plain (Int)))))
   #:fail test-ledger-fail))
(define-syntax-rule (with-branch-data body ...)
  (call-with-trait-ledger branch-ledger (lambda () body ...)))

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

(test-case "Eliminate の root Owned 枝は payload view の encoding を要求する"
  (define option-type '(Option (Owned Res)))
  (define raw
    '(Eliminate (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 1)))
       ((some (raw) ->
          (Scope () (Let (owned let (Owned Res)) raw
                     (Drop (Move owned)))))
        (none () -> unit))))
  (check-equal? (core-type-of raw '() '()) '(Unit (Own)))
  (define missing
    '(Eliminate (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 1)))
       ((some (raw) -> unit)
        (none () -> unit))))
  (check-equal? (key-of missing '()) "E-OWN-034")
  (define wrong-type
    '(Eliminate (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 1)))
       ((some (raw) ->
          (Scope () (Let (owned let Res) raw unit)))
        (none () -> unit))))
  (check-equal? (key-of wrong-type '()) "E-OWN-034")
  (define raw-leak
    '(Eliminate (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 1)))
       ((some (raw) ->
          (Scope ()
            (Let (owned let (Owned Res)) raw
                 (Let (dropped Unit) (Drop (Move owned)) raw))))
        (none () -> unit))))
  (check-equal? (key-of raw-leak '()) "E-OWN-035"))

(test-case "混在した Eliminate field は資源型の位置だけを encoding する"
  (define mixed-type '(Data Mixed ()))
  (define middle-type '(Option (Owned Res)))
  (define valid
    `(Eliminate source
       ((pack (left raw-middle right) ->
          (Scope ()
            (Let (middle let ,middle-type) raw-middle
                 (Let (drop Unit)
                      (Drop (Move middle))
                      1)))))))
  (define result
    (with-branch-data
      (core-type-of valid '() '() `((source ,mixed-type)))))
  (check-equal? result '(Int (Own)))
  (define missing
    '(Eliminate source ((pack (left raw-middle right) -> 1))))
  (check-equal?
   (with-branch-data
     (key-of missing '() '((source (Data Mixed ())))))
   "E-OWN-034"))

(test-case "UnionEliminate の集約資源型の枝は encoding を要求する"
  (define member '(Option (Owned Res)))
  (define union-type (normalize-type `(Union Bool ,member)))
  (define valid
    `(UnionEliminate source
       ((Bool flag -> 0)
        (,member raw ->
         (Scope ()
           (Let (option let ,member) raw
                (Let (drop Unit) (Drop (Move option)) 1)))))))
  (check-equal?
   (core-type-of valid '() '() `((source ,union-type)))
   '(Int (Own)))
  (define missing
    `(UnionEliminate source
       ((Bool flag -> 0)
        (,member raw -> 1))))
  (check-equal?
   (key-of missing '() `((source ,union-type)))
   "E-OWN-034"))

(test-case "線形の穴の枝は root Owned と集約資源型を一度だけ運ぶ"
  (define owned-box '(Data OwnedBox ()))
  (define owned-source
    `(Eliminate source ((box (raw) -> raw))))
  (check-equal?
   (with-branch-data
     (core-type-of owned-source '() '()
                   `((source ,owned-box))))
   '((Owned Res) ()))

  (define aggregate '(Option (Owned Res)))
  (define mixed '(Data Mixed ()))
  (define mixed-source
    '(Eliminate source
       ((pack (left payload right) ->
          (Rec ((saved imm payload)))))))
  (check-equal?
   (with-branch-data
     (core-type-of mixed-source '() '() `((source ,mixed))))
   `((Record ((saved ,aggregate imm))) ()))

  (define union-type (normalize-type `(Union Int ,aggregate)))
  (define union-result `(Record ((saved ,aggregate imm))))
  (define union-source
    `(UnionEliminate source
       ((Int number ->
         (Rec ((saved imm (Construct ,aggregate none)))))
        (,aggregate payload ->
         (Rec ((saved imm payload)))))))
  (check-equal?
   (core-type-of union-source '() '() `((source ,union-type)))
   (list union-result '())))

(test-case "線形の穴の方式では複製と L の外の使用を拒否する"
  (define owned-box '(Data OwnedBox ()))
  (define (eliminate body)
    `(Eliminate source ((box (raw) -> ,body))))
  (for ([body (in-list
               (list '(Rec ((left imm raw) (right imm raw)))
                     '(Drop raw)))])
    (check-equal?
     (with-branch-data
       (key-of (eliminate body) '() `((source ,owned-box))))
     "E-OWN-034")))

(test-case "複数の線形穴 binder は同じ Rec の別欄へ一度ずつ運べる"
  (define member '(Option (Owned Res)))
  (define duo '(Data Duo ()))
  (define output
    `(Record ((first ,member imm) (second ,member imm))))
  (define linear
    '(Eliminate source
       ((pair (first second) ->
         (Rec ((first imm first) (second imm second)))))))
  (check-equal?
   (with-branch-data (core-type-of linear '() '() `((source ,duo))))
   (list output '()))

  (define mixed
    `(Eliminate source
       ((pair (first second) ->
         (Scope ()
           (Let (first-place let ,member) first
                (Rec ((first imm (Move first-place))
                      (second imm second)))))))))
  (check-equal?
   (with-branch-data
     (key-of mixed '() `((source ,duo))))
   "E-OWN-034"))

(test-case "線形の穴の許可は兄弟の枝へ漏れず内側 Let の shadowing を守る"
  (define leaked
    '(Eliminate source
       ((boxed (raw) -> raw)
        (plain (number) -> raw))))
  (check-equal?
   (with-branch-data
     (key-of leaked '() '((source (Data OwnedOrInt ())) (raw (Owned Res)))))
   "E-OWN-019")

  (define mixed '(Data Mixed ()))
  (define shadowed
    '(Eliminate
      source
      ((pack (left raw right) ->
        (Rec ((payload imm raw)
              (shadow imm (Let (raw let Int) 1 raw))))))))
  (check-equal?
   (with-branch-data
     (key-of shadowed '() `((source ,mixed))))
   'ok)

  (define member '(Option (Owned Res)))
  (define shadowed-resource
    `(Eliminate source
       ((pack (left raw right) ->
         (Rec ((outer imm raw)
               (shadow imm
                (Let (raw let ,member)
                     (Construct ,member none)
                     (Rec ((inner imm raw)))))))))))
  (check-equal?
   (with-branch-data
     (key-of shadowed-resource '() `((source ,mixed))))
   "E-OWN-019"))

(test-case "非空 Scope を先頭に持つ枝は encoding と判定して拒否する"
  (define owned-box '(Data OwnedBox ()))
  (define malformed
    '(Eliminate source
       ((box (raw) -> (Scope (13) raw)))))
  (check-equal?
   (with-branch-data
     (key-of malformed '() `((source ,owned-box))))
   "E-OWN-034"))

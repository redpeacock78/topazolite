#lang racket

;; P2m2c1c2 Task 2。関数仮引数の資源型 transfer encoding を検査する。
(require rackunit
         "../annotate.rkt"
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../region.rkt"
         "../traits.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define option-owned-type '(Option (Owned Res)))
(define record-owned-type
  '(Record ((n Int imm) (owned (Owned Res) imm))))
(define handler-record-type
  '(Record ((owned (Owned Res) imm))))
(define handler-record-value
  '(Rec ((owned imm (OwnedLeaf (tok 31) (resource 31))))))
(define handler-source-expression
  '(Apply handler-source unit))
(define handler-source-environment
  `((handler-source (NFn (Unit) ,handler-record-type () (Own) () User))))

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

(test-case "環境の集約資源型の自由変数は裸で読めない"
  (check-equal?
   (key-of 'source '() `((source ,record-owned-type)))
   "E-OWN-019"))

(define (handler-core return-type handler argument)
  `(Handle (Return boundary ,return-type)
           (raw -> ,handler)
           (Perform (Return boundary ,return-type) ,argument)))

(define (runtime-handler-trace return-type handler value tokens)
  (define core
    (handler-core return-type handler '(Move 0)))
  (define start
    `(cfg (Scope (0) ,core)
          ((0 ,value (declared ,return-type)))
          ((0 Available))
          ,tokens
          ()))
  (let loop ([current start] [configs (list start)] [fuel 60])
    (when (zero? fuel)
      (error 'runtime-handler-trace "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _rule next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps
       (error 'runtime-handler-trace "一意な次状態を期待したが複数ある: ~s"
              steps)])))

(define (check-runtime-handler configs expected)
  (for ([config (in-list configs)] [index (in-naturals)])
    (define row (runtime-row config '() expected))
    (check-not-false row
                     (format "runtime row を得られない config ~a: ~s"
                             index config))
    (check-true (config-ok? config '() expected row)
                (format "不正な中間 config ~a: ~s" index config))))

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

(define (type-borrowed-local core environment)
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               '()
               '()
               environment
               (region-ctx ir '() (hash) (hash))))

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

(test-case "Return binder の identity は集約資源型と root Owned で受理される"
  (define aggregate
    (handler-core handler-record-type 'raw '(Move source)))
  (check-equal?
   (core-type-of `(Let (source let ,handler-record-type)
                       ,handler-source-expression ,aggregate)
                 '() '() handler-source-environment)
   (list handler-record-type '(Own)))
  (define owned
    (handler-core '(Owned Res) 'raw '(resource 31)))
  (check-equal? (core-type-of owned '() '()) '((Owned Res) ())))

(test-case "Return binder の encoding は宣言型の payload view で受理される"
  (define aggregate-handler
    `(Scope ()
       (Let (place let ,handler-record-type) raw (Move place))))
  (check-equal?
   (core-type-of `(Let (source let ,handler-record-type)
                       ,handler-source-expression
                   ,(handler-core handler-record-type aggregate-handler
                                  '(Move source)))
                 '() '() handler-source-environment)
   (list handler-record-type '(Own)))
  (define owned-handler
    '(Scope () (Let (place let (Owned Res)) raw (Move place))))
  (check-equal?
   (core-type-of (handler-core '(Owned Res) owned-handler '(resource 31))
                 '() '())
   '((Owned Res) (Own))))

(test-case "Return binder の aggregate identity と encoding は全状態で構成を保つ"
  (define encoded-handler
    `(Scope () (Let (place let ,handler-record-type) raw (Move place))))
  (for ([case
         (in-list
          (list
           (list 'raw handler-record-value '(((tok 31) Available)))
           (list encoded-handler
                 handler-record-value '(((tok 31) Available)))))])
    (define configs
      (runtime-handler-trace handler-record-type
                             (first case)
                             (second case)
                             (third case)))
    (check-runtime-handler configs handler-record-type)
    (check-equal? (match (last configs)
                    [`(cfg ,value ,_heap ,_states ,_tokens ,_) value])
                  handler-record-value)))

(test-case "Return binder の root Owned encoding は全状態で構成を保つ"
  (define configs
    (runtime-handler-trace '(Owned Res)
                           '(Scope ()
                              (Let (owned let (Owned Res)) raw
                                   (Move owned)))
                           '(resource 31)
                           '()))
  (check-runtime-handler configs '(Owned Res)))

(test-case "Return binder の encoding 欠落と生名の漏出は binder ごとの key で拒否する"
  (define record-handler
    (lambda (body)
      `(Let (source let ,handler-record-type) ,handler-source-expression
         ,(handler-core handler-record-type body '(Move source)))))
  (define owned-handler
    (lambda (body)
      (handler-core '(Owned Res) body '(resource 31))))
  (check-equal? (key-of (record-handler 'unit) '()
                        handler-source-environment)
                "E-OWN-034")
  (check-equal?
   (key-of (record-handler
            '(Scope () (Let (place let Int) raw unit)))
           '() handler-source-environment)
   "E-OWN-034")
  (check-equal?
    (key-of
     (record-handler
      `(Scope () (Let (place let ,handler-record-type) raw raw)))
    '() handler-source-environment)
   "E-OWN-035")
  (check-equal? (key-of (owned-handler 'unit) '()) "E-OWN-032")
  (check-equal?
   (key-of (owned-handler '(Drop (Move raw))) '())
   "E-OWN-032")
  (check-equal?
   (key-of
    (owned-handler
     '(Scope () (Let (place let (Owned Res)) raw raw)))
    '())
   "E-OWN-032"))

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
    `(Eliminate
       (Construct ,mixed-type pack 1 (Construct ,middle-type none) 2)
       ((pack (left raw-middle right) ->
          (Scope ()
            (Let (middle let ,middle-type) raw-middle
                 (Let (drop Unit)
                      (Drop (Move middle))
                      1)))))))
  (define result
    (with-branch-data
      (core-type-of valid '() '())))
  (check-equal? result '(Int (Own)))
  (define missing
    `(Eliminate
       (Construct ,mixed-type pack 1 (Construct ,middle-type none) 2)
       ((pack (left raw-middle right) -> 1))))
  (check-equal?
   (with-branch-data (key-of missing '() '()))
   "E-OWN-034"))

(test-case "UnionEliminate の集約資源型の枝は encoding を要求する"
  (define member '(Option (Owned Res)))
  (define union-type (normalize-type `(Union Bool ,member)))
  (define valid
    `(UnionEliminate
       (UnionInject ,union-type Bool (Construct Bool true))
       ((Bool flag -> 0)
        (,member raw ->
         (Scope ()
           (Let (option let ,member) raw
                (Let (drop Unit) (Drop (Move option)) 1)))))))
  (check-equal?
   (core-type-of valid '() '())
   '(Int (Own)))
  (define missing
    `(UnionEliminate
       (UnionInject ,union-type Bool (Construct Bool true))
       ((Bool flag -> 0)
        (,member raw -> 1))))
  (check-equal?
   (key-of missing '())
   "E-OWN-034"))

(test-case "線形の穴の枝は root Owned と集約資源型を一度だけ運ぶ"
  (define owned-box '(Data OwnedBox ()))
  (define owned-source
    `(Eliminate
       (Construct ,owned-box box (OwnLeaf (resource 1)))
       ((box (raw) -> raw))))
  (check-equal?
   (with-branch-data (core-type-of owned-source '() '()))
   '((Owned Res) ()))

  (define aggregate '(Option (Owned Res)))
  (define mixed '(Data Mixed ()))
  (define mixed-source
    `(Eliminate
       (Construct ,mixed pack 1 (Construct ,aggregate none) 2)
       ((pack (left payload right) ->
          (Rec ((saved imm payload)))))))
  (check-equal?
   (with-branch-data (core-type-of mixed-source '() '()))
   `((Record ((saved ,aggregate imm))) ()))

  (define union-type (normalize-type `(Union Int ,aggregate)))
  (define union-result `(Record ((saved ,aggregate imm))))
  (define union-source
    `(UnionEliminate
       (UnionInject ,union-type Int 1)
       ((Int number ->
         (Rec ((saved imm (Construct ,aggregate none)))))
        (,aggregate payload ->
         (Rec ((saved imm payload)))))))
  (check-equal?
   (core-type-of union-source '() '())
   (list union-result '())))

(test-case "線形の穴の方式では複製と L の外の使用を拒否する"
  (define owned-box '(Data OwnedBox ()))
  (define (eliminate body)
    `(Eliminate
       (Construct ,owned-box box (OwnLeaf (resource 1)))
       ((box (raw) -> ,body))))
  (for ([body (in-list
               (list '(Rec ((left imm raw) (right imm raw)))
                     '(Drop raw)
                     '(Eliminate (Construct Bool true)
                        ((true () -> raw)
                         (false () -> raw)))))])
    (check-equal?
     (with-branch-data
       (key-of (eliminate body) '()))
     "E-OWN-034")))

(test-case "借用 scrutinee の資源型枝 binder は encoding なしで受理する"
  (define member '(Option (Owned Res)))
  (define union-type (normalize-type `(Union Int ,member)))
  (define borrowed-union
    `(Scope ()
       (Let (owner let ,union-type)
         (UnionInject ,union-type ,member (Construct ,member none))
         (UnionEliminate (Borrow owner)
           ((Int number -> 0)
            (,member payload -> 0))))))
  (define union-result (type-borrowed-local borrowed-union '()))
  (check-equal? (first union-result) 'ok (format "結果: ~s" union-result))

  (define owned-box '(Data OwnedBox ()))
  (define borrowed-data
    '(Scope ()
       (Let (owner let (Data OwnedBox ()))
         (Construct (Data OwnedBox ()) box (OwnLeaf (resource 1)))
         (Eliminate (Borrow owner)
           ((box (payload) -> 0))))))
  (check-equal?
   (with-branch-data
     (first (type-borrowed-local borrowed-data '())))
   'ok))

(test-case "複数の線形穴 binder は同じ Rec の別欄へ一度ずつ運べる"
  (define member '(Option (Owned Res)))
  (define duo '(Data Duo ()))
  (define output
    `(Record ((first ,member imm) (second ,member imm))))
  (define linear
    `(Eliminate
       (Construct ,duo pair
         (Construct (Option (Owned Res)) none)
         (Construct (Option (Owned Res)) none))
       ((pair (first second) ->
         (Rec ((first imm first) (second imm second)))))))
  (check-equal?
   (with-branch-data (core-type-of linear '() '()))
   (list output '()))

  (define mixed
    `(Eliminate
       (Construct ,duo pair
         (Construct ,member none)
         (Construct ,member none))
       ((pair (first second) ->
         (Scope ()
           (Let (first-place let ,member) first
                (Rec ((first imm (Move first-place))
                      (second imm second)))))))))
  (check-equal?
   (with-branch-data (key-of mixed '()))
   "E-OWN-034"))

(test-case "線形の穴の許可は兄弟の枝へ漏れず内側 Let の shadowing を守る"
  (define leaked
    '(Eliminate
       (Construct (Data OwnedOrInt ()) plain 0)
       ((boxed (raw) -> raw)
        (plain (number) -> raw))))
  (check-equal?
   (with-branch-data (key-of leaked '() '((raw (Owned Res)))))
   "E-OWN-019")

  (define mixed '(Data Mixed ()))
  (define shadowed
    '(Eliminate
      (Construct (Data Mixed ()) pack 1
                 (Construct (Option (Owned Res)) none) 2)
      ((pack (left raw right) ->
        (Rec ((payload imm raw)
              (shadow imm (Let (raw let Int) 1 raw))))))))
  (check-equal?
   (with-branch-data (key-of shadowed '()))
   'ok)

  (define member '(Option (Owned Res)))
  (define shadowed-resource
    `(Eliminate
       (Construct ,mixed pack 1 (Construct ,member none) 2)
       ((pack (left raw right) ->
         (Rec ((outer imm raw)
               (shadow imm
                (Let (raw let ,member)
                     (Construct ,member none)
                     (Rec ((inner imm raw)))))))))))
  (check-equal?
   (with-branch-data (key-of shadowed-resource '()))
   "E-OWN-019"))

(test-case "非空 Scope を先頭に持つ枝は encoding と判定して拒否する"
  (define owned-box '(Data OwnedBox ()))
  (define malformed
    '(Eliminate
       (Construct (Data OwnedBox ()) box (OwnLeaf (resource 1)))
       ((box (raw) -> (Scope (13) raw)))))
  (check-equal?
   (with-branch-data (key-of malformed '()))
   "E-OWN-034"))

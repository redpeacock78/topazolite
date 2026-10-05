#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../compat.rkt"
         "../typing.rkt"
         "../machine.rkt")

(define record-type '(Record ((a Int imm))))
(define record-value '(Rec ((a mut 1))))
(define ρ 'ρ)

(define (has-mutation? term)
  (match term
    [`(Assign ,_ ,_) #t]
    [`(Reassign ,_ ,_) #t]
    [(? list? parts) (ormap has-mutation? parts)]
    [_ #f]))

(define (current-row core row)
  (if (and (member 'Mutation row) (not (has-mutation? core)))
      (remove 'Mutation row)
      row))

(define (result-key core [environment '()])
  (match (type-of/raw core '() '() environment (empty-region-ctx))
    [`(fail ,key ,_ ,_ ...) key]
    [`(ok ,_) 'ok]))

(define (typed-input core [callables '()])
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define mut-types (box 'stale))
  (define result
    (type-of/raw annotated '() callables '()
                 (region-ctx ir '() (hash) (hash))
                 #:mut-types mut-types))
  (values ir annotated result mut-types))

(define (config-control config)
  (match config [`(cfg ,core ,_ ...) core] [_ #f]))

(define (heap-place-value config place)
  (match config
    [`(cfg ,_ ,heap ,_ ...)
     (match (assoc place heap)
       [(list _ value _ ...) value]
       [_ #f])]
    [_ #f]))

(define (contains-form? tree form)
  (or (and (pair? tree) (eq? (first tree) form))
      (and (list? tree)
           (ormap (lambda (part) (contains-form? part form)) tree))))

(define (contains-owned-binding? tree)
  (match tree
    [`(Let (,_ ,_ (Owned ,_)) ,_ ,_) #t]
    [(? list? parts) (ormap contains-owned-binding? parts)]
    [_ #f]))

(define (borrow-allocation-pending? config)
  (match config
    [`(cfg ,core ,heap ,_ ,_ ,_)
     (or (and (null? heap) (contains-owned-binding? core))
         (and (or (contains-form? core 'BorrowAt)
                  (contains-form? core 'BorrowMutAt))
              (for/or ([entry (in-list heap)])
                (match entry
                  [`(,_ ,_ (declared (Owned ,_))) #t]
                  [_ #f]))))]
    [_ #f]))

(define (typed-trace core
                     #:skip-borrow-allocation-prefix? [skip-prefix? #f]
                     #:callables [callables '()])
  (define-values (ir annotated result mut-types) (typed-input core callables))
  (match result
    [`(ok (,expected ,row))
     (define machine-core
       (annotate-mut-binding-types annotated (unbox mut-types)))
     (define configs
       (let loop ([config (inject-g2m machine-core)]
                  [remaining 100]
                  [seen '()])
         (define next (raw-steps-g2 config))
         (cond
           [(null? next) (reverse (cons config seen))]
           [(zero? remaining) (fail (format "machine did not finish: ~s" config))]
           [(= (length next) 1)
            (loop (first next) (sub1 remaining) (cons config seen))]
           [else (fail (format "nondeterministic machine step: ~s" next))])))
     (define (config-valid? config)
       (with-handlers
           ([exn:fail?
             (lambda (problem)
               (error 'typed-trace "config ~s: ~a"
                      config (exn-message problem)))])
         (config-ok? config callables expected
                     (current-row (second config) row))))
     (if skip-prefix?
         (let ([first-valid
                (for/first ([config (in-list configs)]
                            [index (in-naturals)]
                            #:when (config-valid? config))
                  index)])
           (check-not-false first-valid "a well-formed config must be reached")
           (when first-valid
             (define skipped (take configs first-valid))
             (define checked (drop configs first-valid))
             (check-true (positive? first-valid)
                         "borrow allocation setup must precede the first checked config")
             (check-true (andmap borrow-allocation-pending? skipped)
                         "only Owned-place/borrow allocation setup may be skipped")
             (check-true
              (or (contains-form? (second (first checked)) 'BorrowRef)
                  (contains-form? (second (first checked)) 'BorrowMutRef))
              "the first checked config must contain the materialized borrow")
             (check-true (andmap config-valid? checked)
                         "every config after borrow allocation must be valid")))
         (check-true (andmap config-valid? configs)
                     (format "ill-formed intermediate config: ~s"
                             (for/first ([config (in-list configs)]
                                         #:unless (config-valid? config))
                               config))))
     (values expected row configs (last configs))]
    [other (fail (format "type checking failed: ~s" other))]))

(test-case "mut binding は宣言型が imm の値を保存して config-ok? を保つ"
  (define-values (type _row configs final)
    (typed-trace `(Scope () (Let (m mut ,record-type) ,record-value m))))
  (check-equal? type record-type)
  (check-true (pair? configs))
  (check-equal? (match final [`(cfg ,value ,_ ,_ ,_ ,_) value] [_ #f])
                record-value))

(test-case "R-Reassign は mut slot の宣言 metadata を保つ"
  (define core
    `(Scope ()
       (Let (m mut ,record-type) (Rec ((a imm 1)))
         (Let (written let Unit) (Reassign m (Rec ((a imm 2)))) m))))
  (define-values (_type _row configs _final) (typed-trace core))
  (define recorded
    (filter (lambda (config) (pair? (config-declared-types config))) configs))
  (check-true (>= (length recorded) 2))
  (for ([config (in-list recorded)])
    (check-equal? (config-declared-types config) `((0 ,record-type))))
  (define before-index
    (for/first ([config (in-list configs)]
                [index (in-naturals)]
                #:when (and (equal? (heap-place-value config 0)
                                    '(Rec ((a imm 1))))
                            (contains-form? (config-control config) 'Reassign)))
      index))
  (check-not-false before-index)
  (when before-index
    (define after
      (for/first ([config (in-list (drop configs (add1 before-index)))]
                  #:when (equal? (heap-place-value config 0)
                                 '(Rec ((a imm 2)))))
        config))
    (check-not-false after)
    (check-equal? (heap-place-value (list-ref configs before-index) 0)
                  '(Rec ((a imm 1))))
    (when after
      (check-equal? (heap-place-value after 0) '(Rec ((a imm 2))))))
  (check-equal? (match _final [`(cfg ,value ,_ ...) value] [_ #f])
                '(Rec ((a imm 2)))))

(test-case "Reassign の四つの束縛境界で再型付けを保つ"
  (define union-type `(Union ,record-type Bool))
  (define callable-id 'reassign-mut-boundary)
  (define callable-type
    `(NFn (,record-type) Unit () (Mutation) () User))
  (define cores
    (list
     `(Scope ()
        (Let (m mut ,record-type) (Rec ((a imm 1)))
          (Let (s const ,record-type) (Rec ((a mut 2)))
            (Let (written let Unit) (Reassign m s) m))))
     `(Scope ()
        (Let (m mut ,record-type) (Rec ((a imm 1)))
          (Let (called let Unit)
            (Apply (Lam User ,callable-id (s) (Reassign m s))
                   (Rec ((a mut 2))))
            m)))
     `(Scope ()
        (Let (m mut ,record-type) (Rec ((a imm 1)))
          (Eliminate
           (Construct (Option ,record-type) some (Rec ((a mut 2))))
           ((some (s) -> (Let (written let Unit) (Reassign m s) m))
            (none () -> m)))))
     `(Scope ()
        (Let (m mut ,record-type) (Rec ((a imm 1)))
          (UnionEliminate
           (UnionInject ,union-type ,record-type (Rec ((a mut 2))))
           ((,record-type s -> (Let (written let Unit) (Reassign m s) m))
            (Bool b -> m)))))))
  (for ([core (in-list cores)] [index (in-naturals)])
    (define callables (if (= index 1) `((,callable-id ,callable-type)) '()))
    (define-values (type row configs final)
      (typed-trace core #:callables callables))
    (check-equal? type record-type (format "boundary ~a type" index))
    (check-not-false (member 'Mutation row)
                     (format "boundary ~a mutation row" index))
    (check-true (andmap (lambda (config)
                          (config-ok? config callables type
                                      (current-row (second config) row)))
                        configs)
                (format "boundary ~a config validity" index))
    (check-equal? (match final [`(cfg ,value ,_ ...) value] [_ #f])
                  '(Rec ((a mut 2)))
                  (format "boundary ~a final value" index))))

(test-case "Reassign は imm 欄へ mut 欄の値を代入できる"
  (define core
    `(Scope ()
       (Let (m mut ,record-type) (Rec ((a imm 1)))
         (Reassign m (Rec ((a mut 2)))))))
  (define-values (type row _configs _final) (typed-trace core))
  (check-equal? type 'Unit)
  (check-not-false (member 'Mutation row)))

(test-case "Reassign は mut 欄への imm 欄と欄構造の違いを拒む"
  (define mut-record-type '(Record ((a Int mut))))
  (define base-env `((m ,mut-record-type mut)))
  (check-equal?
   (result-key '(Reassign m (Rec ((a imm 2)))) base-env)
   'reassign-type-mismatch "mut slot type mismatch")
  (check-equal?
   (result-key '(Reassign m (Rec ((a imm 2) (b imm 3)))) base-env)
   'reassign-type-mismatch "extra field")
  (check-equal?
   (result-key
    '(Reassign m (Rec ((a imm 2))))
    '((m (Record ((a Int imm opt))) mut)))
   'reassign-type-mismatch "optional mismatch"))

(test-case "Reassign の mut から imm への縮小は入れ子の imm 欄でも再帰する"
  (define nested-imm
    '(Record ((a (Record ((c Int imm))) imm))))
  (check-equal?
   (result-key '(Reassign m (Rec ((a imm (Rec ((c mut 2)))))))
               `((m ,nested-imm mut)))
   'ok)
  (define outer-mut
    '(Record ((a (Record ((c Int imm))) mut))))
  (check-equal?
   (result-key '(Reassign m (Rec ((a mut (Rec ((c mut 2)))))))
               `((m ,outer-mut mut)))
   'reassign-type-mismatch))

(test-case "reassign-narrowing? は wrapper の不変性と Union narrowing を保つ"
  (check-false
   (reassign-narrowing? '(Owned (Record ((a Int mut))))
                        '(Owned (Record ((a Int imm))))))
  (check-true (reassign-narrowing? '(Union Int Bool)
                                   '(Union Int (Union String Bool))))
  (check-false (reassign-narrowing? '(Union Int (Union String Bool))
                                    '(Union Int Bool))))

(test-case "Reassign 専用の緩和は tag narrowing と tag compatibility を変えない"
  (check-false
   (tag-narrowing? '(Record ((a Int mut)))
                   '(Record ((a Int imm)))))
  (check-true
   (tag-compat? '(Record ((a Int mut)))
                '(Record ((a Int imm))))))

(test-case "mut 束縛の有効型を記録して注釈し、residual の射影を保つ"
  (define core
    '(Let (x mut (Record ((a Int imm))))
       (Rec ((a imm 1) (b imm (Construct Bool true))))
       (Proj x b)))
  (define effective-type '(Record ((a Int imm) (b Bool imm))))
  (define-values (_ir annotated result mut-types) (typed-input core))
  (check-equal? result '(ok (Bool ())))
  (check-equal? (unbox mut-types) (hash '() effective-type))
  (check-equal?
   (annotate-mut-binding-types annotated (unbox mut-types))
   `(Let (x mut ,effective-type)
      (Rec ((a imm 1) (b imm (Construct Bool true))))
      (Proj x b)))
  (define-values (type _row configs final) (typed-trace core))
  (check-equal? type 'Bool)
  (define recorded
    (filter (lambda (config) (pair? (config-declared-types config))) configs))
  (check-true (pair? recorded))
  (check-true (andmap (lambda (config)
                        (equal? (config-declared-types config)
                                `((0 ,effective-type))))
                      recorded))
  (check-equal? (match final [`(cfg ,value ,_ ...) value] [_ #f])
                '(Construct Bool true)))

(test-case "const alias の residual も有効型として metadata に記録する"
  (define core
    '(Let (source const (Record ((a Int imm) (b Bool imm))))
       (Rec ((a mut 1) (b mut (Construct Bool true))))
       (Let (m mut (Record ((a Int imm))))
         source
         (Proj m b))))
  (define effective-type '(Record ((a Int imm) (b Bool imm))))
  (define-values (type _row configs final) (typed-trace core))
  (check-equal? type 'Bool)
  (check-true (for/or ([config (in-list configs)])
                (equal? (config-declared-types config)
                        `((0 ,effective-type)))))
  (check-equal? (match final [`(cfg ,value ,_ ...) value] [_ #f])
                '(Construct Bool true))
  (check-equal?
   (proj-borrow-mut
    0 '(b) ρ
    '((0
       (Rec ((a mut 1) (b mut (Construct Bool true))))
       (declared (Record ((a Int imm) (b Bool imm)))))))
   '(BorrowRef 0 (b) ρ)))

(test-case "residual のない mut 束縛は宣言型を記録する"
  (define core
    '(Scope () (Let (m mut (Record ((a Int imm))))
             (Rec ((a imm 1))) m)))
  (define-values (_ir _annotated result mut-types) (typed-input core))
  (check-equal? result '(ok ((Record ((a Int imm))) ())))
  (check-equal? (unbox mut-types)
                (hash '(0) '(Record ((a Int imm)))))
  (define-values (_type _row configs _final) (typed-trace core))
  (check-true (for/or ([config (in-list configs)])
                (equal? (config-declared-types config)
                        '((0 (Record ((a Int imm)))))))))

(test-case "有効型で注釈した三つの項は再型付けで同じ型を得る"
  (define residual-core
    '(Let (x mut (Record ((a Int imm))))
       (Rec ((a imm 1) (b imm (Construct Bool true))))
       (Proj x b)))
  (define alias-core
    '(Let (source const (Record ((a Int imm) (b Bool imm))))
       (Rec ((a mut 1) (b mut (Construct Bool true))))
       (Let (m mut (Record ((a Int imm)))) source (Proj m b))))
  (define reassign-core
    '(Scope ()
       (Let (m mut (Record ((a Int imm)))) (Rec ((a imm 1)))
         (Let (written let Unit) (Reassign m (Rec ((a imm 2)))) m))))
  (for ([core (in-list (list residual-core alias-core reassign-core))])
    (define-values (ir annotated result mut-types) (typed-input core))
    (check-true (match result [`(ok ,_) #t] [_ #f]))
    (define typed-core
      (annotate-mut-binding-types annotated (unbox mut-types)))
    (check-equal?
     (type-of/raw typed-core '() '() '()
                  (region-ctx ir '() (hash) (hash)))
     result)))

(test-case "同名の入れ子 mut 束縛は内側だけ有効型へ置き換える"
  (define core
    '(Let (x mut (Record ((a Int imm))))
       (Rec ((a imm 1)))
       (Let (x mut (Record ((a Int imm))))
         (Rec ((a imm 2) (b imm (Construct Bool true))))
         (Proj x b))))
  (define outer-type '(Record ((a Int imm))))
  (define inner-type '(Record ((a Int imm) (b Bool imm))))
  (define-values (_ir annotated result mut-types) (typed-input core))
  (check-equal? result '(ok (Bool ())))
  (check-equal? (unbox mut-types)
                (hash '() outer-type '(1) inner-type))
  (check-equal?
   (annotate-mut-binding-types annotated (unbox mut-types))
   `(Let (x mut ,outer-type)
      (Rec ((a imm 1)))
      (Let (x mut ,inner-type)
        (Rec ((a imm 2) (b imm (Construct Bool true))))
        (Proj x b)))))

(test-case "mut 型の keyword は各入口で成功時だけ表を返す"
  (define core
    '(Let (m mut (Record ((a Int imm)))) (Rec ((a imm 1))) m))
  (define expected (hash '() '(Record ((a Int imm)))))
  (define raw-types (box 'stale))
  (check-true (match (type-of/raw core '() '() '() (empty-region-ctx)
                                #:mut-types raw-types)
                [`(ok ,_) #t]
                [_ #f]))
  (check-equal? (unbox raw-types) expected)
  (define borrow-types (box 'stale))
  (check-true (match (type-of/raw*+borrows
                      core '() '() '() (empty-region-ctx)
                      #:mut-types borrow-types)
                [`(ok ,_) #t]
                [_ #f]))
  (check-equal? (unbox borrow-types) expected)
  (define ptr-types (box 'stale))
  (check-true (match (type-of/raw*+ptr
                      core '() '() '() (empty-region-ctx)
                      #:mut-types ptr-types)
                [`(ok ,_) #t]
                [_ #f]))
  (check-equal? (unbox ptr-types) expected)
  (define failed-types (box (hash 'stale 'Int)))
  (check-true (match (type-of/raw
                      '(Let (m mut (Record ((a Int imm))))
                         (Rec ((a imm 1)))
                         (Apply 1 2))
                      '() '() '() (empty-region-ctx)
                      #:mut-types failed-types)
                [`(fail ,_ ,_ ,_) #t]
                [_ #f]))
  (check-equal? (unbox failed-types) (hash)))

(test-case "spanful mut Let の位置は spanless の注釈走査と一致する"
  (define span '(#:span src 0 1))
  (define core
    `(Let ,span
       ((#:bind m ,span) mut (#:ty ,record-type ,span))
       (Rec ,span ((a imm (#:lit 1 ,span))))
       (#:var m ,span)))
  (define mut-types (box 'stale))
  (check-true (match (type-of/raw core '() '() '() (empty-region-ctx)
                                #:mut-types mut-types)
                [`(ok ,_) #t]
                [_ #f]))
  (check-equal? (unbox mut-types) (hash '() record-type))
  (check-equal? (annotate-mut-binding-types core (unbox mut-types))
                `(Let (m mut ,record-type)
                   (Rec ((a imm 1)))
                   m)))

(test-case "mut 型の表にない Let は元の型を保つ"
  (define core
    '(Let (m mut (Record ((a Int imm)))) (Rec ((a imm 1))) m))
  (check-equal? (annotate-mut-binding-types core (hash)) core))

(test-case "proj-borrow-mut は runtime の欄印より宣言型を優先する"
  (check-equal?
   (proj-borrow-mut 0 '(a) ρ
                    '((0 (Rec ((a mut 1)))
                         (declared (Record ((a Int imm)))))))
   '(BorrowRef 0 (a) ρ))
  (check-equal?
   (proj-borrow-mut 0 '(a) ρ
                    '((0 (Rec ((a imm 1)))
                         (declared (Record ((a Int mut)))))))
   '(BorrowMutRef 0 (a) ρ)))

(test-case "proj-borrow-mut は入れ子の欄印を宣言型から辿る"
  (check-equal?
   (proj-borrow-mut
    0 '(a c) ρ
    '((0 (Rec ((a mut (Rec ((c mut 1))))))
         (declared (Record ((a (Record ((c Int imm))) mut)))))))
   '(BorrowRef 0 (a c) ρ)))

(test-case "Owned record の slot 書込み後も宣言型の能力を使う"
  (define rec-type '(Record ((a Int mut))))
  (define rec-value '(Rec ((a mut 1))))
  (define core
    `(Scope ()
       (Let (o let (Owned ,rec-type)) ,rec-value
         (Let (r let (BorrowedMut ,rec-type (RVar 0))) (BorrowMut o)
           (Let (written let Unit) (Assign r (Rec ((a mut 3))))
             (Read (ProjBorrow r a)))))))
  (define-values (type row configs final)
    (typed-trace core #:skip-borrow-allocation-prefix? #t))
  (check-equal? type 'Int)
  (check-not-false (member 'Mutation row))
  (check-equal? (match final [`(cfg ,value ,_ ,_ ,_ ,_) value] [_ #f]) 3)
  (check-equal?
   (proj-borrow-mut
    0 '(a) ρ
    '((0 (Rec ((a imm 1)))
         (declared (Owned (Record ((a Int mut))))))))
   '(BorrowMutRef 0 (a) ρ)))

(test-case "Absent 欄とその内側への射影は能力を作らない"
  (define heap
    '((0 (Rec ((b mut (Absent Int))))
         (declared (Record ((b Int imm opt)))))))
  (check-false (proj-borrow-mut 0 '(b) ρ heap))
  (check-false (proj-borrow-mut 0 '(b inner) ρ heap))
  (define core '(Scope (0) (ProjBorrow (BorrowMut 0) b)))
  (define ir (build-region-ir core))
  (define result
    (type-of/raw (annotate-regions core ir)
                 '((0 (Record ((b Int mut opt))))) '() '()
                 (region-ctx ir '() (hash 0 (region-at ir '())) (hash))))
  (check-equal? (match result [`(fail ,key ,_ ,_ ...) key] [_ #f])
                'projborrow-optional-field))

(test-case "metadata のない place からは能力を作らない"
  (check-false (proj-borrow-mut 0 '(a) ρ '((0 (Rec ((a mut 1))))))))

(test-case "UnionVal の Payload path は能力を作らない"
  (check-false
   (proj-borrow-mut
    0 '(payload (Payload) a) ρ
    '((0 (UnionVal (Union (Record ((a Int mut))) String)
                  (Record ((a Int mut)))
                  (Rec ((a mut 1))))
         (declared (Union (Record ((a Int mut))) String)))))))

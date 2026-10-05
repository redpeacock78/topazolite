#lang racket

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
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

(define (typed-trace core #:skip-borrow-allocation-prefix? [skip-prefix? #f])
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define result
    (type-of/raw annotated '() '() '()
                 (region-ctx ir '() (hash) (hash))))
  (match result
    [`(ok (,expected ,row))
     (define configs
       (let loop ([config (inject-g2m annotated)] [remaining 100] [seen '()])
         (define next (raw-steps-g2 config))
         (cond
           [(null? next) (reverse (cons config seen))]
           [(zero? remaining) (fail (format "machine did not finish: ~s" config))]
           [(= (length next) 1)
            (loop (first next) (sub1 remaining) (cons config seen))]
           [else (fail (format "nondeterministic machine step: ~s" next))])))
     (define (config-valid? config)
       (config-ok? config '() expected
                   (current-row (second config) row)))
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
    (check-equal? (config-declared-types config) `((0 ,record-type)))))

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

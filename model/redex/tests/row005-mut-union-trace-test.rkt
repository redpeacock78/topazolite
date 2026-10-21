#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define narrow-union '(Union Bool Int))
(define wide-union '(Union Bool (Union Int Unit)))
(define narrow-record `(Record ((a ,narrow-union mut))))
(define wide-record `(Record ((a ,wide-union mut))))

(define (control cfg)
  (match cfg [`(cfg ,core ,_ ...) core]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (compile source)
  (match (elab source)
    [(list core type _row callables)
     (values (execution-core core callables) type callables)]
    [other (fail-check (format "elaboration に失敗した: ~s" other))]))

(define (replace-symbol tree old new)
  (cond
    [(eq? tree old) new]
    [(pair? tree)
     (cons (replace-symbol (car tree) old new)
           (replace-symbol (cdr tree) old new))]
    [else tree]))

(define (replace-placeholder-with-borrow core borrow-type borrow-expression)
  (define found? #f)
  (define (walk node)
    (match node
      [`(Let (,name let ,type) ,_bound ,body)
       (if (and (not found?) (type-equiv? type narrow-union))
           (begin
             (set! found? #t)
             `(Let (,name let ,borrow-type) ,borrow-expression
                   ,(replace-symbol body name `(Read ,name))))
           `(Let (,name let ,type) ,(walk _bound) ,(walk body)))]
      [(? list? parts) (map walk parts)]
      [_ node]))
  (define result (walk core))
  (check-true found? "借用値の setup 用 placeholder が一つ見つかる")
  result)

(define (check-trace configs callables expected [require-empty-row? #t])
  (define rows
    (for/list ([cfg (in-list configs)] [index (in-naturals)])
      (define row (runtime-row cfg callables expected))
      (check-not-false row (format "config ~a の runtime-row が無い: ~s" index cfg))
      (check-true (config-ok? cfg callables expected row)
                  (format "config ~a が config-ok? を通らない: ~s" index cfg))
      (when require-empty-row?
        (check-equal? row '() (format "config ~a の row が空でない: ~s" index row)))
      row))
  (for ([before (in-list rows)] [after (in-list (cdr rows))] [index (in-naturals)])
    (check-true (row-subset? after before)
                (format "config ~a から row が増えた: ~s -> ~s" index before after))))

(define (checked-borrow-trace configs callables expected)
  ;; shortcut: 挿入した BorrowAt は place 0 の確保前には型付けできないため、最初の確保構成から検査する。
  ;; 前半も必要になれば初期 config を seed する。
  (define initialized
    (for/first ([cfg (in-list configs)] [index (in-naturals)]
                #:when (member (list 0 narrow-record) (config-declared-types cfg)))
      index))
  (check-not-false initialized "狭い旧 place が確保される")
  (when initialized
    (define checked (drop configs initialized))
    (check-trace checked callables expected)
    (for ([cfg (in-list (take configs initialized))])
      (check-false
       (walk-find (lambda (node)
                    (match node
                      [(or `(BorrowRef ,_ ,_ ,_) `(BorrowMutRef ,_ ,_ ,_)) #t]
                      [_ #f]))
                  cfg)))
    checked))

(define (walk-find predicate value)
  (or (and (predicate value) value)
      (and (list? value) (for/or ([child (in-list value)])
                          (walk-find predicate child)))))

(define (make-source [borrow-after-wide? #f])
  `(Apply
    (Fn () ,narrow-union ()
      (Let (u const ,narrow-union) 1
        (Let (old mut ,narrow-record) (Rec ((a mut u)))
          ,(if borrow-after-wide?
               `(Let (wide mut ,wide-record) old
                  (Let (old-ref let ,narrow-union) 1
                    (Let (new-field let ,wide-union) (Proj wide a)
                      old-ref)))
               `(Let (old-ref let ,narrow-union) 1
                  (Let (wide mut ,wide-record) old
                    (Let (new-field let ,wide-union) (Proj wide a)
                      old-ref)))))))))

(define (run-borrowed-source source borrow-type borrow-expression)
  (define-values (core expected callables) (compile source))
  (define with-borrow
    (replace-placeholder-with-borrow core borrow-type borrow-expression))
  (define-values (configs rules) (trace-g2 (inject-g2m with-borrow)))
  (define checked (checked-borrow-trace configs callables expected))
  (check-not-false (member 'R-RecRewrite-Open rules))
  (values checked rules callables expected))

(define (check-old-and-new-declarations configs)
  (define declared
    (for/first ([cfg (in-list configs)]
                #:when (and (member (list 0 narrow-record) (config-declared-types cfg))
                            (member (list 1 wide-record) (config-declared-types cfg))))
      (config-declared-types cfg)))
  (check-not-false declared "狭い旧 place と広い新 place の宣言型が同時に残る"))

(define (available-token-ids cfg)
  (match cfg
    [`(cfg ,_ ,_ ,_ ,token-states ,_)
     (for/list ([entry (in-list token-states)]
                #:when (eq? (second entry) 'Available))
       (first entry))]))

(define (live-token-ids cfg)
  (match cfg
    [`(cfg ,core ,heap ,states ,_ ,_)
     (collect-tokens
      (cons core
            (for/list ([entry (in-list heap)]
                       #:when (match (assoc (first entry) states)
                                [(list _ 'Available) #t]
                                [_ #f]))
              (second entry))))]))

(test-case "ROW-005 再構成中も旧欄の共有 BorrowRef を保つ"
  (define-values (configs rules _callables _expected)
    (run-borrowed-source
     (make-source)
     `(Borrowed ,narrow-union 17)
     '(ProjBorrowAt 17 (BorrowAt 17 (Own 0 ()) 0) a)))
  (check-not-false (member 'R-RecRewrite-Open rules))
  (check-not-false
   (for/or ([cfg (in-list configs)])
     (walk-find (lambda (node) (match node [`(BorrowRef 0 (a) 17) #t] [_ #f])) cfg)))
  (check-old-and-new-declarations configs))

(test-case "ROW-005 広い place の再構成後に旧欄の BorrowMutRef を作る"
  (define-values (configs rules _callables _expected)
    (run-borrowed-source
     (make-source #t)
     `(BorrowedMut ,narrow-union 17)
     '(ProjBorrowAt 17 (BorrowMutAt 17 (Own 0 ()) 0) a)))
  (check-not-false (member 'R-RecRewrite-Open rules))
  (check-not-false
   (for/or ([cfg (in-list configs)])
     (walk-find (lambda (node) (match node [`(BorrowMutRef 0 (a) 17) #t] [_ #f])) cfg)))
  (check-old-and-new-declarations configs))

(test-case "ROW-005 内部 Owned leaf を持つ値の再構成で token を一度だけ保つ"
  (define owned-field '(Option (Owned Res)))
  (define narrow-owned-record
    `(Record ((a ,narrow-union mut) (owned ,owned-field imm))))
  (define wide-owned-record
    `(Record ((a ,wide-union mut) (owned ,owned-field imm))))
  (define source
    `(Apply
      (Fn () ,wide-owned-record (Own)
        (Let (u const ,narrow-union) 1
          (Let (source let ,narrow-owned-record)
               (Rec ((a mut u)
                     (owned imm
                       (Construct some (Types (Owned Res))
                                  (Apply acquire 13)))))
            (Let (target let ,wide-owned-record) (Move source)
              (Move target)))))))
  (define-values (core expected callables) (compile source))
  (define-values (configs rules) (trace-g2 (inject-g2m core)))
  (check-trace configs callables expected #f)
  (check-not-false (member 'R-RecRewrite-Open rules))
  (define token-index
    (for/first ([cfg (in-list configs)] [index (in-naturals)]
                #:when (pair? (available-token-ids cfg)))
      index))
  (check-not-false token-index "生成 token が Available になる")
  (when token-index
    (for ([cfg (in-list (drop configs token-index))])
      (define available (available-token-ids cfg))
      (check-equal? (length available) 1)
      (check-equal? (live-token-ids cfg) available)))
  (check-equal? (length (available-token-ids (last configs))) 1))

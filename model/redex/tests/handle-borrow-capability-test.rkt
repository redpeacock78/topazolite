#lang racket

(require rackunit
         racket/list
         racket/match
         racket/set
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define borrowed '(Borrowed Int (RParam %omitted)))
(define borrowed-mut '(BorrowedMut Int (RParam %omitted)))
(define borrowed-option `(Option ,borrowed))
(define u-borrowed '(Borrowed Int Omitted))
(define return-op `(Return boundary ,borrowed))

(define (typed core)
  (core-type-of/regions core '() '()))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 200])
    (when (zero? fuel) (error 'trace-g2 "fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next)) (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (trace-and-check core expected-type expected-value)
  (define result (typed core))
  (check-true (region-typed? result) (format "受理を期待、実測: ~s" result))
  (when (region-typed? result)
    (check-equal? (region-typed-type result) expected-type)
    (define configs
      (trace-g2 (inject-g2m (erase-core (region-execution-core result)))))
    (for ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config '() expected-type))
      (check-not-false row (format "config ~a に runtime-row がある" index))
      (when row
        (check-true (config-ok? config '() expected-type row)
                    (format "config ~a が config-ok? を通る" index))))
    (match (last configs)
      [`(cfg ,value ,_heap ,_states ,_tokens ,_events)
       (check-equal? value expected-value)]
      [other (fail (format "終端 config を期待、実測: ~s" other))])))

(define (branch-handle-core selected)
  `(Let (x let (Owned Int)) 41
     (Let (y let (Owned Int)) 42
       (Let (bp let ,borrowed) (Borrow x)
         (Let (bq let ,borrowed) (Borrow y)
           (Let (chosen let ,borrowed)
             (Handle ,return-op (returned -> returned)
               (Eliminate ,(if (eq? selected 'some)
                               '(Construct (Option Int) some 0)
                               '(Construct (Option Int) none))
                 ((some (tag) -> bp)
                  (none () -> bq))))
             (Read chosen)))))))

(define return-capture-core
  `(Let (owner let (Owned Int)) 41
     (Let (borrowed-value let ,borrowed)
       (Handle ,return-op
         (returned ->
           (Let (observed let Int) (Read returned) returned))
         (Scope ()
           (Let (source let ,borrowed) (Borrow owner)
             (Perform ,return-op source))))
       (Read borrowed-value))))

(define record-borrowed-type `(Record ((item ,borrowed imm))))
(define record-return-op `(Return boundary ,record-borrowed-type))

(define (mixed-handle-capability-core selected)
  `(Let (x let (Owned Int)) 41
     (Let (y let (Owned Int)) 42
       (Let (bx let ,borrowed) (Borrow x)
         (Let (by let ,borrowed) (Borrow y)
           (Let (result let ,record-borrowed-type)
             (Handle ,record-return-op
               (returned -> returned)
               (Eliminate ,(if (eq? selected 'some)
                               '(Construct (Option Int) some 0)
                               '(Construct (Option Int) none))
                 ((some (tag) -> (Rec ((item imm bx))))
                  (none () ->
                    (Perform ,record-return-op
                             (Rec ((item imm by))))))))
             (Read (Proj result item))))))))

(define nested-return-core
  `(Let (x let (Owned Int)) 41
     (Let (y let (Owned Int)) 42
       (Let (bx let ,borrowed) (Borrow x)
         (Let (by let ,borrowed) (Borrow y)
           (Let (result let ,borrowed)
             (Handle ,return-op
               (outer -> (Let (observed let Int) (Read outer) outer))
               (Handle ,return-op
                 (inner -> (Perform ,return-op by))
                 (Perform ,return-op bx)))
             (Read result)))))))

(define (elaborated-return-source)
  `(Fn ((owner (Owned Int))) Int (Own)
       (Let (borrowed-value const ,u-borrowed)
         (NarrativeExpr (Leave (Borrow owner)))
         (Read borrowed-value))))

(define leave-capture-core
  `(Let (owner let (Owned Int)) 41
     (Let (option-value let ,borrowed-option)
       (Handle (Return boundary ,borrowed-option)
         (returned ->
           (Let (observed let Int)
             (Eliminate returned
               ((none () -> 0)
                (some (item) -> (Read item))))
             returned))
         (Scope ()
           (Let (source let ,borrowed) (Borrow owner)
             (Perform (Return boundary ,borrowed-option)
               (Construct ,borrowed-option some source)))))
       (Eliminate option-value
         ((none () -> 0)
          (some (item) -> (Read item)))))))

(define owner-body-return-escape-core
  `(Handle ,return-op
     (returned -> returned)
     (Let (owner let (Owned Int)) 41
       (Perform ,return-op (Borrow owner)))))

(define captured-share-conflict-core
  `(Let (owner let (Owned Int)) 41
     (Let (result let ,borrowed)
       (Handle ,return-op
         (returned ->
           (Let (mutated let ,borrowed-mut)
                (BorrowMut owner)
             returned))
         (Scope ()
           (Perform ,return-op (Borrow owner))))
       (Read result))))

(define nested-mismatch-return-core
  `(Let (owner let (Owned Int)) 41
     (Let (other let (Owned Int)) 42
     (Let (result let ,borrowed)
        (Handle ,return-op
          (outer -> outer)
          (Handle (Return boundary (Borrowed Int 0))
            (inner -> inner)
            (Scope () (Perform ,return-op (Borrow owner)))))
        (Read result)))))

(define nested-mismatch-return-escape-core
  `(Handle ,return-op
     (returned -> returned)
     (Let (owner let (Owned Int)) 41
       (Handle (Return boundary (Borrowed Int 0))
         (inner -> inner)
         (Scope () (Perform ,return-op (Borrow owner)))))))

(define mismatched-return-after-move-core
  '(Let (owner let (Owned Int)) 41
     (Handle (Return boundary Int)
       (answer ->
         (Let (again let (Owned Int)) (Move owner)
          (Let (discarded let Unit) (Drop (Move again)) 0)))
       (Let (inner-result let Bool)
         (Handle (Return boundary Bool)
           (ignored -> (Construct Bool true))
           (Let (moved let (Owned Int)) (Move owner)
             (Let (discarded let Unit) (Drop (Move moved))
               (Perform (Return boundary Int) 0))))
         0))))

(define (check-diagnostic core expected-id)
  (define result (typed core))
  (check-true (diagnostic? result) (format "拒否を期待、実測: ~s" result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) expected-id)))

(test-case "Handle 内の Eliminate は両枝の借用 capability を結果へ渡す"
  (define core (branch-handle-core 'some))
  (trace-and-check core 'Int 41)
  (trace-and-check (branch-handle-core 'none) 'Int 42))

(test-case "Return の payload capability を handler binder に渡す"
  (trace-and-check return-capture-core 'Int 41))

(test-case "Handle は通常完了と捕捉 payload の欄表を合流する"
  (define capabilities
    (set (cons 'x '()) (cons 'y '())))
  (for ([selected (in-list '(some none))]
        [expected (in-list '(41 42))])
    (define core (mixed-handle-capability-core selected))
    (trace-and-check core 'Int expected)
    (define handle
      (match core
        [`(Let ,_ ,_ (Let ,_ ,_ (Let ,_ ,_ (Let ,_ ,_ (Let ,_ ,handle ,_)))))
         handle]
        [_ #f]))
    (check-not-false handle)
    (define Λ
      (region-ctx-add-token
       (region-ctx-add-token (empty-region-ctx) 'bx (set (cons 'x '())))
       'by (set (cons 'y '()))))
    (check-equal? (borrow-token-key Λ handle)
                  (set (cons 'x '())))
    (check-equal?
     (car (hash-ref (capability-field-table Λ handle)
                    (cons 'record-field 'item)))
     capabilities)))

(test-case "同じ Return を内側で捕捉した handler の Perform は外側へ届く"
  (trace-and-check nested-return-core 'Int 42))

(test-case "elaborate の Leave handler は capture した借用を読む"
  (match (elab (elaborated-return-source))
    [(list core _type _row callables)
     (define result (core-type-of/regions core '() callables))
     (check-true (region-typed? result) (format "elaborated Return: ~s" result))]
    [`(err ,diagnostic)
     (fail (format "elaboration rejected: ~a" (diagnostic-id diagnostic)))]))

(test-case "Leave の Option some payload capability を handler binder に渡す"
  (trace-and-check leave-capture-core 'Int 41))

(test-case "Handle の結果として owner Let から逃げる借用を拒否する"
  (check-diagnostic owner-body-return-escape-core "E-BOR-004"))

(test-case "捕捉した共有借用の生存中に同じ owner を可変借用できない"
  (check-diagnostic captured-share-conflict-core "E-BOR-003"))

(test-case "型の異なる内側 Handle を Skip し外側 binder へ借用を渡す"
  (trace-and-check nested-mismatch-return-core 'Int 41))

(test-case "内側 Handle を Skip して渡す借用も owner Let から出さない"
  (check-diagnostic nested-mismatch-return-escape-core "E-BOR-004"))

(test-case "型の異なる内側 Handle を越える affine escape の row は Own を含む"
  (define result (typed mismatched-return-after-move-core))
  (check-true (region-typed? result) (format "受理を期待、実測: ~s" result))
  (when (region-typed? result)
    (check-not-false (member 'Own (region-typed-row result)))
    (define configs
      (trace-g2 (inject-g2m (erase-core (region-execution-core result)))))
    (for ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config '() (region-typed-type result)))
      (check-not-false row (format "config ~a に runtime-row がある" index))
      (when row
        (check-true (config-ok? config '() (region-typed-type result) row)
                    (format "config ~a が config-ok? を通る" index))))
    (match (last configs)
      [`(cfg (Error ,_) ,_heap ,_states ,_tokens ,_events) (void)]
      [other (fail (format "OwnershipError の終端を期待、実測: ~s" other))])))

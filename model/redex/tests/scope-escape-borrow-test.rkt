#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define borrowed '(Borrowed Int (RParam %omitted)))
(define borrowed-option `(Option ,borrowed))

(define direct-escape
  `(Scope ()
     (Let (borrowed-value let ,borrowed)
          (Scope ()
            (Let (owner let (Owned Int)) 1 (Borrow owner)))
       0)))

(define returned-escape
  '(Scope ()
     (Let (owner let (Owned Int)) 1 (Borrow owner))))

(define option-escape
  `(Scope ()
     (Let (container let ,borrowed-option)
          (Scope ()
            (Let (owner let (Owned Int)) 1
              (Construct ,borrowed-option some (Borrow owner))))
       0)))

(define record-escape
  `(Scope ()
     (Let (container let (Record ((borrowed ,borrowed imm))))
          (Scope ()
            (Let (owner let (Owned Int)) 1
              (Rec ((borrowed imm (Borrow owner))))))
       0)))

(define function-escape
  `(Lam User scope-escape ()
     (Handle (Return boundary Int)
             (returned -> returned)
             (Scope ()
               (Let (borrowed-value let ,borrowed)
                    (Scope ()
                      (Let (owner let (Owned Int)) 1 (Borrow owner)))
                 0)))))

(define ucore-function-escape
  `(Fn ((parameter (Owned Int))) Int (Own)
     (LexicalScope
       (Let (borrowed-value let (Borrowed Int Omitted))
            (LexicalScope
              (Let (owner let (Owned Int)) (Move parameter)
                (Borrow owner)))
         0))))

(define return-escape
  `(Scope ()
     (Handle (Return boundary ,borrowed)
             (returned -> returned)
             (Scope ()
               (Let (owner let (Owned Int)) 1
                 (Perform (Return boundary ,borrowed) (Borrow owner)))))))

(define leave-escape
  `(Scope ()
     (Handle (Return boundary ,borrowed-option)
             (returned -> returned)
             (Scope ()
               (Let (owner let (Owned Int)) 1
                 (Perform (Return boundary ,borrowed-option)
                          (Construct ,borrowed-option some (Borrow owner))))))))

(define let-body-escape
  '(Let (owner let (Owned Int)) 1
     (Scope () (Borrow owner))))

(define let-body-option-escape
  `(Let (owner let (Owned Int)) 1
     (Scope ()
       (Construct ,borrowed-option some (Borrow owner)))))

(define let-body-return-escape
  `(Handle (Return boundary ,borrowed)
           (returned -> returned)
           (Let (owner let (Owned Int)) 1
             (Perform (Return boundary ,borrowed) (Borrow owner)))))

(define let-body-read
  `(Let (owner let (Owned Int)) 41
     (Let (borrowed-value let ,borrowed)
          (Borrow owner)
       (Read borrowed-value))))

(define let-body-scope-read
  `(Let (owner let (Owned Int)) 41
     (Let (borrowed-value let ,borrowed)
          (Scope () (Borrow owner))
       (Read borrowed-value))))

(define scoped-read
  '(Scope ()
     (Let (owner let (Owned Int)) 41
       (Let (borrowed-value let (Borrowed Int (RParam %omitted)))
            (Scope () (Borrow owner))
         (Read borrowed-value)))))

(define handled-return-control
  `(Let (owner let (Owned Int)) 41
     (Yield
      (Handle (Return boundary ,borrowed)
              (returned -> returned)
              (Scope ()
                (Perform (Return boundary ,borrowed) (Borrow owner))))
      0)))

(define handled-leave-control
  `(Let (owner let (Owned Int)) 41
     (Let (r let ,borrowed-option)
          (Handle (Return boundary ,borrowed-option)
                  (returned -> returned)
                  (Scope ()
                    (Perform (Return boundary ,borrowed-option)
                             (Construct ,borrowed-option some (Borrow owner)))))
       0)))

(define closure-return-under-unrelated-handler
  `(Handle (Return boundary Int)
           (returned -> returned)
           (Let (f let
                   (NFn () Never () ((Return boundary ,borrowed)) () User))
                (Lam User f ()
                  (Scope ()
                    (Let (owner let (Owned Int)) 1
                      (Perform (Return boundary ,borrowed)
                               (Borrow owner)))))
             0)))

(define (typed core [callables '()])
  (core-type-of/regions core '() callables))

(define (typed-elaborated source)
  (match (elab source)
    [(list core _type _row callables)
     (core-type-of/regions core '() callables)]
    [`(err ,diagnostic) diagnostic]
    [other (error 'typed-elaborated "unexpected elaboration result: ~s" other)]))

(define (check-escape core name)
  (define result (typed core))
  (check-true (diagnostic? result) (format "~a: ~s" name result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-004" name)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 200])
    (when (zero? fuel) (error 'trace-g2 "fuel exhausted: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next)) (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "expected deterministic reduction: ~s" steps)])))

(define (trace-and-check core expected)
  (define typed-result (typed core))
  (check-true (region-typed? typed-result)
              (format "accepted Core expected, got ~s" typed-result))
  (when (region-typed? typed-result)
    (define actual (region-typed-type typed-result))
    (check-equal? actual expected)
    (define configs
      (trace-g2
       (inject-g2m
        (erase-core (region-execution-core typed-result)))))
    (define rows
      (for/list ([config (in-list configs)])
        (runtime-row config '() actual)))
    (define first-live
      (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
    (check-not-false first-live "trace has a runtime row")
    (for ([config (in-list (drop configs first-live))]
          [row (in-list (drop rows first-live))]
          [index (in-naturals first-live)])
      (check-not-false row (format "config ~a has a runtime row" index))
      (check-true (config-ok? config '() actual row)
                  (format "config ~a passes config-ok?" index)))
    (check-true (redex-match? G2m v
                              (match (last configs)
                                [`(cfg ,value ,_ ...) value]))
                "trace ends in a value")))

(test-case "Scope の外へ let の値として出る借用を拒否する"
  (check-escape direct-escape "outer let"))

(test-case "最上位の結果として Scope から借用を返すのを拒否する"
  (check-escape returned-escape "top-level result"))

(test-case "元の owner-scope escape は終端 config に Dropped owner と BorrowRef を残す"
  ;; 静的拒否の根拠として、修正前に通っていた Core を型検査せず machine で走らせる。
  (define ir (build-region-ir returned-escape))
  (define configs
    (trace-g2 (inject-g2m (annotate-regions returned-escape ir))))
  (define final (last configs))
  (define final-value (second final))
  (check-true (redex-match? G2m v final-value) (format "terminal value: ~s" final-value))
  (match final-value
    [`(BorrowRef ,place ,_ ,ρ)
     (check-equal? (assoc place (list-ref final 3)) (list place 'Dropped))
     (check-false (runtime-row final '() `(Borrowed Int ,ρ)))
     (check-false (config-ok? final '() `(Borrowed Int ,ρ) '()))]
    [other (fail (format "expected dangling BorrowRef terminal config, got ~s" other))]))

(test-case "Option の payload として Scope から借用を出すのを拒否する"
  (check-escape option-escape "Option payload"))

(test-case "record 欄として Scope から借用を出すのを拒否する"
  (check-escape record-escape "record field"))

(test-case "関数本体の block から借用を外へ出すのを拒否する"
  (define result
    (typed function-escape
           `((scope-escape (NFn () Int () (Own) () User)))))
  (check-true (diagnostic? result) (format "typing result: ~s" result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-004")))

(test-case "elaborate 後も Scope から逃げる借用を拒否する"
  (define result (typed-elaborated ucore-function-escape))
  (check-true (diagnostic? result) (format "typing result: ~s" result))
  (when (diagnostic? result)
    (check-equal? (diagnostic-id result) "E-BOR-004")))

(test-case "捕捉される Return と Leave の payload は Scope を越えられない"
  (check-escape return-escape "Return payload")
  (check-escape leave-escape "Leave payload"))

(test-case "owner Let の body から借用を外へ出すのを拒否する"
  (check-escape let-body-escape "owner Let body result")
  (check-escape let-body-option-escape "owner Let Option payload")
  (check-escape let-body-return-escape "owner Let Return payload"))

(test-case "owner Let の body 内では借用を作って読める"
  (trace-and-check let-body-read 'Int)
  (trace-and-check let-body-scope-read 'Int))

(test-case "外側 owner の借用は block を出て読める"
  (trace-and-check scoped-read 'Int))

(test-case "外側 owner の借用は捕捉される Return の payload として残る"
  (trace-and-check handled-return-control 'Int))

(test-case "外側 owner の借用は捕捉される Leave の payload として残る"
  (trace-and-check handled-leave-control 'Int))

(test-case "外側 Handle は定義した関数の Return payload を捕捉しない"
  (define result
    (core-type-of/regions
     closure-return-under-unrelated-handler '()
     '((f (NFn () Never () ((Return boundary (Borrowed Int (RParam %omitted)))
                         ) () User)))))
  (check-true (region-typed? result)
              (format "function boundary isolation: ~s" result)))

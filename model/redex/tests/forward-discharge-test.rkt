#lang racket

(require rackunit
         racket/match
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define owned '(Owned Res))
(define wide-row `(Record ((x ,owned imm) (y Int imm))))
(define narrow-row '(Record ((y Int imm))))
(define rsd-proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,wide-row ,narrow-row)))
(define cap-proof '(ProofRep (Reserved o-type-narrative) TypeNarrativeCap))
(define sink-type `(NFn (,narrow-row) Int () () () User))

(define (make-owner body result-type [first-argument-type sink-type])
  (define owner-type
    `(NFn (,first-argument-type ,wide-row) ,result-type () () () User))
  (values
   `(Lam User owner (h p)
      (Handle (Return owner ,result-type) (answer -> answer)
        (Scope ()
          (Let (x let ,wide-row) p ,body))))
   `((owner ,owner-type) (sink ,sink-type))))

(define (diagnostic-code core callables)
  (diagnostic-id (core-type-of/diagnostic core '() callables)))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 120])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule following))
       (loop following (append configs (list following))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (configuration-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (check-config-trace configs callables expected-type)
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected-type))
    (check-not-false row
                     (format "config ~a の runtime row が無い: ~s"
                             index configuration))
    (check-true (config-ok? configuration callables expected-type row)
                (format "config ~a が不正: ~s" index configuration))))

(test-case "引数位置の RSD Discharge は Forward を含む T として型付けできる"
  (define-values (owner callables)
    (make-owner `(Apply h (Discharge ,rsd-proof (Forward x))) 'Int))
  (check-equal? (core-type-of owner '() callables)
                (list (second (assoc 'owner callables)) '())))

(test-case "結果位置の RSD Discharge は Forward を含む T として型付けできる"
  (define-values (owner callables)
    (make-owner `(Discharge ,rsd-proof (Forward x)) narrow-row))
  (check-equal? (core-type-of owner '() callables)
                (list (second (assoc 'owner callables)) '())))

(test-case "RSD Discharge の内側が T でない Apply なら拒否する"
  (define sink-function-type `(NFn (,narrow-row) Int () () () User))
  (define source-function-type `(NFn (,wide-row) ,wide-row () () () User))
  (define owner-type
    `(NFn (,sink-function-type ,source-function-type ,wide-row)
          Int () () () User))
  (define owner
    `(Lam User owner (sink source p)
       (Handle (Return owner Int) (answer -> answer)
         (Scope ()
           (Let (x let ,wide-row) p
             (Apply sink
                    (Discharge ,rsd-proof (Apply source (Forward x)))))))))
  (check-equal? (diagnostic-code owner `((owner ,owner-type))) "E-OWN-036"))

(test-case "RSD 以外の proposition の Discharge は T に入らない"
  (define sink-function-type `(NFn (,narrow-row) Int () () () User))
  (define cap-function-type
    `(NFn (,wide-row) ,narrow-row () () (TypeNarrativeCap) User))
  (define owner-type
    `(NFn (,sink-function-type ,cap-function-type ,wide-row)
          Int () () () User))
  (define owner
    `(Lam User owner (sink narrative p)
       (Handle (Return owner Int) (answer -> answer)
         (Scope ()
           (Let (x let ,wide-row) p
             (Apply sink
                    (Discharge ,cap-proof (Apply narrative (Forward x)))))))))
  (check-equal? (diagnostic-code owner `((owner ,owner-type))) "E-OWN-036"))

(test-case "span 付きの引数位置と結果位置でも RSD Discharge を判定できる"
  (define-values (argument-owner argument-callables)
    (make-owner `(Apply h (Discharge ,rsd-proof (Forward x))) 'Int))
  (define-values (result-owner result-callables)
    (make-owner `(Discharge ,rsd-proof (Forward x)) narrow-row))
  (check-equal? (core-type-of (annotate-core argument-owner) '()
                              argument-callables)
                (list (second (assoc 'owner argument-callables)) '()))
  (check-equal? (core-type-of (annotate-core result-owner) '()
                              result-callables)
                (list (second (assoc 'owner result-callables)) '())))

(test-case "RSD Discharge は token を Dropped にし全 config の検査を通る"
  (define sink
    `(Lam User sink (argument)
       (Handle (Return sink Int) (answer -> answer)
         (Scope () (Let (discard let ,narrow-row) argument 0)))))
  (define callables `((sink ,sink-type)))
  (define program `(Apply ,sink (Discharge ,rsd-proof (Forward 0))))
  (define source-value '(Rec ((x imm (OwnedLeaf (tok 0) (resource 41)))
                             (y imm 7))))
  (define start
    `(cfg (Scope (0) ,program)
          ((0 ,source-value (declared ,wide-row)))
          ((0 Available))
          (((tok 0) Available))
          ()))
  (define-values (configs rules) (trace-g2 start))
  (check-not-false (memq 'R-DischargeRemainder rules)
                   (format "RSD が実行されなかった: rules=~s final=~s"
                           rules (last configs)))
  (check-config-trace configs callables 'Int)
  (check-equal? (configuration-tokens (last configs)) '(((tok 0) Dropped))))

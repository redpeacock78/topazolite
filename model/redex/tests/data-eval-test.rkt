#lang racket

(require rackunit
         racket/match
         "../classify.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../typing.rkt")

(define (no-fail reason kind key) (error 'test "~s ~s ~s" reason kind key))

(define ledger
  (make-trait-ledger
   canonical-trait-env
   #:data
   '((Pair (A B) ((mkpair ((Param A) (Param B)))))
     (Nat () ((zero ()) (succ ((Data Nat ())))))
     (Chain () ((cnil ()) (ccons (Int (Owned (Data Chain ()))))))
     (Even (A) ((enil ()) (econs ((Param A) (Data Odd ((Param A)))))))
     (Odd (B) ((ocons ((Param B) (Data Even ((Param B)))))))
     (Lazy () ((ldone ())
               (lnext ((NFn (Unit) (Data Lazy ()) () () () User))))))
   #:fail no-fail))

(define-syntax-rule (with-data body ...)
  (call-with-trait-ledger ledger (lambda () body ...)))

(define (data-type source)
  (with-data
    (match (elab source)
      [(list core _ _ callables) (core-type-of core '() callables)]
      [`(err ,diagnostic) (diagnostic-id diagnostic)])))

(define (data-classify source)
  (with-data
    (match (elab source)
      [(list core _ _ callables) (classify (erase-core core) '() callables)]
      [`(err ,_) 'elaboration-error])))

(define (data-run source [fuel 400])
  (with-data
    (match (elab source)
      [(list core _ _ _)
       (match (run-g2 (inject-g2m (erase-core core)) fuel)
         [`(cfg ,result () () () ()) result]
         [other (error 'data-run "unexpected result: ~s" other)])]
      [`(err ,diagnostic) (error 'data-run "elaboration failed: ~s" diagnostic)])))

(define (data-repr-ok? type value)
  (with-data (repr-ok? type value)))

(test-case "Pair の constructor を分解して値を返す"
  (define source
    '(Apply
      (Fn ((ignored Unit)) Int ()
        (Eliminate (Construct mkpair (Types Int Bool) 1 (Construct true))
          ((mkpair (a b) -> a))))
      unit))
  (check-equal? (data-type source) '(Int ()))
  (check-equal? (data-run source) 1))

(test-case "Nat の再帰欄で構造的再帰する"
  (define source
    '(Recur count ((n (Data Nat ()))) Int ()
       (Eliminate n
         ((zero () -> 0)
          (succ (k) -> (Apply add 1 (Apply count k)))))
       (Apply count
         (Construct succ (Types)
           (Construct succ (Types) (Construct zero (Types)))))))
  (check-equal? (data-type source) '(Int ()))
  (check-equal? (data-run source) 2)
  (check-equal? (data-classify source) '(Finite structural)))

(test-case "Owned の data 欄を根とする再帰は構造的である"
  (define source
    '(Recur walk ((node (Owned (Data Chain ())))) Unit (Own)
       (Eliminate (Move node)
         ((cnil () -> unit)
          (ccons (head tail) -> (Apply walk (Move tail)))))
       unit))
  (check-equal? (data-type source) '(Unit ()))
  (check-equal? (data-classify source) '(Finite structural)))

(test-case "相互再帰 data の欄を交互に構成して分解する"
  (define source
    '(Let (value const (Data Even (Int)))
       (Construct econs (Types Int) 1
         (Construct ocons 2 (Construct enil)))
       (Apply
        (Fn ((ignored Unit)) Int ()
         (Eliminate value
           ((enil () -> 0)
            (econs (head odd)
              -> (Eliminate odd ((ocons (tail even) -> head)))))))
        unit)))
  (check-equal? (data-type source) '(Int ()))
  (check-equal? (data-run source) 1))

(test-case "NFn 欄の呼出し結果は構造的減少にならない"
  (define source
    '(Recur walk ((value (Data Lazy ()))) Unit (Partial)
       (Eliminate value
         ((ldone () -> unit)
          (lnext (make-next) -> (Apply walk (Apply make-next unit)))))
       unit))
  (check-equal? (data-type source) '(Unit ()))
  (check-equal? (data-classify source) 'Unknown)
  (check-not-equal? (data-classify source) '(Finite structural)))

(test-case "Owned data 欄も OwnLeaf の外では組み立てられない"
  (define chain-diagnostic
    (with-data
      (core-type-of/diagnostic
       '(Construct (Data Chain ()) ccons 1 (Move tail))
       '() '() '((tail (Owned (Data Chain ())))))))
  (define option-diagnostic
    (core-type-of/diagnostic
     '(Construct (Option (Owned Res)) some (Move tail))
     '() '() '((tail (Owned Res)))))
  (check-equal? (diagnostic-id chain-diagnostic)
                (diagnostic-code-of 'typing 'owned-constructor-field))
  (check-equal? (diagnostic-id chain-diagnostic)
                (diagnostic-id option-diagnostic)))

(test-case "repr-ok? は data schema の tag と各欄を検査する"
  (check-true
   (data-repr-ok? '(Data Nat ())
                  `(PTagged ,(tag-code 'succ)
                            (PTagged ,(tag-code 'zero)))))
  (check-false
   (data-repr-ok? '(Data Nat ())
                  `(PTagged ,(tag-code 'mkpair)))))

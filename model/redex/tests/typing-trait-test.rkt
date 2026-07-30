#lang racket/base

(require rackunit
         redex/reduction-semantics
         "../elaborate.rkt"
         "../typing.rkt")

(define empty '())

(test-case "normal unions are accepted and non-normal types are rejected"
  (check-true
   (core-check 1 empty empty '(Union Int String) empty))
  (check-false
   (core-check 1 empty empty '(Union String Int) empty))
  (check-false
   (core-check 1 empty empty '(Union Int Int) empty))
  (check-equal?
   (core-type-of
    'x
    empty
    empty
    '((x (Intersection (Record ((a Int imm)))
                       (Record ((b Int imm)))))))
   'ill-typed))

(test-case "G2 types may occur in effect rows"
  (define performed
    '(Perform (Return boundary (Untrusted Int)) (UVal 1)))
  (check-true
   (core-check performed
               empty
               empty
               'Never
               '((Return boundary (Untrusted Int))))))

(test-case "typing entry points reject hidden non-normal annotations"
  (define hidden
    '(Let (x (Union String Int)) 1 1))
  (check-equal? (core-type-of hidden empty empty) 'ill-typed)
  (check-false (core-check-row hidden empty empty 'Int))
  (check-false (core-check hidden empty empty 'Int empty))
  (check-false
   (config-ok? `(cfg ,hidden () () ()) empty 'Int empty)))

(test-case "effect rows and their Core annotations must be normal"
  (define performed
    '(Perform (Return boundary (Union String Int)) 1))
  (check-false
   (core-check performed
               empty
               empty
               'Never
               '((Return boundary (Union String Int))))))

(test-case "synthesized record types cross boundaries in normal form"
  (define record
    '(Rec ((z imm 1) (a imm 0))))
  (define record-type
    '(Record ((a Int imm) (z Int imm))))
  (check-equal? (core-type-of record empty empty)
                `(,record-type ()))
  (check-equal? (cadr (elab record)) record-type)
  ;; G1 由来の Let は bound の合成型を Core 注釈へ埋め込む。
  (check-equal?
   (car (elab `(Let x ,record 1)))
   `(Let (x ,record-type) ,record 1))
  ;; 明示注釈も resolve-annotation の出口で正規化する。
  (check-equal?
   (car (elab `(Let (x let (Record ((z Int imm) (a Int imm))))
                 ,record
                 1)))
   `(Let (x let ,record-type) ,record 1))
  (let-values ([(merged _witnesses)
                (merge-record-types
                 (list '(Record ((z Int imm) (a Int imm)))))])
    (check-equal? merged record-type)))

(test-case "UCore carries public trait propositions"
  (check-true
   (redex-match? UCore uφ '(ValidNarrativeTrait Printable)))
  (check-true
   (redex-match? UCore uφ '(Implements Int Printable)))
  (check-true
   (redex-match? UCore uφ '(RequiresBoth Printable Sizable)))
  ;; merge の局所命題は表層注釈へ出さない。
  (check-false
   (redex-match? UCore uφ '(FieldType f Int)))
  (check-false
   (redex-match? UCore uφ '(Presence f))))

(test-case "UCore carries composite types"
  (check-true
   (redex-match? UCore uτ '(Union Int String)))
  (check-true
   (redex-match?
    UCore
    uτ
    '(Intersection (Record ((a Int imm)))
                   (Record ((b Int imm)))))))

(test-case "elaboration normalizes composite annotations"
  (check-equal?
   (elab '(Let (x let (Union String Int)) 1 x))
   (elab '(Let (x let (Union Int String)) 1 x)))
  (define record-type
    '(Record ((a Int imm) (b Int imm))))
  (check-equal?
   (elab
    '(Let (x let
             (Intersection (Record ((a Int imm)))
                           (Record ((b Int imm)))))
       (Rec ((a imm 1) (b imm 2)))
       x))
   `((Let (x let ,record-type)
           (Rec ((a imm 1) (b imm 2)))
           x)
     ,record-type
     ()
     ()))
  (check-equal?
   (elab '(Let (x let (Intersection Int String)) 1 x))
   '(err (invalid-resolved-type (Intersection Int String)))))

(test-case "elaboration normalizes trait propositions in every type position"
  (define source
    '(Fn ((proof (Proof (RequiresBoth Sizable Printable)))
          (refined
           (Refined Int
                    (Implements (Union String Int) Printable)))
          (function
           (NFn () Unit ()
                ((ValidNarrativeTrait Printable)
                 (Implements (Union String Int) Printable)
                 (RequiresBoth Sizable Printable)))))
       Unit
       ()
       unit))
  (check-equal?
   (cadr (elab source))
   '(NFn
     ((Proof (RequiresBoth Printable Sizable))
      (Refined Int
               (Implements (Union Int String) Printable))
      (NFn () Unit ()
           ((ValidNarrativeTrait Printable)
            (Implements (Union Int String) Printable)
            (RequiresBoth Printable Sizable))))
     Unit
     ()
     ())))

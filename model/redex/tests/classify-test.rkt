#lang racket

(require rackunit
         "../classify.rkt")

(define structural-callables
  '((list-loop-id (NFn ((List Int)) Int () ()))))

(define structural-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> (Apply loop tail))))
          (Apply loop (Construct nil))))

(test-case "REC-001: no recursion and structural descent are Finite"
  (check-equal? (classify '(Apply (PrimVal (Reserved o-add) add) 1 2)
                          '() '())
                '(Finite no-recursion))
  (check-equal? (classify structural-loop '() structural-callables)
                '(Finite structural))

  ;; The non-recursive mapper comes from the outer elaboration Γ.
  (define map-environment
    '((mapper (NFn (Int) Int () ()))))
  (define map-callables
    '((map-loop-id (NFn ((List Int)) (List Int) () ()))))
  (define map-loop
    '(Recur map-loop-id go (values)
            (Eliminate values
             ((nil () -> (Construct nil))
              (cons (head tail) ->
                    (Construct cons
                               (Apply mapper head)
                               (Apply go tail)))))
            (Apply go (Construct nil))))
  (check-equal? (classify map-loop map-environment map-callables)
                '(Finite structural)))

(test-case "REC-001: structural calls require one common decreasing position"
  (define callables
    '((pair-loop-id
       (NFn ((List Int) (List Int) Bool) Int () ()))))
  (define no-common-position
    '(Recur pair-loop-id loop (xs ys choose-left)
            (Eliminate choose-left
             ((true () ->
                    (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Apply loop tail ys choose-left)))))
              (false () ->
                     (Eliminate ys
                      ((nil () -> 0)
                       (cons (head tail) ->
                             (Apply loop xs tail choose-left)))))))
            (Apply loop (Construct nil) (Construct nil)
                   (Construct true))))
  (check-equal? (classify no-common-position '() callables) 'Unknown))

(test-case "REC-001: structural descent follows fields, not arbitrary uses of f"
  (define callables
    '((nested-loop-id (NFn ((List Int)) Int () ()))))
  (define nested-descent
    '(Recur nested-loop-id loop (values)
            (Eliminate values
             ((nil () -> 0)
              (cons (head tail) ->
                    (Eliminate tail
                     ((nil () -> 0)
                      (cons (next rest) -> (Apply loop rest)))))))
            (Apply loop (Construct nil))))
  (check-equal? (classify nested-descent '() callables)
                '(Finite structural))

  (define non-call-use
    '(Recur curry-loop-id loop (left right)
            (Let (saved (NFn (Int) Int () ()))
                 (Curry loop left)
                 0)
            (Apply loop 0 0)))
  (check-equal?
   (classify non-call-use '()
             '((curry-loop-id (NFn (Int Int) Int () ()))))
   'Unknown))

(define guarded-callables
  '((nats-id (NFn (Int) Unit ((Yield Int)) ()))))

(define guarded-loop
  '(Recur nats-id nats (n)
          (Yield n
                 (Apply nats
                        (Apply (PrimVal (Reserved o-add) add) n 1)))
          (Apply nats 0)))

(test-case "REC-002: Yield followed by a tail call is Productive"
  (check-equal? (classify guarded-loop '() guarded-callables)
                '(Productive guarded)))

(test-case "REC-002: f-free and Suspend bodies are not guards"
  (define callables '((loop-id (NFn () Unit (Partial) ()))))
  (check-equal?
   (classify '(Recur loop-id loop () unit (Apply loop)) '() callables)
   'Unknown)
  (check-equal?
   (classify
    '(Recur loop-id loop () (Suspend (Apply loop)) (Apply loop))
    '() callables)
   'Unknown))

(test-case "REC-002: a guarded body still requires the initial tail call"
  (define callables
    '((loop-id (NFn () Unit ((Yield Int)) ()))))
  (check-equal?
   (classify
    '(Recur loop-id loop ()
            (Yield 1 (Apply loop))
            unit)
    '() callables)
   'Unknown))

(define (guard-component-loop callable callee-labels)
  (define callables
    `((,callable (NFn () Unit (,@callee-labels (Yield Int)) ()))
      (callee-id (NFn () Int ,callee-labels ()))))
  (define environment
    `((callee (NFn () Int ,callee-labels ()))))
  (values
   `(Recur ,callable loop ()
           (Yield (Apply callee) (Apply loop))
           (Apply loop))
   environment
   callables))

(test-case "REC-002: guard components reject Own and Return, not Compile"
  (define-values (own-loop own-environment own-callables)
    (guard-component-loop 'own-loop-id '(Own)))
  (check-equal?
   (classify own-loop own-environment own-callables)
   'Unknown)

  (define-values (return-loop return-environment return-callables)
    (guard-component-loop
     'return-loop-id '((Return outer-boundary Int))))
  (check-equal?
   (classify return-loop return-environment return-callables)
   'Unknown)

  (define-values (compile-loop compile-environment compile-callables)
    (guard-component-loop 'compile-loop-id '(Compile)))
  (check-equal?
   (classify compile-loop compile-environment compile-callables)
   '(Productive guarded)))

(test-case "REC-001/REC-002: pre rejects nested Partial and Yield rows"
  (for ([labels (in-list '((Partial) ((Yield Int))))]
        [callable (in-list '(partial-outer-id yield-outer-id))])
    (define-values (core environment callables)
      (guard-component-loop callable labels))
    (check-equal? (classify core environment callables) 'Unknown))

  (for ([inner-row (in-list '((Partial) ((Yield Int))))]
        [outer-id (in-list '(nested-partial-id nested-yield-id))]
        [inner-id (in-list '(inner-partial-id inner-yield-id))])
    (define inner-body
      (if (member 'Partial inner-row)
          1
          `(Yield 1 (Apply inner))))
    (define outer-row
      (if (member 'Partial inner-row)
          '(Partial (Yield Int))
          '((Yield Int))))
    (define core
      `(Recur ,outer-id outer ()
              (Yield
               (Recur ,inner-id inner ()
                      ,inner-body
                      (Apply inner))
               (Apply outer))
              (Apply outer)))
    (define callables
      `((,outer-id (NFn () Unit ,outer-row ()))
        (,inner-id (NFn () Int ,inner-row ()))))
    (check-equal? (classify core '() callables) 'Unknown)))

(test-case "PRF-002/PRF-003: type equality is structural and opaque"
  (check-true
   (type-equiv?
    '(NFn ((List Int)) (Proof TypeNarrativeCap)
          (Own (Yield Int)) ())
    '(NFn ((List Int)) (Proof TypeNarrativeCap)
          ((Yield Int) Own) ())))
  (check-false
   (type-equiv? '(Proof TypeNarrativeCap)
                '(Proof ValidNarrativeTrait)))

  ;; This zero-argument Recur is conservatively Unknown but reduces to unit.
  ;; Opaque comparison must not normalize it to the second type expression.
  (define unknown-calculation
    '(Recur opaque-id compute () unit unit))
  (check-equal? (classify unknown-calculation '()
                          '((opaque-id (NFn () Unit () ()))))
                'Unknown)
  (check-true
   (type-equiv? `(Opaque ,unknown-calculation)
                `(Opaque ,unknown-calculation)))
  (check-false
   (type-equiv? `(Opaque ,unknown-calculation)
                '(Opaque unit))))

#lang racket

(require racket/match
         redex/reduction-semantics
         rackunit
         "../elaborate.rkt"
         "../erase.rkt"
         "../lang.rkt"
         "../typing.rkt")

(define (success result)
  (match result
    [(list core type row callables)
     (define erased (erase-core core))
     (check-true
      (redex-match? G1 c erased)
      (format "elaboration produced malformed Typed Core: ~s" core))
     (list erased type row callables)]
    [_ (fail-check (format "expected elaboration success, got ~s" result))]))

(define (elaboration-error? result)
  (match result
    [`(err ,_) #t]
    [_ #f]))

(define (tree-contains? tree wanted)
  (or (equal? tree wanted)
      (and (list? tree)
           (ormap (lambda (part) (tree-contains? part wanted)) tree))))

(define (collect-callable-ids tree tag)
  (define here
    (match tree
      [`(Lam ,_ ,callable ,_ ,_) #:when (eq? tag 'Lam) (list callable)]
      [`(Recur ,callable ,_ ,_ ,_ ,_) #:when (eq? tag 'Recur)
       (list callable)]
      [_ '()]))
  (append here
          (if (list? tree)
              (append-map (lambda (part)
                            (collect-callable-ids part tag))
                          tree)
              '())))

(test-case "RET-001/RET-002/RET-003: return resolves to the nearest boundary"
  (match-define (list function-core _ _ _)
    (success
     (elab
      '(Fn ((flag Bool)) Int ()
           (Eliminate flag
                      ((true () -> (Return 1))
                       (false () -> 0)))))))
  (check-true
   (tree-contains? function-core
                   '(Perform (Return boundary0 Int) 1)))

  (match-define (list narrative-core _ _ _)
    (success
     (elab '(Fn () Int () (NarrativeExpr (Return 2))))))
  (check-true
   (tree-contains? narrative-core
                   '(Perform (Return boundary1 Int) 2)))
  (check-false
   (tree-contains? narrative-core
                   '(Perform (Return boundary0 Int) 2)))

  (match-define (list recur-core _ _ callables)
    (success
     (elab
      '(Fn () Int ()
           (Recur f () Int (Return Partial)
                  (Return 3)
                  0)))))
  (check-true
   (tree-contains? recur-core
                   '(Perform (Return boundary0 Int) 3)))
  (check-equal?
   (second (assoc 'callable1 callables))
   '(NFn () Int ((Return boundary0 Int) Partial) ())))

(test-case "EFF-001: declared rows bound fn and recur bodies"
  (check-true
   (elaboration-error?
    (elab '(Fn () Unit () (Yield 1 unit)))))
  (check-true
   (elaboration-error?
    (elab '(Recur f () Int () 1 1))))
  (match-define (list _ type _ _)
    (success
     (elab '(Fn () Unit ((Yield Int)) (Yield 1 unit)))))
  (check-equal? type '(NFn () Unit ((Yield Int)) ())))

(test-case "REC-001/REC-002: recur uses the real classifier"
  (check-false
   (elaboration-error?
    (elab
     '(Recur loop ((xs (List Int))) Int ()
             (Eliminate xs
              ((nil () -> 0)
               (cons (head tail) -> (Apply loop tail))))
             (Apply loop (Construct nil (Types Int)))))))
  (check-false
   (elaboration-error?
    (elab
     '(Recur nats ((n Int)) Unit ((Yield Int))
             (Yield n (Apply nats (Apply add n 1)))
             (Apply nats 0)))))
  (check-false
   (elaboration-error?
    (elab
     '(Recur loop ((xs (List Int))) Unit ((Yield Int))
             (Yield 1
                    (Apply loop (Construct nil (Types Int))))
             (Apply loop (Construct nil (Types Int)))))))
  (check-false
   (elaboration-error?
    (elab
     '(Recur loop ((xs (List Int))) Unit ((Yield (List Int)))
             (Yield (Construct nil (Types Int))
                    (Apply loop (Construct nil (Types Int))))
             (Apply loop (Construct nil (Types Int))))))))

(test-case "OWN-001/OWN-002: function boundaries carry Owned formals"
  (check-false
   (elaboration-error?
    (elab '(Fn ((item (Owned Res))) Unit () unit))))
  (check-true
   (elaboration-error?
    (elab '(Recur f ((item (Owned Res))) Unit (Partial) unit unit))))
  (check-true
   (elaboration-error?
    (elab
     '(Let item (Apply acquire 1)
           (Fn () (Owned Res) (Own) (Move item))))))
  (check-true
   (elaboration-error?
    (elab
     '(Let item (Apply acquire 1)
           (Recur f () Unit (Partial Own) (Drop item) unit)))))
  ;; Only the visible binding matters: the inner Int shadows the outer Owned.
  (check-false
   (elaboration-error?
    (elab
     '(Let item (Apply acquire 1)
        (Let item 0
          (Fn () Int () item)))))))

(test-case "OWN-001/OWN-002: move and drop preserve the Own marker"
  (match-define (list move-core move-type move-row move-callables)
    (success
     (elab '(Let item (Apply acquire 7) (Move item)))))
  (check-equal? move-type '(Owned Res))
  (check-equal? move-row '(Own))
  (check-true (tree-contains? move-core '(Move item)))
  (check-equal?
   (core-type-of move-core '() move-callables)
   (list move-type move-row))

  (match-define (list drop-core drop-type drop-row _)
    (success
     (elab '(Let item (Apply acquire 7) (Drop item)))))
  (check-equal? drop-type 'Unit)
  (check-equal? drop-row '(Own))
  (check-true (tree-contains? drop-core '(Drop (Move item)))))

(test-case "TYP-001/TYP-002: typeMake interprets saturated specs"
  (match-define (list raw-type-core type type-row callables)
    (elab '(TypeMake (Spec List Int))))
  (define type-core (erase-core raw-type-core))
  (check-equal?
   type-core
   '(TypeRep (Derived (Reserved o-type-narrative)
                      (Make (List Int)))
             (List Int)
             Type))
  (check-equal? type '(TypeInfo Type))
  (check-equal? type-row '(Compile))

  (match-define (list alias-core alias-type alias-row _)
    (success
     (elab
      '(LetType Box (TypeMake List)
         (TypeMake (Spec Box Int))))))
  (check-equal? alias-core type-core)
  (check-equal? alias-type type)
  (check-equal? alias-row '(Compile))
  (check-true
   (elaboration-error?
    (elab '(TypeMake (Spec List Int Unit))))))

(test-case "E-Prim: primitive resolution respects local shadowing"
  (match-define (list raw-core direct-type direct-row direct-callables)
    (elab 'add))
  (check-equal?
   (list (erase-core raw-core) direct-type direct-row direct-callables)
   '((PrimVal (Reserved o-add) add)
     (NFn (Int Int) Int () ())
     ()
     ()))
  (match-define (list core type row _)
    (success (elab '(Let add 1 add))))
  (check-equal? core '(Let (add Int) 1 add))
  (check-equal? type 'Int)
  (check-equal? row '()))

(test-case "E-Apply: proof obligations come from Π0"
  (check-false
   (elaboration-error?
    (elab
     '(Fn ((f (NFn () Int () (TypeNarrativeCap))))
          Int ()
          (Apply f)))))
  (check-true
   (elaboration-error?
    (elab
     '(Fn ((f (NFn () Int () (ValidNarrativeTrait))))
          Int ()
          (Apply f))))))

(test-case "CUR-001/CUR-002: curry preserves the latent signature"
  (match-define (list raw-core type row callables) (elab '(Curry add 1)))
  (check-equal?
   (list (erase-core raw-core) type row callables)
   '((Curry (PrimVal (Reserved o-add) add) 1)
     (NFn (Int) Int () ())
     ()
     ()))
  (check-true
   (elaboration-error?
    (elab
     '(Fn ((f (NFn ((Owned Res)) Unit () ())))
          (NFn () Unit () ()) ()
          (Curry f (Apply acquire 1)))))))

(test-case "E-Construct/E-Eliminate: expected and explicit type arguments"
  (match-define (list raw-core direct-type direct-row direct-callables)
    (elab '(Construct nil (Types Int))))
  (check-equal?
   (list (erase-core raw-core) direct-type direct-row direct-callables)
   '((Construct (List Int) nil) (List Int) () ()))
  (check-true (elaboration-error? (elab '(Construct nil))))
  (match-define (list core type row callables)
    (success
     (elab '(Fn () (List Int) () (Construct nil)))))
  (check-equal? type '(NFn () (List Int) () ()))
  (check-equal? row '())
  (check-equal?
   (core-type-of core '() callables)
   (list type row)))

(test-case "GUN: sibling recurs with the same surface name get distinct IDs"
  (match-define (list core _ _ callables)
    (success
     (elab
      '(Apply
        (Fn ((left Int) (right Bool)) Int () left)
        (Recur f () Int (Partial) 1 1)
        (Recur f () Bool (Partial)
               (Construct true)
               (Construct true (Types)))))))
  (define recur-ids (collect-callable-ids core 'Recur))
  (check-equal? (length recur-ids) 2)
  (check-false (check-duplicates recur-ids))
  (for ([callable (in-list recur-ids)])
    (check-not-false (assoc callable callables))))

(test-case "GUN: zero-argument lambdas get distinct IDs"
  (match-define (list core _ _ callables)
    (success
     (elab
      '(Apply
        (Fn ((left (NFn () Int () ()))
             (right (NFn () Int () ())))
            Int ()
            0)
        (Fn () Int () 1)
        (Fn () Int () 2)))))
  (define lambda-ids (collect-callable-ids core 'Lam))
  (check-equal? (length lambda-ids) 3)
  (check-false (check-duplicates lambda-ids))
  (check-equal? (length callables) 3))

(test-case "elaboration agrees with Typed Core checking on representative terms"
  (for ([source (in-list
                 '(42
                   add
                   (Apply add 1 2)
                   (Fn ((x Int)) Int () x)
                   (Apply
                    (Fn ((g (NFn () Unit (Suspend Own) ())))
                        Unit () unit)
                    (Fn () Unit (Own Suspend) unit))
                   (Yield 1 (Suspend unit))))])
    (match-define (list core type row callables)
      (success (elab source)))
    (check-equal?
     (core-type-of core '() callables)
     (list type row)
     (format "agreement for ~s" source))))

#lang racket

(require rackunit
         racket/match
         "../borrow-gen.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../typing.rkt")

(define (config-core configuration)
  (match configuration
    [`(cfg ,core ,_ ...) core]))

(define (contains-core-head? core head)
  (match core
    [(? list? terms)
     (or (and (pair? terms) (eq? (first terms) head))
         (ormap (lambda (term) (contains-core-head? term head)) terms))]
    [_ #f]))

(define (check-runs-to core expected-value #:callables [callables '()])
  (match (prepare-borrow-term* core #:callables callables)
    [(list 'ok start _sidecar _ir expected-type)
     (let loop ([configuration start] [fuel 200])
       (define row (runtime-row configuration callables expected-type))
       (check-not-false row
                        (format "runtime-row が無い config: ~s" configuration))
       (check-true (config-ok? configuration callables expected-type row)
                   (format "不正な config: ~s" configuration))
       (define next (raw-steps-g2 configuration))
       (cond
         [(null? next)
          (check-equal? (config-core configuration) expected-value)]
         [(zero? fuel) (fail (format "fuel を使い切った: ~s" configuration))]
         [(= (length next) 1)
          (loop (first next) (sub1 fuel))]
         [else (fail (format "一意な次状態でない: ~s" next))]))]
    [other (fail (format "型付けされない fixture ~s: ~s" core other))]))

(define (check-first-step-core core expected-core #:callables [callables '()])
  (match (prepare-borrow-term* core #:callables callables)
    [(list 'ok start _sidecar _ir _type)
     (match (raw-steps-g2 start)
       [(list next) (check-equal? (config-core next) expected-core)]
       [other (fail (format "一意な最初の遷移を期待した: ~s" other))])]
    [other (fail (format "型付けされない fixture ~s: ~s" core other))]))

(define capture-data-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((Box () ((box (Int)))))
   #:fail (lambda (reason kind key)
            (error 'binding-name-capture-test "~s ~s ~s" reason kind key))))

(define (with-capture-data thunk)
  (call-with-trait-ledger capture-data-ledger thunk))

(test-case "Let binder と同名の field label を保って最後まで評価する"
  (check-runs-to
   '(Let (other const Int) 1
      (Proj (Rec ((other imm 2))) other))
   2)
  ;; Matching も label を binder と同じ変数位置として改名しない。
  (define start
    '(cfg (Scope () (Let (other const Int) 1
                     (Proj (Rec ((other imm 2))) other))) () () () ()))
  (match (raw-steps-g2 start)
    [(list next)
     (check-equal? (config-core next)
                   '(Scope () (Proj (Rec ((other imm 2))) other)))]
    [other (fail (format "R-LetB の一歩を期待した: ~s" other))]))

(test-case "ProjOpt と型 row の label を保つ"
  (check-runs-to
   '(Let (field const Int) 0
      (Let (record const (Record ((field Int imm))))
           (Rec ((field imm 2)))
        (ProjOpt Int record field)))
   '(Construct (Option Int) some 2)))

(test-case "RecRewrite の label を保つ"
  (check-runs-to
   '(Let (field const Int) 0
      (RecRewrite (Rec ((field imm 2)))
                  ((field input Int imm Int input))))
   '(Rec ((field imm 2)))))

(test-case "primitive 名、Return 境界名、命題 id を置換しない"
  (check-runs-to
   '(Let (add const Int) 0
      (Apply (PrimVal (Reserved o-add) add) 1 2))
   3)
  (check-runs-to
   '(Let (b const Int) 0
      (Handle (Return b Int)
              (answer -> answer)
              (Perform (Return b Int) 7)))
   7)
  (check-runs-to
   '(Let (p const Int) 0
      (RVal (ProofRep User (Prop p)) 7))
   '(RVal (ProofRep User (Prop p)) 7))
  (check-first-step-core
   '(Let (p const Int) 0
      (RVal (ProofRep User (Prop p)) 7))
   '(Scope () (RVal (ProofRep User (Prop p)) 7))))

(test-case "Let binder と Lam cid の同名衝突を一歩と終端で防ぐ"
  (define callables '((f (NFn (Int) Int () () () User))))
  (define core '(Let (f const Int) 0 (Apply (Lam User f (x) x) 5)))
  (check-first-step-core
   core '(Scope () (Apply (Lam User f (x) x) 5)) #:callables callables)
  (check-runs-to core 5 #:callables callables))

(test-case "Let binder と Recur cid の同名衝突を一歩と終端で防ぐ"
  (define callables '((cid (NFn (Int) Int () () () User))))
  (define core '(Let (cid const Int) 0 (Recur cid f (n) n (Apply f 5))))
  (check-first-step-core
   core '(Scope () (Recur cid f (n) n (Apply f 5))) #:callables callables)
  (check-runs-to core 5 #:callables callables))

(test-case "data 名と構成子名を置換しない"
  (with-capture-data
   (lambda ()
     (check-runs-to
      '(Let (Box const Int) 0
         (Construct (Data Box ()) box 1))
      '(Construct (Data Box ()) box 1))
     (check-runs-to
      '(Let (box const Int) 0
         (Eliminate (Construct (Data Box ()) box 1)
                    ((box (item) -> item))))
      1)
     (define branch-capture
       '(Let (field const Int) 0
          (Eliminate (Construct (Data Box ()) box 1)
                     ((box (field) ->
                            (Proj (Rec ((field imm field))) field))))))
     (match (prepare-borrow-term* branch-capture)
       [(list 'ok start _sidecar _ir _type)
        (check-true (contains-core-head? (config-core start) 'EliminateAt))]
       [other (fail (format "分解 branch fixture の型付け: ~s" other))])
     (check-runs-to branch-capture 1))))

(test-case "R-Let、owned/mut Let、Lam、Recur、Handle の label を保つ"
  (check-runs-to
   '(Let (field Int) 0
      (Proj (Rec ((field imm 2))) field))
   2)
  (check-runs-to
   '(Let (field mut Int) 1
      (Proj (Rec ((field imm 2))) field))
   2)
  (check-runs-to
   '(Let (field let (Owned Res))
        (Apply (PrimVal (Reserved o-acquire) acquire) 9)
      (Let (result const Int)
           (Proj (Rec ((field imm 2))) field)
        (Drop (Move field))))
   'unit)
  (check-runs-to
   '(Apply (Lam User lam-id (field)
             (Proj (Rec ((field imm 2))) field))
           0)
   2
   #:callables '((lam-id (NFn (Int) Int () () () User))))
  (check-runs-to
   '(Recur recur-id loop (n)
      (Proj (Rec ((loop imm n))) loop)
      (Apply loop 2))
   2
   #:callables '((recur-id (NFn (Int) Int () () () User))))
  (check-runs-to
   '(Let (answer const Int) 0
      (Handle (Return boundary Int)
              (answer -> (Proj (Rec ((answer imm answer))) answer))
              (Perform (Return boundary Int) 7)))
   7))

(test-case "開いた Lam の自由変数は Let の束縛子に捕獲されない"
  (define start
    (inject-g2 '(Let (f (NFn () Int () () () User))
                     (Lam User f () z)
                 (Let (z Int) 1 (Apply f)))))
  (match (raw-steps-g2 start)
    [(list next)
     (match (config-core next)
       [`(Scope () (Let (,renamed Int) 1 (Apply (Lam User f () z))))
        (check-not-equal? renamed 'z)]
       [other (fail (format "開いた z を保った Let を期待した: ~s" other))])]
    [other (fail (format "開いた値の置換を期待した: ~s" other))]))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../borrow.rkt"
         "../typing.rkt")

(define empty '())
(define callable-types
  (term ((identity-id (NFn (Int) Int () ()))
         (binary-id (NFn (Int Int) Int () ()))
         (yield-id (NFn () Unit ((Yield Int)) ()))
         (loop-id (NFn (Int) Int () ()))
         (owned-parameter-id (NFn ((Owned Res)) Unit () ()))
         (capture-id (NFn () (Owned Res) (Own) ())))))

;; 既存の callable-types とは分け、CurryVal の heap entry が持つ
;; closure の署名だけをこの configuration 用に宣言する。
(define curry-callables
  (term ((leaf-drop-id (NFn ((Owned Res)) Unit (Own) ())))))

;; G5c5b1 の Owned formal encoding に従う closure。Lam の formal は生名で
;; 受け、Handle と Scope の内側の Let で Owned place へ開いてから Move する。
(define leaf-drop-lam
  (term (Lam User leaf-drop-id (owned0)
             (Handle (Return boundary Unit)
                     (return-value -> return-value)
                     (Scope ()
                            (Let (q let (Owned Res)) owned0
                                 (Drop (Move q))))))))

(test-case "T-Prim/T-MovePlace: synthesis uses Γ0 and Ξ"
  (check-equal?
   (core-type-of (term (PrimVal (Reserved o-lt) lt)) empty empty)
   (term ((NFn (Int Int) Bool () ()) ())))
  (check-equal?
   (core-type-of (term (Move 0)) (term ((0 Res))) empty)
   (term ((Owned Res) (Own))))
  (check-equal? (core-type-of (term x) empty empty) 'ill-typed)
  (check-equal?
   (core-type-of (term (PrimVal User lt)) empty empty)
   'ill-typed))

(test-case "EFF-001: T-Lam synthesizes from Φ and checks its body"
  (check-equal?
   (core-type-of
    (term (Lam User identity-id (x) x))
    empty callable-types)
   (term ((NFn (Int) Int () ()) ())))
  (check-equal?
   (core-type-of
    (term (Lam User yield-id () (Yield 1 unit)))
    empty callable-types)
   (term ((NFn () Unit ((Yield Int)) ()) ())))
  (check-equal?
   (core-type-of
    (term (Lam User identity-id (x) unit))
    empty callable-types)
   'ill-typed)
  (check-equal?
   (core-type-of (term (Lam User missing-id (x) x)) empty callable-types)
   'ill-typed)
  (check-equal?
   (core-type-of
    (term (Lam User owned-parameter-id (item) unit))
    empty callable-types)
   'ill-typed)
  (check-equal?
   (core-type-of
    (term (Let (owned-item (Owned Res))
               (resource 1)
               (Lam User capture-id () (Move owned-item))))
    empty callable-types)
   'ill-typed))

(test-case "CUR-001/CUR-002: callable values synthesize through curry"
  (define binary
    (term (Lam User binary-id (x y) x)))
  (define expected
    (term ((NFn (Int) Int () ()) ())))
  (check-equal?
   (core-type-of (term (Apply ,binary 1 2)) empty callable-types)
   (term (Int ())))
  (check-equal?
   (core-type-of (term (Curry ,binary 1)) empty callable-types)
   expected)
  (check-equal?
   (core-type-of (term (CurryVal User ,binary 1)) empty callable-types)
   expected)
  ;; Reduction may duplicate a callable value; GUN gates elaboration only.
  (check-equal?
   (core-type-of
    (term (Let (first Int)
               (Apply (Lam User identity-id (x) x) 1)
               (Apply (Lam User identity-id (x) x) 2)))
    empty callable-types)
   (term (Int ()))))

(test-case "REC-001: T-Recur and T-RecurVal use Φ(r)"
  (check-equal?
   (core-type-of
    (term (Recur loop-id loop (x) x (Apply loop 1)))
    empty callable-types)
   (term (Int ())))
  (check-equal?
   (core-type-of
    (term (RecurVal loop-id loop (x) x))
    empty callable-types)
   (term ((NFn (Int) Int () ()) ())))
  (check-equal?
   (core-type-of
    (term (Recur loop-id loop (x) unit (Apply loop 1)))
    empty callable-types)
   'ill-typed))

(test-case "T-Construct/T-Eliminate: retained data types synthesize"
  (check-equal?
   (core-type-of (term (Construct (List Int) nil)) empty empty)
   (term ((List Int) ())))
  (check-true
   (core-check (term (Construct (List Int) nil))
               empty empty (term (List Int)) empty))
  (check-equal?
   (core-check-row (term (Construct (List Int) nil))
                   empty empty (term (List Int)))
   empty)
  (check-true
   (core-check (term (Construct (List Int) cons 1
                                (Construct (List Int) nil)))
               empty empty (term (List Int)) empty))
  (check-false
   (core-check (term (Construct (List Int) cons unit
                                (Construct (List Int) nil)))
               empty empty (term (List Int)) empty))
  (check-false
   (core-check (term (Construct (List Int) nil))
               empty empty (term (Option Int)) empty))
  (check-equal?
   (core-type-of (term (Construct (List Int) some 1)) empty empty)
   'ill-typed)
  (check-equal?
   (core-type-of
    (term (Eliminate (Construct (List Int) nil)
                     ((nil () -> 0)
                      (cons (head tail) -> head))))
    empty empty)
   (term (Int ())))
  (check-equal?
   (core-type-of
    (term (Eliminate (Construct (List Int) nil)
                     ((nil () -> 0))))
    empty empty)
   'ill-typed))

(test-case "RET-002: Perform and Handle track the resolved Return label"
  (define performed
    (term (Perform (Return boundary Int) 7)))
  (check-equal?
   (core-type-of performed empty empty)
   (term (Never ((Return boundary Int)))))
  (check-equal?
   (core-type-of
    (term (Handle (Return boundary Int)
                  (result -> result)
                  ,performed))
    empty empty)
   (term (Int ()))))

(test-case "OWN-001/REC-002: Scope, Drop, Yield, and Suspend compose rows"
  (define places (term ((0 Res))))
  (check-equal?
   (core-type-of (term (Scope (0) (Drop (Move 0)))) places empty)
   (term (Unit (Own))))
  (check-equal?
   (core-type-of (term (Yield 1 (Suspend unit))) empty empty)
   (term (Unit (Suspend (Yield Int)))))
  (check-equal?
   (core-type-of (term (Scope (1) unit)) places empty)
   'ill-typed)
  (check-true
   (core-check (term (Error 0)) places empty (term Bool) empty)))

(test-case "T-Val: resource, TypeRep, and ProofRep synthesize"
  (check-equal? (core-type-of (term (resource 9)) empty empty)
                (term ((Owned Res) ())))
  (check-equal?
   (core-type-of (term (TypeRep User List (Type -> Type))) empty empty)
   (term ((TypeInfo (Type -> Type)) ())))
  (check-equal?
   (core-type-of (term (ProofRep User ValidNarrativeTrait)) empty empty)
   (term ((Proof ValidNarrativeTrait) ()))))

(test-case "T-Config: reconstructs Ξ and checks all domains"
  (define good
    (term (cfg (Scope (0) (Move 0))
               ((0 (resource 7)))
               ((0 Available))
               () ())))
  (check-true
   (config-ok? good empty (term (Owned Res)) (term (Own))))
  (check-true
   (config-ok?
    (term (cfg (Error 0)
               ((0 (resource 7)))
               ((0 Moved))
               () ()))
    empty (term Int) empty))
  (check-false
   (config-ok?
    (term (cfg unit ((0 (resource 7))) () () ()))
    empty (term Unit) empty))
  (check-false
   (config-ok?
    (term (cfg unit
               ((0 (resource 7)) (0 (resource 8)))
               ((0 Available) (0 Moved))
               () ()))
    empty (term Unit) empty))
  (check-false
   (config-ok?
    (term (cfg unit ((0 1)) ((0 Available)) () ()))
    empty (term Unit) empty)))

(test-case "typing environments must be finite maps"
  (check-equal?
   (core-type-of (term (Move 0)) (term ((0 Res) (0 Int))) empty)
   'ill-typed)
  (check-equal?
   (core-type-of
    (term (Lam User identity-id (x) x))
    empty
    (term ((identity-id (NFn (Int) Int () ()))
           (identity-id (NFn (Bool) Bool () ())))))
   'ill-typed))

(test-case "typing accepts an explicit elaboration Γ"
  (define environment (term ((x Int) (item (Owned Res)))))
  (check-equal?
   (core-type-of (term x) empty empty environment)
   (term (Int ())))
  (check-equal?
   (core-type-of (term (Move item)) empty empty environment)
   (term ((Owned Res) (Own))))
  (check-true
   (core-check (term x) empty empty (term Int) empty environment)))

(test-case "heap の CurryVal を config-ok? が受理する"
  (define curried (term (CurryVal User ,leaf-drop-lam (resource 1))))
  (define config
    (term (cfg unit ((0 ,curried)) ((0 Available)) () ())))
  (check-true (config-ok? config curry-callables (term Unit) empty)))

(test-case "H の entry の並び順が Ξ の導出を変えない"
  (define ascending (term ((0 (resource 1)) (1 (resource 2)))))
  (define descending (term ((1 (resource 2)) (0 (resource 1)))))
  (check-equal? (derive-places ascending empty)
                (derive-places descending empty)))

(define (leaf-config value tokens)
  (term (cfg unit ((0 ,value)) ((0 Available)) ,tokens ())))

(test-case "Available の token は live 集合にちょうど一度現れる"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))
  (check-true (config-ok? (leaf-config value (term (((tok 0) Available))))
                          empty (term Unit) empty)))

(test-case "同じ token が二箇所に現れる configuration を拒否する"
  (define value
    (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))
                (g mut (OwnedLeaf (tok 0) (resource 2)))))))
  (check-false (config-ok? (leaf-config value (term (((tok 0) Available))))
                           empty (term Unit) empty)))

(test-case "Λtok に無い token を拒否する"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 9) (resource 1)))))))
  (check-false (config-ok? (leaf-config value (term ()))
                           empty (term Unit) empty)))

(test-case "Available なのに値に現れない token を拒否する"
  (check-false (config-ok? (leaf-config (term (resource 1))
                                        (term (((tok 0) Available))))
                           empty (term Unit) empty)))

(test-case "Dropped の tombstone は値に現れなくても受理する"
  (check-true (config-ok? (leaf-config (term (resource 1))
                                       (term (((tok 0) Dropped))))
                          empty (term Unit) empty)))

(test-case "Dropped の token が live 集合に現れる configuration を拒否する"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))
  (check-false (config-ok? (leaf-config value (term (((tok 0) Dropped))))
                           empty (term Unit) empty)))

(test-case "値の根の位置の leaf を拒否する"
  (check-false (config-ok? (leaf-config (term (OwnedLeaf (tok 0) (resource 1)))
                                        (term (((tok 0) Available))))
                           empty (term Unit) empty)))

(test-case "OwnedLeaf の型は payload の型そのもの"
  (check-equal? (type-of/raw (term (OwnedLeaf (tok 0) (resource 1))) empty empty)
                (term (ok ((Owned Res) ())))))

(test-case "owned でない payload を包んだ leaf は ill-typed"
  (define result (type-of/raw (term (OwnedLeaf (tok 0) Unit)) empty empty))
  (check-false (and (pair? result) (eq? (first result) 'ok))))

(test-case "通常の型検査は Rec の欄の裸の資源を拒否し続ける"
  (define result (type-of/raw (term (Rec ((f mut (resource 1))))) empty empty))
  (check-false (and (pair? result) (eq? (first result) 'ok))))

(test-case "leaf-positions-ok? が走査で辿れない位置を拒否する"
  (define leaf (term (OwnedLeaf (tok 0) (resource 1))))
  (check-false (leaf-positions-ok? leaf))
  (check-false
   (leaf-positions-ok?
    (term (Rec ((f mut (OwnedLeaf (tok 0)
                                  (OwnedLeaf (tok 1) (resource 1)))))))))
  (check-false (leaf-positions-ok? (term (CurryVal User ,leaf (resource 2)))))
  (check-false (leaf-positions-ok? (term (UVal ,leaf))))
  (check-true (leaf-positions-ok? (term (Rec ((f mut ,leaf)))))))

(test-case "leaf-positions-ok? が未対応の構成子の内部の Rec を拒否する"
  (define leaf (term (OwnedLeaf (tok 0) (resource 1))))
  (define rec (term (Rec ((f mut ,leaf)))))
  (check-false (leaf-positions-ok? (term (UVal ,rec))))
  (check-false (leaf-positions-ok? (term (CurryVal User ,rec (resource 2)))))
  (check-false (leaf-positions-ok? (term (Scope (0) ,rec))))
  (check-false (leaf-positions-ok? (term (Let (x Int) ,rec Unit))))
  (check-false (leaf-positions-ok? (term (UVal (UVal ,rec)))))
  (check-true (leaf-positions-ok? (term (Rec ((f mut ,rec)))))))

(test-case "leaf-positions-ok? が Construct の引数の leaf を拒否する"
  (define leaf (term (OwnedLeaf (tok 0) (resource 1))))
  (check-false (leaf-positions-ok? (term (Construct T K ,leaf))))
  (check-false
   (leaf-positions-ok?
    (term (Construct T K (Rec ((f mut ,leaf)))))))
  (check-true (leaf-positions-ok? (term (Construct T K (resource 1))))))

(test-case "leaf を含まない値は未対応の構成子の内部でも通る"
  (check-true (leaf-positions-ok? (term (UVal (Rec ((f mut (resource 1))))))))
  (check-true (leaf-positions-ok? (term (BorrowMutRef 0 (a) ρ)))))

(test-case "制御項の値の位置の leaf を config-ok? が拒否する"
  (define leaf (term (OwnedLeaf (tok 0) (resource 1))))
  (check-false
   (config-ok? (term (cfg (Scope () ,leaf)
                          ()
                          ()
                          (((tok 0) Available))
                          ()))
               empty (term (Owned Res)) (term (Own))))
  (check-false
   (config-ok? (term (cfg (Drop (UVal (Rec ((f mut ,leaf)))))
                          ()
                          ()
                          (((tok 0) Available))
                          ()))
               empty (term Unit) (term (Own)))))

(test-case "制御項の値でない位置の下の Rec の leaf は通る"
  (check-true
   (control-leaf-positions-ok?
    (term (Drop (Rec ((f mut (OwnedLeaf (tok 0) (resource 1))))))))))

(test-case "根位置の leaf を持つ configuration を config-ok? が拒否する"
  (define leaf (term (OwnedLeaf (tok 0) (resource 7))))
  (check-false
   (config-ok? (term (cfg (Scope (0) (Move 0))
                          ((0 ,leaf))
                          ((0 Available))
                          (((tok 0) Available))
                          ()))
               empty (term (Owned Res)) (term (Own))))
  (check-false
   (config-ok? (term (cfg ,leaf () () (((tok 0) Available)) ()))
               empty (term (Owned Res)) (term (Own)))))

(test-case "未対応の構成子へ隠した leaf を config-ok? が拒否する"
  (define leaf (term (OwnedLeaf (tok 0) (resource 7))))
  (check-false
   (config-ok? (term (cfg (Scope (0) (Move 0))
                          ((0 (UVal (Rec ((f mut ,leaf))))))
                          ((0 Available))
                          (((tok 0) Available))
                          ()))
               empty (term (Owned Res)) (term (Own)))))

#lang racket

(require racket/match
         redex/reduction-semantics
         rackunit
         "../elaborate.rkt"
         "../classify.rkt"
         "../diagnostic.rkt"
         "../erase.rkt"
         "../lang.rkt"
         "../machine.rkt"
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

(define (run-elaborated core)
  (run-g2 (inject-g2m (erase-core core)) 10000))

(define (check-owned-return-finalization core)
  (check-equal?
   (run-elaborated core)
   '(cfg unit ((0 (resource 1)) (1 (resource 2)))
         ((0 Moved) (1 Dropped)) () ((fin 1)))))

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
   '(NFn () Int () ((Return boundary0 Int) Partial) () User)))

(test-case "SUR-015: FnDecl が独自の Return 境界を持つ"
  (match-define (list core type _row _callables)
    (success
     (elab '(FnDecl f ((x Int)) Int () (Return x) (Apply f 7)))))
  (check-equal? type 'Int)
  (check-equal? (run-elaborated core)
                '(cfg 7 () () () ())))

(test-case "SUR-015: 入れ子 FnDecl の宣言 row は外側の境界を参照する"
  (match-define (list _core _type _row callables)
    (success
     (elab '(FnDecl outer () Int ()
                   (FnDecl inner () Int (Return) 0 0)
                   0))))
  (check-not-false
   (member '(callable1 (NFn () Int () ((Return boundary0 Int)) () User))
           callables)))

(test-case "SUR-015: Recur の本体の Return は外側の Fn が受ける"
  (match-define (list core _type _row _callables)
    (success
     (elab '(Apply (Fn () Int ()
                       (Recur f () Int (Return) (Return 3) (Apply f)))))))
  (check-equal? (run-elaborated core)
                '(cfg 3 () () () ())))

(test-case "SUR-015: Return の無い FnDecl は Recur と Core と分類が同じ"
  (define declared (elab '(FnDecl f ((x Int)) Int () x 1)))
  (define recurred (elab '(Recur f ((x Int)) Int () x 1)))
  (match* (declared recurred)
    [((list declared-core _ _ declared-callables)
      (list recurred-core _ _ recurred-callables))
     (check-equal? (erase-core declared-core) (erase-core recurred-core))
     (check-equal? declared-callables recurred-callables)
     (check-equal? (classify (erase-core declared-core) '() declared-callables)
                   (classify (erase-core recurred-core) '() recurred-callables))]
    [(_ _) (fail-check
            (format "FnDecl と Recur の成功を期待した: ~s / ~s"
                    declared recurred))]))

(test-case "SUR-015: mentions-return は束縛名、変数名、型注釈を走査しない"
  (define s '(#:span synthetic 0 0))
  (check-false (mentions-return? `(#:bind Return ,s)))
  (check-false (mentions-return? `(#:var Return ,s)))
  (check-false
   (mentions-return? `(#:ty (Fn () Int (#:ef (Return) ,s)) ,s)))
  (check-true (mentions-return? `(Return ,s (#:lit 1 ,s))))
  (check-true (mentions-return? `(#:ef (Return) ,s))))

(test-case "SUR-015: Owned の仮引数の包み内で Handle が本体を囲み分類を保つ"
  (define result
    (elab
     '(FnDecl f ((xs (List Int)) (item (Owned Res))) Int (Own)
               (Eliminate xs
                          ((nil () -> (Return 0))
                           (cons (head tail) ->
                                 (Apply f tail (Move item)))))
               (Apply f (Construct nil (Types Int)) (Apply acquire 1)))))
  (match result
    [(list core _type _row _callables)
     (define recur-body (list-ref core 5))
     (check-true
      (match recur-body
        [`(Scope ,_ () (Let ,_ ,_ ,_ (Handle ,_ ,_ ,_ (Scope ,_ () ,_))))
         #t]
        [_ #f]))]
    [_ (fail-check (format "elaboration success を期待したが ~s" result))]))

(test-case "SUR-015: Owned を Return すると残りと返却値を一度ずつ解放する"
  (define result
    (elab
     '(FnDecl f ((returned (Owned Res)) (remaining (Owned Res)))
               (Owned Res) (Own)
               (Return (Move returned))
               (Drop (Apply f (Apply acquire 1) (Apply acquire 2))))))
  (match result
    [(list core _type _row _callables)
     (check-owned-return-finalization core)]
    [_ (fail-check (format "elaboration success を期待したが ~s" result))]))

(test-case "RET-002: E-Lambda は Owned Return の payload を一度ずつ解放する"
  (define result
    (elab
     '(Drop
       (Apply
        (Fn ((returned (Owned Res)) (remaining (Owned Res)))
            (Owned Res) (Own)
            (Return (Move returned)))
        (Apply acquire 1)
        (Apply acquire 2)))))
  (match result
    [(list core _type _row _callables)
     (check-owned-return-finalization core)]
    [_ (fail-check (format "elaboration success を期待したが ~s" result))]))

(test-case "RET-002: NarrativeExpr と Fn の Owned Return handler は共に恒等"
  (define result
    (elab
     '(Drop
       (Apply
        (Fn ((returned (Owned Res)) (remaining (Owned Res)))
            (Owned Res) (Own)
            (NarrativeExpr (Return (Move returned))))
        (Apply acquire 1)
        (Apply acquire 2)))))
  (match result
    [(list core _type _row _callables)
     (define erased (erase-core core))
     (define (identity-handles term)
       (match term
         [`(Handle ,_ (,name -> ,handler) ,body)
          (+ (if (eq? name handler) 1 0) (identity-handles body))]
         [(? list?) (for/sum ([part (in-list term)]) (identity-handles part))]
         [_ 0]))
     (check-equal? (identity-handles erased) 2)
     (check-owned-return-finalization core)]
    [_ (fail-check (format "elaboration success を期待したが ~s" result))]))

(test-case "EFF-001: declared rows bound fn and recur bodies"
  (check-true
   (elaboration-error?
    (elab '(Fn () Unit () (Yield 1 unit)))))
  (check-false
   (elaboration-error?
    (elab '(Recur f () Int () 1 1))))
  (define self-application
    (elab '(Recur f () Int () (Apply f) (Apply f))))
  (check-true (elaboration-error? self-application))
  (check-equal?
   (match self-application
     [`(err ,diagnostic) (diagnostic-id diagnostic)]
     [_ #f])
   (diagnostic-code-of 'elaborate 'unknown-recur-requires-partial))
  (match-define (list _ type _ _)
    (success
     (elab '(Fn () Unit ((Yield Int)) (Yield 1 unit)))))
  (check-equal? type '(NFn () Unit () ((Yield Int)) () User)))

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
  (check-false
   (elaboration-error?
    (elab '(Recur f ((item (Owned Res))) Unit (Partial) unit unit))))
  (check-false
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
  (check-true (tree-contains? move-core '(Move item⟨1⟩)))
  (check-equal?
   (core-type-of move-core '() move-callables)
   (list move-type move-row))

  (match-define (list drop-core drop-type drop-row _)
    (success
     (elab '(Let item (Apply acquire 7) (Drop item)))))
  (check-equal? drop-type 'Unit)
  (check-equal? drop-row '(Own))
  (check-true (tree-contains? drop-core '(Drop (Move item⟨1⟩)))))

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
     (NFn (Int Int) Int () () () (Reserved o-add))
     ()
     ()))
  (match-define (list core type row _)
    (success (elab '(Let add 1 add))))
  (check-equal? core '(Let (add⟨1⟩ Int) 1 add⟨1⟩))
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
     (NFn (Int) Int () () ()
          (Derived (Reserved o-add) (Curry 1)))
     ()
     ()))
  (match-define (list _core curry-type _row _callables)
    (elab '(Fn ((f (NFn ((Owned Res)) Unit () ())))
              (Owned (NFn () Unit () ())) (Own)
              (Curry f (Apply acquire 1)))))
  (check-equal? curry-type
                '(NFn ((NFn ((Owned Res)) Unit () () () User))
                      (Owned (NFn () Unit () () () User)) () (Own) () User)))

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
  (check-equal? type '(NFn () (List Int) () () () User))
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

(test-case "C4-001: Owned を包んだ走査対象の Eliminate が elaborate できる"
  (check-false
   (elaboration-error?
    (elab
     '(Fn ((xs (Owned (List Int)))) Int (Own)
          (Eliminate (Move xs)
                     ((nil () -> 0)
                      (cons (head tail) -> 0))))))))

;; ucore.rkt の uτ に Borrowed が無いため、UCore+ と UCore の照合が
;; 両方失敗し、elab は invalid-syntax で落ちる。
;; resolve-annotation の invalid-type-annotation には届かない。
(test-case "C4-006a: surface の Borrowed 注釈は文法の照合で落ちる"
  (check-true
   (elaboration-error?
    (elab
     '(Fn ((xs (Borrowed (List Int) 0))) Int ()
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> 0))))))))

;; cons の再帰欄は (List Int) であり (Owned (List Int)) ではない。
;; したがって末尾 tail を Owned の仮引数へ渡す再帰呼び出しは型が付かない。
;; 実測の失敗理由は E-TYP-012 (type-mismatch) である。
;; 外側の Fn は、走査対象と初期値を Owned のまま用意するためだけに置く。
(test-case "C4-005: Owned の位置そのものを根とする再帰は依然として書けない"
  (check-true
   (elaboration-error?
    (elab
     '(Fn ((xs0 (Owned (List Int)))) Int (Own)
          (Recur loop ((xs (Owned (List Int)))) Int (Own)
                 (Eliminate (Move xs)
                            ((nil () -> 0)
                             (cons (head tail) -> (Apply loop tail))))
                 (Apply loop (Move xs0))))))))

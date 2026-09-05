#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt")

(define fuel 50)
(define acquire (term (PrimVal (Reserved o-acquire) acquire)))

(define (cfg-tokens configuration)
  (match configuration
    [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (cfg-events configuration)
  (match configuration
    [`(cfg ,_ ,_ ,_ ,_ ,events) events]))

(test-case "OWN-001: move succeeds once and reuse raises OwnershipError"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 0)
                (Move r))))
    fuel)
   (term (cfg (resource 0)
              ((0 (resource 0)))
              ((0 Moved))
              () ())))
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 0)
                (Let (used Res) (Move r) (Move r)))))
    fuel)
   (term (cfg (Error 0)
              ((0 (resource 0)))
              ((0 Moved))
              () ())))
  (check-equal?
   (run
    (term (cfg (Move 0)
               ((0 (resource 0)))
               ((0 Dropped))
               () ()))
    fuel)
   (term (cfg (Error 0)
              ((0 (resource 0)))
              ((0 Dropped))
              () ()))))

(test-case "R-Drop: evaluated values become unit"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 0)
                (Drop (Move r)))))
    fuel)
   (term (cfg unit
              ((0 (resource 0)))
              ((0 Moved))
              () ()))))

(test-case "R-LetOwned: deterministic allocation targets the nearest Scope"
  (define source
    (term (cfg
           (Scope ()
                  (Scope ()
                         (Handle (Return b Int)
                                 (answer -> answer)
                                 (Let (r (Owned Res))
                                      (resource 9)
                                      (Move r)))))
           ((0 (resource 0)) (3 (resource 3)))
           ((0 Moved) (3 Moved))
           () ())))
  (define expected
    (term (cfg
           (Scope ()
                  (Scope (4)
                         (Handle (Return b Int)
                                 (answer -> answer)
                                 (Move 4))))
           ((0 (resource 0)) (3 (resource 3)) (4 (resource 9)))
           ((0 Moved) (3 Moved) (4 Available))
           () ())))
  (match (apply-reduction-relation -->g1 source)
    [(list actual) (check-true (alpha-equivalent? G1m actual expected))]
    [actual (fail-check (format "expected one successor, got ~e" actual))])
  (define root-leaf-source
    (term (cfg
           (Scope ()
                  (Let (r (Owned Res))
                       (OwnedLeaf (tok 5) (resource 9))
                       (Move r)))
           () () (((tok 5) Available)) ())))
  (define root-leaf-results
    (apply-reduction-relation -->g1 root-leaf-source))
  (check-equal? (length root-leaf-results) 1)
  (check-equal?
   (first root-leaf-results)
   (term (cfg (Scope (0) (Move 0))
              ((0 (resource 9)))
              ((0 Available))
              (((tok 5) Dropped)) ())))
  (define root-leaf-source-g2
    (term (cfg
           (Scope ()
                  (Let (r let (Owned Res))
                       (OwnedLeaf (tok 6) (resource 10))
                       (Move r)))
           () () (((tok 6) Available)) ())))
  (define root-leaf-results-g2
    (apply-reduction-relation -->g2 root-leaf-source-g2))
  (check-equal? (length root-leaf-results-g2) 1)
  (check-equal?
   (first root-leaf-results-g2)
   (term (cfg (Scope (0) (Move 0))
              ((0 (resource 10)))
              ((0 Available))
              (((tok 6) Dropped)) ())))
  (check-equal?
   (run
    (term (cfg (Scope ()
                      (Let (x (Owned Res)) (resource 1) 42))
               ()
               ((0 Moved))
               () ()))
    fuel)
   (term (cfg 42
              ((1 (resource 1)))
              ((0 Moved) (1 Dropped))
              () ((fin 1))))))

(test-case "OWN-002: scope finalizes available places once in reverse order"
  (check-equal?
   (run
    (inject
     (term (Let (first (Owned Res))
                (Apply ,acquire 10)
                (Let (second (Owned Res))
                     (Apply ,acquire 20)
                     unit))))
    fuel)
   (term (cfg unit
              ((0 (resource 10)) (1 (resource 20)))
              ((0 Dropped) (1 Dropped))
              () ((fin 1) (fin 0)))))
  (check-equal?
   (run
    (term (cfg (Scope (0 0) unit)
               ((0 (resource 1)))
               ((0 Available))
               () ()))
    fuel)
   (term (cfg unit
              ((0 (resource 1)))
              ((0 Dropped))
              () ((fin 0))))))

(test-case "OWN-003: abort and error exits finalize remaining places"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 7)
                (Perform (Return boundary Int) 42))))
    fuel)
   (term (cfg (Perform (Return boundary Int) 42)
              ((0 (resource 7)))
              ((0 Dropped))
              () ((fin 0)))))
  (check-equal?
   (run
    (term (cfg (Scope (0)
                      (Scope (1)
                             (Perform (Return boundary Int) 42)))
               ((0 (resource 0)) (1 (resource 1)))
               ((0 Available) (1 Available))
               () ()))
    fuel)
   (term (cfg (Perform (Return boundary Int) 42)
              ((0 (resource 0)) (1 (resource 1)))
              ((0 Dropped) (1 Dropped))
              () ((fin 1) (fin 0)))))
  (check-equal?
   (run
    (inject
     (term (Let (first (Owned Res))
                (Apply ,acquire 10)
                (Let (second (Owned Res))
                     (Apply ,acquire 20)
                     (Let (used Res)
                          (Move second)
                          (Move second))))))
    fuel)
   (term (cfg (Error 1)
              ((0 (resource 10)) (1 (resource 20)))
              ((0 Dropped) (1 Moved))
              () ((fin 0))))))

(test-case "R-HandleError: ownership errors bypass handlers"
  (check-equal?
   (run
    (inject
     (term (Let (r (Owned Res))
                (Apply ,acquire 5)
                (Handle (Return boundary Int)
                        (answer -> answer)
                        (Let (used Res)
                             (Move r)
                             (Move r))))))
    fuel)
   (term (cfg (Error 0)
              ((0 (resource 5)))
              ((0 Moved))
              () ()))))

;; Lam の本体が G2 だけの形（modeful な Let）なので、G1 の origin-of では
;; 照合できない。G2m の R-CurryVal が同じ生成を継続することを確かめる。
(test-case "G2 だけの本体を持つ Lam の Curry が簡約できる"
  (define config
    (term (cfg (Curry (Lam User g2-id (x) (Let (y let Res) x y)) 1)
               () () () ())))
  (check-true (redex-match? G2m config config))
  (define results (apply-reduction-relation -->g2 config))
  (check-equal? (length results) 1)
  (check-true
   (redex-match? G2m
                 (cfg (CurryVal any_o any_f any_a)
                      any_h any_s any_t any_e)
                 (first results))))

(test-case "substitute* は leaf の payload だけを置き換え token を変えない"
  (check-equal?
   (term (substitute*/g2
          (OwnedLeaf (tok 3) (Lam User leaf-sub-id () x))
          (x) ((resource 1))))
   (term (OwnedLeaf (tok 3) (Lam User leaf-sub-id () (resource 1))))))

(test-case "scope 終了が値の内部の leaf を一度だけ回収する"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))
  (define config
    (term (cfg (Scope (0) unit) ((0 ,value)) ((0 Available))
               (((tok 0) Available)) ())))
  (define results (apply-reduction-relation -->g2 config))
  (check-equal? (length results) 1)
  (define after (first results))
  (check-equal? (cfg-tokens after) (term (((tok 0) Dropped))))
  (check-equal? (cfg-events after) (term ((finLeaf 0 (f)) (fin 0)))))

(test-case "Moved の root は走査しない"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))
  (define config
    (term (cfg (Scope (0) unit) ((0 ,value)) ((0 Moved))
               (((tok 0) Available)) ())))
  (define results (apply-reduction-relation -->g2 config))
  (check-equal? (length results) 1)
  (check-equal? (cfg-tokens (first results))
                (term (((tok 0) Available)))))

(test-case "R-Drop は値の内部の leaf を Dropped にして観測を積まない"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))
  (define config
    (term (cfg (Drop ,value) ((0 ,value)) ((0 Available))
               (((tok 0) Available)) ())))
  (define results (apply-reduction-relation -->g2 config))
  (check-equal? (length results) 1)
  (define after (first results))
  (check-equal? (cfg-tokens after) (term (((tok 0) Dropped))))
  (check-equal? (cfg-events after) (term ()))
  (check-equal?
   (apply-reduction-relation
    -->g2
    (term (cfg (Drop (OwnedLeaf (tok 1) (resource 2)))
               () () (((tok 1) Available)) ())))
   (list (term (cfg unit () () (((tok 1) Dropped)) ())))))

(test-case "leaf の token が Available でなければ R-Drop は発火しない"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))
  (for ([tokens (in-list (list (term (((tok 0) Moved)))
                               (term (((tok 0) Dropped)))
                               (term ())))])
    (define config
      (term (cfg (Drop ,value) ((0 ,value)) ((0 Available)) ,tokens ())))
    (check-equal? (apply-reduction-relation -->g2 config) '())))

(test-case "leaf の token が Available でなければ scope 終了が発火しない"
  (define value (term (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))))
  (for ([tokens (in-list (list (term (((tok 0) Moved)))
                               (term (((tok 0) Dropped)))
                               (term ())))])
    (define config
      (term (cfg (Scope (0) unit) ((0 ,value)) ((0 Available)) ,tokens ())))
    (check-equal? (apply-reduction-relation -->g2 config) '())))

(test-case "fresh-token は決定的で Dropped の番号を再利用しない"
  (define config
    (term (cfg unit ((0 (resource 1))) ((0 Available))
               (((tok 0) Dropped)) ())))
  (check-equal? (fresh-token config) (term (tok 1)))
  (check-equal? (fresh-token config) (term (tok 1))))

(test-case "fresh-token は Λtok 以外の走査対象も見る"
  (define leaf (term (OwnedLeaf (tok 0) (resource 1))))
  ;; Λtok は空。token は制御項にだけある。
  (check-equal?
   (fresh-token (term (cfg (Drop (Rec ((f mut ,leaf)))) () () () ())))
   (term (tok 1)))
  ;; Λtok は空。token は H にだけある。
  (check-equal?
   (fresh-token
    (term (cfg unit ((0 (Rec ((f mut ,leaf))))) ((0 Available)) () ())))
   (term (tok 1)))
  ;; Λtok は空。token は θ の (obs v) にだけある。
  (check-equal?
   (fresh-token (term (cfg unit () () () ((obs (Rec ((f mut ,leaf))))))))
   (term (tok 1))))

(test-case "R-Yield は leaf token の tombstone を保持する"
  (define config
    (term (cfg (Yield 0 unit) () () (((tok 0) Dropped)) ())))
  (check-equal?
   (apply-reduction-relation -->g2 config)
   (list (term (cfg unit () () (((tok 0) Dropped)) ((obs 0)))))))

(test-case "二 place の scope が place の逆順で finLeaf と fin を並べる"
  (define leaf0 (term (OwnedLeaf (tok 0) (resource 10))))
  (define leaf1 (term (OwnedLeaf (tok 1) (resource 20))))
  (define heap
    (term ((0 (Rec ((f mut ,leaf0))))
           (1 (Rec ((g mut ,leaf1)))))))
  (define results
    (apply-reduction-relation
     -->g2
    (term (cfg (Scope (0 1) unit) ,heap
                ((0 Available) (1 Available))
                (((tok 0) Available) ((tok 1) Available))
                ()))))
  (check-equal? results
                (list
                 (term (cfg unit ,heap
                            ((0 Dropped) (1 Dropped))
                            (((tok 0) Dropped) ((tok 1) Dropped))
                            ((finLeaf 1 (g)) (fin 1)
                             (finLeaf 0 (f)) (fin 0)))))))

;; Yield は payload の leaf token を Available から Observed へ移す。
(test-case
 "R-Retire drops every Observed token at the terminal"
 (define result
   (run-g2 (term (cfg (Yield (OwnedLeaf (tok 0) (resource 1)) unit)
                      () () (((tok 0) Available)) ()))
           10))
 (check-equal? (list-ref result 4) (term (((tok 0) Dropped))))
 (check-equal? (list-ref result 5)
               (term ((obs (OwnedLeaf (tok 0) (resource 1)))))))

;; Yield の直後は Observed であり、終端に達するまで retire しない。
(test-case
 "R-Yield leaves the payload token Observed before the terminal"
 (define next
   (apply-reduction-relation
   -->g2
    (term (cfg (Yield (OwnedLeaf (tok 0) (resource 1)) unit)
               () () (((tok 0) Available)) ()))))
 (check-equal? (length next) 1)
 (check-equal? (list-ref (car next) 4) (term (((tok 0) Observed)))))

;; 同じ観測 payload に複数の leaf がある場合、全 token が同時に遷移する。
(test-case
 "R-Yield moves every payload leaf token in one transition"
 (define next
   (apply-reduction-relation
    -->g2
    (term (cfg (Yield (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))
                            (g mut (OwnedLeaf (tok 1) (resource 2)))))
                       unit)
               () () (((tok 0) Available) ((tok 1) Available)) ()))))
 (check-equal? (length next) 1)
 (check-equal? (list-ref (car next) 4)
               (term (((tok 0) Observed) ((tok 1) Observed)))))

;; 未登録の token を含む payload の Yield は発火しない。
(test-case
 "R-Yield does not fire for an unregistered payload token"
 (check-equal?
  (apply-reduction-relation
   -->g2
   (term (cfg (Yield (OwnedLeaf (tok 0) (resource 1)) unit) () () () ())))
  '()))

;; 一つの payload に同じ token が二度現れる Yield は発火しない。
(test-case
 "R-Yield rejects duplicate payload leaf tokens"
 (check-equal?
  (apply-reduction-relation
   -->g2
   (term
    (cfg (Yield (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))
                      (g mut (OwnedLeaf (tok 0) (resource 1)))))
                unit)
          () () (((tok 0) Available)) () )))
  '()))

;; Observed token は二度目の Yield で再観測できない。
(test-case
 "R-Yield rejects a non-Available payload token"
 (check-equal?
  (apply-reduction-relation
   -->g2
   (term (cfg (Yield (OwnedLeaf (tok 0) (resource 1)) unit)
              () () (((tok 0) Observed)) () )))
  '()))

;; 内側 Scope の finalize は Observed を触らない。retire は終端だけで起きる。
(test-case
 "inner Scope finalization keeps Observed tokens Observed"
 (define next
   (apply-reduction-relation
    -->g2
    (term (cfg (Scope ()
                      (Scope ()
                             (Yield (OwnedLeaf (tok 0) (resource 1)) unit)))
               () () (((tok 0) Available)) ()))))
 (define after-yield (car next))
 (define after-exit
   (car (apply-reduction-relation -->g2 after-yield)))
 (check-equal? (list-ref after-exit 4) (term (((tok 0) Observed)))))

;; G2m の Rec を payload に持つ観測でも、終端で Observed が Dropped になる。
(test-case
 "R-Retire fires for a Rec payload terminal in G2m"
 (define result
   (run-g2 (term (cfg (Yield (Rec ((f mut (OwnedLeaf (tok 0) (resource 1)))))
                             unit)
                      () () (((tok 0) Available)) ()))
           10))
 (check-equal? (list-ref result 4) (term (((tok 0) Dropped)))))

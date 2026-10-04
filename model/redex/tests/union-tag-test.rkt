#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../annotate.rkt"
         "../borrow.rkt"
         "../compat.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../machine.rkt"
         "../borrow-oracle.rkt"
         "../borrow-gen.rkt"
         "../region.rkt"
         "../span-core.rkt"
         "../type-shape.rkt"
         "../type-equiv.rkt"
         "../typing.rkt"
         "../uniquify.rkt")

(define U '(Union Int (Union String Bool)))
(define U1 '(Union Int Bool))
(define U2 '(Union String Bool))
(define IS '(Union Int String))
(define nfn-u1 `(NFn (,U1) Int () () () User))
(define nfn-u `(NFn (,U) Int () () () User))

(define inject-int `(UnionInject ,IS Int 1))
(define elim-is
  `(UnionEliminate ,inject-int ((Int i -> i) (String s -> 0))))

(define (contains-union-form? tree form)
  (or (and (pair? tree) (eq? (car tree) form))
      (and (pair? tree) (ormap (lambda (part)
                                 (contains-union-form? part form))
                               tree))))

(define (tree-any? tree predicate)
  (or (predicate tree)
      (and (pair? tree) (ormap (lambda (part) (tree-any? part predicate)) tree))))

(define (contains-symbol? tree name)
  (or (eq? tree name)
      (and (pair? tree) (ormap (lambda (part) (contains-symbol? part name)) tree))))

(test-case "Union の生成経路は opt-in である"
  (check-false (generate-union-core))
  (define core (generate-union-core #:include-union? #t))
  (check-true (redex-match? G2 c core))
  (check-true (contains-union-form? core 'UnionInject))
  (check-true (contains-union-form? core 'UnionEliminate))
  (check-false (redex-match? G1gen g core))
  (check-false (contains-union-form? (gen-borrow-term 4) 'UnionInject))
  (define borrowed (gen-borrow-term 4 #:include-union? #t))
  (check-true (contains-union-form? borrowed 'UnionInject))
  (check-true (contains-union-form? borrowed 'UnionEliminate)))

(test-case "opt-in Union generator varies values, branches, and tag-preserving joins"
  (define limits (struct-copy bounds (read-bounds) [attempts 120]))
  (define generated
    (call-with-search-seed
     limits
     (lambda ()
       (for/list ([_ (in-range (bounds-attempts limits))])
         (generate-union-core #:include-union? #t)))))
  (define (union-let-and-eliminate? node)
    (match node
      [`(Let (,name const (Union ,_ ...))
             (UnionInject ,_ ,_ ,_)
             ,body)
       (tree-any? body
                  (lambda (candidate)
                    (match candidate
                      [`(UnionEliminate ,scrutinee ,_) (eq? scrutinee name)]
                      [_ #f])))]
      [_ #f]))
  (define (union-merge? node)
    (match node
      [`(Eliminate (Construct Bool ,_) ,arms)
       (define injected-types
         (for/list ([arm (in-list arms)]
                    #:when (match arm
                             [`(,_ () -> (UnionInject ,_ ,_ ,_)) #t]
                             [_ #f]))
           (match arm
             [`(,_ () -> (UnionInject ,type ,_ ,_)) type])))
       (and (= (length injected-types) 2)
            (not (equal? (first injected-types) (second injected-types))))]
      [_ #f]))
  (define (used-union-binder? node)
    (match node
      [`(UnionEliminate ,_ ,arms)
       (for/or ([arm (in-list arms)])
         (match arm
           [`(,_ ,binder -> ,body) (contains-symbol? body binder)]
           [_ #f]))]
      [_ #f]))
  (define (permuted-union-arms? node)
    (match node
      [`(UnionEliminate ,_ ,arms)
       (define arm-types
         (for/list ([arm (in-list arms)])
           (match arm [`(,type ,_ -> ,_) type])))
       (and (> (length arm-types) 1)
            (not (equal? arm-types
                         (union-members (normalize-type `(Union ,@arm-types))))))]
      [_ #f]))
  (define (three-member-union? node)
    (match node
      [`(UnionInject ,type ,_ ,_)
       (and (match type [`(Union ,_ ,_) #t] [_ #f])
            (>= (length (union-members type)) 3))]
      [`(Let (,_ ,_ ,type) ,_ ,_)
       (and (match type [`(Union ,_ ,_) #t] [_ #f])
            (>= (length (union-members type)) 3))]
      [_ #f]))
  (define (union-types-normal? node)
    (and (or (not (match node [`(Union ,_ ,_ ...) #t] [_ #f]))
             (equal? node (normalize-type node)))
         (or (not (pair? node))
             (andmap union-types-normal? node))))
  (check-true (ormap (lambda (core) (tree-any? core union-let-and-eliminate?)) generated))
  (check-true (ormap (lambda (core) (tree-any? core union-merge?)) generated))
  (check-true (ormap (lambda (core) (tree-any? core used-union-binder?)) generated))
  (check-true
   (ormap (lambda (core) (tree-any? core (lambda (node)
                                          (match node
                                            [`(UnionInject ,_ Bool ,_) #t]
                                            [_ #f]))))
          generated))
  (check-true
   (ormap (lambda (core) (tree-any? core (lambda (node)
                                          (match node
                                            [`(UnionInject ,_ (Record ,_) ,_) #t]
                                            [_ #f]))))
          generated))
  (check-true (ormap (lambda (core) (tree-any? core three-member-union?)) generated))
  (check-true (ormap (lambda (core) (tree-any? core permuted-union-arms?)) generated))
  (check-true (andmap union-types-normal? generated))
  (check-true (> (set-count (list->set generated)) 80)))

(define (if-term then else)
  `(Eliminate (Construct Bool true)
              ((true () -> ,then) (false () -> ,else))))

(define plain-record-join-term
  (if-term '(Rec ((a imm 1)))
           '(Rec ((a imm (Construct Bool true))))))
(define record-imm-join-term
  (if-term `(Rec ((a imm (UnionInject ,U1 Int 1)) (b imm 2)))
           `(Rec ((a imm (UnionInject ,U2 String "s")) (c imm 3)))))
(define record-mut-join-term
  (if-term `(Rec ((a mut (UnionInject ,U1 Int 1))))
           `(Rec ((a mut (UnionInject ,U2 String "s"))))))

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment)
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define-syntax-rule (tagged body ...)
  (parameterize ([current-union-tag-mode #t]) body ...))

(define (type-of core [environment '()])
  (match (type-of/raw core '() '() environment)
    [(list 'ok (list type _row)) type]
    [other other]))

(define (tc? actual expected)
  (tag-compat? actual expected '() equal?))

(define (type-of/in-regions core places owner-points)
  (define ir (build-region-ir core))
  (define owners
    (for/hash ([place (in-list places)])
      (define id (first place))
      (values id (region-at ir (hash-ref owner-points id)))))
  (type-of/raw (annotate-regions core ir)
               places '() '()
               (region-ctx ir '() owners (hash))))

(define (result-of/owned-place core)
  (tagged (type-of/in-regions core '((1 Res)) (hash 1 '()))))

(define (key-of/owned-place core)
  (match (result-of/owned-place core)
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (machine-config core [heap '()] [states '()] [tokens '()] [trace '()])
  `(cfg ,core ,heap ,states ,tokens ,trace))

(define (machine-run config)
  (run-g2 config 200))

(define (machine-steps config)
  (raw-steps-g2 config))

(define (lower-value-result value)
  (define-values (status result) (lower-value value 'racket-cs))
  (check-eq? status 'ok (format "lower-value: ~s" result))
  result)

(define (contains-mutation? core)
  (match core
    [`(Assign ,_ ,_) #t]
    [`(Reassign ,_ ,_) #t]
    [(? list? parts) (ormap contains-mutation? parts)]
    [_ #f]))

(define (contains-runtime-borrow? core)
  (match (peel-node core)
    [`(BorrowRef ,_ ,_ ,_) #t]
    [`(BorrowMutRef ,_ ,_ ,_) #t]
    [_ (and (list? core) (ormap contains-runtime-borrow? core))]))

(define (current-config-row config row)
  (match config
    [`(cfg ,core ,_ ,_ ,_ ,_)
     (if (and (member 'Mutation row) (not (contains-mutation? core)))
         (remove 'Mutation row)
         row)]
    [_ row]))

(define (check-config-run config expected [row '()] [fuel-limit 20])
  (tagged
   (let loop ([current config] [fuel fuel-limit])
     (check-true (config-ok? current '() expected
                             (current-config-row current row))
                 (format "ill-formed intermediate config: ~s" current))
     (if (zero? fuel)
         (fail (format "machine did not finish: ~s" current))
         (match (machine-steps current)
           ['() current]
           [(list next) (loop next (sub1 fuel))]
           [many (fail (format "nondeterministic machine step: ~s" many))])))))

;; 既存の §2.8 machine fixture は実行時 BorrowMutRef を初期 Core に直接書く。
;; place が確保される前は config-ok? が拒否するため、最初に成立する config から
;; 終状態までを検査する。
(define (check-config-run-from-first-valid config expected row)
  (tagged
   (let loop ([current config] [fuel 200] [skipped 0])
     (define current-row (current-config-row current row))
     (cond
       [(config-ok? current '() expected current-row)
        (check-true (positive? skipped)
                    "the helper must skip place-allocation steps")
        (check-true
         (match current
           [`(cfg ,core ,_ ,_ ,_ ,_) (contains-runtime-borrow? core)]
           [_ #f])
         "type recovery must be exercised in the first checked config")
        (check-config-run current expected row 100)]
       [(zero? fuel)
        (fail (format "no well-formed config before machine stopped: ~s" current))]
       [else
        (match (machine-steps current)
          ['() (fail (format "no well-formed config before machine stopped: ~s"
                             current))]
          [(list next) (loop next (sub1 fuel) (add1 skipped))]
          [many (fail (format "nondeterministic machine step: ~s" many))])]))))

(define (steps-ok? core expected row [fuel 200])
  (tagged
   (let loop ([cfg `(cfg ,core () () () ())] [fuel fuel] [initial? #t])
     (define current-row
       (match cfg
         [`(cfg ,current-core ,heap ,_ ,_ ,_)
          (define places
            (derive-places heap '() #:declared (config-declared-types cfg)))
          (and places
               (match (type-of/raw current-core places '() '())
                 [(list 'ok (list _ inferred-row)) inferred-row]
                 [_ #f]))]
         [_ #f]))
     (and current-row
          (or (not initial?) (equal? current-row row))
          (config-ok? cfg '() expected current-row)
          (match (raw-steps-g2 cfg)
            ['() #t]
            [(list next)
             (and (positive? fuel) (loop next (sub1 fuel) #f))]
            [_ #f])))))

(test-case "G2 と G2m は UnionInject と UnionEliminate を受理する"
  (check-true (redex-match? G2 c inject-int))
  (check-true (redex-match? G2 c elim-is))
  (check-true (redex-match? G2m c elim-is)))

(test-case "UnionVal は G2m の値であり、G2 と G2+ は受理しない"
  (define tagged `(UnionVal ,IS Int 1))
  (check-true (redex-match? G2m v tagged))
  (check-false (redex-match? G2 c tagged))
  (check-false (redex-match? G2+ c tagged)))

(test-case "G2m の評価文脈は inject と eliminate の穴を受理する"
  (check-true
   (redex-match? G2m F (term (UnionInject (Union Int String) Int hole))))
  (check-true
   (redex-match? G2m E (term (UnionInject (Union Int String) Int hole))))
  (check-true
   (redex-match? G2m G (term (UnionInject (Union Int String) Int hole))))
  (check-true
   (redex-match? G2m F (term (UnionEliminate hole ((Int i -> i))))))
  (check-true
   (redex-match? G2m E (term (UnionEliminate hole ((Int i -> i))))))
  (check-true
   (redex-match? G2m G (term (UnionEliminate hole ((Int i -> i)))))))

(test-case "fseg は (Payload) を受理する"
  (check-true (redex-match? G2m fp '(a (Payload) 0))))

(test-case "spanful Union Core は G2+ に属し erase と uniquify を保つ"
  (define raw
    '(Let (x Int) 0
       (UnionEliminate (UnionInject (Union Int String) Int 1)
         ((Int x -> x) (String y -> x)))))
  (define spanful (annotate-core raw))
  (check-true (redex-match? G2+ c spanful))
  (check-equal? (erase-core spanful) raw)
  (define branch
    (first (list-ref (peel-node (list-ref (peel-node spanful) 3)) 2)))
  (check-true (span-ok? (branch-span branch)))
  (check-true (span-ok? (ubr-span branch)))
  (check-equal? (erase-core (peel-ubr branch)) '(Int x -> x))
  (define renamed (erase-core (uniquify-binders spanful)))
  (match renamed
    [`(Let (,outer Int) 0
       (UnionEliminate ,_
         ((Int ,inner -> ,inner-body)
          (String ,other -> ,other-body))))
     (check-not-equal? outer inner)
     (check-not-equal? inner other)
     (check-equal? inner inner-body)
     (check-equal? outer other-body)]
    [_ (fail (format "unexpected uniquified core: ~s" renamed))]))

(test-case "core-types-normal? は inject の型を正規化し ubr の型を走査する"
  (check-true (core-types-normal? inject-int))
  (check-true (core-types-normal? elim-is))
  (check-true
   (core-types-normal?
    '(UnionInject (Union (Union Int Bool) String) Int 1)))
  (check-false
   (core-types-normal?
    '(UnionEliminate 1 (((Union (Union Int Bool) String) x -> x))))))

(test-case "構造的な走査は ubr の本体を子として扱い束縛を閉じる"
  (check-equal? (core-children elim-is) (list inject-int 'i 0))
  (check-equal? (core-with-children elim-is (list inject-int 'i 0)) elim-is)
  (check-true (set-empty? (core-free-vars elim-is))))

(test-case "erase-core と inject-g2m は Union Core の形を保つ"
  (check-equal? (erase-core elim-is) elim-is)
  (match (inject-g2m elim-is)
    [`(cfg (Scope () ,core) () () () ())
     (check-equal? core elim-is)]
    [other (fail (format "unexpected injected config: ~s" other))]))

(test-case "tag mode の既定は #t で、新しい構成子を型付けする"
  (check-true (current-union-tag-mode))
  (check-equal? (type-of inject-int) IS)
  (check-equal? (type-of elim-is) 'Int))

(test-case "tag 保存互換：Union は既に tag を持つ部分集合だけを渡す"
  (check-true (tc? U1 U))
  (check-true (tc? 'Never U))
  (check-false (tc? 'Int U))
  (check-false (tc? U 'Int))
  (check-false (tc? U U1)))

(test-case "tag 保存互換：record の imm 欄と関数の変性"
  (check-true (tc? `(Record ((a ,U1 imm))) `(Record ((a ,U imm)))))
  (check-false (tc? '(Record ((a Int imm))) `(Record ((a ,U imm)))))
  (check-false (tc? '(NFn (Int) Int () () () User) nfn-u)))

(test-case "tag 保存互換：借用と Untrusted、Refined の payload"
  (check-true (tc? `(Borrowed ,U1 0) `(Borrowed ,U 0)))
  (check-false (tc? `(BorrowedMut ,U1 0) `(BorrowedMut ,U 0)))
  (check-true (tc? `(Untrusted ,U1) `(Untrusted ,U)))
  (check-false (tc? `(Untrusted Int) `(Untrusted ,U)))
  (check-true (tc? `(Refined ,U1 (Prop p)) `(Refined ,U (Prop p)))))

(test-case "tag の狭まり：Union と Record の構造を保つ"
  (check-true (tag-narrowing? U1 U))
  (check-true (tag-narrowing? 'Never U))
  (check-false (tag-narrowing? 'Int U))
  (check-false (tag-narrowing? 'Int 'Bool))
  (check-true
   (tag-narrowing? `(Record ((a ,U1 mut))) `(Record ((a ,U mut)))))
  (check-false
   (tag-narrowing? `(Record ((a ,U1 mut) (b Int imm)))
                   `(Record ((a ,U mut)))))
  (check-false
   (tag-narrowing? `(Record ((a ,U1 imm))) `(Record ((a ,U mut)))))
  (check-false
   (tag-narrowing? `(Record ((a ,U1 imm opt))) `(Record ((a ,U imm))))))

(test-case "tag の狭まり：NFn、借用、data 型の内側は緩めない"
  (check-false (tag-narrowing? nfn-u1 nfn-u))
  (check-false
   (tag-narrowing? `(Record ((f ,nfn-u1 mut))) `(Record ((f ,nfn-u mut)))))
  (check-false (tag-narrowing? `(Owned ,nfn-u1) `(Owned ,nfn-u)))
  (check-false
   (tag-narrowing? `(Owned (Record ((f (Option ,U1) mut))))
                   `(Owned (Record ((f (Option ,U) mut))))))
  (check-false (tag-narrowing? `(Borrowed ,U1 0) `(Borrowed ,U 0)))
  (check-false
   (tag-narrowing? `(Data Box (,U1)) `(Data Box (,U)))))

(test-case "tag 保存互換：mut 欄と Owned payload は tag の狭まりを求める"
  (check-true (tc? `(Record ((a ,U1 mut))) `(Record ((a ,U mut)))))
  (check-false (tc? '(Record ((a Int mut))) '(Record ((a Bool mut)))))
  (check-true (tc? `(Owned ,U1) `(Owned ,U)))
  (check-false (tc? `(Owned ,nfn-u1) `(Owned ,nfn-u))))

(test-case "UnionInject：成分の inject と正規化"
  (tagged
   (check-equal? (type-of inject-int) (normalize-type IS))
   (check-equal? (type-of '(UnionInject (Union Int (Union Int String)) Int 1))
                 (normalize-type IS))
   (check-equal? (key-of `(UnionInject ,IS Bool (Construct Bool true)))
                 'union-inject-not-member)
   (check-equal? (key-of '(UnionInject Int Int 1)) 'union-inject-not-member)
   (check-not-equal? (key-of `(UnionInject ,IS Int (Construct Bool true))) 'ok)
   (check-equal?
    (type-of '(UnionInject (Union (Option Int) String) (Option Int)
                           (Construct (Option Int) some 1)))
    '(Union (Option Int) String))))

(test-case "UnionEliminate：synth、check、枝検査"
  (tagged
   (check-equal? (type-of elim-is) 'Int)
   (check-equal? (key-of '(UnionEliminate 1 ((Int i -> i)))) 'non-union-eliminate)
   (check-equal? (key-of `(UnionEliminate ,inject-int ((Int i -> i))))
                 'non-exhaustive-union-eliminate)
   (check-equal? (key-of `(UnionEliminate ,inject-int
                            ((Int i -> i) (Int j -> j) (String s -> 0))))
                 'non-exhaustive-union-eliminate)
   (check-equal? (key-of `(UnionEliminate ,inject-int
                            ((Int i -> i) (String s -> (Construct Bool true)))))
                         'type-mismatch)
   (check-equal?
    (type-of '(Let (y const Int)
                (UnionEliminate (UnionInject (Union Int String) Int 1)
                  ((Int i -> i) (String s -> 0)))
                y))
    'Int)
   (check-equal?
    (type-of `(UnionEliminate ,inject-int
                ((Int i -> (Perform (Return boundary Int) 1))
                 (String s -> 0))))
    'Int)))

(test-case "UnionEliminate：余った枝も型付けする"
  (tagged
   (check-equal? (type-of `(UnionEliminate ,inject-int
                             ((Int i -> i) (String s -> 0) (Bool b -> 0))))
                 'Int)
   (check-equal? (key-of `(UnionEliminate ,inject-int
                            ((Int i -> i) (String s -> 0) (Bool b -> (Read b)))))
                 'read-non-borrow)))

(test-case "Owned を直接の成分に持つ Union は入れ子でも拒否する"
  (tagged
   (check-equal? (key-of `(UnionInject (Union Int (Union String (Owned Res))) Int 1))
                 'owned-union-member)
   (check-equal?
    (key-of '(Let (x const (Union Int (Owned Res)))
               (UnionInject (Union Int (Owned Res)) Int 1)
               x))
    'owned-union-member)))

(test-case "Data 型の引数にある Owned 成分の Union も well-formedness 検査が見つける"
  (check-true
   (owned-union-member? '(Data Phantom ((Union Int (Owned Res)))))))

(test-case "Owned を直接の成分に持つ Union は tag mode でも拒否する"
  (check-true (current-union-tag-mode))
  (check-equal? (key-of '(Let (x const (Union Int (Owned Res))) 1 x))
                'owned-union-member)
  (check-equal?
   (key-of '(Let (x const (Union Int (Union String (Owned Res)))) 1 x))
   'owned-union-member))

(test-case "Owned Union の scrutinee は解析前に non-union-eliminate で拒否する"
  (tagged
   (check-equal?
    (key-of '(UnionEliminate (Move u) ((Int i -> 0) (String s -> 0)))
            `((u (Owned ,IS) const)))
    'non-union-eliminate)))

(test-case "tag mode の check 境界は tag の無い値を Union の位置へ入れない"
  (tagged
   (check-not-equal?
    (key-of `(UnionInject (Union (Record ((a ,IS imm))) Bool)
                          (Record ((a ,IS imm)))
                          (Rec ((a imm 1)))))
    'ok)
   (check-not-equal?
    (key-of `(Let (y const ,IS)
                  (UnionEliminate ,inject-int ((Int i -> i) (String s -> 0)))
                  y))
    'ok)))

(test-case "tag 保存の上界"
  (check-equal? (tag-upper-bound 'Never U1) (normalize-type U1))
  (check-equal? (tag-upper-bound U1 'Never) (normalize-type U1))
  (check-equal? (tag-upper-bound U1 U2) (normalize-type U))
  (check-false (tag-upper-bound U1 'Int))
  (check-false (tag-upper-bound 'Int 'Bool))
  (check-equal? (tag-upper-bound 'Int 'Int) 'Int)
  (check-equal?
   (tag-upper-bound `(Record ((a ,U1 imm) (b Int imm)))
                    `(Record ((a ,U2 imm) (c Int imm))))
   (normalize-type `(Record ((a ,U imm)))))
  (check-equal?
   (tag-upper-bound `(Record ((a ,U1 mut))) `(Record ((a ,U2 mut))))
   (normalize-type `(Record ((a ,U mut))))))

(test-case "synth 合流は tag 保存の上界を使い tag の無い値から Union を作らない"
  (tagged
   (check-equal? (key-of plain-record-join-term) 'unmergeable-branch-records)
   (check-equal? (type-of record-imm-join-term)
                 (normalize-type `(Record ((a ,U imm)))))
   (check-equal? (type-of record-mut-join-term)
                 (normalize-type `(Record ((a ,U mut)))))))

(test-case "UnionEliminate の synth は枝の tag 保存の上界を使う"
  (define core
    `(UnionEliminate ,inject-int
       ((Int i -> (UnionInject ,U1 Int 1))
        (String s -> (UnionInject ,U2 String "s")))))
  (tagged
   (check-equal? (type-of core) (normalize-type U))))

(test-case "tag mode の Eliminate と UnionEliminate は枝の借用寿命を合流する"
  (define cores
    (list
     '(Scope (1)
        (Eliminate (Construct Bool true)
          ((true () -> (Borrow 1)) (false () -> (Borrow 1)))))
     '(Scope (1) (Scope (2)
        (Eliminate (Construct Bool true)
          ((true () -> (Borrow 1)) (false () -> (Borrow 2))))))
     `(Scope (1)
        (UnionEliminate (UnionInject ,IS Int 1)
          ((Int i -> (Borrow 1)) (String s -> (Borrow 1)))))
     `(Scope (1) (Scope (2)
        (UnionEliminate (UnionInject ,IS Int 1)
          ((Int i -> (Borrow 1)) (String s -> (Borrow 2))))))))
  (for ([core (in-list cores)])
    (define has-second-place
      (match core [`(Scope (1) (Scope (2) ,_)) #t] [_ #f]))
    (define owner-points (if has-second-place (hash 1 '() 2 '()) (hash 1 '())))
    (define result
      (tagged (type-of/in-regions
               core
               (if has-second-place
                   '((1 Int) (2 Int))
                   '((1 Int)))
               owner-points)))
    (check-equal? (first result) 'ok
                  (format "core: ~s; result: ~s" core result))))

(test-case "tag mode の UnionEliminate は 3 枝の record 借用寿命を一度に合流する"
  (define union-type U)
  (define core
    `(Scope (1)
       (UnionEliminate (UnionInject ,union-type Int 1)
         ((Int i -> (Rec ((a imm (Borrow 1)))))
          (String s -> (Rec ((a imm (Borrow 1)))))
          (Bool b -> (Rec ((a imm (Borrow 1)))))))))
  (define ir (build-region-ir core))
  (define inference
    (tagged
     (typing-inference (annotate-regions core ir)
                       '((1 Res)) '() '()
                       (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))))
  (define result-type (first inference))
  (define merged-region
    (match result-type
      [`(Record ((a (Borrowed Res ,ρ) imm))) ρ]
      [other (error 'union-tag-test "unexpected result type: ~s" other)]))
  (define merge-constraints
    (filter (lambda (constraint)
              (eq? (region-constraint-kind constraint) 'merge))
            (third inference)))
  (check-equal? (length merge-constraints) 3)
  (check-equal? (remove-duplicates
                 (map region-constraint-right merge-constraints))
                (list merged-region)))

(test-case "tag mode の借用枝は内側 owner からの脱出を拒む"
  (define cores
    (list
     '(Scope (1) (Scope (2)
        (Eliminate (Construct Bool true)
          ((true () -> (Borrow 1)) (false () -> (Borrow 2))))))
     `(Scope (1) (Scope (2)
        (UnionEliminate (UnionInject ,IS Int 1)
          ((Int i -> (Borrow 1)) (String s -> (Borrow 2))))))))
  (for ([core (in-list cores)])
    (define result
      (tagged
       (type-of/in-regions core '((1 Int) (2 Int))
                           (hash 1 '() 2 '(0)))))
    (check-equal? (first result) 'fail (format "core: ~s" core))
    (check-equal? (second result) 'borrow-escapes-owner
                  (format "core: ~s; result: ~s" core result))))

(test-case "UnionEliminate と Eliminate の借用 record 合流は同じ Move を拒む"
  (define (record-with-type type eliminate)
    `(Scope (1)
       (Let (record let ,type)
         ,eliminate
         (Let (m const (Owned Res)) (Move 1) 0))))
  (define (record-eliminate)
    '(Eliminate (Construct Bool true)
       ((true () -> (Rec ((a imm (Borrow 1)))))
        (false () -> (Rec ((a imm (Borrow 1))))))))
  (define (record-union-eliminate)
    `(UnionEliminate (UnionInject ,IS Int 1)
       ((Int i -> (Rec ((a imm (Borrow 1)))))
        (String s -> (Rec ((a imm (Borrow 1))))))))
  (define (record-result-type eliminate)
    (define core `(Scope (1) ,eliminate))
    (define ir (build-region-ir core))
    (first
     (tagged
      (typing-inference (annotate-regions core ir)
                        '((1 Res)) '() '()
                        (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))))
  (define (result eliminate)
    (define type (record-result-type eliminate))
    (define core (record-with-type type eliminate))
    (define ir (build-region-ir core))
    (tagged
     (type-of/raw (annotate-regions core ir)
                  '((1 Res)) '() '()
                  (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))))
  (define (result-key result)
    (match result
      [(list 'fail key _node _details ...) key]
      [_ 'ok]))
  (define eliminate-result (result (record-eliminate)))
  (define union-eliminate-result (result (record-union-eliminate)))
  (define eliminate-key (result-key eliminate-result))
  (define union-eliminate-key (result-key union-eliminate-result))
  (tagged
   (check-equal? eliminate-key 'move-borrowed
                 (format "Eliminate: ~s" eliminate-result))
   (check-equal? union-eliminate-key eliminate-key
                 (format "UnionEliminate: ~s" union-eliminate-result))))

(test-case "UnionEliminate は余った枝も借用と所有の検査へ渡す"
  (define (branch-elimination branch-type branch-body other-body)
    `(UnionEliminate u
       ((Int i -> ,(if (eq? branch-type 'Int) branch-body other-body))
        (String s -> ,other-body)
        (Bool b -> ,(if (eq? branch-type 'Bool) branch-body other-body)))))
  (define (with-branch branch-type branch-body other-body)
    `(Scope (1)
       (Let (u const ,IS) ,inject-int
         ,(branch-elimination branch-type branch-body other-body))))
  (define (with-owned-branch branch-type branch-body other-body)
    `(Scope (1)
       (Let (owned const (Owned Res)) (Move 1)
         (Let (u const ,IS) ,inject-int
           ,(branch-elimination branch-type branch-body other-body)))))
  (define unreachable-borrow
    (key-of/owned-place
     (with-branch 'Bool '(Yield (BorrowMut 1) (BorrowMut 1)) '(BorrowMut 1))))
  (define reachable-borrow
    (key-of/owned-place
     (with-branch 'Int '(Yield (BorrowMut 1) (BorrowMut 1)) '(BorrowMut 1))))
  (check-equal? (key-of/owned-place
                 (with-owned-branch 'Int '(Drop (Move owned)) 'unit))
                'ok)
  (check-equal? (key-of/owned-place
                 (with-owned-branch #f '(Drop (Move owned))
                                    '(Drop (Move owned))))
                'ok)
  (check-equal? unreachable-borrow reachable-borrow)
  (check-not-equal? unreachable-borrow 'ok))

(test-case "tag mode の値を渡す境界は暗黙の tag 無し widening を拒否する"
  (define rec-term
    `(Let (r const (Record ((a ,IS imm))))
          (Rec ((a imm (UnionInject ,IS Int 1))))
          (Proj r a)))
  (define assign-term
    `(Let (m mut ,IS) ,inject-int
          (Assign (BorrowMut m) 1)))
  (define bare-let
    `(Let (x const ,IS) 1
          (UnionEliminate x ((Int i -> 0) (String s -> 0)))))
  (define rec-union
    '(Union (Record ((a Int imm) (b Int imm)))
            (Record ((a Int imm) (c Bool imm)))))
  (define union-to-rec
    `(Let (u const ,rec-union)
          (UnionInject ,rec-union
                       (Record ((a Int imm) (b Int imm)))
                       (Rec ((a imm 1) (b imm 2))))
          (Let (r const (Record ((a Int imm)))) u (Proj r a))))
  (check-equal? (type-of rec-term) IS)
  (tagged
   (check-equal? (key-of rec-term) 'ok)
   (check-not-equal? (key-of assign-term) 'ok)
   (check-not-equal? (key-of bare-let) 'ok)
   (check-not-equal? (key-of union-to-rec) 'ok)))

(test-case "Reassign は tag の狭まりを受け入れ、Owned 欄の損失を拒否する"
  (define wide-union (normalize-type U))
  (define narrow-reassign
    `(Let (x mut ,wide-union)
          (UnionInject ,U1 Int 1)
          (Reassign x (UnionInject ,U1 Int 2))))
  (define owned-loss-environment
    '((slot (Record ((y Int imm))) mut)
      (source (Record ((x (Owned Res) imm) (y Int imm))) const)))
  (tagged
   (check-equal? (key-of narrow-reassign) 'ok)
   (check-equal? (key-of '(Reassign slot source) owned-loss-environment)
                 'reassign-type-mismatch)))

(define borrowed-union-core
  '(Scope (1)
     (UnionEliminate (Borrow 1)
                     ((Int i -> (Let (value const Int) (Read i) unit))
                      (String s -> (Let (value const String) (Read s) unit))))))
(define borrowed-union-ir (build-region-ir borrowed-union-core))
(define borrowed-union-Λ
  (region-ctx borrowed-union-ir '()
              (hash 1 (region-at borrowed-union-ir '()))
              (hash)))

(test-case "借用した Union の枝は成分の共有借用を渡す"
  (define result
    (tagged
     (type-of/raw (annotate-regions borrowed-union-core borrowed-union-ir)
                  (list (list 1 IS)) '() '() borrowed-union-Λ)))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

(define borrowed-mut-union-core
  '(Scope (1)
     (UnionEliminate (BorrowMut 1)
                     ((Int i -> (Assign i 7))
                      (String s -> (Assign s "s"))))))
(define borrowed-mut-union-ir (build-region-ir borrowed-mut-union-core))
(define borrowed-mut-union-Λ
  (region-ctx borrowed-mut-union-ir '()
              (hash 1 (region-at borrowed-mut-union-ir '()))
              (hash)))

(test-case "借用した Union の枝は成分の可変借用を渡す"
  (define result
    (tagged
     (type-of/raw (annotate-regions borrowed-mut-union-core
                                    borrowed-mut-union-ir)
                  (list (list 1 IS)) '() '() borrowed-mut-union-Λ)))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

(test-case "UnionInject と UnionEliminate が値を正規化して分岐する"
  (tagged
   (define start (machine-config
                  '(UnionInject (Union Int (Union String Int)) Int 1)))
   (define after-inject (machine-steps start))
   (check-equal? (length after-inject) 1)
   (check-equal? (first after-inject)
                 `(cfg (UnionVal ,(normalize-type IS) Int 1) () () () ()))
   (define finished
     (machine-run
      (machine-config
       `(UnionEliminate (UnionInject ,IS String "s")
          ((Int i -> 1) (String s -> 2))))))
   (check-equal? finished '(cfg 2 () () () ()))
   (check-equal?
    (machine-steps
     (machine-config
      `(UnionEliminate (UnionVal ,(normalize-type IS) Int 1)
         ((String s -> 0)))))
    '())))

(test-case "config-ok? は UnionVal の形と payload token を検査する"
  (define record-type '(Record ((owned (Owned Res) imm))))
  (define normalized-union
    (normalize-type `(Union ,record-type String)))
  (define good-value
    `(UnionVal ,normalized-union ,record-type
               (Rec ((owned imm (OwnedLeaf (tok 0) (resource 1)))))))
  (define bad-tag
    `(UnionVal ,normalized-union Bool (Construct Bool true)))
  (define bad-payload `(UnionVal ,normalized-union ,record-type "s"))
  (define bad-union `(UnionVal Int Int 1))
  (tagged
   (check-true
    (config-ok? (machine-config good-value '() '() '(((tok 0) Available)))
                '() normalized-union '()))
   (check-false
    (config-ok? (machine-config good-value)
                '() normalized-union '()))
   (check-false
    (config-ok? (machine-config bad-tag) '() normalized-union '()))
   (check-false
    (config-ok? (machine-config bad-payload) '() normalized-union '()))
   (check-false
    (config-ok? (machine-config bad-union) '() normalized-union '()))))

(test-case "UnionVal は well-formedness を満たすと型付けされる"
  (define value `(UnionVal ,(normalize-type IS) Int 1))
  (check-equal? (type-of value) (normalize-type IS))
  (tagged
   (check-equal? (type-of value) (normalize-type IS))
   (check-equal? (key-of `(UnionVal ,(normalize-type IS) Bool
                                   (Construct Bool true)))
                 'ill-typed)
   (check-equal? (key-of `(UnionVal ,(normalize-type IS) Int "s"))
                 'ill-typed)))

(test-case "tag mode の repr-ok? は Union の tag と payload を検査する"
  (define normalized (normalize-type IS))
  (tagged
   (check-true (repr-ok? normalized `(PTagged ,(union-tag-code 'Int) 1)))
   (check-false
    (repr-ok? normalized
              `(PTagged ,(union-tag-code 'Bool) (PTagged ,(tag-code 'true)))))
   (check-false (repr-ok? normalized `(PTagged ,(union-tag-code 'Int) "s")))
   (check-false (repr-ok? normalized 1))))

(test-case "UnionVal の lowering と union tag code は型を正規化する"
  (define member-raw '(Record ((a (Union String Int) imm))))
  (define member-normal '(Record ((a (Union Int String) imm))))
  (check-equal? (union-tag-code member-raw)
                (union-tag-code member-normal))
  ;; Typed Core は UnionEliminate の枝型を入口で正規化検査する。
  ;; union-tag-code 内の正規化は、検証済み Core の通常経路では要らない防御である。
  (define non-normal-branch
    '(UnionEliminate
      (UnionInject (Union Int String) Int 1)
      (((Record ((a (Union String Int) imm))) r -> 0))))
  (tagged
   (check-equal? (key-of non-normal-branch) 'non-normal-type))
  (check-not-equal? (union-tag-code '(Record ((|a:b| Int imm))))
                    (union-tag-code '(Record ((ab Int imm)))))
  (check-equal?
   (lower-value-result `(UnionVal ,IS Int 1))
   `(PTagged ,(union-tag-code 'Int) 1))
  (define nested
    (lower-value-result
     '(Rec ((a imm (UnionVal (Union Int String) Int 1))))))
  (check-true
   (tagged
    (repr-ok? (normalize-type `(Union ,member-raw Bool))
              `(PTagged ,(union-tag-code member-normal) ,nested)))))

(test-case "borrowed member の capability は UnionInject、UnionVal、枝選択で保たれる"
  (define member-type '(Borrowed Int (RVar 0)))
  (define union-type `(Union ,member-type String))
  (define injected `(UnionInject ,union-type ,member-type (Borrow 1)))
  (define value `(UnionVal ,(normalize-type union-type) ,member-type
                           (BorrowRef 1 () (RVar 0))))
  (define eliminated
    `(UnionEliminate ,value
       ((,member-type borrowed -> borrowed)
        (String text -> 0))))
  (define Λ (region-ctx #f '() (hash) (hash)))
  (define expected (set '(1)))
  (check-equal? (borrow-token-key Λ injected) expected)
  (check-equal? (borrow-token-key Λ value) expected)
  (check-equal? (borrow-token-key Λ eliminated) expected)
  (check-equal? (capability-field-table Λ injected)
                (capability-field-table Λ value)))

(test-case "BorrowRef の UnionEliminate は payload path を渡す"
  (define union-value `(UnionVal ,(normalize-type IS) Int 17))
  (define config
    (machine-config
     '(UnionEliminate (BorrowRef 0 () 0)
        ((Int i -> (Read i)) (String s -> 0)))
     `((0 ,union-value (declared (Owned ,(normalize-type IS)))))
     '((0 Available))))
  (tagged
   (check-equal? (check-config-run config 'Int)
                 `(cfg 17 ((0 ,union-value (declared (Owned ,(normalize-type IS)))))
                       ((0 Available)) () ()))
   (check-equal? (heap-walk-path union-value '((Payload))) 17)
   (check-equal? (path-lookup `((0 ,union-value)) 0 '((Payload))) 17)
   (check-false (path-lookup '((0 17)) 0 '((Payload))))))

(test-case "BorrowMutRef は UnionVal の payload だけを書き換える"
  (define union-value `(UnionVal ,(normalize-type IS) Int 17))
  (define config
    (machine-config
     '(UnionEliminate (BorrowMutRef 0 () 0)
        ((Int i -> (Assign i 23)) (String s -> (Assign s "changed"))))
     `((0 ,union-value (declared (Owned ,(normalize-type IS)))))
     '((0 Available))))
  (tagged
   (check-equal?
    (check-config-run config 'Unit '(Mutation))
    `(cfg unit ((0 (UnionVal ,(normalize-type IS) Int 23)
                    (declared (Owned ,(normalize-type IS)))))
          ((0 Available)) () ()))
   (check-equal?
    (value-set-path union-value '((Payload)) 23)
    `(UnionVal ,(normalize-type IS) Int 23))
   (check-false (value-set-path 17 '((Payload)) 23))))

(test-case "実行時借用値の回復は config-ok? に限る"
  (tagged
   (for ([borrow (in-list '((BorrowRef 0 () 0)
                            (BorrowMutRef 0 () 0)))])
     (check-equal? (key-of borrow) 'ill-typed)
     (check-false (match (type-of borrow)
                    [`(Borrowed ,_ ,_) #t]
                    [`(BorrowedMut ,_ ,_) #t]
                    [_ #f])))))

(test-case "config-ok? は不正な借用 path と place state を拒否する"
  (define available '((0 Available)))
  (define (int-config path state)
    (machine-config `(Read (BorrowRef 0 ,path 0))
                    '((0 17 (declared (Owned Int)))) state))
  (check-false
   (tagged
    (config-ok? (int-config '((Payload)) available)
     '() 'Int '())))
  (check-true
   (tagged
    (config-ok? (int-config '() available) '() 'Int '())))
  (define union-type (normalize-type IS))
  (define payload-config
    (machine-config '(Read (BorrowRef 0 ((Payload)) 0))
                    `((0 (UnionVal ,union-type String "s")
                         (declared (Owned ,union-type))))
                    available))
  (check-false
   (tagged
    (config-ok? payload-config '() 'Int '())))
  (check-true
   (tagged
    (config-ok? payload-config '() 'String '())))
  (define dropped-config (int-config '() '((0 Dropped))))
  (check-false
   (tagged
    (config-ok? dropped-config '() 'Int '())))
  (check-true
   (tagged
    (config-ok? (int-config '() available) '() 'Int '())))
  (define record-config
    (machine-config '(Read (BorrowRef 0 (missing) 0))
                    '((0 (Rec ((a imm 17)))
                        (declared (Owned (Record ((a Int imm)))))))
                    available))
  (check-false
   (tagged
    (config-ok? record-config '() 'Int '())))
  (check-true
   (tagged
    (config-ok?
     (machine-config '(Read (BorrowRef 0 (a) 0))
                     '((0 (Rec ((a imm 17)))
                         (declared (Owned (Record ((a Int imm)))))))
                     available)
     '() 'Int '()))))

(test-case "Union payload 内の record 欄は ProjBorrowAt から読める"
  (define record-type '(Record ((a Int imm))))
  (define union-type `(Union ,record-type String))
  (define union-value `(UnionVal ,(normalize-type union-type)
                                 ,(normalize-type record-type)
                                 (Rec ((a imm 31)))))
  (define config
    (machine-config
     `(UnionEliminate (BorrowRef 0 () 0)
        ((,record-type record ->
          (Read (ProjBorrowAt 0 (Own 0 ((Payload) a)) record a)))
         (String text -> 0)))
     `((0 ,union-value)) '((0 Available))))
  (tagged (check-equal? (machine-run config) `(cfg 31 ((0 ,union-value))
                                                  ((0 Available)) () ()))))

(test-case "config-ok? は宣言欄と constructor 欄から借用型を回復する"
  (define wide (normalize-type U))
  (define narrow (normalize-type U1))
  (define record-type `(Record ((u ,wide imm))))
  (define record-value
    `(Rec ((u imm (UnionVal ,narrow Int 17)))))
  (define record-config
    (machine-config
     '(Read (BorrowRef 0 (u (Payload)) 0))
     `((0 ,record-value (declared (Owned ,record-type))))
     '((0 Available))))
  (check-equal?
   (check-config-run record-config 'Int)
   `(cfg 17 ((0 ,record-value (declared (Owned ,record-type))))
         ((0 Available)) () ()))
  (define list-value
    '(Construct (List Int) cons 1 (Construct (List Int) nil)))
  (define list-config
    (machine-config
     '(Read (BorrowRef 0 (1) 0))
     `((0 ,list-value (declared (Owned (List Int)))))
     '((0 Available))))
  (check-equal?
   (check-config-run list-config '(List Int))
   `(cfg (Construct (List Int) nil)
         ((0 ,list-value (declared (Owned (List Int)))))
         ((0 Available)) () ())))

(test-case "UnionVal の token walker は payload を一度だけ辿る"
  (define record-type '(Record ((a (Owned Res) imm))))
  (define union-type `(Union ,record-type String))
  (define value `(UnionVal ,(normalize-type union-type)
                           ,(normalize-type record-type)
                           (Rec ((a imm (OwnedLeaf (tok 9) (resource 4)))))))
  (check-equal? (collect-tokens value) '((tok 9)))
  (check-true (leaf-positions-ok? value))
  (check-equal? (walk-owned-leaves value) '(((tok 9) ((Payload) a))))
  (check-equal? (walk-owned-leaves-for-drop value)
                '(((tok 9) ((Payload) a))))
  (check-true (contains-owned-leaf? value)))

(test-case "UnionEliminate 後の Drop は payload token を一度だけ Dropped にする"
  (define record-type '(Record ((a (Owned Res) imm))))
  (define union-type `(Union ,record-type String))
  (define value `(UnionVal ,(normalize-type union-type)
                           ,(normalize-type record-type)
                           (Rec ((a imm (OwnedLeaf (tok 12) (resource 4)))))))
  (define config
    (machine-config
     `(UnionEliminate ,value
        ((,record-type record -> (Drop (Proj record a)))
         (String text -> unit)))
     '() '() '(((tok 12) Available))))
  (check-equal? (machine-run config)
                '(cfg unit () () (((tok 12) Dropped)) ())))

(test-case "UnionInject と値の UnionEliminate の全中間 config が config-ok? を満たす"
  (define injected-config
    (machine-config `(UnionInject (Union Int (Union String Int)) Int 1)))
  (define eliminated-config
    (machine-config
     `(UnionEliminate ,inject-int ((Int i -> i) (String s -> 0)))))
  (check-equal?
   (check-config-run injected-config (normalize-type IS))
   `(cfg (UnionVal ,(normalize-type IS) Int 1) () () () ()))
  (check-equal?
   (check-config-run eliminated-config 'Int)
   '(cfg 1 () () () ())))

(test-case "§2.8：狭い τ_U を const へ渡し、余った枝で消費する"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define narrow (normalize-type '(Union Int Bool)))
  (check-true
   (steps-ok?
    `(Let (x const ,wide) (UnionInject ,narrow Int 1)
       (UnionEliminate x ((Int i -> 0) (String s -> 0) (Bool b -> 0))))
    'Int '())))

(test-case "§2.8：互いに合わない狭い Union を If の枝に置く"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define left (normalize-type '(Union Int Bool)))
  (define right (normalize-type '(Union String Bool)))
  (check-true
   (steps-ok?
    `(Let (x const ,wide) (UnionInject ,left Int 1)
       (Let (y const ,wide) (UnionInject ,right String "s")
         (Let (z const ,wide)
              (Eliminate (Construct Bool true)
                ((true () -> x) (false () -> y)))
           (UnionEliminate z
             ((Int i -> 0) (String s -> 0) (Bool b -> 0))))))
    'Int '())))

(test-case "tagged Union と wide Union の If 合流を再型付けできる"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define narrow (normalize-type '(Union Int Bool)))
  (define core
    `(Eliminate (Construct Bool true)
       ((true () -> (UnionInject ,narrow Int 7))
        (false () -> (UnionInject ,wide Int 8)))))
  (check-equal? (tagged (type-of core)) wide)
  (check-true (steps-ok? core wide '())))

(test-case "record の imm 欄で狭い Union を合流し、残余欄を落とす"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define left (normalize-type '(Union Int Bool)))
  (define right (normalize-type '(Union String Bool)))
  (define core
    (if-term `(Rec ((a imm (UnionInject ,left Int 1)) (b imm 2)))
             `(Rec ((a imm (UnionInject ,right String "s")) (c imm 3)))))
  (check-equal? (tagged (type-of core))
                (normalize-type `(Record ((a ,wide imm)))))
  (check-true
   (steps-ok? core (normalize-type `(Record ((a ,wide imm)))) '())))

(test-case "R-LetMutB は slot の宣言型を記録する"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define narrow (normalize-type '(Union Int Bool)))
  (define value `(UnionVal ,narrow Int 1))
  (define start
    (machine-config `(Scope () (Let (m mut ,wide) ,value 0))))
  (check-equal?
   (machine-steps start)
   (list `(cfg (Scope (0) 0)
                ((0 ,value (declared ,wide)))
                ((0 Available)) () ()))))

(test-case "R-LetOwned と R-LetOwnedB は束縛の宣言型を記録する"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define narrow (normalize-type '(Union Int Bool)))
  (define value `(UnionVal ,narrow Int 1))
  (for ([binding (in-list `((o (Owned ,wide))
                            (o const (Owned ,wide))))])
    (define start
      (machine-config `(Scope () (Let ,binding ,value 0))))
    (check-equal?
     (machine-steps start)
     (list `(cfg (Scope (0) 0)
                  ((0 ,value (declared (Owned ,wide))))
                  ((0 Available)) () ())))))

(test-case "Owned place の Ξ と Move は記録した広い Union 型を使う"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define narrow (normalize-type '(Union Int Bool)))
  (define value `(UnionVal ,narrow Int 1))
  (for ([binding (in-list `((o (Owned ,wide))
                            (o const (Owned ,wide))))])
    (define start
      (machine-config `(Scope () (Let ,binding ,value (Move o)))))
    (define next (first (machine-steps start)))
    (define heap (match next [`(cfg ,_ ,heap ,_ ,_ ,_) heap]))
    (define declared (config-declared-types next))
    (define places
      (tagged (derive-places heap '() #:declared declared)))
    (check-equal? declared `((0 (Owned ,wide))))
    (check-equal? places `((0 ,wide)))
    (check-equal? (tagged (type-of/raw '(Move 0) places '() '()))
                  `(ok ((Owned ,wide) (Own))))
    (tagged
     (check-true (config-ok? next '() `(Owned ,wide) '(Own))))))

(test-case "R-LetMutB の後も narrow な UnionVal を wide slot に再代入できる"
  (define wide (normalize-type '(Union Int (Union String Bool))))
  (define narrow (normalize-type '(Union Int Bool)))
  (check-true
   (steps-ok?
    `(Scope ()
       (Let (m mut ,wide) (UnionInject ,narrow Int 1)
         (Reassign m (UnionInject ,wide Bool (Construct Bool true)))))
    'Unit '(Mutation))))

(test-case "const alias を mut binding へ渡した後も wide slot に再代入できる"
  (define wide (normalize-type U))
  (define narrow (normalize-type U1))
  (check-true
   (steps-ok?
    `(Scope ()
       (Let (x const ,wide) (UnionInject ,narrow Int 1)
         (Let (m mut ,wide) x
           (Reassign m (UnionInject ,wide Bool (Construct Bool true))))))
    'Unit '(Mutation))))

(test-case "config-ok? は heap 値を記録した宣言型と照合する"
  (define wide (normalize-type U))
  (define narrow (normalize-type U1))
  (define (config-with value declared)
    (machine-config 1 `((0 ,value (declared ,declared))) '((0 Available))))
  (tagged
   (check-true (config-ok? (config-with 2 'Int) '() 'Int '()))
   (check-false (config-ok? (config-with "s" 'Int) '() 'Int '()))
   (check-true
    (config-ok? (config-with `(UnionVal ,narrow Int 1) wide) '() 'Int '()))
   (check-false
    (config-ok? (config-with `(UnionVal ,wide Int 1) narrow) '() 'Int '()))
   (check-false
    (config-ok? (config-with `(UnionVal ,narrow Int 1) 'Int) '() 'Int '()))))

(test-case "Assign、Reassign、BorrowMutRef の書込みは宣言型 metadata を保つ"
  (define record-type '(Record ((a Int mut))))
  (define record '(Rec ((a mut 1))))
  (define wide (normalize-type U))
  (define narrow (normalize-type U1))
  (define union-type (normalize-type `(Union ,record-type String)))
  (define union-value
    `(UnionVal ,union-type ,record-type (Rec ((a mut 1)))))
  (define assigned
    (machine-run
     `(cfg (Assign (BorrowMutRef 0 (a) 0) 2)
           ((0 ,record (declared ,record-type))) ((0 Available)) () ())))
  (define union-written
    (machine-run
     `(cfg (Assign (BorrowMutRef 0 ((Payload) a) 0) 3)
           ((0 ,union-value (declared (Owned ,union-type))))
           ((0 Available)) () ())))
  (define reassigned
    (machine-run
     `(cfg (Reassign (MutSlot 0) (UnionInject ,wide Int 5))
           ((0 (UnionVal ,narrow Int 1) (declared ,wide)))
           ((0 Available)) () ())))
  (check-equal? assigned
                `(cfg unit ((0 (Rec ((a mut 2))) (declared ,record-type)))
                      ((0 Available)) () ()))
  (check-equal? union-written
                `(cfg unit
                      ((0 (UnionVal ,union-type ,record-type
                                    (Rec ((a mut 3))))
                          (declared (Owned ,union-type))))
                      ((0 Available)) () ()))
  (check-equal? (config-declared-types reassigned) `((0 ,wide))))

(test-case "const alias から Assign で狭い値を書き、別の成分へ書き換えて分岐する"
  (define wide (normalize-type U))
  (define core
    `(Scope ()
       (Let (source const ,wide) (UnionInject ,U1 Int 1)
         (Let (slot mut ,wide) (UnionInject ,wide String "initial")
           (Let (first-write const Unit)
                (Assign (BorrowMutRef 0 () 0) source)
             (Let (second-write const Unit)
                  (Assign (BorrowMutRef 0 () 0)
                          (UnionInject ,wide Bool (Construct Bool true)))
               (UnionEliminate (MutSlot 0)
                 ((Int i -> 0) (String s -> 1) (Bool b -> 2)))))))))
  (define final
    (check-config-run-from-first-valid (machine-config core) 'Int '(Mutation)))
  (check-equal? (match final [`(cfg ,result ,_ ,_ ,_ ,_) result]) 2)
  (check-equal? (config-declared-types final) `((0 ,wide)))
  (check-equal?
   (second (first (match final [`(cfg ,_ ,heap ,_ ,_ ,_) heap])))
   `(UnionVal ,wide Bool (Construct Bool true))))

(test-case "mut 欄の Union 合流は slot の宣言型を保って書換え後に分岐する"
  (define wide (normalize-type U))
  (define left (normalize-type U1))
  (define right (normalize-type U2))
  (define record-type `(Record ((a ,wide mut))))
  (define join
    (if-term `(Rec ((a mut (UnionInject ,left Int 1))))
             `(Rec ((a mut (UnionInject ,right String "s"))))))
  (define read-member
    '(UnionEliminate (Proj (MutSlot 0) a)
       ((Int i -> 0) (String s -> 1) (Bool b -> 2))))
  (define const-final
    (tagged
     (machine-run
      (machine-config `(Let (record const ,record-type) ,join
                         (UnionEliminate (Proj record a)
                           ((Int i -> 0) (String s -> 1) (Bool b -> 2))))))))
  (check-equal? (match const-final [`(cfg ,result ,_ ,_ ,_ ,_) result]) 0)
  (define mut-core
    `(Scope ()
       (Let (record mut ,record-type) ,join
         (Let (written const Unit)
              (Assign (BorrowMutRef 0 (a) 0)
                      (UnionInject ,wide String "written"))
           ,read-member))))
  (define mut-final
    (check-config-run-from-first-valid
     (machine-config mut-core) 'Int '(Mutation)))
  (check-equal? (match mut-final [`(cfg ,result ,_ ,_ ,_ ,_) result]) 1)
  (check-equal? (config-declared-types mut-final) `((0 ,record-type)))
  (check-equal?
   (second (first (match mut-final [`(cfg ,_ ,heap ,_ ,_ ,_) heap])))
   `(Rec ((a mut (UnionVal ,wide String "written"))))))

(test-case "Owned Union と Owned record の BorrowMutRef 書込みは宣言型を保つ"
  (define wide (normalize-type U))
  (define union-value `(UnionInject ,U1 Int 1))
  (define record-type `(Record ((a ,wide mut))))
  (define record-value `(Rec ((a mut ,union-value))))
  (define cases
    (list
     (list `(Owned ,wide) wide union-value '()
           `(UnionInject ,wide String "written")
           `(UnionVal ,wide String "written"))
     (list `(Owned ,record-type) record-type record-value '(a)
           `(UnionInject ,wide String "written")
           `(Rec ((a mut (UnionVal ,wide String "written")))))))
  (for ([case (in-list cases)])
    (match-define
      (list declared-type source-type value path replacement final-value)
      case)
    (define core
      `(Scope ()
         (Let (source const ,source-type) ,value
           (Let (owned const ,declared-type) source
             (Let (written const Unit)
                  (Assign (BorrowMutRef 0 ,path 0) ,replacement)
               unit)))))
    (define config
      (check-config-run-from-first-valid
       (machine-config core) 'Unit '(Mutation)))
    (check-equal?
     (match config [`(cfg ,result ,_ ,_ ,_ ,_) result])
     'unit)
    (check-equal? (config-declared-types config) `((0 ,declared-type)))
    (check-equal?
     (second (first (match config [`(cfg ,_ ,heap ,_ ,_ ,_) heap])))
     final-value)))

(test-case "R-LetOwned と R-LetOwnedB の後に BorrowMutRef を型回復する"
  (define record-type '(Record ((a Int mut))))
  (define record '(Rec ((a mut 1))))
  (for ([binding (in-list
                  (list `(owned (Owned ,record-type))
                        `(owned const (Owned ,record-type))))])
    (define start
      (machine-config
       `(Scope ()
          (Let ,binding ,record
            (Assign (BorrowMutRef 0 (a) 0) 2)))))
    (define after-allocation
      (match (tagged (machine-steps start))
        [(list next) next]
        [steps (fail (format "expected one place-allocation step: ~s" steps))]))
    (check-equal? (config-declared-types after-allocation)
                  `((0 (Owned ,record-type))))
    (define final
      (check-config-run after-allocation 'Unit '(Mutation)))
    (check-equal? (config-declared-types final)
                  `((0 (Owned ,record-type))))
    (check-equal?
     (second (first (match final [`(cfg ,_ ,heap ,_ ,_ ,_) heap])))
     '(Rec ((a mut 2))))))

(test-case "Scope 後も stale heap entry と一緒に宣言型 metadata が残る"
  (define final
    (machine-run (machine-config '(Scope () (Let (m mut Int) 1 0)))))
  (check-equal? (config-declared-types final) '((0 Int)))
  (check-equal? (third (first (match final [`(cfg ,_ ,heap ,_ ,_ ,_) heap])))
                '(declared Int)))

(test-case "derive-places は tag mode で宣言型を読む"
  (define heap '((0 (resource 4) (declared String))))
  (check-equal? (derive-places heap '() #:declared '((0 String)))
                '((0 String))))

(test-case "heap の宣言型 metadata は値、token、借用として走査されない"
  (define value `(Rec ((owned imm (OwnedLeaf (tok 8) (resource 9))))))
  (define value-type '(Record ((owned (Owned Res) imm))))
  (define plain
    `(cfg unit ((0 ,value)) ((0 Available)) (((tok 8) Available)) ()))
  (define recorded
    `(cfg unit ((0 ,value (declared ,value-type)))
          ((0 Available)) (((tok 8) Available)) ()))
  (define borrow-core
    '(Scope (0) (Assign (BorrowMutRef 0 () 1)
                        (Read (BorrowRef 0 () 0)))))
  (define borrowed-value '(BorrowRef 0 () 0))
  (define plain-borrow
    `(cfg ,borrow-core ((0 ,borrowed-value)) ((0 Available)) () ()))
  (define recorded-borrow
    `(cfg ,borrow-core ((0 ,borrowed-value (declared Int)))
          ((0 Available)) () ()))
  (check-equal? (fresh-token plain) '(tok 9))
  (check-equal? (fresh-token recorded) '(tok 9))
  (check-equal? (collect-tokens (second (first (third recorded))))
                '((tok 8)))
  (tagged
   (check-true (config-ok? plain '() 'Unit '()))
   (check-true (config-ok? recorded '() 'Unit '())))
  (check-true (pair? (live-borrows plain-borrow)))
  (check-equal? (live-borrows plain-borrow)
                (live-borrows recorded-borrow))
  (check-equal? (check-mut-exclusive plain-borrow)
                (check-mut-exclusive recorded-borrow)))

(test-case "tag-types-upper-bound は文脈を取らずに上界を返す"
  (check-equal? (tag-types-upper-bound (list U1 U2)) (normalize-type U))
  (check-equal? (tag-types-upper-bound '(Never Int)) 'Int)
  (check-equal?
   (tag-types-upper-bound
    '((Record ((a Int imm) (b Bool imm)))
      (Record ((a Int imm) (c String imm)))))
   '(Record ((a Int imm))))
  (check-equal?
   (tag-types-upper-bound
    `((Record ((a Int imm) (b ,U1 imm)))
      (Record ((a Int imm) (b ,U2 imm)))))
   `(Record ((a Int imm) (b ,(normalize-type U) imm))))
  (check-equal?
   (tag-types-upper-bound '(Int String))
   (tag-bound-failure 'type-mismatch '(Int String)))
  (check-equal?
   (tag-types-upper-bound '((Record ((a Int imm))) Int))
   (tag-bound-failure 'incompatible-branch-types '()))
  (check-equal?
   (tag-types-upper-bound
    '((Record ((a Int imm) (b Int imm)))
      (Record ((a Int imm) (b String imm)))))
   (tag-bound-failure 'unmergeable-branch-records '())))

;; P2m2b spec §4。elaborate が生成する形（全ての枝を同じ Union へ inject した形）で、
;; tag mode の Core が枝の借用の寿命を合わせる。
(test-case "同じ Union へ inject した枝の借用寿命を tag mode で合流する"
  (define bool-core
    `(Scope (1) (Scope (2)
       (Eliminate (Construct Bool true)
         ((true () -> (Rec ((r imm (Borrow 1))
                            (u imm (UnionInject ,IS Int 1)))))
          (false () -> (Rec ((r imm (Borrow 2))
                             (u imm (UnionInject ,IS String "s")))))))))
  )
  (define option-core
    `(Scope (1) (Scope (2)
       (Eliminate (Construct (Option Int) some 1)
         ((some (y) -> (Rec ((r imm (Borrow 1))
                             (u imm (UnionInject ,IS Int y)))))
          (none () -> (Rec ((r imm (Borrow 2))
                            (u imm (UnionInject ,IS String "s")))))))))
  )
  (for ([core (list bool-core option-core)])
    (define result
      (tagged (type-of/in-regions core '((1 Int) (2 Int))
                                  (hash 1 '() 2 '()))))
    (check-equal? (first result) 'ok
                  (format "core: ~s; result: ~s" core result))))

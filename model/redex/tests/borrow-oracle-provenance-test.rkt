#lang racket

(require rackunit
         redex/reduction-semantics
         "../borrow-oracle.rkt"
         "../machine.rkt")

(test-case "既知の置換規則と非置換規則を仕分ける"
  (check-equal? (rule-bucket 'R-LetOwnedB) 'substituting)
  (check-equal? (rule-bucket 'R-EliminateRef) 'substituting)
  (check-equal? (rule-bucket 'R-EliminateMutRef) 'substituting)
  (check-equal? (rule-bucket 'R-Borrow) 'non-substituting)
  (check-equal? (rule-bucket 'R-Assign) 'non-substituting))

(test-case "規則名集合の全要素を未知扱いしない"
  (check-true
   (for/and ([name (in-list (reduction-relation->rule-names -->g2/rules))])
     (not (eq? (rule-bucket (if (string? name)
                                (string->symbol name)
                                name))
               'unknown)))))

(test-case "未知の規則名は unknown になる"
  (check-equal? (rule-bucket 'R-NotARule) 'unknown))

(test-case "未知の規則を渡すと provenance-extend は fail を返す"
  (check-equal? (provenance-extend (empty-provenance) 'R-NotARule
                                   '(cfg unit () () () ())
                                   '(cfg unit () () () ()))
                'fail))

(test-case "R-LetOwnedB は H の増分から fresh place を取る"
  (define pre
    '(cfg (Scope () (Let (x let (Owned Res)) (resource 1) (Read x)))
          () () () ()))
  (define post
    '(cfg (Scope (0) (Read 0)) ((0 (resource 1))) ((0 Available)) () ()))
  (define prov (provenance-extend (empty-provenance) 'R-LetOwnedB pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'x) '(0)))

(test-case "H の増分が 2 件なら fail を返す"
  (define pre
    '(cfg (Scope () (Let (x let (Owned Res)) (resource 1) (Read x)))
          () () () ()))
  (define post
    '(cfg (Scope (0 1) (Read 0))
          ((0 (resource 1)) (1 (resource 2)))
          ((0 Available) (1 Available)) () ()))
  (check-equal? (provenance-extend (empty-provenance) 'R-LetOwnedB pre post)
                'fail))

(test-case "H には増えたが Ω に増えていなければ fail を返す"
  (define pre
    '(cfg (Scope () (Let (x let (Owned Res)) (resource 1) (Read x)))
          () () () ()))
  (define post
    '(cfg (Scope (0) (Read 0)) ((0 (resource 1))) () () ()))
  (check-equal? (provenance-extend (empty-provenance) 'R-LetOwnedB pre post)
                'fail))

(test-case "R-LetB は借用値の束縛を記録する"
  (define pre
    '(cfg (Scope (0) (Let (y let (Borrowed Res (RVar 0)))
                       (BorrowRef 0 () (RVar 0))
                       (Read y)))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 () (RVar 0))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define prov (provenance-extend (empty-provenance) 'R-LetB pre post))
  (check-equal? (resolve-designator prov 'y) '(0)))

(test-case "place は自分自身へ解ける"
  (check-equal? (resolve-designator (empty-provenance) 3) '(3)))

(test-case "未記録の記号は空 list へ解ける"
  (check-equal? (resolve-designator (empty-provenance) 'z) '()))

(test-case "同じ記号が二度束縛されたら両方を保つ"
  (define pre-1
    '(cfg (Scope (0) (Let (y let (Borrowed Res (RVar 0)))
                       (BorrowRef 0 () (RVar 0)) (Read y)))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post-1
    '(cfg (Scope (0) (Read (BorrowRef 0 () (RVar 0))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define pre-2
    '(cfg (Scope (0 1) (Let (y let (Borrowed Res (RVar 0)))
                         (BorrowRef 1 () (RVar 0)) (Read y)))
          ((0 (resource 1)) (1 (resource 2)))
          ((0 Available) (1 Available)) () ()))
  (define post-2
    '(cfg (Scope (0 1) (Read (BorrowRef 1 () (RVar 0))))
          ((0 (resource 1)) (1 (resource 2)))
          ((0 Available) (1 Available)) () ()))
  (define prov
    (provenance-extend
     (provenance-extend (empty-provenance) 'R-LetB pre-1 post-1)
     'R-LetB pre-2 post-2))
  (check-equal? (sort (resolve-designator prov 'y) <) '(0 1)))

(test-case "R-EliminateRef は未使用の束縛子も位置へ対応づける"
  (define pre
    '(cfg (Scope (0) (Eliminate (BorrowRef 0 () (RVar 0))
                                ((KA (a b) -> (Read a))
                                 (KB (b c) -> (Pair (Read b) (Read c))))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 (0) (RVar 0))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define prov (provenance-extend (empty-provenance) 'R-EliminateRef pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'a) '(0))
  (check-equal? (resolve-designator prov 'b) '(0)))

(test-case "R-EliminateRef は同じ arity の候補を多価へ合併する"
  (define pre
    '(cfg (Scope (0) (Eliminate (BorrowRef 0 () (RVar 0))
                                ((KA (a) -> (Read a))
                                 (KB (b) -> (Read b)))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 (0) (RVar 0))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define prov (provenance-extend (empty-provenance) 'R-EliminateRef pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'a) '(0))
  (check-equal? (resolve-designator prov 'b) '(0)))

(test-case "R-EliminateRef は arity が一致する枝が無ければ fail を返す"
  (define pre
    '(cfg (Scope (0) (Eliminate (BorrowRef 0 () (RVar 0))
                                ((KA (a b) -> (Pair (Read a) (Read b))))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 (0) (RVar 0))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (check-equal? (provenance-extend (empty-provenance) 'R-EliminateRef pre post)
                'fail))

(test-case "R-EliminateRef は arity 0 の候補を空の対応として受理する"
  (define pre
    '(cfg (Eliminate (BorrowRef 0 () (RVar 0))
                     ((true () -> 0)
                      (false () -> 0)))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg 0 ((0 (resource 1))) ((0 Available)) () ()))
  (check-true
   (provenance?
    (provenance-extend (empty-provenance) 'R-EliminateRef pre post))))

(test-case "R-EliminateRef は同じ arity の Result 候補を合併する"
  (define pre
    '(cfg (Eliminate (BorrowRef 0 () (RVar 0))
                     ((ok (left) -> (Read left))
                      (ng (right) -> (Read right))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Read (BorrowRef 0 (0) (RVar 0)))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define prov (provenance-extend (empty-provenance) 'R-EliminateRef pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'left) '(0))
  (check-equal? (resolve-designator prov 'right) '(0)))

(test-case "R-Eliminate は同じ K の枝が二つなら fail を返す"
  (define pre
    '(cfg (Scope (0) (Eliminate (Construct Res KA (BorrowRef 0 () (RVar 0)))
                                ((KA (a) -> (Read a))
                                 (KA (b) -> (Read b)))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (define post
    '(cfg (Scope (0) (Read (BorrowRef 0 () (RVar 0))))
          ((0 (resource 1))) ((0 Available)) () ()))
  (check-equal? (provenance-extend (empty-provenance) 'R-Eliminate pre post)
                'fail))

(test-case "R-HandleReturn は handler 本体と contractum から payload を復元する"
  (define pre
    '(cfg (Handle (Return answer Int)
                  (x -> (Read x))
                  (Perform (Return answer Int) 7))
          () ((7 Available)) () ()))
  (define post
    '(cfg (Read 7) () ((7 Available)) () ()))
  (define prov
    (provenance-extend (empty-provenance) 'R-HandleReturn pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'x) '(7)))

(test-case "実機の R-Eliminate 遷移から provenance を取る"
  (define pre
    '(cfg (Eliminate (Construct (List Int) cons 0 1)
                     ((nil () -> 0)
                      (cons (head tail) -> (Read head))))
          ((0 (resource 1)) (1 (resource 2)))
          ((0 Available) (1 Available)) () ()))
  (define step
    (for/first ([candidate (in-list (raw-steps-g2/named pre))]
                #:when (eq? (first candidate) 'R-Eliminate))
      candidate))
  (check-not-false step)
  (define post (second step))
  (define prov
    (provenance-extend (empty-provenance) (first step) pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'head) '(0))
  (check-equal? (resolve-designator prov 'tail) '(1)))

(test-case "実機の R-EliminateRef 遷移から provenance を取る"
  (define pre
    '(cfg (Eliminate (BorrowRef 0 () (RVar 0))
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Rec ((a imm (Read head))
                                  (b imm (Read tail)))))))
          ((0 (Construct (List Int) cons 7
                         (Construct (List Int) nil))))
          ((0 Available)) () ()))
  (define step
    (for/first ([candidate (in-list (raw-steps-g2/named pre))]
                #:when (eq? (first candidate) 'R-EliminateRef))
      candidate))
  (check-not-false step)
  (define post (second step))
  (define prov
    (provenance-extend (empty-provenance) (first step) pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'head) '(0))
  (check-equal? (resolve-designator prov 'tail) '(0)))

(test-case "実機の R-EliminateMutRef 遷移から provenance を取る"
  (define pre
    '(cfg (Eliminate (BorrowMutRef 0 () (RVar 0))
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Rec ((a imm (Read head))
                                  (b imm (Read tail)))))))
          ((0 (Construct (List Int) cons 7
                         (Construct (List Int) nil))))
          ((0 Available)) () ()))
  (define step
    (for/first ([candidate (in-list (raw-steps-g2/named pre))]
                #:when (eq? (first candidate) 'R-EliminateMutRef))
      candidate))
  (check-not-false step)
  (define post (second step))
  (define prov
    (provenance-extend (empty-provenance) (first step) pre post))
  (check-true (provenance? prov))
  (check-equal? (resolve-designator prov 'head) '(0))
  (check-equal? (resolve-designator prov 'tail) '(0)))

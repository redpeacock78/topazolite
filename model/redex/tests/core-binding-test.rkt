#lang racket

(require rackunit
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../core-binding.rkt"
         "../borrow-oracle.rkt"
         "../region.rkt")

(test-case "置換は record label を変えず field の変数だけを置き換える"
  (check-equal?
   (raw-subst* (term (Proj (Rec ((other imm other))) other)) '(other) '(2))
   (term (Proj (Rec ((other imm 2))) other))))

(test-case "置換は data 名と構成子名を変えず field の変数だけを置き換える"
  (check-equal?
   (raw-subst* (term (Construct (Data Box ()) Box Box)) '(Box) '(1))
   (term (Construct (Data Box ()) Box 1))))

(test-case "Let の束縛する式は外側の置換を受け、body は shadow する"
  (check-equal?
   (raw-subst* (term (Let (x const Int) x x)) '(x) '(5))
   (term (Let (x const Int) 5 x)))
  (check-equal? (raw-free-vars (term (Let (x const Int) x 1))) (set 'x)))

(test-case "捕獲回避は value の自由変数を保ち、binder を «N» で改名する"
  (define result
    (raw-subst* (term (Lam User g (z) (Apply y z))) '(y)
                (list (term (Lam User h () z)))))
  (match result
    [`(Lam User g (,z2) (Apply (Lam User h () z) ,z3))
     (check-equal? z2 z3)
     (check-not-equal? z2 'z)
     (check-equal? (normalize-binder z2) 'z)]
    [other (fail (format "捕獲回避の結果: ~s" other))]))

(test-case "捕獲回避の fresh name は body の label と value の全記号を避ける"
  (match (raw-subst* '(Lam User g (z) (Proj (Rec ((z«1» imm y))) z«1»))
                     '(y) '(z))
    [`(Lam User g (,z2) (Proj (Rec ((z«1» imm z))) z«1»))
     (check-false (memq z2 '(z z«1»)))]
    [other (fail (format "label と衝突しない改名: ~s" other))]))

(test-case "Recur の f は body と continuation、仮引数は body だけを束縛する"
  (check-equal?
   (raw-free-vars (term (Recur loop-id f (n) (Apply f n) (Apply f k))))
   (set 'k))
  (match (raw-subst* (term (Recur loop-id f (n) (Apply f k) (Apply f k)))
                     '(k) (list (term f)))
    [`(Recur loop-id ,f1 (n) (Apply ,f2 f) (Apply ,f3 f))
     (check-equal? f1 f2)
     (check-equal? f1 f3)
     (check-not-equal? f1 'f)]
    [other (fail (format "Recur の改名: ~s" other))]))

(test-case "同時置換で挿入した値を別の置換対象として再走査しない"
  (define replacements (list (term y) 1))
  (check-equal?
   (raw-subst* (term (Recur loop-id f (n) (Apply x y) 0)) '(x y) replacements)
   (term (Recur loop-id f (n) (Apply y 1) 0)))
  (check-equal?
   (raw-subst* (term (Lam User g () (Apply x y))) '(x y) replacements)
   (term (Lam User g () (Apply y 1))))
  (check-equal?
   (raw-subst* (term (Let (z const Int) 0 (Apply x y))) '(x y) replacements)
   (term (Let (z const Int) 0 (Apply y 1)))))

(test-case "注釈付き Data 枝の binder scope と scrutinee は分離される"
  (define eliminate
    (term (EliminateAt s
                       ((K (y) (7) -> (Apply y s))))))
  (check-equal?
   (raw-subst* eliminate '(s) (list (term q)))
   (term (EliminateAt q
                      ((K (y) (7) -> (Apply y q))))))
  (check-equal?
   (raw-subst* eliminate '(y) (list (term q)))
   eliminate)
  (check-equal? (raw-free-vars eliminate) (set 's))
  (check-equal?
   (raw-free-vars eliminate)
   (core-free-vars eliminate)))

(test-case "注釈付き Union 枝の binder scope と scrutinee は分離される"
  (define eliminate
    (term (UnionEliminateAt s
                            ((Int y 7 -> (Apply y s))))))
  (check-equal?
   (raw-subst* eliminate '(s) (list (term q)))
   (term (UnionEliminateAt q
                           ((Int y 7 -> (Apply y q))))))
  (check-equal?
   (raw-subst* eliminate '(y) (list (term q)))
   eliminate)
  (check-equal? (raw-free-vars eliminate) (set 's))
  (check-equal?
   (raw-free-vars eliminate)
   (core-free-vars eliminate)))

(test-case "BorrowAt は Own root と designator を置換し fp の label を保つ"
  (check-equal?
   (raw-subst* (term (BorrowAt 7 (Own x (x)) x)) '(x) (list (term y)))
   (term (BorrowAt 7 (Own y (x)) y)))
  (check-equal? (raw-free-vars (term (BorrowAt 7 (Own x (x)) x)))
                (set 'x)))

(test-case "Lam origin の Curry operand は静的で body の変数だけ置換する"
  (check-equal?
   (raw-subst* (term (Lam (Derived User (Curry x)) f () x))
               '(x) (list (term y)))
   (term (Lam (Derived User (Curry x)) f () y))))

(test-case "Handle と RecRewrite の各 binder scope は body だけ"
  (check-equal?
   (raw-free-vars (term (Handle (Return b Int) (x -> x) x)))
   (set 'x))
  (check-equal?
   (raw-free-vars (term (RecRewrite r ((field x Int imm Int x)))))
   (set 'r)))

(test-case "静的記号の多重集合は置換する変数出現数に従う"
  (define (law body x value occurrences)
    (define result (raw-subst* body (list x) (list value)))
    (check-equal?
     (raw-static-symbols result)
     (sort (append (raw-static-symbols body)
                   (apply append
                          (for/list ([_ (in-range occurrences)])
                            (raw-static-symbols value))))
           symbol<?)))
  (law (term (Proj (Rec ((x imm x) (b imm x))) x))
       'x (term (Construct (Data Box ()) Box)) 2))

(test-case "raw-symbols は静的位置と変数位置を含む全記号を集める"
  (check-equal?
   (raw-symbols (term (Proj (Rec ((field imm x))) field)))
   (set 'Proj 'Rec 'field 'imm 'x)))

(test-case "同時置換の arity 不一致と重複 binder は拒否する"
  (check-false (raw-subst* (term x) '(x y) '(1)))
  (check-false (raw-subst* (term x) '(x x) '(1 2))))

(test-case "α 同値は binder renaming を認めるが static label は固定する"
  (check-true
   (raw-alpha-equivalent?
    (term (Let (x const Int) 1 (Proj (Rec ((x imm x))) x)))
    (term (Let (y const Int) 1 (Proj (Rec ((x imm y))) x)))))
  (check-false
   (raw-alpha-equivalent?
    (term (Let (x const Int) 1 (Proj (Rec ((x imm x))) x)))
    (term (Let (y const Int) 1 (Proj (Rec ((y imm y))) y))))))

(test-case "α 同値は不正な Core 入力を false に隠さず例外にする"
  (check-exn exn:fail?
             (lambda ()
               (raw-alpha-equivalent? '(not-a-core x) '(not-a-core x)))))

(test-case "移動した child API は意味上の子を往復する"
  (for ([core (in-list (list (term (Apply f x))
                            (term (Construct (Data Box ()) Box x))
                            (term (EliminateAt x ((Box (y) (7) -> y))))
                            (term (UnionEliminateAt x ((Int y 7 -> y))))
                            (term (BorrowAt 7 (Own x (field)) x))
                            (term (Lam (Derived User (Curry x)) f () x))))])
    (check-equal? (core-with-children core (core-children core)) core)))

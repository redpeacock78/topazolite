#lang racket

(require racket/match
         racket/set
         rackunit
         "../pr-binding.rkt")

;; [REQ: SCP-002] PR の置換は変数の位置だけに作用し、捕獲を避ける。

(test-case "PR の変数は文法の literal を含まない"
  (check-true (pr-variable? 'v:x))
  (check-true (pr-variable? 'x))
  (check-false (pr-variable? 'unit))
  (check-false (pr-variable? 'drop))
  (check-false (pr-variable? 'return))
  (check-false (pr-variable? 'PLet))
  (check-false (pr-variable? 'Available))
  (check-false (pr-variable? 3)))

(test-case "束縛形ごとの scope で自由変数を数える"
  (check-equal? (pr-free-vars '(PLet x y (PApp x z))) (set 'y 'z))
  ;; 束縛する式は外側の scope にある。
  (check-equal? (pr-free-vars '(PLet x x x)) (set 'x))
  (check-equal? (pr-free-vars '(PLetOwned x x x)) (set 'x))
  ;; PLetrec の束縛子は両側を束縛する。
  (check-equal? (pr-free-vars '(PLetrec f (PLam (n) (PApp f n m)) (PApp f k)))
                (set 'm 'k))
  ;; PClosure の環境値は外側、key と仮引数は本体の scope にある。
  (check-equal?
   (pr-free-vars '(PClosure ((e (PClosure () () z))) (p) (PApp e p q)))
   (set 'z 'q))
  (check-equal?
   (pr-free-vars '(PMatch s ((k:some (x) -> (PApp x y)) (k:none () -> x))))
   (set 's 'y 'x))
  (check-equal? (pr-free-vars '(PRecRewrite r ((f:a x (PApp x y)))))
                (set 'r 'y)))

(test-case "静的な位置の名前は自由変数に数えない"
  (check-equal? (pr-free-vars '(PProj (PRec ((x 1))) x)) (set))
  (check-equal? (pr-free-vars '(PTagged x)) (set))
  (check-equal? (pr-free-vars '(PPrim x y)) (set 'y))
  (check-equal? (pr-free-vars '(PProjOpt x x r x)) (set 'r))
  (check-equal? (pr-free-vars '(PRecRemove r (x))) (set 'r))
  (check-equal? (pr-free-vars '(PEffect (return x ty:Int) x)) (set 'x))
  (check-equal? (pr-free-vars '(PRuntime drop x)) (set 'x))
  (check-equal? (pr-free-vars '(PApp (PResource 1) (PPlace 2))) (set)))

(test-case "置換は label、tag、境界名、primitive 名を書き換えない"
  (check-equal? (pr-subst* '(PProj (PRec ((x 2))) x) '(x) '(1))
                '(PProj (PRec ((x 2))) x))
  (check-equal? (pr-subst* '(PTagged x x) '(x) '(1)) '(PTagged x 1))
  (check-equal? (pr-subst* '(PPrim x x) '(x) '(1)) '(PPrim x 1))
  (check-equal? (pr-subst* '(PMatch x ((x (y) -> x))) '(x) '(1))
                '(PMatch 1 ((x (y) -> 1))))
  (check-equal? (pr-subst* '(PEffect (return x ty:Int) x) '(x) '(1))
                '(PEffect (return x ty:Int) 1))
  (check-equal? (pr-subst* '(PApp (PResource 1) (PPlace 2)) '(x) '(3))
                '(PApp (PResource 1) (PPlace 2)))
  ;; entry の label は束縛子と同名でも変えず、本体の自由な x は置換する。
  (check-equal? (pr-subst* '(PRecRewrite x ((x y x))) '(x) '(1))
                '(PRecRewrite 1 ((x y 1)))))

(test-case "束縛子は shadowing する"
  (check-equal? (pr-subst* '(PLet x x x) '(x) '(1)) '(PLet x 1 x))
  (check-equal? (pr-subst* '(PLetrec x (PLam () x) x) '(x) '(1))
                '(PLetrec x (PLam () x) x))
  (check-equal? (pr-subst* '(PRecRewrite r ((f:a x x))) '(x) '(1))
                '(PRecRewrite r ((f:a x x))))
  (check-equal? (pr-subst* '(PMatch s ((k:a (x) -> x))) '(x) '(1))
                '(PMatch s ((k:a (x) -> x))))
  ;; 環境値は外側の scope にあるので置換され、本体は仮引数が隠す。
  (check-equal?
   (pr-subst* '(PClosure ((e (PClosure () () x))) (x) x) '(x) '(1))
   '(PClosure ((e (PClosure () () 1))) (x) x)))

(test-case "置換は同時に行う"
  (check-equal? (pr-subst* '(PApp x y) '(x y) '((PClosure () () y) 1))
                '(PApp (PClosure () () y) 1)))

(test-case "開いた値の自由変数を捕獲しない"
  (match (pr-subst* '(PLet z 0 (PApp y z)) '(y) '((PClosure () () z)))
    [`(PLet ,renamed 0 (PApp (PClosure () () z) ,renamed-use))
     (check-not-equal? renamed 'z)
     (check-equal? renamed renamed-use)]
    [other (fail (format "改名した PLet を期待した: ~s" other))])
  ;; PLetrec は両側で束縛子を改名する。
  (match (pr-subst* '(PLetrec z (PLam () (PApp z y)) (PApp z y))
                    '(y) '((PClosure () () z)))
    [`(PLetrec ,f (PLam () (PApp ,f-left (PClosure () () z)))
               (PApp ,f-right (PClosure () () z)))
     (check-not-equal? f 'z)
     (check-equal? f f-left)
     (check-equal? f f-right)]
    [other (fail (format "両側の改名を期待した: ~s" other))])
  ;; 接頭辞付きの名前も PR の変数として改名する。
  (match (pr-subst* '(PLet v:z 0 (PApp v:y v:z))
                    '(v:y) '((PClosure () () v:z)))
    [`(PLet ,renamed 0 (PApp (PClosure () () v:z) ,_))
     (check-not-equal? renamed 'v:z)
     (check-true (pr-variable? renamed))]
    [other (fail (format "接頭辞付きの改名を期待した: ~s" other))]))

(test-case "新しい名前は本体と値のどの記号とも衝突しない"
  (match (pr-subst* '(PLet z 0 (PApp y z (PProj (PRec ((z«1» 1))) z«1»)))
                    '(y) '((PClosure () () z)))
    [`(PLet ,renamed 0 (PApp ,_ ,_ (PProj (PRec ((z«1» 1))) z«1»)))
     (check-false (memq renamed '(z z«1»)))]
    [other (fail (format "衝突しない改名を期待した: ~s" other))]))

(test-case "arity 不一致、重複、変数でない束縛子は #f を返す"
  (check-false (pr-subst* 'x '(x y) '(1)))
  (check-false (pr-subst* 'x '(x x) '(1 2)))
  (check-false (pr-subst* 'x '(unit) '(1))))

(test-case "α 同値は束縛子の改名だけを同一視する"
  (check-true (pr-alpha-equivalent? '(PLam (a) a) '(PLam (b) b)))
  (check-true (pr-alpha-equivalent? '(PLet a 1 a) '(PLet b 1 b)))
  (check-true (pr-alpha-equivalent? '(PLetrec a (PLam (c) a) a)
                                    '(PLetrec b (PLam (d) b) b)))
  (check-true (pr-alpha-equivalent? '(PClosure ((e 7)) (a) (PApp e a))
                                    '(PClosure ((g 7)) (b) (PApp g b))))
  (check-true (pr-alpha-equivalent? '(PMatch s ((k (a) -> a)))
                                    '(PMatch s ((k (b) -> b)))))
  (check-true (pr-alpha-equivalent? '(PRecRewrite r ((f a a)))
                                    '(PRecRewrite r ((f b b)))))
  ;; label は束縛子と同名でも改名の対象にしない。
  (check-true (pr-alpha-equivalent? '(PLet a 1 (PProj a a))
                                    '(PLet b 1 (PProj b a))))
  (check-false (pr-alpha-equivalent? '(PLet a 1 (PProj a a))
                                     '(PLet b 1 (PProj b b))))
  ;; 自由変数と環境値は文字どおりに比べる。
  (check-false (pr-alpha-equivalent? '(PLam (a) c) '(PLam (b) d)))
  (check-false (pr-alpha-equivalent? '(PLam (a) 1) '(PLam (a) 2)))
  (check-false (pr-alpha-equivalent? '(PClosure ((e 7)) () e)
                                     '(PClosure ((e 8)) () e))))

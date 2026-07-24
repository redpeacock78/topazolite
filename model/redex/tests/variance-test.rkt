#lang racket

(require rackunit
         "../compat.rkt"
         "../type-equiv.rkt")

;; record の width で「広い引数」「狭い引数」を作る。
;; wide-arg はどの record でも受けられる引数要求、narrow-arg は field a を要求する。
(define wide-arg '(Record ()))
(define narrow-arg '(Record ((a Int imm))))

(test-case "VAR-001: 引数は反変"
  ;; 広い引数を受ける関数は、狭い引数を要求する期待を満たす
  (check-true  (compat? `(NFn (,wide-arg) Int () ())
                        `(NFn (,narrow-arg) Int () ())))
  (check-false (compat? `(NFn (,narrow-arg) Int () ())
                        `(NFn (,wide-arg) Int () ()))))

(test-case "VAR-001: 返り値は共変"
  (check-true  (compat? '(NFn () Never () ()) '(NFn () Int () ())))
  (check-false (compat? '(NFn () Int () ()) '(NFn () Never () ())))
  ;; record width の返り値
  (check-true  (compat? `(NFn () ,narrow-arg () ()) `(NFn () ,wide-arg () ())))
  (check-false (compat? `(NFn () ,wide-arg () ()) `(NFn () ,narrow-arg () ()))))

(test-case "VAR-001: 引数個数は一致を要求"
  (check-false (compat? '(NFn (Int) Int () ()) '(NFn (Int Int) Int () ())))
  (check-false (compat? '(NFn (Int Int) Int () ()) '(NFn (Int) Int () ()))))

(test-case "VAR-001: 深さ 2 で極性が反転する（高階引数）"
  (define needs-a-callback `(NFn (,narrow-arg) Int () ()))
  (define any-record-callback `(NFn (,wide-arg) Int () ()))
  ;; 「field a 付き record を受ける callback」を渡せる位置には、
  ;; 「任意 record を受ける callback」を要求する期待を満たせない、の逆。
  ;; 引数位置の引数位置は共変へ戻る。
  (check-true  (compat? `(NFn (,needs-a-callback) Int () ())
                        `(NFn (,any-record-callback) Int () ())))
  (check-false (compat? `(NFn (,any-record-callback) Int () ())
                        `(NFn (,needs-a-callback) Int () ()))))

(test-case "VAR-002: latent effect は共変の集合包含"
  (check-true  (compat? '(NFn () Int () ()) '(NFn () Int (Suspend) ())))
  (check-true  (compat? '(NFn () Int (Suspend) ()) '(NFn () Int (Suspend Own) ())))
  (check-false (compat? '(NFn () Int (Suspend Own) ()) '(NFn () Int (Suspend) ())))
  ;; 順序に依存しない
  (check-true  (compat? '(NFn () Int (Suspend (Yield Int)) ())
                        '(NFn () Int ((Yield Int) Suspend Own) ())))
  ;; ラベル同一性は effect-equiv?（Yield payload の field 順序違いを同一視）
  (check-true  (compat?
                '(NFn () Int ((Yield (Record ((a Int imm) (b Bool imm))))) ())
                '(NFn () Int ((Yield (Record ((b Bool imm) (a Int imm))))) ()))))

(test-case "VAR-002: Proof obligation は反変の集合包含"
  ;; sub の Q ⊆ sup の Q。期待側が引き受けると宣言した obligation の
  ;; 範囲内でだけ、実際側は discharge を要求できる。
  (check-true  (compat? '(NFn () Int () ())
                        '(NFn () Int () (ValidNarrativeTrait))))
  (check-true  (compat? '(NFn () Int () (ValidNarrativeTrait))
                        '(NFn () Int () (ValidNarrativeTrait TypeNarrativeCap))))
  (check-false (compat? '(NFn () Int () (ValidNarrativeTrait TypeNarrativeCap))
                        '(NFn () Int () (ValidNarrativeTrait))))
  ;; 順序に依存しない
  (check-true  (compat? '(NFn () Int () (TypeNarrativeCap ValidNarrativeTrait))
                        '(NFn () Int () (ValidNarrativeTrait TypeNarrativeCap)))))

(test-case "VAR-003: imm field の関数型は関数 variance で判定"
  (define sub-fn `(NFn (,wide-arg) Int () ()))
  (define sup-fn `(NFn (,narrow-arg) Int () ()))
  (check-true  (compat? `(Record ((f ,sub-fn imm))) `(Record ((f ,sup-fn imm)))))
  (check-false (compat? `(Record ((f ,sup-fn imm))) `(Record ((f ,sub-fn imm))))))

(test-case "VAR-003: mut field の関数型は型同値の不変に留まる"
  (define sub-fn `(NFn (,wide-arg) Int () ()))
  (define sup-fn `(NFn (,narrow-arg) Int () ()))
  (check-false (compat? `(Record ((f ,sub-fn mut))) `(Record ((f ,sup-fn mut)))))
  (check-false (compat? `(Record ((f ,sup-fn mut))) `(Record ((f ,sub-fn mut)))))
  ;; 型同値なら mut でも互換
  (check-true  (compat? `(Record ((f ,sup-fn mut))) `(Record ((f ,sup-fn mut))))))

(test-case "VAR-002: type-equiv? の NFn 判定は G2c 前後で不変"
  ;; 互換だが同値でないペアは同値でないまま
  (check-false (type-equiv? '(NFn () Never () ()) '(NFn () Int () ())))
  (check-false (type-equiv? '(NFn () Int () ()) '(NFn () Int (Suspend) ())))
  ;; Q の順序は type-equiv? では区別される（equal? 比較のまま）
  (check-false (type-equiv? '(NFn () Int () (ValidNarrativeTrait TypeNarrativeCap))
                            '(NFn () Int () (TypeNarrativeCap ValidNarrativeTrait)))))

#lang racket

;; SUR-008 / SUR-015。戻り型を省略した Fn と Recur の elaboration を UCore の入力で固定する。

(require racket/match
         rackunit
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt")

(define (code-of term)
  (match (elab term)
    [`(err ,d) (diagnostic-id d)]
    [_ 'ok]))

(define (found-of term)
  (match (elab term)
    [`(err ,d) (diagnostic-found d)]
    [other (error 'found-of "失敗しなかった: ~s" other)]))

(define (type-of term)
  (match (elab term)
    [(list _ type _ _) type]
    [other (error 'type-of "成功しなかった: ~s" other)]))

(define (tree-contains? tree wanted)
  (or (equal? tree wanted)
      (and (pair? tree)
           (or (tree-contains? (car tree) wanted)
               (tree-contains? (cdr tree) wanted)))))

(define e-typ-024 (diagnostic-code-of 'elaborate 'return-type-not-inferable))

(test-case "SUR-008: 合成位置の省略 Fn は本体の型を戻り型にする"
  (check-match (type-of '(Fn ((x Int)) #:infer () x))
               `(NFn (Int) Int . ,_))
  (check-equal? (type-of '(Apply (Fn ((x Int)) #:infer () x) 1)) 'Int))

(test-case "SUR-008: 省略 Recur は本体の型を戻り型にする"
  (check-equal?
   (type-of '(Recur f ((x Int)) #:infer (Partial) x (Apply f 1)))
   'Int))

(test-case "SUR-015: 合成位置の省略 Fn は Return payload から戻り型を推論する"
  (define t '(Fn () #:infer () (Return 1)))
  (check-equal? (code-of t) 'ok)
  (check-match (type-of t) `(NFn () Int . ,_)))

(test-case "SUR-015: 候補があれば入れ子の関数宣言 row の Return は解決する"
  (define t '(Fn () #:infer () (Let g (Fn () Int (Return) 1) 0)))
  (match (elab t)
    [(list _ type _ callables)
     (check-equal? type '(NFn () Int () () () User))
     (check-true
      (for/or ([entry (in-list callables)])
        (match (second entry)
          [`(NFn () Int () ((Return ,_ Int)) () User) #t]
          [_ #f])))]
    [other (fail-check (format "成功しなかった: ~s" other))]))

(test-case "SUR-015: 拒否で終わる下見は内側 callable と boundary の連番を消費しない"
  ;; 最初の field の Return payload が内側 Fn を合成し、callable/boundary を
  ;; 割り当てて候補を残す。次の field の省略仮引数 Fn は合成時に拒否されるため
  ;; Rec 全体の下見も失敗するが、本番は先の候補 Record 型で検査できる。
  (define inner-fn '(Fn ((x Int)) Int () x))
  (define inferred-fn '(Fn ((x #:infer)) #:infer () x))
  (define candidate-record
    (list 'Rec (list (list 'a 'imm 1) (list 'b 'imm inner-fn))))
  (define body
    (list 'Rec
          (list (list 'a 'imm (list 'Return candidate-record))
                (list 'b 'imm inferred-fn))))
  (define inferred (elab `(Fn () #:infer () ,body)))
  (define explicit
    (elab `(Fn () (Record ((a Int imm) (b (NFn (Int) Int () ()) imm)))
                () ,body)))
  (match* (inferred explicit)
    [((list core-i _ _ callables-i) (list core-e _ _ callables-e))
     (check-equal? (erase-core core-i) (erase-core core-e))
     (check-equal? callables-i callables-e)]
    [(_ _) (fail-check (format "成功しなかった: ~s ~s" inferred explicit))]))

;; 外側の戻り型を Return row に持つ閉包を返すと、推論型が自己参照する。
(test-case "SUR-015: 自己参照する戻り型の閉包は E-TYP-012 で拒否する"
  (define t '(Fn () #:infer () (Fn () Int (Return) 1)))
  (check-equal? (code-of t)
                (diagnostic-code-of 'elaborate 'type-mismatch)))

(test-case "SUR-015: 候補が無い入れ子の関数宣言 row は E-TYP-024 を保つ"
  (check-equal? (code-of '(Fn () #:infer () (Fn () Int (Return) y)))
                e-typ-024))

(test-case "SUR-015: 期待型付き Fn の省略戻り型は明示注釈と同じ Core と Φ を作る"
  (define inferred
    (elab '(Fn () (NFn () Int () ()) () (Fn () #:infer () (Return 1)))))
  (define explicit
    (elab '(Fn () (NFn () Int () ()) () (Fn () Int () (Return 1)))))
  (match* (inferred explicit)
    [((list core-i _ _ callables-i) (list core-e _ _ callables-e))
     (check-equal? (erase-core core-i) (erase-core core-e))
     (check-equal? callables-i callables-e)]
    [(_ _) (fail-check (format "成功しなかった: ~s ~s" inferred explicit))]))

(test-case "SUR-015: 省略戻り型の FnDecl は明示注釈と同じ Core と Φ を作る"
  (define inferred
    (elab '(FnDecl f ((x Int)) #:infer () (Return x) 0)))
  (define explicit
    (elab '(FnDecl f ((x Int)) Int () (Return x) 0)))
  (match* (inferred explicit)
    [((list core-i _ _ callables-i) (list core-e _ _ callables-e))
     (check-equal? (erase-core core-i) (erase-core core-e))
     (check-equal? callables-i callables-e)]
    [(_ _) (fail-check (format "成功しなかった: ~s ~s" inferred explicit))]))

(test-case "SUR-008: 検査位置の省略 Fn の本体の Return は受理される"
  (check-equal?
   (code-of '(Fn () (NFn () Int () ()) () (Fn () #:infer () (Return 1))))
   'ok))

(test-case "SUR-008: 型引数の無い Construct は合成位置で E-TYP-003、検査位置で受理"
  (check-equal? (code-of '(Fn () #:infer () (Construct none)))
                (diagnostic-code-of 'elaborate 'constructor-needs-expected-type))
  (check-equal?
   (code-of '(Fn () (NFn () (Option Int) () ()) ()
                 (Fn () #:infer () (Construct none))))
   'ok))

(test-case "SUR-008: 期待型が関数型でない位置の省略 Fn は type-mismatch を返す"
  (check-equal? (code-of '(Fn () Int () (Fn () #:infer () 1)))
                (diagnostic-code-of 'elaborate 'type-mismatch)))

(test-case "SUR-008: 本体が自身を参照する省略 Recur は E-TYP-024 を返す"
  (define t '(Recur f ((x Int)) #:infer (Partial) (Apply f x) (Apply f 1)))
  (check-equal? (code-of t) e-typ-024)
  (check-equal? (found-of t) 'self-reference))

(test-case "SUR-008: 省略 Recur の Owned 捕捉は注釈付きと同じ診断を返す"
  (check-equal?
   (code-of '(Fn ((p (Owned Res))) Unit (Partial)
                 (Recur f () #:infer (Partial) p unit)))
   (code-of '(Fn ((p (Owned Res))) Unit (Partial)
                 (Recur f () Res (Partial) p unit))))
  (check-equal?
   (code-of '(Fn ((p (Owned Res))) Unit (Partial)
                 (Recur f () #:infer (Partial) p unit)))
   (diagnostic-code-of 'elaborate 'owned-recur-capture)))

(test-case "SUR-008: 省略 Recur の Owned 捕捉は自己参照より先に報告する"
  ;; 本体は Owned の外側の束縛 p と自身 f の両方を参照する。
  ;; 自己参照の検査が先なら E-TYP-024 になり、この試験は落ちる。
  (check-equal?
   (code-of '(Fn ((p (Owned Res))) Unit (Partial)
                 (Recur f () #:infer (Partial) (Apply f p) unit)))
   (diagnostic-code-of 'elaborate 'owned-recur-capture)))

(test-case "SUR-008: 期待戻り型が関数型の検査位置の省略 Fn は受理される"
  ;; 期待型の σ は Typed Core の 6 欄の NFn である。resolve-annotation に
  ;; 通すと invalid-type-annotation になるため、解決済みの経路を固定する。
  (check-equal?
   (code-of '(Fn () (NFn () (NFn (Int) Int () ()) () ()) ()
                 (Fn () #:infer () (Fn ((y Int)) Int () y))))
   'ok))

(test-case "SUR-008: 期待型が Owned 関数型でも検査位置の省略 Fn は受理される"
  (check-equal?
   (code-of '(Fn ((p (Owned Res)))
                 (Owned (NFn () (Owned Res) (Own) ()))
                 (Own)
                 (Fn () #:infer (Own) (Move p))))
   'ok))

(test-case "SUR-008: 出力の Typed Core と Φ に #:infer が現れない"
  (for ([t (list '(Apply (Fn ((x Int)) #:infer () x) 1)
                 '(Recur f ((x Int)) #:infer (Partial) x (Apply f 1))
                 '(Fn () (NFn () Int () ()) () (Fn () #:infer () (Return 1))))])
    (define r (elab t))
    (check-false (tree-contains? r '#:infer))))

(test-case "SUR-008: 推論経路の CallableId は相異なる"
  (match (elab '(Apply (Fn ((g (NFn (Int) Int () ()))) Int () (Apply g 1))
                       (Fn ((y Int)) #:infer () y)))
    [(list _ _ _ callables)
     (define ids (map car callables))
     (check-equal? (length ids) 2)
     (check-equal? (length (remove-duplicates ids)) (length ids))]
    [other (fail-check (format "成功しなかった: ~s" other))]))

#lang racket

;; SUR-008。戻り型を省略した Fn と Recur の elaboration を UCore の入力で固定する。

(require racket/match
         rackunit
         "../diagnostic.rkt"
         "../elaborate.rkt")

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

(test-case "SUR-008: 合成位置の省略 Fn の本体の Return は E-TYP-024 を返す"
  (define t '(Fn () #:infer () (Return 1)))
  (check-equal? (code-of t) e-typ-024)
  (check-equal? (found-of t) 'return-in-synth))

(test-case "SUR-008: 入れ子の関数の宣言 row の Return label も E-TYP-024 を返す"
  (define t '(Fn () #:infer () (Fn () Int (Return) 1)))
  (check-equal? (code-of t) e-typ-024)
  (check-equal? (found-of t) 'return-in-synth))

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

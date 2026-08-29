#lang racket

;; G5c5b1。Owned を取る仮引数の符号化を検査する。
;; [REQ: OWN-006] Owned の仮引数を取る関数と再帰関数。
(require rackunit
         racket/match
         "../classify.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define (elaborate-surface source)
  (match (elab source)
    [(list core _type _row _callables) core]
    [other (error 'elaborate-surface "elaboration failed: ~s" other)]))

(define (elaborate-diagnostic-of source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [other (error 'elaborate-diagnostic-of "elaboration succeeded: ~s" other)]))

(define (typing-diagnostic-of core [parameter-types '((Owned Res))])
  (diagnostic-id
   (core-type-of/diagnostic
    core
    '()
    (list (list 'f `(NFn ,parameter-types Int () ()))))))

(define (owned-span start end)
  (list '#:span 'src start end))

(define (owned-handle inner)
  (define s (owned-span 0 100))
  `(Handle ,s
           (Return boundary (#:ty Int ,s))
           (,s (#:bind return-value ,s) -> (#:var return-value ,s))
           (Scope ,s () ,inner)))

(define (owned-core-lam parameter-names parameter-types inner)
  (define s (owned-span 0 100))
  `(Lam ,s User f
        ,(for/list ([name (in-list parameter-names)])
           `(#:bind ,name ,s))
        ,(owned-handle inner)))

(define (owned-let binder raw type next)
  (define s (owned-span 0 100))
  `(Let ,s ((#:bind ,binder ,s) let (#:ty ,type ,s))
        (#:var ,raw ,s)
        ,next))

(define owned-identity-surface
  '(Fn ((p (Owned Res))) (Owned Res) (Own) (Move p)))
(define owned-pair-surface
  '(Fn ((p (Owned Res)) (q (Owned Res))) Unit (Own) (Drop p)))
(define owned-mixed-surface
  '(Fn ((p (Owned Res)) (n Int)) Unit (Own) (Drop p)))
(define plain-identity-surface
  '(Fn ((n Int)) Int () n))
(define owned-name-clash-surface
  '(Fn ((p (Owned Res)) (owned0 Int)) Unit (Own) (Drop p)))
(define nested-owned-surface
  '(Fn ((p (Owned Res))) Unit (Own)
       (Let g
            (Fn ((q (Owned Res))) Unit (Own) (Drop q))
            (Drop p))))
(define owned-capture-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Fn () Unit (Own) (Drop p))))

(define owned-recur-surface
  '(Recur f ((item (Owned Res))) Unit ((Yield Int))
          (Yield 1 (Apply f (Apply acquire 1)))
          (Apply f (Apply acquire 1))))
(define plain-recur-surface
  '(Recur f ((item Int)) Unit ((Yield Int))
          (Yield 1 (Apply f 0))
          (Apply f 0)))
(define guarded-owned-recur-surface owned-recur-surface)
(define guarded-plain-recur-surface plain-recur-surface)
(define structural-with-owned-surface
  '(Recur f ((xs (List Int)) (item (Owned Res))) Unit ()
          (Eliminate xs
                     ((nil () -> unit)
                      (cons (head tail) ->
                            (Apply f tail (Apply acquire 1)))))
          (Apply f (Construct nil (Types Int)) (Apply acquire 1))))
(define structural-without-owned-surface
  '(Recur f ((xs (List Int)) (item Int)) Unit ()
          (Eliminate xs
                     ((nil () -> unit)
                      (cons (head tail) -> (Apply f tail 0))))
          (Apply f (Construct nil (Types Int)) 0)))
(define recur-name-clash-surface
  '(Recur owned0 ((item (Owned Res))) Unit (Partial) unit unit))

(define broken-missing-let-core
  (owned-core-lam '(owned0) '((Owned Res))
                  `(#:lit 1 ,(owned-span 50 51))))
(define broken-let-type-core
  (owned-core-lam '(owned0) '((Owned Res))
                  (owned-let 'p 'owned0 '(Owned Int)
                             `(#:lit 1 ,(owned-span 50 51)))))
(define broken-binder-clash-core
  (owned-core-lam '(owned0) '((Owned Res))
                  (owned-let 'owned0 'owned0 '(Owned Res)
                             `(#:lit 1 ,(owned-span 50 51)))))
(define broken-binding-mode-core
  (let ([s (owned-span 0 100)])
    `(Lam ,s User f
          ((#:bind owned0 ,s))
          (Handle ,s
                  (Return boundary (#:ty Int ,s))
                  (,s (#:bind return-value ,s) -> (#:var return-value ,s))
                  (Scope ,s ()
                         (Let ,s ((#:bind p ,s) const (#:ty (Owned Res) ,s))
                              (#:var owned0 ,s)
                              (#:lit 1 ,s)))))))
(define broken-raw-use-core
  (owned-core-lam '(owned0) '((Owned Res))
                  (owned-let 'p 'owned0 '(Owned Res)
                             `(#:var owned0 ,(owned-span 50 51)))))
(define broken-raw-shadow-core
  (owned-core-lam '(owned0) '((Owned Res))
                  (owned-let 'p 'owned0 '(Owned Res)
                             `(Let ,(owned-span 50 70)
                                   ((#:bind owned0 ,(owned-span 51 57))
                                    let
                                    (#:ty Int ,(owned-span 58 61)))
                                   (#:lit 1 ,(owned-span 62 63))
                                   (#:lit 0 ,(owned-span 64 65))))))
(define broken-binder-duplicate-core
  (let ([s (owned-span 0 100)])
    `(Lam ,s User f
          ((#:bind owned0 ,s) (#:bind owned1 ,s))
          (Handle ,s
                  (Return boundary (#:ty Int ,s))
                  (,s (#:bind return-value ,s) -> (#:var return-value ,s))
                  (Scope ,s ()
                         ,(owned-let 'p 'owned0 '(Owned Res)
                                     (owned-let 'p 'owned1 '(Owned Res)
                                                `(#:lit 1 ,s))))))))
(define broken-recur-value-core
  (let ([s (owned-span 0 100)])
    `(RecurVal ,s f (#:bind loop ,s)
               ((#:bind owned0 ,s))
               (#:lit 1 ,s))))
(define broken-recur-core
  (let ([s (owned-span 0 100)])
    `(Recur ,s f (#:bind loop ,s)
            ((#:bind owned0 ,s))
            (#:lit 1 ,s)
            (#:lit 0 ,s))))
(define owned-borrow-payload-core
  '(Let (x let (Owned (BorrowedMut Int 0)))
        (BorrowMut 1)
        1))

(define (classification-of source)
  (match (elab source)
    [(list core _ _ callables) (classify core '() callables)]
    [other (error 'classification-of "elaboration failed: ~s" other)]))

;; R-RecurBind と実引数の評価と R-RecurUnfold を順に適用し、展開された
;; 本体を取り出す。
(define (reduce-owned-recur source)
  (define core (erase-core (elaborate-surface source)))
  (match (raw-steps-g2 `(cfg ,core () () ()))
    [(list bound)
     (match (raw-steps-g2 bound)
       [(list evaluated-argument)
        (match (raw-steps-g2 evaluated-argument)
          [(list unfolded) (second unfolded)]
          [other
           (error 'reduce-owned-recur
                  "expected R-RecurUnfold after argument evaluation: ~s"
                  other)])]
       [other
        (error 'reduce-owned-recur
               "expected argument evaluation after R-RecurBind: ~s"
               other)])]
    [other (error 'reduce-owned-recur "expected R-RecurBind: ~s" other)]))

(define (scope-count-of core)
  (cond
    [(not (list? core)) 0]
    [(and (pair? core) (eq? (car core) 'Scope))
     (+ 1 (scope-count-of (third core)))]
    [else (apply + (map scope-count-of core))]))

;; 段 1
(test-case
 "function-body-environment は Owned の位置に payload の型を与える"
 (define environment '((outer (Owned Res)) (plain Int)))
 (define result
   (function-body-environment environment
                              '(owned0 n)
                              '((Owned Res) Int)))
 (check-equal? (assoc 'owned0 result) '(owned0 Res))
 (check-equal? (assoc 'n result) '(n Int))
 ;; 外側の Owned は落ちる。捕捉は仮引数として渡すため、本体の環境へ
 ;; 外側の Owned を入れる必要が無い。
 (check-false (assoc 'outer result))
 (check-equal? (assoc 'plain result) '(plain Int)))

(test-case
 "function-body-environment は Owned が無ければ従来と同じ環境を作る"
 (define environment '((plain Int)))
 (check-equal? (function-body-environment environment '(a b) '(Int Bool))
               '((a Int) (b Bool) (plain Int))))

;; 段 2
(define owned-callables
  '((callable0 (NFn ((Owned Res) Int) Int () ()))))
(define plain-callables
  '((callable1 (NFn (Int) Int () ()))))

(test-case
 "strip-owned-prefix は Owned が無ければ本体と環境をそのまま返す"
 (define body '(Yield Int (Apply f n)))
 (check-equal? (strip-owned-prefix 'callable1 '(n) body '((n Int))
                                   plain-callables)
               (list body '((n Int)))))

(test-case
 "strip-owned-prefix は Scope と Let の連なりを署名の個数だけ外す"
 (define inner '(Yield Int (Apply f p n)))
 (define body
   `(Scope () (Let (p let (Owned Res)) owned0 ,inner)))
 (define result
   (strip-owned-prefix 'callable0 '(owned0 n) body
                       '((owned0 Res) (n Int)) owned-callables))
 (check-equal? (first result) inner)
 (check-equal? (assoc 'p (second result)) '(p (Owned Res))))

(test-case
 "strip-owned-prefix は普通の Let を残す"
 (define ordinary '(Let (q let Int) 1 q))
 (define body
   `(Scope () (Let (p let (Owned Res)) owned0 ,ordinary)))
 (define result
   (strip-owned-prefix 'callable0 '(owned0 n) body
                       '((owned0 Res) (n Int)) owned-callables))
 (check-equal? (first result) ordinary)
 (check-equal? (second result)
               '((p (Owned Res)) (owned0 Res) (n Int))))

(test-case
 "strip-owned-prefix は契約を満たさない形へ #f を返す"
 (define inner '(Yield Int (Apply f p n)))
 ;; 管理する place を持つ Scope
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope (q) (Let (p let (Owned Res)) owned0 ,inner))
                      '((owned0 Res) (n Int)) owned-callables))
 ;; 宣言型が署名と食い違う Let
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope () (Let (p let (Owned Int)) owned0 ,inner))
                      '((owned0 Res) (n Int)) owned-callables))
 ;; 右辺が仮引数の名前でない Let
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope () (Let (p let (Owned Res)) n ,inner))
                      '((owned0 Res) (n Int)) owned-callables))
 ;; Let が足りない
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope () ,inner)
                      '((owned0 Res) (n Int)) owned-callables))
 ;; Scope が無い
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Let (p let (Owned Res)) owned0 ,inner)
                      '((owned0 Res) (n Int)) owned-callables))
 ;; 契約を満たす Let がもう 1 段続く
 (check-false
  (strip-owned-prefix 'callable0 '(owned0 n)
                      `(Scope ()
                              (Let (p let (Owned Res)) owned0
                                   (Let (q let (Owned Res)) owned0 ,inner)))
                      '((owned0 Res) (n Int)) owned-callables)))

;; 段 3
(test-case
 "Owned の仮引数を 1 つ取る Fn が生名と Let を持つ節へ写る"
 (define core (elaborate-surface owned-identity-surface))
 (match core
   [`(Lam ,s_fn User ,_ ((#:bind ,raw ,s_b))
          (Handle ,_ ,_ ,_
                  (Scope ,s_scope ()
                         (Let ,s_let ((#:bind p ,s_pb) let
                                      (#:ty (Owned Res) ,s_ty))
                              (#:var ,rhs ,s_rhs) ,_))))
    (check-eq? rhs raw)
    (check-false (eq? raw 'p))
    (check-equal? s_let s_b)
    (check-equal? s_pb s_b)
    (check-equal? s_ty s_b)
    (check-equal? s_rhs s_b)
    (check-equal? s_scope s_fn)]
   [_ (fail "生成した節の形が合わない")]))

(test-case
 "Owned の仮引数を 2 つ取る Fn の Let が仮引数の順序で入れ子になる"
 (define core (elaborate-surface owned-pair-surface))
 (match core
   [`(Lam ,_ User ,_ ((#:bind ,raw0 ,_) (#:bind ,raw1 ,_))
          (Handle ,_ ,_ ,_
                  (Scope ,_ ()
                         (Let ,_ ((#:bind p ,_) ,_ ,_) (#:var ,rhs0 ,_)
                              (Let ,_ ((#:bind q ,_) ,_ ,_)
                                   (#:var ,rhs1 ,_) ,_)))))
    (check-eq? rhs0 raw0)
    (check-eq? rhs1 raw1)
    (check-false (eq? raw0 raw1))]
   [_ (fail "入れ子の順序が仮引数の順序と合わない")] ))

(test-case
 "Owned と非 Owned を混ぜた仮引数列で非 Owned の名前が変わらない"
 (define core (elaborate-surface owned-mixed-surface))
 (match core
   [`(Lam ,_ User ,_ ((#:bind ,raw ,_) (#:bind n ,_)) ,_)
    (check-false (eq? raw 'p))]
   [_ (fail "非 Owned の位置の名前が動いた")]))

(test-case
 "Owned の仮引数を持たない Fn の節の形が変わらない"
 (define core (elaborate-surface plain-identity-surface))
 (match core
   [`(Lam ,_ User ,_ ((#:bind n ,_))
          (Handle ,_ ,_ ,_ (Scope ,_ () (#:var n ,_))))
    (check-true #t)]
   [_ (fail "Owned を持たない節の形が動いた")]))

(test-case
 "生名は surface が書いた記号と本体に現れない仮引数の名前を避ける"
 (define core (elaborate-surface owned-name-clash-surface))
 (match core
   [`(Lam ,_ User ,_ ((#:bind ,raw ,_) ,_ ...) ,_)
    (check-false (eq? raw 'owned0))]
   [_ (fail "生名が予約した記号と衝突した")]))

(test-case
 "入れ子の Fn が重ならない生名で Typed Core へ写る"
 (match (elab nested-owned-surface)
   [(list core type row callables)
    (check-equal?
     (core-type-of core '() callables)
     (list type row))]
   [other (fail (format "入れ子の Fn の elaboration が失敗した: ~s" other))]))

(test-case
 "Owned の仮引数を持つ署名で本体に Let が無い Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-missing-let-core)
               "E-OWN-023"))

(test-case
 "Owned を返す Fn の核が型付く"
 (match-define (list core type row callables) (elab owned-identity-surface))
 (check-equal? type '(NFn ((Owned Res)) (Owned Res) (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

(test-case
 "Let の宣言型が署名と食い違う Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-let-type-core)
               "E-OWN-023"))

(test-case
 "Let の binder が仮引数の名前と衝突する Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-binder-clash-core)
               "E-OWN-023"))

(test-case
 "束縛の様式が let でない Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-binding-mode-core)
               "E-OWN-023"))

(test-case
 "生名が Let の右辺の外に現れる Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-raw-use-core)
               "E-OWN-024"))

(test-case
 "内側の Let が生名を shadow する Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-raw-shadow-core)
               "E-OWN-024"))

(test-case
 "Let の連鎖の中で binder が重複する Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-binder-duplicate-core
                                    '((Owned Res) (Owned Res)))
               "E-OWN-023"))

(test-case
 "Owned の仮引数を内側の Fn が捕捉する surface を受け入れる"
 (match-define (list core type row callables) (elab owned-capture-surface))
 (check-equal? type '(NFn ((Owned Res))
                          (Owned (NFn () Unit (Own) ())) (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

(test-case
 "Owned の借用 payload を取る仮引数を拒否する"
 (check-equal? (typing-diagnostic-of owned-borrow-payload-core)
               "E-OWN-022"))

;; 段 4
(test-case
 "Owned の仮引数を取る Recur が本体を Scope で包む"
 (define core (elaborate-surface owned-recur-surface))
 (match core
   [`(Recur ,s_rec ,_ ,_ ((#:bind ,raw ,s_b) ,_ ...)
            (Scope ,s_scope ()
                   (Let ,s_let ((#:bind item ,_) let
                                (#:ty (Owned Res) ,_))
                        (#:var ,rhs ,_) ,_))
            ,_)
    (check-eq? rhs raw)
    (check-equal? s_scope s_rec)
    (check-equal? s_let s_b)]
   [_ (fail "Recur の包みの形が合わない")]))

(test-case
 "Owned の仮引数を持たない Recur は Scope で包まれない"
 (define core (elaborate-surface plain-recur-surface))
 (match core
   [`(Recur ,_ ,_ ,_ ,_ (Scope ,_ () ,_) ,_)
    (fail "Owned を持たない Recur に Scope が入った")]
   [_ (check-true #t)]))

(test-case
 "展開のたびに RecurVal が自分の Scope を持つ"
 (define traced (reduce-owned-recur owned-recur-surface))
 (match traced
   [`(Scope () (Let ,_ ,_ ,_))
    ;; 外側の Scope と、次の展開を待つ RecurVal の本体の Scope を数える。
    (check-equal? (scope-count-of traced) 2)]
   [_ (fail "R-RecurUnfold 後の本体が Scope と Let で包まれていない")]))

(test-case
 "Yield で守られた再帰は Owned の仮引数の有無で分類を変えない"
 (check-equal? (classification-of guarded-owned-recur-surface)
               '(Productive guarded))
 (check-equal? (classification-of guarded-plain-recur-surface)
               '(Productive guarded)))

(test-case
 "data の位置の structural は Owned の仮引数を足しても変わらない"
 (check-equal? (classification-of structural-with-owned-surface)
               '(Finite structural))
 (check-equal? (classification-of structural-with-owned-surface)
               (classification-of structural-without-owned-surface)))

(test-case
 "生名は Recur が宣言した関数の名前を避ける"
 (define core (elaborate-surface recur-name-clash-surface))
 (match core
   [`(Recur ,_ ,_ (#:bind ,function ,_)
            ((#:bind ,raw ,_) ,_ ...) ,_ ,_)
    (check-false (eq? raw function))]
   [_ (fail "生名が関数の名前と衝突した")]))

(test-case
 "RecurVal の本体で符号化が壊れた Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-recur-value-core)
               "E-OWN-023"))

(test-case
 "Recur の本体で符号化が壊れた Typed Core を拒否する"
 (check-equal? (typing-diagnostic-of broken-recur-core)
               "E-OWN-023"))

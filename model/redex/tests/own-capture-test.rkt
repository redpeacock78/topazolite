#lang racket

;; G5c5b2。Owned を捕捉する closure の生成を検査する。
;; [REQ: OWN-007] Owned を捕捉する closure。
(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (elaboration-of source)
  (match (elab source)
    [(list core type row callables) (list core type row callables)]
    [other (error 'elaboration-of "elaboration failed: ~s" other)]))

(define (find-capture-let core)
  (cond
    [(and (pair? core)
          (eq? (car core) 'Let)
          (match (third core)
            [`(Curry (Lam User ,_ ,_ ,_) ,_) #t]
            [_ #f]))
     core]
    [(pair? core)
     (for/or ([item (in-list core)])
       (find-capture-let item))]
    [else #f]))

(define (find-lam-by-callable core callable)
  (cond
    [(and (pair? core)
          (eq? (car core) 'Lam)
          (equal? (fourth core) callable))
     core]
    [(pair? core)
     (for/or ([item (in-list core)])
       (find-lam-by-callable item callable))]
    [else #f]))

;; Owned を 1 件捕捉する closure。
(define capture-one-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Fn () Unit (Own) (Drop p))))

(test-case
 "Owned を 1 件捕捉する closure を elaborate でき、型が Owned<NFn> になる"
 (match-define (list core type row callables) (elaboration-of capture-one-surface))
 (check-equal? type '(NFn ((Owned Res)) (Owned (NFn () Unit (Own) ())) (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; Owned を 2 件捕捉する closure。
(define capture-two-surface
  '(Fn ((z (Owned Res)) (a (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Fn () Unit (Own) (Let r (Drop z) (Drop a)))))

(test-case
 "Owned を 2 件捕捉する closure を elaborate できる"
 (match-define (list core type row callables) (elaboration-of capture-two-surface))
 (check-equal? type '(NFn ((Owned Res) (Owned Res))
                          (Owned (NFn () Unit (Own) ())) (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

(test-case
 "捕捉の生名は関数境界の自由変数の検査を通る"
 (match-define (list core type row callables)
   (elaboration-of capture-two-surface))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; 捕捉が 0 件なら素の NFn を返す。
(define capture-none-surface
  '(Fn ((n Int)) (NFn () Int () ()) ()
       (Fn () Int () 1)))

(test-case
 "捕捉が 0 件の closure は素の NFn を返す"
 (match-define (list core type row callables) (elaboration-of capture-none-surface))
 (check-equal? type '(NFn (Int) (NFn () Int () ()) () ()))
 (check-equal? (core-type-of core '() callables) (list type row))
 (match (erase-core core)
   [`(Lam User ,_ ,_ ,_) (void)]
   [_ (fail "捕捉 0 件の closure が Lam でない")]))

(test-case
 "捕捉 1 件の closure は Let と Curry の連鎖へ脱糖される"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-one-surface))
 (match (find-capture-let (erase-core core))
   [`(Let (,place let ,let-type)
          (Curry (Lam User ,_ ,capture-binders ,_)
                 (OwnLeaf (Move p)))
          (Move ,same-place))
    (check-equal? let-type '(Owned (NFn () Unit (Own) ())))
    (check-equal? same-place place)
    (check-equal? (length capture-binders) 1)]
   [_ (fail "捕捉 1 件の Let/Curry 形が合わない")]))

(test-case
 "捕捉 formal の binder span は内側の Lam span と一致する"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-one-surface))
 (match (find-lam-by-callable core 'callable1)
   [`(Lam ,lam-span User ,_ ((#:bind ,_ ,binder-span)) ,_)
    (check-equal? binder-span lam-span)]
   [_ (fail "捕捉 formal の span を取り出せない")]))

(test-case
 "捕捉 2 件の Let と Curry は辞書順で並ぶ"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-two-surface))
 (match (find-capture-let (erase-core core))
   [`(Let (,first-place let ,first-type)
          (Curry (Lam User ,_ ,_ ,_) (OwnLeaf (Move a)))
          (Let (,second-place let ,second-type)
               (Curry (Move ,moved-place) (OwnLeaf (Move z)))
               (Move ,last-place)))
    (check-equal? first-type
                  '(Owned (NFn ((Owned Res)) Unit (Own) ())))
    (check-equal? second-type '(Owned (NFn () Unit (Own) ())))
    (check-equal? moved-place first-place)
    (check-equal? last-place second-place)]
   [_ (fail "捕捉 2 件の Let/Curry 順序が合わない")]))

(define capture-name-clash-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Fn () Unit (Own)
           (Let owned1
                (Apply acquire 1)
                (Let tmp (Drop p) (Drop owned1))))))

(test-case
 "捕捉 formal の生名は本体の surface 名と衝突しない"
 (match-define (list core _type _row _callables)
   (elaboration-of capture-name-clash-surface))
 (match (find-lam-by-callable core 'callable1)
   [`(Lam ,_ User ,_ ((#:bind ,raw ,_)) ,_)
    (check-not-equal? raw 'owned1)]
   [_ (fail "捕捉 formal の生名を取り出せない")]))

(test-case
 "捕捉した closure の callable 署名は捕捉型を先頭へ持つ"
 (match-define (list _core _type _row callables)
   (elaboration-of capture-one-surface))
 (check-not-false
  (member '(callable1 (NFn ((Owned Res)) Unit (Own) ())) callables)))

;; inline の Apply。関数の位置に捕捉する closure を直に置く。
(define inline-apply-surface
  '(Fn ((p (Owned Res))) Unit (Own)
       (Apply (Fn () Unit (Own) (Drop p)))))

(test-case
 "closure を inline で Apply する形が外側の Owned な Let へ正規化される"
 (match-define (list core type row callables)
   (elaboration-of inline-apply-surface))
 (check-equal? type '(NFn ((Owned Res)) Unit (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; inline の Curry。関数の位置に捕捉する closure を直に置く。
(define inline-curry-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Curry (Fn ((n Int)) Unit (Own) (Drop p)) 1)))

(test-case
 "closure を inline で Curry する形が外側の Owned な Let へ正規化される"
 (match-define (list core type row callables)
   (elaboration-of inline-curry-surface))
 (check-equal? type '(NFn ((Owned Res)) (Owned (NFn () Unit (Own) ())) (Own) ()))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; 宣言 row が空のため、捕捉した closure の Own を覆えない負例。
(define undeclared-capture-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) ()
       (Fn () Unit (Own) (Drop p))))

(define (elaborate-diagnostic-of source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [other (error 'elaborate-diagnostic-of
                  "elaboration succeeded: ~s" other)]))

(test-case
 "捕捉する closure を作る式の row を宣言が覆わないと落ちる"
 (check-equal? (elaborate-diagnostic-of undeclared-capture-surface)
               "E-EFF-002"))

;; Owned closure の名前参照は、関数位置でも Move を明示する。
(define bound-capture-apply-surface
  '(Fn ((p (Owned Res))) Unit (Own)
       (Let g
            (Fn () Unit (Own) (Drop p))
            (Apply (Move g)))))

(test-case
 "捕捉する closure を g へ束ね、Move g で Apply すると通る"
 (match-define (list core type row callables)
   (elaboration-of bound-capture-apply-surface))
 (check-equal? (core-type-of core '() callables) (list type row)))

(test-case
 "Owned closure の裸の g を Apply すると E-OWN-010 で落ちる"
 (check-equal?
  (elaborate-diagnostic-of
   '(Fn ((p (Owned Res))) Unit (Own)
        (Let g
             (Fn () Unit (Own) (Drop p))
             (Apply g))))
  "E-OWN-010"))

(define (nodes-of term head)
  (cond
    [(and (pair? term) (eq? (car term) head))
     (cons term (append-map (lambda (item) (nodes-of item head)) (cdr term)))]
    [(pair? term)
     (append-map (lambda (item) (nodes-of item head)) term)]
    [else '()]))

(define (normalization-let? node)
  ;; spanful の fixture は義務を持たないため、ここでは body 直下の
  ;; Curry/Apply だけを判定する。Discharge を含む形は対象外である。
  (match node
    [(list 'Let (list name 'let _type) _bound
           (list (or 'Curry 'Apply) (list 'Move used) _ ...))
     (equal? name used)]
    [(list 'Let _span
           (list (list '#:bind name _) 'let (list '#:ty _ _))
           _bound
           (list (or 'Curry 'Apply) _span2
                 (list 'Move _span3 (list '#:var used _)) _ ...))
     (equal? name used)]
    [_ #f]))

(define (count-moves-to term name)
  (cond
    [(and (pair? term)
          (match term
            [`(Move ,used) (equal? used name)]
            [_ #f]))
     1]
    [(pair? term)
     (for/sum ([item (in-list term)])
       (count-moves-to item name))]
    [else 0]))

(define (normalization-lets core)
  (filter normalization-let? (nodes-of core 'Let)))

(define (normalization-body core)
  (match (normalization-lets core)
    [(list (list 'Let _binding _bound body)) body]
    [other (error 'normalization-body "normalization Let が 1 件でない: ~s" other)]))

;; サーフェイスの入れ子の Curry。内側の Curry の型が Owned<NFn (Int) …> になる。
(define nested-curry-surface
  '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
       (Curry (Curry (Fn ((q (Owned Res)) (n Int)) Unit (Own) (Drop q))
                     (Move p))
              1)))

(test-case
 "サーフェイスの入れ子の Curry は正規化を経て通る"
 (match-define (list core type row callables)
   (elaboration-of nested-curry-surface))
 (check-equal? (core-type-of core '() callables) (list type row))
 (match (normalization-body (erase-core core))
   [`(Curry (Move ,_) ,_) (void)]
   [_ (fail "入れ子の Curry の関数位置が Move へ正規化されていない")]))

(test-case
 "正規化した関数を束ねる Let の bound と Move は 1 回ずつである"
 (match-define (list core _type _row _callables)
   (elaboration-of inline-apply-surface))
 (define erased (erase-core core))
 (match (normalization-lets erased)
   [(list (list 'Let (list name 'let let-type) bound body))
    (check-equal? let-type '(Owned (NFn () Unit (Own) ())))
    (check-true (pair? bound))
    (check-equal? (count-moves-to body name) 1)]
   [_ (fail "inline Apply の正規化 Let が 1 件でない")]))

(test-case
 "正規化した Let の span は関数部分式の span である"
 (match-define (list core _type _row _callables)
   (elaboration-of nested-curry-surface))
 (match (normalization-lets core)
   [(list (list 'Let let-span _binding bound body))
    (check-equal? let-span (span-of bound))
    (check-not-equal? let-span (span-of body))]
   [_ (fail "spanful な正規化 Let が 1 件でない")]))

;; Core を直に書いた形。Curry ノードが関数の位置に残る。
(define bare-nested-curry-core
  '(Curry (Curry g (OwnLeaf (Move p))) 1))

(define bare-nested-curry-environment
  (list (list 'g '(NFn ((Owned Res) Int) Unit (Own) ()))
        (list 'p '(Owned Res))))

(define (owned-capture-diagnostic-of core environment)
  (diagnostic-id (core-type-of/diagnostic core '() '() environment)))

(test-case
 "Core を直に書いた Curry の根は owned-function-requires-move で落ちる"
 (check-equal? (owned-capture-diagnostic-of bare-nested-curry-core
                                            bare-nested-curry-environment)
               "E-OWN-025"))

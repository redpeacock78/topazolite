#lang racket

(require rackunit
         redex/reduction-semantics
         "../annotate.rkt"
         "../classify.rkt"
         "../compat.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../lowering.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../span.rkt"
         "../erase.rkt"
         "../typing.rkt")

;; span.md §7.3: 判定に span を使わない項面の関数は、投影を通してから既存の
;; 走査へ渡す。ここで固定するのは「spanful な項の判定が spanless 版と一致する」
;; ことである。
;; ill-typed 側の一致では契約を固定できない。投影が入っていない実装でも
;; redex-match? が落ちて 'ill-typed になり、同じ値が返るためである。
;; そのため各 test-case は well-typed な項の型が一致することを見る。

(define callable-types
  (term ((identity-id (NFn (Int) Int () ()))
         (binary-id (NFn (Int Int) Int () ())))))

(test-case "span.md §7.3: core-type-of は spanful な c を投影して受理する"
  (define prim '(PrimVal (Reserved o-lt) lt))
  (check-equal? (core-type-of (annotate-core prim) '() '())
                '((NFn (Int Int) Bool () ()) ()))
  (check-equal? (core-type-of (annotate-core prim) '() '())
                (core-type-of prim '() '()))
  ;; #:bind と Lam の span を含む項。
  (define lam '(Lam User identity-id (x) x))
  (check-equal? (core-type-of (annotate-core lam) '() callable-types)
                '((NFn (Int) Int () ()) ()))
  ;; #:lit と Apply の span を含む項。
  (define applied `(Apply (Lam User binary-id (x y) x) 1 2))
  (check-equal? (core-type-of (annotate-core applied) '() callable-types)
                '(Int ()))
  ;; #:ty と #:bind を持つ Let。
  (define bound '(Let (n Int) 1 n))
  (check-equal? (core-type-of (annotate-core bound) '() '())
                (core-type-of bound '() '()))
  (check-equal? (core-type-of (annotate-core bound) '() '())
                '(Int ())))

(test-case "span.md §7.3: core-check-row と core-check も spanful な c を受ける"
  (define prim '(PrimVal (Reserved o-lt) lt))
  (define signature '(NFn (Int Int) Bool () ()))
  (check-equal? (core-check-row (annotate-core prim) '() '() signature)
                '())
  (check-true (core-check (annotate-core prim) '() '() signature '())))

;; 分類の 3 判定のうち no-recursion? は Recur の有無だけを見るため、spanful でも
;; 偶然一致しうる。投影の有無を分けるのは structural? と guarded? であり、
;; どちらも Eliminate と Apply の内側まで構造を照合する。
(define structural-callables
  '((list-loop-id (NFn ((List Int)) Int () ()))))

(define structural-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> (Apply loop tail))))
          (Apply loop (Construct (List Int) nil))))

(test-case "span.md §7.3: classify は spanful な c を投影して分類する"
  (check-equal? (classify (annotate-core structural-loop) '() structural-callables)
                '(Finite structural))
  (check-equal? (classify (annotate-core structural-loop) '() structural-callables)
                (classify structural-loop '() structural-callables))
  (check-equal? (classify (annotate-core '(Apply (PrimVal (Reserved o-add) add) 1 2))
                          '() '())
                '(Finite no-recursion)))

;; span.md §7 の lowering 行は「出力に span を残さない」である。写しが spanless
;; 版と一致することでこれを固定する。PR の符号化そのものは lowering-test.rkt が
;; 固定しているため、ここでは書き下さない。
(test-case "span.md §7: lower は spanful な core を投影して写す"
  (define core '(Apply (PrimVal (Reserved o-add) add) 1 2))
  (define-values (spanless-status spanless-result) (lower core 'racket-cs))
  (define-values (spanful-status spanful-result)
    (lower (annotate-core core) 'racket-cs))
  (check-eq? spanless-status 'ok)
  (check-eq? spanful-status 'ok)
  (check-equal? spanful-result spanless-result))

(test-case "span.md §7: lower-value も spanful な値を投影して写す"
  (define value '(PrimVal (Reserved o-add) add))
  (define-values (spanless-status spanless-result) (lower-value value 'racket-cs))
  (define-values (spanful-status spanful-result)
    (lower-value (annotate-core value) 'racket-cs))
  (check-eq? spanless-status 'ok)
  (check-eq? spanful-status 'ok)
  (check-equal? spanful-result spanless-result))

;; span.md §7.3: 型の位置の包みは、境界検査より前に compat? 自身が落とす。
(define wrapped-int '(#:ty Int (#:span #:synthetic 0 0)))

(test-case "span.md §7.3: compat? は型の位置の包みを自身の error で落とす"
  (check-exn #rx"^compat\\?"
             (lambda () (compat? wrapped-int 'Int)))
  (check-exn #rx"^compat\\?"
             (lambda () (compat? 'Int wrapped-int)))
  ;; Never は全型と互換だが、短絡より前に包みを落とす。
  (check-exn #rx"^compat\\?"
             (lambda () (compat? 'Never wrapped-int)))
  (check-exn #rx"^compat\\?"
             (lambda ()
               (compat? `(Record ((a ,wrapped-int imm)))
                        '(Record ((a Int imm)))))))

(test-case "span.md §7.3: compat? の義務も型面の fail-closed を保つ"
  ;; 義務の側は proposition-equiv? 経由で normalize-proposition が落とす。
  (check-exn #rx"^normalize-proposition"
             (lambda ()
               (compat? `(NFn () Int () (,wrapped-int))
                        `(NFn () Int () (,wrapped-int))))))

(test-case "span.md §7.1: 候補の読み出しは ProofRep の両形を受ける"
  (define spanless '(Candidate (ProofRep (Reserved o-type-narrative) TypeNarrativeCap)
                               typeNarrativeCap root default ()))
  (define spanful '(Candidate (ProofRep (#:span #:synthetic 0 0)
                                        (Reserved o-type-narrative)
                                        TypeNarrativeCap)
                              typeNarrativeCap root default ()))
  (check-equal? (candidate-prop spanful) (candidate-prop spanless))
  (check-equal? (candidate-origin spanful) (candidate-origin spanless))
  (check-true (wf-candidate? spanful (make-goal 'TypeNarrativeCap))))

(test-case "span.md §7.1: transportable-proof は ProofRep の両形を受ける"
  (define phi 'TypeNarrativeCap)
  (define spanless `(ProofRep (Reserved o-type-narrative) ,phi))
  (define spanful `(ProofRep (#:span #:synthetic 0 0)
                             (Reserved o-type-narrative) ,phi))
  (check-equal? (transportable-proof spanless phi) spanless)
  (check-equal? (transportable-proof spanful phi) spanful))

(test-case "span.md §7.1: ProofRep の要素数は 3 と 4 だけである"
  (define phi 'TypeNarrativeCap)
  (define overlong
    `(ProofRep (#:span #:synthetic 0 0) extra (Reserved o-type-narrative) ,phi))
  (check-equal? (transportable-proof overlong phi) #f)
  (check-exn #rx"^proofrep-parts"
             (lambda ()
               (candidate-prop `(Candidate ,overlong cap root default ())))))

(test-case "span.md §7.3: goal と候補文脈は span 機構の包みを受理しない"
  (check-exn #rx"^make-goal"
             (lambda () (make-goal '(#:ty TypeNarrativeCap (#:span #:synthetic 0 0)))))
  (check-exn #rx"^candidateize"
             (lambda ()
               (candidateize
                '((cap ((#:ty TypeNarrativeCap (#:span #:synthetic 0 0))
                        (Reserved o-type-narrative))))))))

(test-case "span.md §7.3: 命題の内側の包みも拒否する"
  (check-exn #rx"^make-goal"
             (lambda ()
               (make-goal '(Implements (#:ty Int (#:span #:synthetic 0 0)) Printable))))
  (check-exn #rx"^candidateize"
             (lambda ()
               (candidateize
                '((imp ((Implements (#:ty Int (#:span #:synthetic 0 0)) Printable)
                        (Reserved o-impl-printable-int)))))))
  ;; head の検査だけを残す位置は従来どおり通る。
  (check-not-exn
   (lambda ()
     (check-spanless! 'type-equiv?
                      '(Implements (#:ty Int (#:span #:synthetic 0 0)) Printable)))))

;; span.md §7.4: 表層の span は結果を変えない。annotate-surface を通した項と
;; 通さない項で、elab の返り値が一致する。
(define spanful-corpus
  '(1
    add
    (Apply add 1 2)
    (Let x 1 (Apply add x 2))
    (Let (x const Int) 1 x)
    (Fn ((n Int)) Int () (Apply add n 1))
    (Fn () Int () (NarrativeExpr (Return 2)))
    (Fn ((n Int)) Int (Partial) (Recur f ((m Int)) Int (Partial) (Apply f m) n))
    (Fn ((flag Bool)) Int () (Eliminate flag ((true () -> 1) (false () -> 2))))
    (Rec ((a imm 1) (b mut 2)))
    (Proj (Rec ((a imm 1))) a)
    (Construct nil (Types Int))
    (Fn () (Option Int) () (Construct none))
    (Let item (Apply acquire 7) (Move item))
    (Let item (Apply acquire 7) (Drop item))
    (Fn () Unit ((Yield Int)) (Yield 1 unit))
    (Fn () Unit () (Suspend unit))
    (Curry add 1)
    (TypeMake (Spec List Int))
    (LetType MyList (TypeMake (Spec List Int)) 1)))

(define discharge-source
  '(Fn ((f (NFn () Int () (TypeNarrativeCap)))) Int () (Apply f)))

(define (invalid-syntax-diagnostic term)
  (match (elab term)
    [`(err ,d) d]
    [other (fail-check (format "elaboration succeeded unexpectedly: ~s" other))]))

(test-case "span.md §7.4: elab の結果は表層の span に依らない"
  (for ([source (in-list spanful-corpus)])
    (check-equal? (elab (annotate-surface source))
                  (elab source)
                  (format "span 付きと span なしで結果が違う: ~s" source))))

;; span.md §7: elaboration の出力は G2+ である。
(test-case "span.md §7: elab の core は G2+ に属する"
  (define checked 0)
  (for ([source (in-list spanful-corpus)])
    (match (elab (annotate-surface source))
      [(list core _ _ _)
       (set! checked (add1 checked))
       (check-true (redex-match? G2+ c core)
                   (format "G2+ の c に属さない: ~s -> ~s" source core))]
      ;; 効果宣言が不足する fixture は core を生成しないため対象外とする。
      [`(err ,_) (void)]))
  ;; 空振りで通らないよう、検査した件数を固定する。
  (check-equal? checked 19))

;; span.md §7.1: search が生成する ProofRep の span は goal と候補文脈に依らない。
(test-case "span.md §7.1: search の ProofRep は synthetic の空 span を持つ"
  (define sigma (project-goal Γ-pc0 '(root) (make-goal 'TypeNarrativeCap)))
  (check-true (pair? sigma))
  (for ([candidate (in-list sigma)])
    (match-define (list 'ProofRep s _ _) (candidate-proof candidate))
    (check-equal? s '(#:span #:synthetic 0 0))))

(test-case "span.md §7: Discharge を含む core も G2+ に属する"
  (match-define (list core _ _ _)
    (elab (annotate-surface discharge-source)))
  (check-true (redex-match? G2+ c core)
              (format "Discharge を含む core が G2+ に属さない: ~s" core)))

(test-case "span.md §7.4: span を一部だけ持つ項は拒否する"
  ;; UCore+ にも UCore にも属さない。
  ;; erase-surface は列の要素の span を落とすため、投影を通す形では
  ;; (Apply add) へ縮退して受理されてしまう（erase.rkt:43）。
  ;; 第 2 要素が span でないため入口で span を取れない。§8 の条件 2 である。
  (let ([d (invalid-syntax-diagnostic '(Apply add (#:span #:synthetic 0 0)))])
    (check-equal? (diagnostic-id d)
                  (diagnostic-code-of 'elaborate 'invalid-syntax))
    (check-equal? (diagnostic-primary-span d) '(#:span #:synthetic 0 0))
    (check-equal? (diagnostic-found d)
                  '(Apply add (#:span #:synthetic 0 0))))
  ;; 最外の span を取れるため §8 の条件 1 でそれを使う。
  (let ([d (invalid-syntax-diagnostic '(Apply (#:span #:synthetic 0 0) add 1))])
    (check-equal? (diagnostic-id d)
                  (diagnostic-code-of 'elaborate 'invalid-syntax))
    (check-equal? (diagnostic-primary-span d) '(#:span #:synthetic 0 0))
    (check-equal? (diagnostic-found d)
                  '(Apply (#:span #:synthetic 0 0) add 1))))

(test-case "span.md §3: 座標が逆順の span を持つ項は拒否する"
  ;; 文法は startByte <= endByte を書けない。UCore+ には属するが span として
  ;; 妥当でない項であり、入口の span-ok? の再帰検査で落ちる。
  (define reversed
    '(Apply (#:span #:synthetic 10 0)
            (#:var add (#:span #:synthetic 0 3))
            (#:lit 1 (#:span #:synthetic 4 5))))
  (check-true (redex-match? UCore+ e reversed))
  ;; 最外の span が span-ok? を満たさないため条件 2 へ落ちる。
  (let ([d (invalid-syntax-diagnostic reversed)])
    (check-equal? (diagnostic-id d)
                  (diagnostic-code-of 'elaborate 'invalid-syntax))
    (check-equal? (diagnostic-primary-span d) '(#:span #:synthetic 0 0))
    (check-equal? (diagnostic-found d) reversed))
  ;; 節点の span が正しく、内側の包みだけが逆順の場合も落ちる。
  (define reversed-inner
    '(Apply (#:span #:synthetic 0 5)
            (#:var add (#:span #:synthetic 3 0))
            (#:lit 1 (#:span #:synthetic 4 5))))
  ;; 最外の span は妥当であり、内側だけが逆順である。条件 1 が働く。
  (let ([d (invalid-syntax-diagnostic reversed-inner)])
    (check-equal? (diagnostic-id d)
                  (diagnostic-code-of 'elaborate 'invalid-syntax))
    (check-equal? (diagnostic-primary-span d) '(#:span #:synthetic 0 5))
    (check-equal? (diagnostic-found d) reversed-inner)))

(test-case "span.md §7.4: UCore+ の Let の包みは erase 後の Let に対応する"
  ;; 注釈ありの Let で、包みの span が第 3 要素にあることを固定する。
  ;; span-of は節点の第 2 要素を読むため、この位置には使えない。
  (define annotated (annotate-surface '(Let (x const Int) 1 x)))
  (match-define `(Let ,_ (,binder const ,annotation) ,_ ,_) annotated)
  (check-equal? (first binder) '#:bind)
  (check-equal? (second binder) 'x)
  (check-true (span-ok? (third binder)))
  (check-equal? (first annotation) '#:ty)
  (check-equal? (second annotation) 'Int)
  (check-true (span-ok? (third annotation)))
  (check-equal? (erase-surface annotated) '(Let (x const Int) 1 x)))

;; span.md §7.4: 投影すると Task 4 までの core と一致する。
(test-case "span.md §7.4: core の span を落とすと従来の core と一致する"
  (match-define (list core _ _ _) (elab '(Let x 1 (Apply add x 2))))
  (check-equal?
   (erase-core core)
   '(Let (x Int) 1 (Apply (PrimVal (Reserved o-add) add) x 2))))

(test-case "span.md §7.4: 表層の span が core へ写る"
  (match-define (list core _ _ _)
    (elab (annotate-surface '(Apply add 1 2))))
  (check-true (span-ok? (second core))
              (format "Apply の span が無い: ~s" core))
  (match-define (list 'Apply _ function argument-1 argument-2) core)
  (check-equal? (first argument-1) '#:lit)
  (check-equal? (second argument-1) 1)
  (check-true (span-ok? (third argument-1)))
  (check-equal? (first function) 'PrimVal)
  (check-true (span-ok? (second function))))

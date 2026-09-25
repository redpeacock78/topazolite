#lang racket

(require rackunit
         redex/reduction-semantics
         "../surface.rkt"
         "../ucore.rkt"
         "../../../tools/fstar-parity.rkt")

(define s0 '(#:span src 0 1))

(test-case
 "3 つのリストの要素数が spec §10.2 と一致する"
 (check-equal? (length racket-surface-constructors) 28)
 (check-equal? (length racket-ucore-constructors) 9)
 (check-equal? (length fstar-constructors) 26))

(test-case
 "対応表に違反が無い"
 (check-equal? (parity-errors) '()))

(test-case
 "片側にだけ構成子を足すと違反が出る"
 (check-equal? (parity-errors (cons 'SNewForm racket-surface-constructors))
               '("SNewForm が対応表の左欄に無い"))
 (check-equal? (parity-errors racket-surface-constructors
                              racket-ucore-constructors
                              (cons 'CNewForm fstar-constructors))
               '("CNewForm が対応表の右欄に無い")))

(test-case
 "同じ名前を 2 度並べると重複として出る"
 (check-equal? (parity-errors (cons 'SInt racket-surface-constructors))
               '("リスト 1 に SInt が重複している")))

(test-case
 "対応表の左欄にだけある名前は違反になる"
 (check-equal? (parity-errors racket-surface-constructors
                              racket-ucore-constructors
                              fstar-constructors
                              (cons (corr-row '(SGhost) '(SInt) 'one-to-one)
                                    correspondence-rows))
               '("対応表の左欄の SGhost がリスト 1 にもリスト 2 にも無い")))

(test-case
 "対応表の右欄にだけある名前は違反になる"
 (check-equal? (parity-errors racket-surface-constructors
                              racket-ucore-constructors
                              fstar-constructors
                              (cons (corr-row '(SInt) '(CGhost) 'one-to-one)
                                    correspondence-rows))
               '("対応表の右欄の CGhost がリスト 3 に無い")))

(test-case
 "対象外の行にリストの名前を置くと違反になる"
 (check-equal? (parity-errors racket-surface-constructors
                              racket-ucore-constructors
                              fstar-constructors
                              (cons (corr-row '(SInt) '() 'excluded)
                                    correspondence-rows))
               '("対象外の行の SInt がリスト 1 から 3 のどれかに在る")))

(test-case
 "kind と欄の数が食い違うと違反になる"
 (check-equal? (parity-errors racket-surface-constructors
                              racket-ucore-constructors
                              fstar-constructors
                              (cons (corr-row '(SInt SStr) '(SInt) 'one-to-one)
                                    correspondence-rows))
               '("one-to-one の行 (SInt SStr) の左欄が 1 つではない")))

(define (row-kind name)
  (for/first ([row (in-list correspondence-rows)]
              #:when (member name (corr-row-lefts row)))
    (corr-row-kind row)))

(test-case
 "命題 3 と 4 の対象外は対応表でも「対応なし」である"
 ;; spec §10.2。F* 側に節点が無いので、全称の対象集合にも入らない。
 (check-equal? (row-kind 'STypeDecl) 'none)
 (check-equal? (row-kind 'STraitDecl) 'none)
 (check-equal? (row-kind 'SImplDecl) 'none)
 (check-equal? (row-kind 'SDeriveDecl) 'none)
 (check-equal? (row-kind 'SProgram) 'none)
 (check-equal? (row-kind 'SBind) 'many-to-one)
 (check-equal? (row-kind 'SFnDecl) 'many-to-one))

;; リスト 1 と 2 の名前が、実際に Surface と UCore+ の項として組めることを見る。
;; 名前を並べた順序はリストと同じであり、数の一致も同時に確かめる。
(define surface-witnesses
  (list
   (cons 'SProgram  (redex-match? Surface sprog `(SProgram ,s0 () (SInt ,s0 1))))
   (cons 'SBind     (redex-match? Surface spitem `(SBind ,s0 let (SName ,s0 x) #:none (SInt ,s0 1))))
   (cons 'SFnDecl   (redex-match? Surface spitem `(SFnDecl ,s0 (SName ,s0 f)
                                                           ((SParam ,s0 (SName ,s0 x) (TName ,s0 Int)))
                                                           (TName ,s0 Int) (SInt ,s0 1))))
   (cons 'STypeDecl (redex-match? Surface spitem `(STypeDecl ,s0 (SName ,s0 A) (TName ,s0 Int))))
   (cons 'STraitDecl (redex-match? Surface spitem `(STraitDecl ,s0 (SName ,s0 P) ())))
   (cons 'SImplDecl  (redex-match? Surface spitem `(SImplDecl ,s0 (SName ,s0 P) (TName ,s0 Int) (SRec ,s0 ()))))
   (cons 'SDeriveDecl (redex-match? Surface spitem `(SDeriveDecl ,s0 (SName ,s0 P) (TName ,s0 Int))))
   (cons 'SInt      (redex-match? Surface sexpr `(SInt ,s0 1)))
   (cons 'SStr      (redex-match? Surface sexpr `(SStr ,s0 "a")))
   (cons 'SUnit     (redex-match? Surface sexpr `(SUnit ,s0)))
   (cons 'SBool     (redex-match? Surface sexpr `(SBool ,s0 true)))
   (cons 'SVar      (redex-match? Surface sexpr `(SVar ,s0 x)))
   (cons 'SFn       (redex-match? Surface sexpr `(SFn ,s0 ((SParam ,s0 (SName ,s0 x) (TName ,s0 Int)))
                                                      (TName ,s0 Int) (SInt ,s0 1))))
   (cons 'SApply    (redex-match? Surface sexpr `(SApply ,s0 (SVar ,s0 f) ((SInt ,s0 1)))))
   (cons 'SProj     (redex-match? Surface sexpr `(SProj ,s0 (SVar ,s0 x) (SLabel ,s0 a))))
   (cons 'SProjRec  (redex-match? Surface sexpr
                                  `(SProjRec ,s0 (SVar ,s0 x) ((SLabel ,s0 a)))))
   (cons 'SRec      (redex-match? Surface sexpr `(SRec ,s0 ((SField ,s0 (SLabel ,s0 a) (SInt ,s0 1))))))
   (cons 'SBlock    (redex-match? Surface sexpr `(SBlock ,s0 ((SBind ,s0 let (SName ,s0 x) #:none (SInt ,s0 1)))
                                                         (SVar ,s0 x))))
   (cons 'TName     (redex-match? Surface sty `(TName ,s0 Int)))
   (cons 'TRec      (redex-match? Surface sty `(TRec ,s0 ((TField ,s0 (SLabel ,s0 a) (TName ,s0 Int))))))
   (cons 'TFn       (redex-match? Surface sty `(TFn ,s0 ((TName ,s0 Int)) (TName ,s0 Int))))
   (cons 'TUnion    (redex-match? Surface sty `(TUnion ,s0 (TName ,s0 Int) (TName ,s0 String))))
   (cons 'TInter    (redex-match? Surface sty `(TInter ,s0 (TName ,s0 Int) (TName ,s0 String))))
   (cons 'SName     (redex-match? Surface sname `(SName ,s0 x)))
   (cons 'SParam    (redex-match? Surface sparam `(SParam ,s0 (SName ,s0 x) (TName ,s0 Int))))
   (cons 'SField    (redex-match? Surface sfield `(SField ,s0 (SLabel ,s0 a) (SInt ,s0 1))))
   (cons 'SLabel    (redex-match? Surface slabel `(SLabel ,s0 a)))
   (cons 'TField    (redex-match? Surface styfield `(TField ,s0 (SLabel ,s0 a) (TName ,s0 Int))))))

(define ucore-witnesses
  (list
   (cons '#:lit    (redex-match? UCore+ e `(#:lit 1 ,s0)))
   (cons '#:var    (redex-match? UCore+ e `(#:var x ,s0)))
   (cons 'Apply    (redex-match? UCore+ e `(Apply ,s0 (#:var f ,s0) (#:lit 1 ,s0))))
   (cons 'Proj     (redex-match? UCore+ e `(Proj ,s0 (#:var x ,s0) (#:lbl a ,s0))))
   (cons 'Rec      (redex-match? UCore+ e `(Rec ,s0 (((#:lbl a ,s0) imm (#:lit 1 ,s0))))))
   (cons 'Fn       (redex-match? UCore+ e `(Fn ,s0 (((#:bind x ,s0) (#:ty Int ,s0)))
                                               (#:ty Int ,s0) (#:ef () ,s0) (#:var x ,s0))))
   (cons 'Construct (redex-match? UCore+ e `(Construct ,s0 true)))
   (cons 'Let      (redex-match? UCore+ e `(Let ,s0 ((#:bind x ,s0) let) (#:lit 1 ,s0) (#:var x ,s0))))
   (cons 'Recur    (redex-match? UCore+ e `(Recur ,s0 (#:bind f ,s0) (((#:bind x ,s0) (#:ty Int ,s0)))
                                                  (#:ty Int ,s0) (#:ef () ,s0) (#:var x ,s0) (#:var f ,s0))))))

(test-case
 "リスト 1 の名前がすべて Surface の項として組める"
 (check-equal? (map car surface-witnesses) racket-surface-constructors)
 (for ([w (in-list surface-witnesses)])
   (check-true (and (cdr w) #t) (format "~a が Surface に合う" (car w)))))

(test-case
 "リスト 2 の名前がすべて UCore+ の項として組める"
 (check-equal? (map car ucore-witnesses) racket-ucore-constructors)
 (for ([w (in-list ucore-witnesses)])
   (check-true (and (cdr w) #t) (format "~a が UCore+ に合う" (car w)))))

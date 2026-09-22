#lang racket

(require redex/reduction-semantics
         "span-core.rkt")

(provide Surface surface-prog? surface-expr?)

;; spec §5.2 の Surface AST である。
;; span-core.rkt の Span は sid と s しか定義しないため、ident と label は
;; ここで定義する。
;; variable-not-otherwise-mentioned を使わないのは、それが言語の literal に
;; 現れる記号をすべて除くからである。SInt や TName は構成子名であると同時に
;; 変数名や label 名として書ける必要があり、lexer もそれらを ident として
;; 字句化する。variable-except なら除く記号を §3.1 の予約語 7 語と
;; ちょうど一致させられる。
;; usid の上書きは spec §5.4 である。Span の usid は
;; variable-not-otherwise-mentioned なので、Surface へ拡張すると Surface の
;; literal がその除外集合へ入り、(#:span SInt 0 1) が不正になる。
;; source-id は任意の symbol なので variable へ広げる。
(define-extended-language Surface Span
  (usid ::= variable)
  (ident ::= (variable-except const let mut fn type true false))
  (label ::= (variable-except const let mut fn type true false))
  (sbool ::= true false)
  (sbmode ::= const let mut)
  (sname ::= (SName s ident))
  (slabel ::= (SLabel s label))
  (sty-or-none ::= sty #:none)
  (sparam ::= (SParam s sname sty))
  (sfield ::= (SField s slabel sexpr))
  (styfield ::= (TField s slabel sty))
  (sty ::= (TName s ident)
           (TRec s (styfield ...))
           (TFn s (sty ...) sty))
  (sbind ::= (SBind s sbmode sname sty-or-none sexpr))
  (sexpr ::= (SInt s natural)
             (SStr s string)
             (SUnit s)
             (SBool s sbool)
             (SVar s ident)
             (SFn s (sparam ...) sty sexpr)
             (SApply s sexpr (sexpr ...))
             (SProj s sexpr slabel)
             (SProjRec s sexpr (slabel ...))
             (SRec s (sfield ...))
             (SBlock s (sbind ...) sexpr))
  (spitem ::= (STypeDecl s sname sty)
              (SFnDecl s sname (sparam ...) sty sexpr)
              sbind)
  (sprog ::= (SProgram s (spitem ...) sexpr)))

;; spec §11 の provide。判定は redex-match? の薄い包みである。
;; 述語を surface.rkt へ置くのは、非終端の名前を外へ漏らさないためである。
(define (surface-prog? t) (and (redex-match? Surface sprog t) #t))
(define (surface-expr? t) (and (redex-match? Surface sexpr t) #t))

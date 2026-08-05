#lang racket

(require redex/reduction-semantics)

(provide PR)

;; 目標言語。G2m の拡張にしない。extend すると τ と ε と Q が目標言語へ漏れて
;; 入り、「Portable Racket は意味論を決定しない」という不変条件が言語定義の時点
;; で崩れる。代償として pl と v の literal の定義が重複する。
(define-language PR
  (px   ::= variable-not-otherwise-mentioned)    ; 変数
  (pnm  ::= variable-not-otherwise-mentioned)    ; shim / Effect 境界の名前
  (prt  ::= move drop yield suspend curry)       ; runtime 呼び出しの名前
  (ptycode ::= variable-not-otherwise-mentioned) ; 型に由来する dispatch tag
  (K    ::= variable-not-otherwise-mentioned)    ; ADT tag
  (label ::= variable-not-otherwise-mentioned)   ; record の field 名
  (pp   ::= natural)                             ; 場所
  (pn   ::= integer)                             ; 資源識別子
  (pl   ::= integer unit string)                 ; literal

  (pop  ::= (return pnm ptycode))                ; Effect ラベル

  (penv ::= ((px pv) ...))
  (pv   ::= pl
            (PClosure penv (px ...) pc)
            (PTagged K pv ...)
            (PRec ((label pv) ...))
            (PResource pn)
            (PPlace pp))

  (pbr  ::= (K (px ...) -> pc))
  (pc   ::= pv
            px
            (PLam (px ...) pc)
            (PApp pc pc ...)
            (PLet px pc pc)
            (PLetOwned px pc pc)
            (PLetrec px pc pc)
            (PTagged K pc ...)
            (PRec ((label pc) ...))
            (PProj pc label)
            (PMatch pc (pbr ...))
            (PPrim pnm pc ...)
            (PEffect pop pc)
            (PInstall pop pc pc)
            (PRuntime prt pc ...)
            (PScopeExit (pp ...) pc)
            (PError pp))

  (pstate ::= Available Moved Dropped)
  (PH   ::= ((pp pv) ...))
  (PΩ   ::= ((pp pstate) ...))
  (event ::= (obs pv) (fin pp))
  (θ    ::= (event ...))
  (pconfig ::= (pcfg pc PH PΩ θ))

  ;; PF / PG / PE は 3 つを別々に展開する。PF の句を貼ったうえで PInstall の句
  ;; だけを足す書き方では、PE が PInstall の本体の内側へ届かない。
  ;; PRuntime の評価位置は lang.rkt:128-137 の F と同じ 4 本に限る。総称の
  ;; (PRuntime prt pv ... PF pc ...) を置くと yield の継続と suspend の本体まで
  ;; 掘れてしまい、後続が 2 つ残って §5.2 の決定性が壊れる。
  (PF ::= hole
          (PApp pv ... PF pc ...)
          (PLet px PF pc)
          (PLetOwned px PF pc)
          (PTagged K pv ... PF pc ...)
          (PRec ((label pv) ... (label PF) (label pc) ...))
          (PProj PF label)
          (PMatch PF (pbr ...))
          (PPrim pnm pv ... PF pc ...)
          (PEffect pop PF)
          (PRuntime drop PF)
          (PRuntime yield PF pc)
          (PRuntime curry PF pc)
          (PRuntime curry pv PF))
  (PG ::= hole
          (PApp pv ... PG pc ...)
          (PLet px PG pc)
          (PLetOwned px PG pc)
          (PTagged K pv ... PG pc ...)
          (PRec ((label pv) ... (label PG) (label pc) ...))
          (PProj PG label)
          (PMatch PG (pbr ...))
          (PPrim pnm pv ... PG pc ...)
          (PEffect pop PG)
          (PRuntime drop PG)
          (PRuntime yield PG pc)
          (PRuntime curry PG pc)
          (PRuntime curry pv PG)
          (PInstall pop pc PG))
  (PE ::= hole
          (PApp pv ... PE pc ...)
          (PLet px PE pc)
          (PLetOwned px PE pc)
          (PTagged K pv ... PE pc ...)
          (PRec ((label pv) ... (label PE) (label pc) ...))
          (PProj PE label)
          (PMatch PE (pbr ...))
          (PPrim pnm pv ... PE pc ...)
          (PEffect pop PE)
          (PRuntime drop PE)
          (PRuntime yield PE pc)
          (PRuntime curry PE pc)
          (PRuntime curry pv PE)
          (PInstall pop pc PE)
          (PScopeExit (pp ...) PE))

  #:binding-forms
  (PLam (px ...) pc #:refers-to (shadow px ...))
  (PClosure penv (px ...) pc #:refers-to (shadow px ...))
  (PLet px pc_1 pc_2 #:refers-to px)
  (PLetOwned px pc_1 pc_2 #:refers-to px)
  (PLetrec px pc_1 #:refers-to px pc_2 #:refers-to px)
  (K (px ...) -> pc #:refers-to (shadow px ...)))

#lang racket

(require rackunit
         redex/reduction-semantics
         "../pr-lang.rkt")

;; [REQ: BAK-001] 目標言語 PR の構文（backend-matrix.md §3）

;; 証人被覆の限界：これは公開 API で実施できる有限の証人被覆であり、言語定義と
;; の機械的な完全一致ではない。句を足したときに証人を足し忘れれば検出できず、
;; 一覧に無い句の欠落も検出できない。Redex 9.2 の language-nts は非終端名しか
;; 返さず、生成規則の右辺を返す公開 accessor が無いため、句数の突合はできない。

(define pop-a (term (return b:alpha ty:Int)))
(define pop-b (term (return b:alpha ty:Bool)))

(test-case
 "pconfig matches the pcfg constructor"
 (check-true (redex-match? PR pconfig (term (pcfg 1 () () ()))))
 (check-true
  (redex-match? PR pconfig
                (term (pcfg (PError 0) ((0 1)) ((0 Dropped)) ((fin 0))))))
 ;; 非終端名を構成子の頭に置いた形はマッチしない。
 (check-false (redex-match? PR pconfig (term (pconfig 1 () () ())))))

(test-case
 "values and computations are separated where the design requires"
 (check-true (redex-match? PR pv (term (PClosure () (a) a))))
 (check-true (redex-match? PR pv (term (PTagged k:true))))
 (check-true (redex-match? PR pv (term (PResource 3))))
 (check-true (redex-match? PR pv (term (PPlace 0))))
 (check-true (redex-match? PR pc (term (PLam (a) a))))
 ;; PLam は計算側にしか無い。
 (check-false (redex-match? PR pv (term (PLam (a) a)))))

;; PF の各句の証人。hole の位置がその文脈自身であることを確かめる。
(define pf-witnesses
  (list (term (PApp (PClosure () (a) a) hole))
        (term (PLet a hole 1))
        (term (PLetOwned a hole 1))
        (term (PTagged some hole))
        (term (PRec ((f hole))))
        (term (PProj hole f))
        (term (PMatch hole ((some (a) -> a))))
        (term (PPrim tz:add hole 1))
        (term (PEffect ,pop-a hole))
        (term (PRuntime drop hole))
        (term (PRuntime yield hole 1))
        (term (PRuntime curry hole 1))
        (term (PRuntime curry (PClosure () (a) a) hole))))

;; PG だけが持つ句。
(define pg-only-witnesses
  (list (term (PInstall ,pop-a (PLam (a) a) hole))))

;; PE だけが持つ句。
(define pe-only-witnesses
  (list (term (PScopeExit () hole))
        ;; spec §4.2 の反例項。PInstall の本体の hole を PG のままにすると
        ;; PE がここへ届かず、この行が落ちる。
        (term (PInstall ,pop-a (PLam (a) a) (PScopeExit () hole)))))

(test-case
 "every PF clause is reachable in all three contexts"
 (for ([witness (in-list pf-witnesses)])
   (check-true (redex-match? PR PF witness) (format "PF: ~s" witness))
   (check-true (redex-match? PR PG witness) (format "PG: ~s" witness))
   (check-true (redex-match? PR PE witness) (format "PE: ~s" witness))))

(test-case
 "PInstall is in PG and PE but not in PF"
 (for ([witness (in-list pg-only-witnesses)])
   (check-false (redex-match? PR PF witness) (format "PF: ~s" witness))
   (check-true (redex-match? PR PG witness) (format "PG: ~s" witness))
   (check-true (redex-match? PR PE witness) (format "PE: ~s" witness))))

(test-case
 "PScopeExit is in PE only, including under PInstall"
 (for ([witness (in-list pe-only-witnesses)])
   (check-false (redex-match? PR PF witness) (format "PF: ~s" witness))
   (check-false (redex-match? PR PG witness) (format "PG: ~s" witness))
   (check-true (redex-match? PR PE witness) (format "PE: ~s" witness))))

(test-case
 "the handler position of PInstall is not a hole"
 (check-false (redex-match? PR PE (term (PInstall ,pop-a hole 1)))))

(test-case
 "PRuntime evaluation positions match lang.rkt's F, not a generic rule"
 ;; 源の F は (Drop F) (Yield F c) (Curry F c) (Curry v F) の 4 本だけを持つ。
 ;; yield の継続、suspend の本体、move の引数は評価位置にない。総称の句を置くと
 ;; 後続が 2 つ残り、§5.2 の決定性が壊れる。
 (check-false (redex-match? PR PE (term (PRuntime yield 1 hole))))
 (check-false (redex-match? PR PE (term (PRuntime suspend hole))))
 (check-false (redex-match? PR PE (term (PRuntime move hole)))))

(test-case
 "runtime names are literals, separate from shim names"
 (check-true (redex-match? PR prt (term yield)))
 (check-true (redex-match? PR pnm (term tz:add)))
 ;; prt を独立の非終端にするのは、literal を pnm の除外集合へ入れないためである。
 (check-false (redex-match? PR pnm (term yield)))
 (check-false (redex-match? PR prt (term tz:add))))

(test-case
 "encoded source names are accepted where raw literals are not"
 ;; spec §6.4。源の x / K / label / b / nm は G2m の literal でなければ何でも取れる。
 ;; PR の literal はそれと違うので、素の名前を写すと項が PR に入らない。
 (check-false (redex-match? PR px (term yield)))
 (check-false (redex-match? PR px (term PLet)))
 (check-true (redex-match? PR px (term v:yield)))
 (check-true (redex-match? PR px (term v:PLet)))
 (check-true (redex-match? PR K (term k:true)))
 (check-true (redex-match? PR label (term f:drop)))
 (check-true (redex-match? PR pnm (term b:return)))
 ;; 構造化された τ の符号は括弧と空白を含む記号になる。
 (check-true (redex-match? PR ptycode (term |ty:(List Int)|)))
 ;; 符号化した名前は束縛子としても使える。
 (check-true (alpha-equivalent? PR
                                (term (PLet v:yield 1 v:yield))
                                (term (PLet v:return 1 v:return)))))

(test-case
 "pop compares boundary name and type code together"
 ;; equal? だけでは pop の形を確かめられない。ptycode を落とした定義でも 2 つの
 ;; 項は違うままなので、まず両方が pop に入ることを見る。
 (check-true (redex-match? PR pop pop-a))
 (check-true (redex-match? PR pop pop-b))
 (check-false (redex-match? PR pop (term (return b:alpha))))
 (check-false (equal? pop-a pop-b)))

(test-case
 "binding forms are declared"
 (check-true (alpha-equivalent? PR (term (PLam (a) a)) (term (PLam (b) b))))
 (check-true (alpha-equivalent? PR
                                (term (PLet a 1 a))
                                (term (PLet b 1 b))))
 (check-true (alpha-equivalent? PR
                                (term (PLetrec a (PLam (c) c) a))
                                (term (PLetrec b (PLam (c) c) b))))
 (check-true (alpha-equivalent? PR
                                (term (PClosure () (a) a))
                                (term (PClosure () (b) b))))
 (check-false (alpha-equivalent? PR (term (PLam (a) 1)) (term (PLam (a) 2)))))

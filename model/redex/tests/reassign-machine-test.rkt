#lang racket

(require rackunit redex/reduction-semantics
         "../lang.rkt" "../machine.rkt")

;; P1c2b。SCP-001。mut の Let は Scope の内側で place を確保する。
(define (run c)
  (apply-reduction-relation* -->g2/rules
                             (term (cfg ,c () () () ()))))

;; 再代入した値が読み出せる。
(check-equal?
 (run '(Scope () (Let (x mut Int) 1 (Let (y const Unit) (Reassign x 2) x))))
 '((cfg 2 ((0 2)) ((0 Dropped)) () ((fin 0)))))

;; MutSlot は値位置で読める。R-ReadMutSlot が無いと Proj が詰まる。
(check-equal?
 (run '(Scope ()
              (Let (r mut (Record ((a Int imm))))
                   (Rec ((a imm 1)))
                   (Proj r a))))
 '((cfg 1 ((0 (Rec ((a imm 1))))) ((0 Dropped)) () ((fin 0)))))

;; Scope 退出の観測は (fin p) 1 件だけであり、finLeaf は出ない。
(check-equal?
 (sixth (first (run '(Scope () (Let (x mut Int) 1 x)))))
 '((fin 0)))

;; 裸の place を target に書いた項は詰まる。target は (MutSlot p) のみである。
;; H に 0 を置いても R-Reassign は撃たない。
(check-equal?
 (apply-reduction-relation
  -->g2/rules
  (term (cfg (Reassign 0 1) ((0 1)) ((0 Available)) () ())))
 '())

;; R-LetB は mut の Let を受けない。側条件を狭めた結果を直接押さえる。
(check-equal?
 (length (apply-reduction-relation
          -->g2/rules
          (term (cfg (Scope () (Let (x mut Int) 1 x)) () () () ()))))
 1)

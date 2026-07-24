#lang racket

(require rackunit
         "../compat.rkt"
         "../gen.rkt"
         "../type-equiv.rkt"
         "properties-test.rkt")

;; ---------------------------------------------------------------------------
;; Preservation 回帰: elaboration は全型 compat? で受理するのに、⊢core の
;; check-as が type-equiv? へ落ちると、簡約途中の Lam 値（callables 署名は
;; 互換だが非同値の NFn）で型付けが破れる。
;; ---------------------------------------------------------------------------

;; VAR-003: 注釈型の imm field は narrow-arg を受ける NFn を要求し、
;; 実 record は wide-arg（任意 record）を受ける Fn を格納する。
(define proj-variance-source
  '(Let (x const (Record ((f (NFn ((Record ((a Int imm)))) Int () ()) imm))))
        (Rec ((f imm (Fn ((r (Record ()))) Int () 7))))
        (Proj x f)))

;; VAR-001: 高階 Apply。callback 引数の注釈は narrow-arg を受ける NFn、
;; 実引数は wide-arg を受ける Fn（互換だが非同値）。
(define apply-variance-source
  '(Apply (Fn ((callback (NFn ((Record ((a Int imm)))) Int () ())))
              Int ()
              (Apply callback (Rec ((a imm 1)))))
          (Fn ((r (Record ()))) Int () 7)))

(test-case "VAR-003: imm field の互換非同値関数を Proj する Preservation 回帰"
  (check-true (preservation-g2? proj-variance-source)))

(test-case "VAR-001: 互換非同値関数を渡す高階 Apply の Preservation 回帰"
  (check-true (preservation-g2? apply-variance-source)))

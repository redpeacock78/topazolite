#lang racket

;; [REQ: SUR-006] 多 field 射影の型付け。
;; Surface は Owned 型を綴れない（surface.md §7.2.1）ため、lowering の出力
;; （surface-lower.rkt の SProjRec 節）と同じ形を Typed Core で組んで検査する。

(require rackunit
         racket/match
         "../borrow.rkt"
         "../region.rkt"
         "../typing.rkt")

;; 余剰の Owned 欄と、mut の欄を持つ record である。
(define r-type '(Record ((x (Owned Res) imm) (y Int imm) (z Int mut))))
(define environment `((r ,r-type)))

;; lowering の出力に elaborate が型注釈を付けたあとの形である。
;; 受け側の束縛は const、結果の欄はすべて imm である。
(define (projrec labels)
  `(Let (%projrec const ,r-type)
        r
        (Rec ,(for/list ([l (in-list labels)])
                `(,l imm (Proj %projrec ,l))))))

(define (result-of core)
  (match (type-of/raw core '() '() environment (empty-region-ctx))
    [(list 'ok (list type _row)) type]
    [(list 'fail key _node _details ...) key]))

;; spec §6.4。選んだ欄だけを持つ record になり、型の row は正規形になる。
(test-case "選んだ欄だけの record になる"
  (check-equal? (result-of (projrec '(y)))
                '(Record ((y Int imm)))))

(test-case "欄の型は row の正規形になる"
  (check-equal? (result-of (projrec '(z y)))
                '(Record ((y Int imm) (z Int imm)))))

;; spec §6.4。元が mut でも結果は imm である。
(test-case "mut の欄も結果では imm になる"
  (check-equal? (result-of (projrec '(z)))
                '(Record ((z Int imm)))))

;; spec §6.5。残す label に Owned があると T-Rec が拒否する。
(test-case "Owned の欄を残す射影は拒否する"
  (check-equal? (result-of (projrec '(x y))) 'owned-record-field))

;; spec §6.6。余剰の Owned 欄を残さない射影は、narrowing ではないので
;; Proof を要求しない。r は const で束縛するだけで move されない。
(test-case "余剰の Owned 欄を落とす射影は Proof を要求しない"
  (check-equal? (result-of (projrec '(y z)))
                '(Record ((y Int imm) (z Int imm)))))

;; 射影のあとも r をそのまま使える。
(test-case "射影は受け側を消費しない"
  (check-equal?
   (result-of `(Let (q const (Record ((y Int imm)))) ,(projrec '(y)) (Proj r y)))
   'Int))

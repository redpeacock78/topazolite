#lang racket

;; [REQ: SUR-006] 多 field 射影の型付け。
;; Surface は Owned 型を綴れない（surface.md §7.2.1）ため、lowering の出力
;; （surface-lower.rkt の SProjRec 節）と同じ形を Typed Core で組んで検査する。

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../borrow.rkt"
         "../lang.rkt"
         "../machine.rkt"
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
(test-case "Owned の欄を射影すると移動必須で拒否する"
  (check-equal? (result-of (projrec '(x y)))
                'owned-variable-requires-move))

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

(define resource-record-type
  '(Record ((a Int imm)
            (optional Int imm opt)
            (owner (Option (Owned Res)) imm))))
(define resource-record-value
  '(Rec ((a imm 41)
         (optional imm (Absent Int))
         (owner imm
                (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 13)))))))
(define resource-record-present-value
  '(Rec ((a imm 41)
         (optional imm 53)
         (owner imm
                (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 13)))))))
(define (resource-let body)
  `(Let (x let ,resource-record-type) ,resource-record-value ,body))
(define (resource-let/value value body)
  `(Let (x let ,resource-record-type) ,value ,body))

(define (run-g2-value core)
  (match (run-g2 (inject-g2m core) 300)
    [`(cfg ,value ,_heap ,_states ,_tokens ,_trace) value]
    [other (error 'run-g2-value "unexpected configuration: ~s" other)]))

(test-case "資源型の Let 変数から非資源型の欄を読める"
  (check-equal? (result-of (resource-let '(Proj x a))) 'Int)
  (check-equal?
   (result-of (resource-let '(Rec ((a imm (Proj x a))
                                   (optional imm
                                     (ProjOpt Int x optional))))))
    '(Record ((a Int imm) (optional (Option Int) imm))))
  (check-equal? (run-g2-value (resource-let '(Proj x a))) 41)
  (check-equal?
   (run-g2-value (resource-let '(ProjOpt Int x optional)))
   '(Construct (Option Int) none))
  (check-equal?
   (run-g2-value (resource-let/value resource-record-present-value
                                     '(ProjOpt Int x optional)))
   '(Construct (Option Int) some 53)))

(test-case "資源型の欄は射影せず、射影後も record 全体を Move できる"
  (define moved
    (run-g2-value
     (resource-let '(Let (n const Int) (Proj x a) (Move x)))))
  (check-equal?
   (result-of (resource-let '(Proj x owner)))
   'owned-variable-requires-move)
  (check-true (redex-match? G2m v moved)))

(test-case "非変数の資源型 record を多 field 射影しても停止しない"
  (define projection
    `(Let (%projrec const ,resource-record-type)
          ,resource-record-value
          (Rec ((a imm (Proj %projrec a))
                (optional imm (ProjOpt Int %projrec optional))))))
  (check-equal?
   (result-of projection)
   '(Record ((a Int imm) (optional (Option Int) imm))))
  (check-equal?
   (run-g2-value projection)
   '(Rec ((a imm 41)
          (optional imm (Construct (Option Int) none))))))

(test-case "資源型欄の読みは label path を持ち、同じ欄の mut 借用と競合する"
  (define (check-projection core label other-label)
    (define ir (build-region-ir core))
    (define Λ (region-ctx ir '() (hash) (hash)))
    (define requests (fourth (typing-inference core '() '() '() Λ)))
    (define projection-use (findf use-request? requests))
    (define root (region-at ir '()))
    (define (check-conflict path)
      (let/ec escape
        (check-borrows
         ir (hash) (empty-psi)
         (cons (borrow-request 'x path 'mut root root core) requests)
         (lambda (_sigma rho) rho)
         (lambda (key _node) (escape key)))
        'ok))
    (check-equal? (use-request-w projection-use) 'x)
    (check-equal? (use-request-fp projection-use) (list label))
    (check-equal? (check-conflict (list label)) 'borrow-conflicting-use)
    (check-equal? (check-conflict (list other-label)) 'ok))
  (check-projection (resource-let '(Proj x a)) 'a 'optional)
  (check-projection (resource-let '(ProjOpt Int x optional))
                    'optional 'a))

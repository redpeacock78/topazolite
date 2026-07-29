#lang racket
(require rackunit "../compat.rkt")

(define (nfn obligations)
  `(NFn (Int) Int () ,obligations))

;; 大域の候補文脈。(Prop ValidPort) の witness を一つ持つ。
(define gamma
  (list (list 'portWitness
              (list '(Prop ValidPort) '(Reserved o-valid-port)
                    'portWitness 'root 'default '()))))

;; VAR-002 の回帰: 文脈を渡さなければ従来どおり集合包含だけを見る。
(check-true (compat? (nfn '()) (nfn '((Prop ValidPort)))))
(check-false (compat? (nfn '((Prop ValidPort))) (nfn '())))
(check-true (compat? (nfn '((Prop ValidPort))) (nfn '((Prop ValidPort)))))

;; RFN-003: 文脈が witness を持つ義務は、包含が無くても充足できる。
(check-true (compat? (nfn '((Prop ValidPort))) (nfn '()) gamma))
;; 文脈が持たない義務は通らない。
(check-false (compat? (nfn '((Prop NonEmpty))) (nfn '()) gamma))
;; 包含と discharge のどちらかが成り立てばよい。
(check-true (compat? (nfn '((Prop NonEmpty))) (nfn '((Prop NonEmpty)))
                     gamma))
(check-true (compat? (nfn '((Prop ValidPort) (Prop NonEmpty)))
                     (nfn '((Prop NonEmpty)))
                     gamma))
(check-false (compat? (nfn '((Prop ValidPort) (Prop NonEmpty)))
                      (nfn '())
                      gamma))

;; RFN-003: 文脈は入れ子の関数型へも伝わる。引数位置は反変であるため、
;; sub と sup が入れ替わる。
(check-true
 (compat? `(NFn (,(nfn '())) Int () ())
          `(NFn (,(nfn '((Prop ValidPort)))) Int () ())
          gamma))
(check-true
 (compat? `(NFn (Int) ,(nfn '((Prop ValidPort))) () ())
          `(NFn (Int) ,(nfn '()) () ())
          gamma))
;; record の field 位置にも伝わる。
(check-true
 (compat? `(Record ((f ,(nfn '((Prop ValidPort))) imm)))
          `(Record ((f ,(nfn '()) imm)))
          gamma))
(check-false
 (compat? `(Record ((f ,(nfn '((Prop NonEmpty))) imm)))
          `(Record ((f ,(nfn '()) imm)))
          gamma))

;; 既存の構造的な互換性は文脈を渡しても変わらない。
(check-true (compat? 'Never '(List Int) gamma))
(check-true (compat? '(Untrusted Int) '(Untrusted Int) gamma))
(check-false (compat? '(Refined Int (Prop ValidPort))
                      '(Refined Int (Prop NonEmpty))
                      gamma))

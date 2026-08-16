#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../type-equiv.rkt"
         "../compat.rkt"
         "../type-shape.rkt"
         "../typing.rkt"
         "../elaborate.rkt"
         "../diagnostic.rkt")

;; 文法。ρ の欄は natural と (RVar natural) の 2 択である。
(check-true (redex-match? G2 τ '(Borrowed Int (RVar 0))))
(check-true (redex-match? G2 τ '(BorrowedMut Int (RVar 7))))
(check-true (redex-match? G2 τ '(Borrowed Int 0)))

;; normalize-type は RVar をそのまま通す。
(check-equal? (normalize-type '(Borrowed Int (RVar 0)))
              '(Borrowed Int (RVar 0)))

;; type-equiv? は同じ k のときだけ等しい。
(check-true (type-equiv? '(Borrowed Int (RVar 0)) '(Borrowed Int (RVar 0))))
(check-false (type-equiv? '(Borrowed Int (RVar 0)) '(Borrowed Int (RVar 1))))
(check-false (type-equiv? '(Borrowed Int (RVar 0)) '(Borrowed Int 0)))

;; compat? も同じである。異なる寿命変数を暗黙に結び付けない。
(check-true (compat? '(Borrowed Int (RVar 0)) '(Borrowed Int (RVar 0))))
(check-false (compat? '(Borrowed Int (RVar 0)) '(Borrowed Int (RVar 1))))

;; 命題の鍵も k の違いを鍵の違いにする。
;; 公開されているのは canonical-proposition-key であり、型を直接受ける
;; canonical-key/normal は type-equiv.rkt の内部名である。
(check-not-equal? (canonical-proposition-key '(FieldType f (Borrowed Int (RVar 0))))
                  (canonical-proposition-key '(FieldType f (Borrowed Int (RVar 1)))))

;; 形の検査は region の欄を読まない。ρ が natural でも RVar でも通る。
(check-true (type-shape-ok? '(Borrowed Int (RVar 0))))
(check-true (type-shape-ok? '(Borrowed Int 0)))

;; 書き手は RVar を書けない。表層の型注釈の構文検査が、
;; resolve-annotation より前に借用の型そのものを拒む。
(define (annotation-error-id type)
  (define span '(#:span src 0 1))
  (match (elab `(Let ,span ((#:bind x ,span) let (#:ty ,type ,span))
                     (#:lit 1 ,span) (#:var x ,span)))
    [`(err ,d) (diagnostic-id d)]
    [other (error 'annotation-error-id "失敗しなかった: ~s" other)]))

(check-equal? (annotation-error-id '(Borrowed Int (RVar 0)))
              (diagnostic-code-of 'elaborate 'invalid-syntax))
;; 借用の型そのものが表層の語彙に無い。RVar を外しても同じ理由で落ちる。
;; したがって RVar 専用の入口検査は要らない。拒む位置が早いだけで結論は同じである。
(check-equal? (annotation-error-id '(Borrowed Int 0))
              (diagnostic-code-of 'elaborate 'invalid-syntax))

;; Diagnostic を作る側が寿命変数を印字しない。
(check-exn exn:fail?
           (lambda ()
             (diagnostic-of 'typing 'type-mismatch
                            #:primary-span '(#:span src 0 4)
                            #:expected '(Borrowed Int (RVar 0)))))
(check-not-exn
 (lambda ()
   (diagnostic-of 'typing 'type-mismatch
                  #:primary-span '(#:span src 0 4)
                  #:expected '(Borrowed Int 0))))

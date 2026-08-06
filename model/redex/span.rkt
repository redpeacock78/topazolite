#lang racket

(require redex/reduction-semantics)

(provide Span span-ok?)

;; CanonicalSpan。sourceId は利用者が与える記号か、予約 keyword #:synthetic である。
;; 予約値と利用者の sourceId は値の種類で分かれるため、名前による予約を置かない。
(define-language Span
  (rsid ::= #:synthetic)
  (usid ::= variable-not-otherwise-mentioned)
  (sid ::= usid rsid)
  (s ::= (#:span sid natural natural)))

;; 文法に合い、かつ startByte <= endByte であることを判定する。空 span は許す。
(define (span-ok? t)
  (and (redex-match? Span s t)
       (match t
         [(list '#:span _ start end) (<= start end)]
         [_ #f])))

#lang racket

(provide erase-core erase-surface)

;; 列の要素として現れた span を判定する。
(define (span-element? t)
  (and (list? t)
       (= 4 (length t))
       (eq? (car t) '#:span)))

;; span 機構の 6 つの包みを開き、構成子の直後にある span を落とす。
;; production ごとの節を書かない。span 機構の head は 7 つに固定されており、
;; 構造の再帰 1 本で UCore+ と G1+ と G2+ の全 production を覆える。
;; spanless な入力に対しては恒等写像になる。
;;
;; 再帰は閉世界である。head が keyword の list は、上の 7 節のいずれかに
;; 一致しなければ誤りとして落とす。head を将来足したときに、span が出力へ残る、
;; あるいは意図せず落ちる境界を、黙って通さずここで検出する。
(define (erase-term t)
  (match t
    [(list '#:var x _) x]
    [(list '#:lit l _) l]
    [(list '#:bind x _) x]
    [(list '#:lbl label _) label]
    [(list '#:ty type _) (erase-term type)]
    [(list '#:ef row _) (erase-term row)]
    [(list '#:span _ _ _)
     (error 'erase-term "span が項の位置に現れた: ~a" t)]
    [(? pair?)
     #:when (keyword? (car t))
     (error 'erase-term "span 機構が知らない keyword head である: ~a" t)]
    [(? list?) (map erase-term (filter (λ (u) (not (span-element? u))) t))]
    [_ t]))

(define (erase-core t) (erase-term t))
(define (erase-surface t) (erase-term t))

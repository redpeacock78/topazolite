#lang racket

;; spanful Core（G2+）の上の自由変数と捕捉回避置換。
;; Redex の substitute は (#:var x s) の包みの中へ置換項を差し込むため、
;; spanful な項には使えない（tests/span-binding-test.rkt が結果を固定している）。
;; この module は置換の単位を (#:var x s) の節点全体に取り直す。

(require redex/reduction-semantics
         "span-core.rkt")

(provide span-free-vars)

;; (#:bind x s_b) から束縛名を取り出す。
(define (bind-name b)
  (match b
    [`(#:bind ,x ,_s) x]))

;; spanful な束縛子だけを束縛形の節へ渡す。
;; spanless な G1 の分岐も 4 要素で -> を持つため、形だけでは区別できない。
(define (bind? b)
  (match b
    [`(#:bind ,_x ,_s) #t]
    [_ #f]))

;; 束縛名を bound へ足す。
(define (extend bound binds)
  (append (map bind-name binds) bound))

;; 自由変数の収集。s、cid、K、(#:bind ...) は変数参照を含まないため、
;; 束縛形の節では本体だけを名指しし、残りは一般の list 再帰へ委ねる。
;; 束縛形は span-core.rkt:142-151 と :175-176 の 7 つである。
(define (free-vars t bound)
  (match t
    [`(#:var ,x ,_s)
     (if (memq x bound) '() (list x))]
    [`(Lam ,_s ,O ,_cid ,binds ,c)
     (append (free-vars O bound)
             (free-vars c (extend bound binds)))]
    [`(Let ,_s (,b ,_ts) ,c_1 ,c_2)
     (append (free-vars c_1 bound)
             (free-vars c_2 (extend bound (list b))))]
    [`(Let ,_s (,b ,_bmode ,_ts) ,c_1 ,c_2)
     (append (free-vars c_1 bound)
             (free-vars c_2 (extend bound (list b))))]
    [`(,_s ,_K ,binds -> ,c)
     #:when (and (list? binds) (andmap bind? binds))
     (free-vars c (extend bound binds))]
    [`(,_s ,b -> ,c)
     #:when (bind? b)
     (free-vars c (extend bound (list b)))]
    [`(Recur ,_s ,_cid ,b_f ,binds ,c_1 ,c_2)
     (append (free-vars c_1 (extend (extend bound (list b_f)) binds))
             (free-vars c_2 (extend bound (list b_f))))]
    [`(RecurVal ,_s ,_cid ,b_f ,binds ,c)
     (free-vars c (extend (extend bound (list b_f)) binds))]
    [(? list?)
     (append-map (lambda (u) (free-vars u bound)) t)]
    [_ '()]))

;; 項の中で自由に現れる変数を、最初の出現順で重複なく返す。
(define (span-free-vars t)
  (remove-duplicates (free-vars t '())))

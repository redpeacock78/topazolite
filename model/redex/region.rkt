#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt"
         "erase.rkt")

(provide core-children core-points core-node)

;; 意味的な子。c の位置に来る部分項だけが子である（spec §4）。
;; span、束縛子、型注釈、label、op、O、cid、π、構築子名 K は子に数えない。
;; 子の並びは項の書き順に従う。
;;
;; Construct と Rec は c 側と v 側で同じ形を持つため、1 つの節が両方を受ける。
;; 形が同じでも production は 2 つあり、その網羅は試験の側で押さえる。
(define (core-children t)
  (match t
    [`(Apply ,c_f ,c_a ...) (cons c_f c_a)]
    [`(Let (,_ ...) ,c_1 ,c_2) (list c_1 c_2)]
    [`(Construct ,_ ,_ ,cs ...) cs]
    [`(Eliminate ,c ,brs)
     (cons c (for/list ([br (in-list brs)]) (last br)))]
    [`(Perform ,_ ,c) (list c)]
    [`(Handle ,_ ,h ,c) (list (last h) c)]
    [`(Scope ,_ ,c) (list c)]
    [`(Recur ,_ ,_ ,_ ,c_1 ,c_2) (list c_1 c_2)]
    [`(Yield ,c_1 ,c_2) (list c_1 c_2)]
    [`(Suspend ,c) (list c)]
    [`(Drop ,c) (list c)]
    [`(Curry ,c_1 ,c_2) (list c_1 c_2)]
    [`(Rec ((,_ ,_ ,cs) ...)) cs]
    [`(Proj ,c ,_) (list c)]
    [`(Discharge (ProofRep ,_ ,_) ,c) (list c)]
    [`(Lam ,_ ,_ ,_ ,c) (list c)]
    [`(RecurVal ,_ ,_ ,_ ,c) (list c)]
    [`(UVal ,v) (list v)]
    [`(RVal (ProofRep ,_ ,_) ,v) (list v)]
    [`(CurryVal ,_ ,v_1 ,v_2) (list v_1 v_2)]
    [`(Move ,_) '()]
    [`(PrimVal ,_ ,_) '()]
    [`(TypeRep ,_ ,_ ,_) '()]
    [`(ProofRep ,_ ,_) '()]
    [`(resource ,_) '()]
    ;; l ::= integer unit string、x ::= variable-not-otherwise-mentioned。
    ;; 素の値をまとめて空へ落とさず、G2 の production に属することを確かめる。
    [(? exact-integer?) '()]
    [(? string?) '()]
    [(? symbol? s)
     #:when (or (redex-match? G2 x s) (redex-match? G2 l s))
     '()]
    [other (error 'core-children "Core の形ではない: ~s" other)]))

;; point は根から目的の節点までの意味的な子の添字列である。
;; 定義域は elaboration が返す Core、すなわち G2 の項である。
;; erase-core を入口に通すため、spanful な項を渡しても同じ結果になる。
(define (core-points core)
  (let walk ([t (erase-core core)] [prefix '()])
    (cons (reverse prefix)
          (append*
           (for/list ([k (in-list (core-children t))]
                      [i (in-naturals)])
             (walk k (cons i prefix)))))))

;; point が Core の節点を指さないとき、#f を返さず error を出す。
;; #f を返すと、呼び出し側が「point が無効である」と「その位置に region が
;; 無い」を区別できない。
(define (core-node core point)
  (for/fold ([t (erase-core core)]) ([i (in-list point)])
    (let ([kids (core-children t)])
      (unless (and (exact-nonnegative-integer? i) (< i (length kids)))
        (error 'core-node "Core の節点を指さない point: ~s" point))
      (list-ref kids i))))

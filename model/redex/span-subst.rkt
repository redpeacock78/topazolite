#lang racket

;; spanful Core（G2+）の上の自由変数と捕捉回避置換。
;; Redex の substitute は (#:var x s) の包みの中へ置換項を差し込むため、
;; spanful な項には使えない（tests/span-binding-test.rkt が結果を固定している）。
;; この module は置換の単位を (#:var x s) の節点全体に取り直す。

(require redex/reduction-semantics
         "span-core.rkt")

(provide span-free-vars span-free-var-nodes span-subst)

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
;; 束縛形は span-core.rkt:142-151 と :178-179 の 7 つである。
;; 返すのは (#:var x s) の節点そのものであり、出現順に並ぶ。重複は除かない。
;; 診断の primary span には出現位置の span が要るため、名前ではなく節点を返す。
(define (free-var-nodes t bound)
  (match t
    [`(#:var ,x ,_s)
     (if (memq x bound) '() (list t))]
    [`(Lam ,_s ,O ,_cid ,binds ,c)
     (append (free-var-nodes O bound)
             (free-var-nodes c (extend bound binds)))]
    [`(Let ,_s (,b ,_ts) ,c_1 ,c_2)
     (append (free-var-nodes c_1 bound)
             (free-var-nodes c_2 (extend bound (list b))))]
    [`(Let ,_s (,b ,_bmode ,_ts) ,c_1 ,c_2)
     (append (free-var-nodes c_1 bound)
             (free-var-nodes c_2 (extend bound (list b))))]
    [`(,_s ,_K ,binds -> ,c)
     #:when (and (list? binds) (andmap bind? binds))
     (free-var-nodes c (extend bound binds))]
    [`(,_s ,b -> ,c)
     #:when (bind? b)
     (free-var-nodes c (extend bound (list b)))]
    [`(Recur ,_s ,_cid ,b_f ,binds ,c_1 ,c_2)
     (append (free-var-nodes c_1 (extend (extend bound (list b_f)) binds))
             (free-var-nodes c_2 (extend bound (list b_f))))]
    [`(RecurVal ,_s ,_cid ,b_f ,binds ,c)
     (free-var-nodes c (extend (extend bound (list b_f)) binds))]
    [(? list?)
     (append-map (lambda (u) (free-var-nodes u bound)) t)]
    [_ '()]))

;; 項の中で自由に現れる変数の出現節点を、出現順に返す。
(define (span-free-var-nodes t [bound '()])
  (free-var-nodes t bound))

;; 項の中で自由に現れる変数を、最初の出現順で重複なく返す。
(define (span-free-vars t)
  (remove-duplicates (map second (free-var-nodes t '()))))

;; (#:bind x s_b) の span。改名しても束縛子の span は動かないため、
;; 新しい束縛子はこの span を引き継ぐ。
(define (bind-span b)
  (match b
    [`(#:bind ,_x ,s) s]))

;; σ の要素。name は置き換える変数、fvs は像の自由変数、make は
;; 出現位置の span から像を作る手続きである。
;; 引数の置換は出現位置の span を捨てて像自身の span を使い、α 改名は
;; 出現位置の span を保った (#:var y* s) を作る。両者を同じ走査で扱うため、
;; 像を項ではなく「span を受け取って項を返す手続き」として持つ。
(struct repl (name fvs make) #:transparent)

;; α 改名のための σ 要素。
(define (rename-repl y y*)
  (repl y (list y*) (lambda (s) `(#:var ,y* ,s))))

;; 束縛子 binds が bodies へ届くときの前処理。
;; σ の鍵から束縛名を落とし、捕捉が起きる束縛子だけを改名する。
;; 返り値は改名後の束縛子、改名後の本体、束縛名を落とした σ である。
(define (open-scope binds bodies σ)
  (define names (map bind-name binds))
  (define σ*
    (for/list ([r (in-list σ)] #:unless (memq (repl-name r) names)) r))
  ;; 本体に自由に現れる鍵の像だけが捕捉の危険を持ち込む。
  (define live
    (for/list ([r (in-list σ*)]
               #:when (ormap (lambda (c) (memq (repl-name r) (span-free-vars c)))
                             bodies))
      r))
  (define incoming (append-map repl-fvs live))
  (for/fold ([bs '()] [bd bodies] #:result (values (reverse bs) bd σ*))
            ([b (in-list binds)])
    (define y (bind-name b))
    (cond
      [(memq y incoming)
       ;; 兄弟の束縛子と同じ名前を選ぶと、同じ並びに同名の束縛子が 2 つ並ぶ。
       ;; 本体に現れない兄弟は bd からは見えないため、binds と選択済みの bs も
       ;; 避ける対象へ入れる。
       (define y* (variable-not-in (list bd incoming binds bs) y))
       (values (cons `(#:bind ,y* ,(bind-span b)) bs)
               (map (lambda (c) (subst c (list (rename-repl y y*)))) bd))]
      [else (values (cons b bs) bd)])))

;; σ を項へ適用する。束縛形の節は free-vars と同じ 7 つである。
(define (subst t σ)
  (cond
    [(null? σ) t]
    [else
     (match t
       [`(#:var ,x ,s)
        (define r (findf (lambda (r) (eq? (repl-name r) x)) σ))
        (if r ((repl-make r) s) t)]
       [`(Lam ,s ,O ,cid ,binds ,c)
        (define-values (binds* bodies* σ*) (open-scope binds (list c) σ))
        `(Lam ,s ,(subst O σ) ,cid ,binds* ,(subst (car bodies*) σ*))]
       [`(Let ,s (,b ,ts) ,c_1 ,c_2)
        (define-values (binds* bodies* σ*) (open-scope (list b) (list c_2) σ))
        `(Let ,s (,(car binds*) ,ts) ,(subst c_1 σ) ,(subst (car bodies*) σ*))]
       [`(Let ,s (,b ,bmode ,ts) ,c_1 ,c_2)
        (define-values (binds* bodies* σ*) (open-scope (list b) (list c_2) σ))
        `(Let ,s (,(car binds*) ,bmode ,ts)
              ,(subst c_1 σ) ,(subst (car bodies*) σ*))]
       [`(,s ,K ,binds -> ,c)
        #:when (and (list? binds) (andmap bind? binds))
        (define-values (binds* bodies* σ*) (open-scope binds (list c) σ))
        `(,s ,K ,binds* -> ,(subst (car bodies*) σ*))]
       [`(,s ,b -> ,c)
        #:when (bind? b)
        (define-values (binds* bodies* σ*) (open-scope (list b) (list c) σ))
        `(,s ,(car binds*) -> ,(subst (car bodies*) σ*))]
       [`(Recur ,s ,cid ,b_f ,binds ,c_1 ,c_2)
        ;; f は c_1 と c_2 の両方へ、x ... は c_1 だけへ届く。
        (define-values (bf* bodies-f σ_f) (open-scope (list b_f) (list c_1 c_2) σ))
        (define-values (binds* bodies-x σ_x)
          (open-scope binds (list (car bodies-f)) σ_f))
        `(Recur ,s ,cid ,(car bf*) ,binds*
                ,(subst (car bodies-x) σ_x) ,(subst (cadr bodies-f) σ_f))]
       [`(RecurVal ,s ,cid ,b_f ,binds ,c)
        (define-values (bf* bodies-f σ_f) (open-scope (list b_f) (list c) σ))
        (define-values (binds* bodies-x σ_x) (open-scope binds bodies-f σ_f))
        `(RecurVal ,s ,cid ,(car bf*) ,binds* ,(subst (car bodies-x) σ_x))]
       [(? list?)
        (map (lambda (u) (subst u σ)) t)]
       [_ t])]))

;; σ-alist のすべての鍵を同時に置き換える。
;; 鍵は互いに異なるものとする。像は出現位置の span を捨てて自分の span を保つ。
(define (span-subst t σ-alist)
  (subst t
         (for/list ([p (in-list σ-alist)])
           (define img (cdr p))
           (repl (car p) (span-free-vars img) (lambda (_s) img)))))

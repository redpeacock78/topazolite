#lang racket

;; macro.md §4: マクロ定義の並びの妥当性を検査する。macro-env は module の
;; 定数ではなく引数である（traits.rkt:54 の trait-table と同じ扱いである）。

(require redex/reduction-semantics
         "span-core.rkt"
         "span-subst.rkt"
         "diagnostic.rkt"
         racket/set)

(provide macro-env-errors expand-macros macro-depth-limit)

;; 定義の 4 つ組 (nm s pattern template) を受け、違反の診断を並べて返す。
;; 順序は定義の順、1 つの定義の中では §4.3 の 3 条件の順である。
(define (macro-env-errors defs)
  (for/fold ([seen (hash)] [out '()] #:result (reverse out))
            ([d (in-list defs)])
    (match-define (list nm s pattern template) d)
    (define dup
      (cond
        [(hash-ref seen nm #f)
         => (lambda (s_prev)
              (list (diagnostic-of 'expand 'macro-name-duplicate
                                   #:primary-span s
                                   #:related (list (list 'previous-definition s_prev
                                                         "先に現れた定義である")))))]
        [else '()]))
    (define pat-dup
      (if (= (length pattern) (length (remove-duplicates pattern)))
          '()
          (list (diagnostic-of 'expand 'macro-pattern-duplicate #:primary-span s))))
    ;; template の自由変数は pattern の変数に収まらなければならない。
    ;; 主 span は当該の (#:var x s) の span であるため、自由変数の名前では
    ;; なく出現節点を拾う。
    (define free-nodes (span-free-var-nodes template pattern))
    (define free-errs
      (for/list ([node (in-list free-nodes)])
        (diagnostic-of 'expand 'macro-template-free-var
                       #:primary-span (span-of node)
                       #:related (list (list 'macro-definition s "当該のマクロ定義である")))))
    ;; template の中の Lam と MacroCall の origin は User でなければならない。
    (define origin-errs
      (for/list ([node (in-list (user-origin-violations template))])
        (diagnostic-of 'expand 'macro-origin-invalid
                       #:primary-span (span-of node)
                       #:related (list (list 'macro-definition s "当該のマクロ定義である")))))
    (values (hash-set seen nm s)
            (append (reverse (append dup pat-dup free-errs origin-errs)) out))))

;; 前順で t の部分項を歩き、pred を満たす節点を並べて返す。
;; Task 5 の non-user-macro-calls と synthetic-spans-of も同じ走査を使う。
;; 前順という順序の約束を 1 箇所へ閉じ込めるため、走査を書くのはここだけである。
(define (nodes-where t pred)
  (append (if (pred t) (list t) '())
          (if (list? t)
              (append-map (lambda (u) (nodes-where u pred)) t)
              '())))

(define (macro-call? t)
  (match t [(list 'MacroCall _s _O _nm _args) #t] [_ #f]))

(define (lam-node? t)
  (match t [(list 'Lam _s _O _cid _binds _c) #t] [_ #f]))

;; Lam も MacroCall も第 3 要素が origin である
;; （span-core.rkt:136 と macro.md §5.1）。
(define (node-origin t) (third t))

;; template の中の Lam と MacroCall のうち、origin が User でない節点を
;; 前順で並べて返す。macro.md §4.3 の第 3 条件である。
(define (user-origin-violations term)
  (nodes-where term
               (lambda (t)
                 (and (or (lam-node? t) (macro-call? t))
                      (not (eq? (node-origin t) 'User))))))

;; macro.md §6.4: 1 つの MacroCall から数えた再帰の深さの上限である。
;; 展開の総数ではない。起点の呼出しを展開する時点が深さ 1 である。
(define macro-depth-limit 32)

;; Task 4 の nodes-where を使う 2 つの述語である。
;; user-origin-violations は Lam と MacroCall の両方を見るのに対し、
;; non-user-macro-calls は MacroCall だけを見る。起点の項では Lam の
;; origin は書き手の由来をそのまま持ってよく、User 以外でも誤りではない。
(define (non-user-macro-calls term)
  (nodes-where term
               (lambda (t) (and (macro-call? t)
                                (not (eq? (node-origin t) 'User))))))

;; 入力の項が持つ合成 span を並べる。連番の起点を決めるためだけに使う。
(define (synthetic-spans-of term)
  (nodes-where term
               (lambda (t)
                 (match t
                   [(list '#:span '#:synthetic _ _) #t]
                   [_ #f]))))

;; 合成 span の連番を作る。起点は入力の項が持つ #:synthetic の k の
;; 最大値へ 1 を足した値である。span-ok? は入力の span にも #:synthetic を
;; 許すため（span-core.rkt:20-24）、起点を 0 にすると展開器の割り当てが
;; 入力の span と衝突し、展開表の鍵の意味が定まらなくなる。
;; 起点を数えるのは入力の項だけでよい。template 由来の節点は必ず新しい
;; span を受け取り、引数由来の節点の span は入力の項から来るためである。
(define (make-span-counter term)
  (define n0
    (for/fold ([m 0]) ([s (in-list (synthetic-spans-of term))])
      (max m (third s))))
  (let ([n n0])
    (lambda ()
      (set! n (add1 n))
      `(#:span #:synthetic ,n ,n))))

;; template 単体へ、置換の前に呼ぶ。
;; 返り値は span を配り直した項と、この呼出しが割り当てた span の並びである。
;; 並びは展開表の鍵の候補になる。
(define (assign-template-spans t fresh)
  (define allocated '())
  (define (walk u)
    (match u
      [(list '#:span _sid _start _end)
       (define s* (fresh))
       (set! allocated (cons s* allocated))
       s*]
      [(? list?) (for/list ([x (in-list u)]) (walk x))]
      [_ u]))
  (define t* (walk t))
  (values t* (reverse allocated)))

;; span を配った後、置換の前に呼ぶ。対象は template 由来の節点だけである。
;; PrimVal と TypeRep と ProofRep は O の欄を飛ばす。値の欄は項ではない。
;; CurryVal は O が v_f と v_a に等式で結ばれているため、丸ごと素通しする。
;; RVal は (RVal s (ProofRep s O φ) v) であり、第 2 要素は項であるから
;; 汎用の list 節が辿ってよい。
(define (rewrite-template-origins t O nm)
  (define o* `(Derived ,O (Expand ,nm)))
  (define (rec u) (rewrite-template-origins u O nm))
  (match t
    [(list 'Lam s _o cid binds body)
     (list 'Lam s o* cid binds (rec body))]
    [(list 'MacroCall s _o nm_inner args)
     (list 'MacroCall s o* nm_inner (for/list ([a (in-list args)]) (rec a)))]
    [(list 'PrimVal s o nm_p) (list 'PrimVal s o nm_p)]
    ;; CurryVal は O と等式で結ばれた部分項を持つため、丸ごと素通しする。
    [(list 'CurryVal s o v_f v_a) (list 'CurryVal s o v_f v_a)]
    [(list 'TypeRep s o ty κ) (list 'TypeRep s o ty κ)]
    [(list 'ProofRep s o φ) (list 'ProofRep s o φ)]
    [(? list?) (for/list ([u (in-list t)]) (rec u))]
    [_ t]))

;; 展開結果に残った span の集合を作る。
(define (spans-of t)
  (list->set
   (nodes-where t
                (lambda (u)
                  (match u
                    [(list '#:span _ _ _) #t]
                    [_ #f])))))

;; 公開の入口。項の中のすべての MacroCall の O が User であることを要求する。
;; 内側の展開器が作る MacroCall は (Derived O_call (Expand nm)) を持つため、
;; この不変条件は展開器の外から来た項にだけ課される。
(define (expand-macros term env)
  (define bad (non-user-macro-calls term))
  (define env-errs (macro-env-errors env))
  (cond
    [(pair? bad)
     (values #f
             (hash)
             (for/list ([node (in-list bad)])
               (diagnostic-of 'expand 'macro-origin-invalid
                              #:primary-span (span-of node))))]
    [(pair? env-errs)
     (values #f (hash) env-errs)]
    [else
     (define fresh (make-span-counter term))
     (expand-macros/internal term env fresh 0 '() (hash))]))

;; 項の子を左から順に展開する。診断が出ても兄弟の走査を続け、最後に
;; 診断を連結する。失敗した子の値は親の失敗時には使わない。
(define (expand-children children env fresh depth trace table)
  (define-values (out tbl ds)
    (for/fold ([out '()] [tbl table] [ds '()])
              ([child (in-list children)])
      (define-values (child* tbl* ds*)
        (expand-macros/internal child env fresh depth trace tbl))
      (values (cons child* out) tbl* (append ds ds*))))
  (values (reverse out) tbl ds))

;; 1 つの MacroCall を展開する。引数の子は先に走査し、兄弟の診断を
;; 連結してから自身の定義を調べる。
(define (expand-macro-call term env fresh depth trace table)
  (match-define (list 'MacroCall s_call O nm args) term)
  (define-values (args* tbl-args arg-diags)
    (expand-children args env fresh depth trace table))
  (cond
    [(pair? arg-diags)
     (values #f (hash) arg-diags)]
    [(>= depth macro-depth-limit)
     (define primary
       (if (pair? trace) (second (first trace)) s_call))
     (values #f
             (hash)
             (list (diagnostic-of 'expand 'macro-depth-exceeded
                                  #:primary-span primary
                                  #:expansion-trace trace)))]
    [else
     (define def (findf (lambda (d) (eq? (first d) nm)) env))
     (cond
       [(not def)
        (values #f
                (hash)
                (list (diagnostic-of 'expand 'macro-unknown-name
                                     #:primary-span s_call
                                     #:expansion-trace trace)))]
       [else
        (match-define (list _def-name _def-span pattern template) def)
        (cond
          [(not (= (length args*) (length pattern)))
           (values #f
                   (hash)
                   (list (diagnostic-of 'expand 'macro-arity-mismatch
                                        #:primary-span s_call
                                        #:expansion-trace trace)))]
          [else
           (define-values (template* allocated)
             (assign-template-spans template fresh))
           (define rewritten
             (rewrite-template-origins template* O nm))
           (define sigma (map cons pattern args*))
           (define expanded (span-subst rewritten sigma))
           (define s_top (span-of expanded))
           (define trace* (append trace (list (list nm s_call s_top))))
           (define-values (out tbl-inner ds)
             (expand-macros/internal expanded env fresh (add1 depth)
                                     trace* tbl-args))
           (if (pair? ds)
               (values #f (hash) ds)
               (let ([live (spans-of out)])
                 (define table*
                   (for/fold ([m tbl-inner])
                             ([s (in-list allocated)])
                     (if (and (set-member? live s)
                              (not (hash-has-key? m s)))
                         (hash-set m s trace*)
                         m)))
                 (values out table* '())))])])]))

;; 展開の再帰入口。公開入口から直接呼ばず、親の MacroCall が作った
;; (Derived O_call (Expand nm)) をそのまま次の展開へ渡す。
(define (expand-macros/internal term env fresh depth trace table)
  (match term
    [(list 'MacroCall _s _O _nm _args)
     (expand-macro-call term env fresh depth trace table)]
    [(? list?)
     (define-values (children* tbl* ds)
       (expand-children term env fresh depth trace table))
     (if (pair? ds)
         (values #f (hash) ds)
         (values children* tbl* '()))]
    [_ (values term table '())]))

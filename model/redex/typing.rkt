#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "borrow.rkt"
         "compat.rkt"
         "diagnostic.rkt"
         "erase.rkt"
         "lang.rkt"
         "origins.rkt"
         "policy.rkt"
         "region.rkt"
         "region-param.rkt"
         "rows.rkt"
         "schema.rkt"
         "search.rkt"
         "span-core.rkt"
         "type-equiv.rkt"
         "type-shape.rkt"
         "validators.rkt")

(provide core-type-of
         core-type-of/diagnostic
         core-check
         core-check-row
         type-of/raw
         typing-visited-points
         config-ok?
         with-config-typing
         ownleaf-permitted
         ownleaf-root?
         require-ownleaf-root
         config-runtime-leaf?
         control-leaf-positions-ok?
         derive-places
         join-types
         merge-field
         presence-binding-name
         field-type-binding-name
         merge-record-types/impl
         merge-record-types
         check-merge-return
         merge-witnesses-dischargeable?
         lifetime-unify-context
         unify-borrow-lifetimes
         with-lifetime-unify
         merge-position
         merge-alpha-sources
         lifetime-counter
         alpha-table
         lifetime-owner-region
         borrow-payload-borrow-free?
         payload-borrows-traceable?
         register-owner
         lifetime-collector
         emit-constraint!
         collected-constraints
         with-lifetime-collector
         (struct-out region-arg-request)
         region-arg-collector
         emit-region-arg-request!
         collected-region-args
         check-region-args
         (struct-out callable-summary)
         collected-callable-summaries
         collect-use-regions!
         typing-inference
         typing-solve
         sigma-ref
         subst-type-regions
         alpha-set
         capability-source
         contains-lifetime-var?
         materialize-fail-result
         core-type-of/materialized
         unwrap-forall-region
         function-body-environment
         check-owned-encoding)

;; 段 1 の試験専用。既定は何もしない。
;; 本体の走査へ観測を混ぜないため、probe の呼出しは infer と check-as の入口、
;; および Discharge の層を降りる loop の 3 箇所に限る。
(define typing-point-probe (make-parameter void))

;; config-ok? が heap の値を再型付けするときだけ、OwnedLeaf を持つ Rec 欄を
;; 通す。通常の Core 型検査では従来どおり owned-record-field を拒否する。
(define deriving-config? (make-parameter #f))

;; configuration の型導出と runtime-row が同じ抑止範囲を共有する。
(define (with-config-typing thunk)
  (parameterize ([deriving-config? #t])
    (thunk)))

;; 制約の収集器（spec §5.2）。既定は #f であり、その場合は何も記録しない。
;; G4b が入れた typing-point-probe と同じ形の記録先である。
;; 走査の各段へ手を入れず、infer の出口 1 か所で集める。
(define lifetime-collector (make-parameter #f))

(define (emit-constraint! c)
  (define b (lifetime-collector))
  (when b (set-box! b (cons c (unbox b)))))

(define (collected-constraints)
  (define b (lifetime-collector))
  (if b (reverse (unbox b)) '()))

(define (with-lifetime-collector thunk)
  (define b (box '()))
  (parameterize ([lifetime-collector b]) (thunk))
  (reverse (unbox b)))

;; 判定の要求の収集器（spec §7.3）。既定は #f であり、その場合は何も記録しない。
(define request-collector (make-parameter #f))

(define (emit-request! r)
  (define b (request-collector))
  (when b (set-box! b (cons r (unbox b)))))

(define (collected-requests)
  (define b (request-collector))
  (if b (reverse (unbox b)) '()))

;; §5.4。formal 鍵の designator。出現の point と節点と仮引数の位置から決める。
;; 仮引数の名前から採ると同名の仮引数を持つ入れ子の Lam が衝突し、callable の
;; 識別子から採ると 1 つの識別子を使う複数の出現が衝突し、処理系全体の
;; counter から採ると同じ項を二度型付けした結果が一致しなくなる。
;; point だけでも足りない。Task 4a の付け替えは同じ形の部分項を複製するため、
;; 1 つの点へ別の Lam が来る形がある。summary-key と同じ組を土台にする。
;; 先頭の 'formal は形で見分けるための札である。利用者の designator は
;; borrow-designator? が示すとおり記号か非負整数であり、この形とは重ならない。
;; 見分けは全形で行う。先頭の札だけを見ると、長さや添字の壊れた (formal ...)
;; を内部の鍵として受け入れてしまい、fail closed の主張が弱くなる。
(define (formal-designator Λ node index)
  (list 'formal (region-ctx-point Λ) (peel-node node) index))

(define (formal-key? w)
  (match w
    [(list 'formal _point _node (? exact-nonnegative-integer?)) #t]
    [_ #f]))

;; §5.4。雛形の収集器。関数の本体を型付けしているあいだだけ積みが伸びる。
;; 各段は自分が採った formal 鍵の集合と箱の対である。
;; 鍵の持ち主は最も内側から順に探す。積みの先頭へ無条件に入れてはならない。
;; 外側の仮引数を実引数として内側の呼出しへ渡すと、内側を実体化した結果が
;; 外側の鍵を持つ要求になる。その要求を受けるのは外側の段である。
(struct template-frame (formals box) #:transparent)
(define template-collectors (make-parameter '()))

(define (owning-frame w)
  (for/first ([f (in-list (template-collectors))]
              #:when (set-member? (template-frame-formals f) w))
    f))

;; §5.4。要求と制約を出す唯一の窓口。formal 鍵が残っていれば、関数の本体を
;; 型付けしている最中である。そのまま出さず雛形として溜め、Apply が実引数の
;; capability と RegionApp が受けた region 項で置き換えてから出す。
;; 持ち主の段が積みに無い形は、実体化の経路が抜けているということなので
;; fail closed にする。
(define (route-deferred! item w node fail)
  (cond
    [(not (formal-key? w)) #f]
    [else
     (define f (owning-frame w))
     (unless f (fail 'unresolved-borrow-owner node))
     (define b (template-frame-box f))
     (set-box! b (cons item (unbox b)))
     #t]))

(define (route-request! r node fail)
  (define w
    (if (borrow-request? r) (borrow-request-w r) (use-request-w r)))
  (unless (route-deferred! r w node fail)
    (emit-request! r)))

;; 本体の Reborrow は親が (RParam rp) であり、呼出し位置で RegionApp が
;; 受けた region 項へ置き換わるまで具体の region へ落とせない。
(define (rparam-term? t)
  (match t [`(RParam ,_) #t] [_ #f]))

;; §5.4。region-constraint は所有者の designator を欄に持たない。
;; 雛形として溜めるときは、振り分けに使った鍵を添える。
;; 実体化した後にもう一段外の雛形へ回すかどうかを、この鍵で決める。
(struct deferred-constraint (w constraint) #:transparent)

(define (route-constraint! c w node fail)
  (unless (route-deferred! (deferred-constraint w c) w node fail)
    (emit-constraint! c)))

;; Reborrow の token 集合は 1 つの収集先へしか送れない。formal 鍵と通常の
;; designator が混ざる形を任意の 1 要素で代表させると、制約の行き先が集合の
;; 反復順で変わる。formal 鍵どうしも別の frame に属するなら同じ問題なので、
;; その形を unresolved-borrow-owner で閉じる。
;; 同じ frame の formal が複数ある場合は許すが、返す代表鍵は frame の同一性を
;; 示す routing 専用であり、呼出し側の実引数 capability の選択には使わない。
;; 実体化では token 集合全体と formal の位置対応から選ぶ。
(define (uniform-token-designator tokens node fail)
  (define caps (set->list tokens))
  (define first-w (car (first caps)))
  (define first-frame (and (formal-key? first-w)
                           (owning-frame first-w)))
  (define uniform?
    (if (formal-key? first-w)
        (and first-frame
             (for/and ([cap (in-list caps)])
               (define w (car cap))
               (and (formal-key? w)
                    (eq? first-frame (owning-frame w)))))
        (for/and ([cap (in-list caps)])
          (not (formal-key? (car cap))))))
  (unless uniform?
    (fail 'unresolved-borrow-owner node))
  first-w)

;; §5.4。関数の出現ごとの要約。formals は仮引数の位置に対応する formal
;; designator の並びであり、借用でない位置は #f である。deferred は本体で
;; 集めた雛形、result-index は結果の借用が対応する仮引数の位置または #f、
;; region-subst は RegionApp が解いた rp から ρ への写像である。
(struct callable-summary (formals deferred result-index region-subst)
  #:transparent)

;; 要約を出現ごとに溜める表。既定の #f は「収集の外」であり、書き込みを
;; 黙って捨てる位置と区別する。typing の入口 2 つが parameterize する。
(define callable-summaries (make-parameter #f))

;; 鍵は point と node の対である。point だけでは足りない。同じ point へ別の
;; 節点が来る形が 2 つある。1 つは再推論であり、check-as が落ちた後に infer が
;; 同じ位置を測り直す。もう 1 つは入れ子であり、Task 4a の付け替えが同じ形の
;; 部分項を複製する。span の包みは剥がしてから鍵にする。
(define (summary-key Λ node)
  (cons (region-ctx-point Λ) (peel-node node)))

(define (record-callable-summary! Λ node summary fail)
  (define table (callable-summaries))
  (when table
    (define key (summary-key Λ node))
    (define previous (hash-ref table key #f))
    (cond
      [(not previous) (hash-set! table key summary)]
      ;; 同じ鍵へ同じ要約が来るのは再推論であり、正しい。
      [(equal? previous summary) (void)]
      ;; 別の要約が来たら鍵が出現を一意に指していない。黙って上書きすると、
      ;; 後から読む Apply が別の関数の雛形を実体化する。
      [else (fail 'unresolved-borrow-owner node)])))

(define (lookup-callable-summary Λ node)
  (define table (callable-summaries))
  (and table (hash-ref table (summary-key Λ node) #f)))

;; 借用型の region 欄を返す。借用型でなければ #f を返す。
(define (borrow-region type)
  (match (normalize-type type)
    [`(Borrowed ,_ ,ρ) ρ]
    [`(BorrowedMut ,_ ,ρ) ρ]
    [_ #f]))

;; 型木のどこかに借用があるかを、region の束縛状態に関係なく検出する。
;; 借用の所有者をこの型から復元できない位置で使う。
(define (borrowed-type-anywhere? type)
  (unbound-borrowed-type? type (set)))

;; §5.4。結果の借用と同じ region を持つ仮引数の位置を 1 つに定める。
;; 位置が無いときも 2 つ以上あるときも所有者が定まらないので #f を返す。
(define (forwarding-index parameter-types return-type)
  (define ρ-result (borrow-region return-type))
  (and ρ-result
       (match (for/list ([τ (in-list parameter-types)]
                         [i (in-naturals)]
                         #:when (equal? (borrow-region τ) ρ-result))
                i)
         [(list i) i]
         [_ #f])))

;; §5.4。呼出しの結果が運ぶ借用が、どの実引数の capability を指すのかを表す。
(struct forwarding-summary (index keys source) #:transparent)

;; §5.4。起点を解く 3 段。第 1 段は region-ctx の token を designator で引き、
;; 第 2 段は関数を通った結果に付く要約を引き、第 3 段は型が運ぶ capability を
;; 読む。Let の束縛位置と実引数の位置がこれを共有する。
(define (argument-source Λ core type index)
  (define designator (peel-node core))
  (define summary
    (or (lookup-forwarding-summary Λ core)
        (lookup-forwarding-summary (enter-child Λ index) core)))
  (or (and (borrow-designator? designator)
           (region-ctx-source Λ designator))
      (and summary (forwarding-summary-source summary))
      (capability-source type)))

;; §5.4。実引数が運ぶ capability。起点と同じ 3 段で引く。
(define (argument-capabilities Λ core index fail)
  (define summary
    (or (lookup-forwarding-summary Λ core)
        (lookup-forwarding-summary (enter-child Λ index) core)))
  (if summary
      (forwarding-summary-keys summary)
      (borrow-token-key Λ core #:fail fail)))

;; §8.1。使用の要求へ載せる起点。使用の被演算子はいずれも 0 番目の子である。
(define (use-source Λ operand type)
  (argument-source Λ operand type 0))

;; §5.4。雛形の formal 鍵、region、局所 α を呼出し位置へ置き換えて要求を出す。
(define (instantiate-deferred! summary Λ node subst sources Ψ fail)
  (define region-subst (callable-summary-region-subst summary))
  (define deferred (callable-summary-deferred summary))
  (define locals (make-hash))
  (define point (region-ctx-point Λ))
  (define ir (region-ctx-ir Λ))
  (define current-psi Ψ)
  (define (fresh-local α)
    (hash-ref! locals α (lambda () (fresh-local-lifetime!))))
  (define (subst-term t)
    (match t
      [`(RParam ,rp)
       (define mapped (hash-ref region-subst rp #f))
       (cond
         [mapped (subst-term mapped)]
         ;; 内側の Apply が外側の RegionLam の引数をまだ運ぶことがある。
         ;; 外側の雛形 frame に委ね、呼出し位置で実体化した後に収集器が
         ;; 無い場合は、写像の欠落として fail-closed にする。
         [(pair? (template-collectors)) `(RParam ,rp)]
         [else (fail 'unresolved-borrow-owner node)])]
      [_ (cond
           [(lifetime-var? t) (fresh-local t)]
           ;; 遅延した Reborrow の制約は region 項を使う一方、RegionApp の
           ;; 代入表は素の rho 整数を持つ。infer-reborrow と同じ IR ごとの
           ;; 橋を通して整数を戻してから制約を振り分ける。
           [(and ir (exact-nonnegative-integer? t)) (rho->region ir t)]
           [else t])]))
  (define (actual-caps w)
    (hash-ref subst w
              (lambda () (fail 'unresolved-borrow-owner node))))
  ;; 遅延した共有借用は Reborrow から来ている。定義時の親は formal capability
  ;; なので通常の infer-reborrow 経路では呼出し側の可変借用をまだ停止できない。
  ;; formal 鍵を実体化した後、対応する遅延制約から親を復元する。
  (define (reborrow-parent-term w)
    (for/first ([item (in-list deferred)]
                #:when (and (deferred-constraint? item)
                            (equal? (deferred-constraint-w item) w)
                            (eq? (region-constraint-kind
                                  (deferred-constraint-constraint item))
                                 'reborrow)))
      (region-constraint-left
       (deferred-constraint-constraint item))))
  (for ([item (in-list deferred)])
    (cond
      [(borrow-request? item)
       (define w (borrow-request-w item))
       (define caps (actual-caps w))
       (define child-alpha (subst-term (borrow-request-alpha item)))
       (define parent-template (reborrow-parent-term w))
       (for ([cap (in-set caps)])
         (route-request!
          (borrow-request (car cap)
                          (append (cdr cap) (borrow-request-fp item))
                          (borrow-request-mode item)
                          child-alpha
                          node)
          node fail)
         (when (and (eq? (borrow-request-mode item) 'shared)
                    parent-template)
           (define parent-term (subst-term parent-template))
           (define parent-alphas
             (for/list ([entry (in-set (psi-mut current-psi))]
                        #:when (and (equal? (first entry) (car cap))
                                    (equal? (second entry) (cdr cap))))
               (third entry)))
           (if (null? parent-alphas)
               (set! current-psi
                     (psi-suspend
                      (psi-add-mut current-psi (car cap) (cdr cap)
                                   parent-term)
                      (car cap) (cdr cap) parent-term child-alpha))
               (for ([parent-alpha (in-list parent-alphas)])
                 (set! current-psi
                       (psi-suspend current-psi
                                    (car cap) (cdr cap)
                                    parent-alpha child-alpha))))))]
      [(use-request? item)
       (define w (use-request-w item))
       ;; 遅延した Reborrow が作った局所 alpha を保つ。全ての use source を
       ;; 呼出し側の formal source に置き換えると、子借用の read が停止済みの
       ;; 親借用の read に戻る。雛形 source が空なら formal capability の直接使用
       ;; なので、呼出し側から与えた source へ戻す。
       (define template-source (use-request-source item))
       (define source
         (if (set-empty? template-source)
             (hash-ref sources w '())
             (for/set ([α (in-set template-source)])
               (if (lifetime-var? α) (fresh-local α) α))))
       (for ([cap (in-set (actual-caps w))])
         (route-request!
          (use-request (car cap)
                       (append (cdr cap) (use-request-fp item))
                       (use-request-operation item)
                       source
                       (region-at (region-ctx-ir Λ) point)
                       node
                       (use-request-kind item)
                       (use-request-otherwise item))
          node fail))]
      [else
       (define w (deferred-constraint-w item))
       (define c (deferred-constraint-constraint item))
       (define c-new
         (if (eq? (region-constraint-kind c) 'contains)
             (region-constraint 'contains
                                (subst-term (region-constraint-left c))
                                (region-at (region-ctx-ir Λ) point)
                                point node)
             (region-constraint 'reborrow
                                (subst-term (region-constraint-left c))
                                (subst-term (region-constraint-right c))
                                point node)))
       (for ([cap (in-set (actual-caps w))])
         (route-constraint! c-new (car cap) node fail))]))
  current-psi)

;; §5.5。呼出しの結果に付く要約を出現ごとに溜める表。
;; 既定の #f は「収集の外」であり、書き込みを黙って捨てる位置と区別する。
(define forwarding-summaries (make-parameter #f))

(define (record-forwarding-summary! Λ node summary fail)
  (define table (forwarding-summaries))
  (when table
    (define key (summary-key Λ node))
    (define previous (hash-ref table key #f))
    (cond
      [(not previous) (hash-set! table key summary)]
      [(equal? previous summary) (void)]
      [else (fail 'unresolved-borrow-owner node)])))

(define (lookup-forwarding-summary Λ node)
  (define table (forwarding-summaries))
  (and table (hash-ref table (summary-key Λ node) #f)))

;; §5.4。集めた要約の写し。要約は不変な構造体であり、雛形はその欄が持つ
;; 不変な並びである。可変の表そのものは外へ出さない。summary-key の文字列表現
;; で並べ、hash の走査順を外へ漏らさない。
;; 収集器の箱から読む形は採れない。箱は Lam の本体を出た時点で積みから
;; 外れており、入口まで戻ったときには空である。
(define (collected-callable-summaries)
  (define table (callable-summaries))
  (if table
      (map cdr
           (sort (hash->list table)
                 string<?
                 #:key (lambda (entry) (format "~s" (car entry)))))
      '()))

;; 使用の要求を立てる。ir が無い形では借用も無いので何もしない。
;; fp/operation/source/node/kind は要求の契約なので必須にする。
(define (emit-use-request! Λ w fp operation source node kind [otherwise #f]
                           [fail #f])
  (define ir (region-ctx-ir Λ))
  (when ir
    (define r
      (use-request w fp operation source
                   (region-at ir (region-ctx-point Λ)) node kind otherwise))
    (if fail (route-request! r node fail) (emit-request! r))))

;; spec §5.6。RegionApp の実引数は借用の使用要求とは別に集め、段 3 で
;; σ を解いた後に生存を検査する。
(struct region-arg-request (rho point node bound) #:transparent)
(define region-arg-collector (make-parameter #f))

(define (emit-region-arg-request! rho point node)
  (define collector (region-arg-collector))
  (unless collector
    (error 'emit-region-arg-request!
           "region-arg-collector が parameterize されていない: ~s" node))
  ;; spec §5.6。束縛中かどうかは発行した時点で決まる。段 3 では
  ;; RegionLam を降りた文脈が残っていないので、ここで写しを採る。
  (set-box! collector
            (cons (region-arg-request rho point node (bound-region-params))
                  (unbox collector))))

(define (collected-region-args)
  (define collector (region-arg-collector))
  (if collector (reverse (unbox collector)) '()))

;; 段 3。実引数の region が適用位置で生きていることを確認する。
;; spec §5.6。実引数が束縛中の (RParam rp) である場合は判定を通さない。
;; rp を束縛する RegionLam の本体は、rp へ渡る具体的な region が生きて
;; いる位置でしか評価されない。適用位置はその内側なので生存は保たれる。
;; 外側の RegionApp が既に検査しているため、ここで再び呼ぶ必要はない。
(define (check-region-args ir sigma requests relation fail)
  (for ([request (in-list requests)])
    (define raw (region-arg-request-rho request))
    (define bound-here?
      (match raw
        [`(RParam ,rp)
         (set-member? (region-arg-request-bound request) rp)]
        [_ #f]))
    (unless bound-here?
      (unless ir
        (fail 'region-arg-not-live (region-arg-request-node request)))
      (define rho
        (subst-type-regions raw sigma ir))
      (define at
        (region->rho ir
                     (region-at ir (region-arg-request-point request))))
      (unless (relation rho at)
        (fail 'region-arg-not-live (region-arg-request-node request))))))

;; 段 2。下限制約から σ を作る。spec §6.1。
;; ir が無い形では借用が立たないので、制約も空であり σ も空である。
(define (typing-solve ir constraints)
  (if ir
      (region-solve ir constraints)
      (list 'ok (hash))))

;; σ を読む唯一の窓口。寿命変数なら引き、具体的な region ならそのまま返す。
(define (sigma-ref σ t)
  (if (lifetime-var? t)
      (hash-ref σ (lifetime-var-index t))
      t))

;; 型が運び手である（spec §5.1）。
;; point π で推論した型の中に α が現れるなら region-at ir π は α の下限である。
;; 値の流れを別に追う解析を書くと、型の側と二重に管理することになる。
(define (collect-use-regions! type ir point)
  (when (and ir (lifetime-collector))
    (define ρ (region-at ir point))
    (let walk ([t type])
      (match t
        [`(RVar ,k)
         (emit-constraint!
          (region-constraint 'contains `(RVar ,k) ρ point #f))]
        [(? list? ts) (for-each walk ts)]
        [_ (void)]))))

;; 寿命変数の採番（spec §3.2）。借用の項 1 つにつき 1 つ作る。
;; 番号は走査の順に依存するため、診断の本文へ番号を出してはならない
;; （region.md §2 の識別子の不透明性）。
(define lifetime-counter (make-parameter #f))
(define alpha-table (make-parameter #f))

;; §5.4。alpha-table へ登録せずに寿命変数だけを採る。
(define (fresh-local-lifetime!)
  (define c (lifetime-counter))
  (define k (unbox c))
  (set-box! c (add1 k))
  `(RVar ,k))

(define (fresh-lifetime! point)
  (define α (fresh-local-lifetime!))
  (unless (and (pair? point) (eq? (car point) 'merge))
    (define t (alpha-table))
    (when t (set-box! t (hash-set (unbox t) point α))))
  α)

(define (lookup table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

(define (record-type? type)
  (match type
    [`(Record ,_) #t]
    [_ #f]))

(define (row-union left right)
  (term (row-∪ ,left ,right)))

(define (rows-union rows)
  (for/fold ([combined '()])
            ([row (in-list rows)])
    (row-union combined row)))

(define (row-difference row removed)
  (term (row-\\ ,row ,removed)))

(define (row-subset? left right)
  (term (row-⊆ ,left ,right)))

(define (row=? left right)
  (row-equiv? left right))

;; VAR-001..003: checking は elaboration と同じ compat? を全型で共有する。
;; Never の bottom 受理は compat? の Never 分岐が担う。
;; RFN-003: discharge に使う文脈は大域の Γ_pc⁰ に限る。merge の W は渡さない。
;; region どうしの関係は current-region-relation から取る。既定は equal? で
;; あり、region 引数を書かない programme の判定は変わらない。
(define (type-compatible? actual expected)
  (compat? actual expected Γ-pc0 (current-region-relation)))

;; ROW-005。Eliminate が作った Union の導入点だけで、各枝の具体型を
;; 合流型の成分として再照合する。一般の mut field 互換性は不変のままにし、
;; Assign の全成分検査へこの緩和を漏らさない。
;; mut の否定側は fail-closed の番人である。infer-eliminate の expected は
;; 常に枝型の merge なので、well-formed な枝では member 性が構造的に成り立つ。
;; この側は将来の不正な拡張を黙って受理しないために残す。
(define (merge-branch-compatible? actual expected)
  (define (union-type? type)
    (and (pair? type) (eq? (first type) 'Union)))
  (define (union-members-compatible? actual expected)
    (and (union-type? expected)
         (for/and ([actual-member
                    (in-list (if (union-type? actual)
                                 (union-members actual)
                                 (list actual)))])
           (for/or ([expected-member (in-list (union-members expected))])
             (type-equiv? actual-member expected-member)))))
  (match* (actual expected)
    [('Never _) #t]
    [((list 'Record actual-row) (list 'Record expected-row))
     (for/and ([field (in-list expected-row)])
       (match field
         [`(,label ,expected-type ,expected-mode)
          (match (field-row-lookup actual-row label)
            [`(,actual-type ,actual-mode)
             (case expected-mode
               [(imm) (and (memq actual-mode '(imm mut))
                           (type-compatible? actual-type expected-type))]
               [(mut) (and (eq? actual-mode 'mut)
                           (or (type-equiv? actual-type expected-type)
                               (union-members-compatible?
                                actual-type expected-type)))]
               [else #f])]
            [_ #f])]
         [_ #f]))]
    [(_ _) (type-compatible? actual expected)]))

(define (type? value)
  (and (redex-match? G2m τ value)
       (type-shape-ok? value)
       (type-normal? value)))

(define (row? value)
  (and (redex-match? G2m ε value)
       (effect-row-normal? value)))

(define (callable-id? value)
  (redex-match? G1 cid value))

(define (unique-table? table)
  (and (list? table)
       (andmap (λ (entry)
                 (and (list? entry) (= (length entry) 2)))
               table)
       (not (check-duplicates (map first table)))))

(define (valid-places? places)
  (and (unique-table? places)
       (for/and ([entry (in-list places)])
         (match entry
           [(list (? exact-nonnegative-integer?) type)
            (type? type)]
           [_ #f]))))

;; 一番外の位置より内側に ForallRegion が現れないか。
;; type? は redex の τ を見るだけであり、ForallRegion をどの位置にも許す。
;; type-shape-ok? も ForallRegion の本体へ素通しで降りるだけである。
;; そのため入れ子を入口で落とすのはこの検査の仕事である。
(define (forall-region-free? type)
  (match type
    [`(ForallRegion ,_ ,_) #f]
    [(? list? parts) (andmap forall-region-free? parts)]
    [_ #t]))

(define (valid-callables? callables)
  (and (unique-table? callables)
       (for/and ([entry (in-list callables)])
         (match entry
           [(list callable signature)
            (and (callable-id? callable)
                 (type? signature)
                 (match signature
                   [`(NFn ,_ ,_ ,_ ,_) (forall-region-free? signature)]
                   [`(ForallRegion (,rps ...) (NFn ,_ ,_ ,_ ,_))
                    (and (andmap symbol? rps)
                         (forall-region-free? (third signature)))]
                   [_ #f]))]
           [_ #f]))))

;; callables の署名から ForallRegion の包みを 1 段剥がす。
;; 剥がした本体の (RParam rp) は、context が渡した付け替え後の名前へ位置で
;; 対応させる。context が無い形と束縛の数が合わない形は #f を返す。
(define (unwrap-forall-region signature context)
  (match signature
    [`(ForallRegion (,rps ...) ,body)
     (and (list? context)
          (= (length rps) (length context))
          (subst-region-params
           body
           (for/hash ([rp (in-list rps)] [name (in-list context)])
             (values rp `(RParam ,name)))))]
    [_ #f]))

(define (valid-environment? environment)
  (and (list? environment)
       (for/and ([entry (in-list environment)])
         (match entry
           [(list (? symbol?) type) (type? type)]
           [_ #f]))))

(define (extend environment names types)
  (append (map list names types) environment))

(define (without-owned environment)
  (filter (λ (entry) (not (owned-type? (second entry))))
          environment))

;; G5c5b1 spec §7 と §8。本体の環境を作る。Owned<τ> の仮引数は payload の型
;; τ で束縛する。生名は本体から直接見えず、生成した Let が surface の名前へ
;; Owned<τ> を与えるためである。E-Var は Owned<_> の変数を裸で参照すること
;; を禁じており、生名を Owned<τ> で入れると Let の右辺の参照が落ちる。
;; 外側の環境から Owned の項目を落とすのは従来どおりである。Owned の捕捉は
;; elaborate が Curry の固定引数へ変換するため、この補助は外側の Owned を
;; 本体へ直接見せない。
(define (function-body-environment environment parameters parameter-types)
  (extend (without-owned environment)
          parameters
          (for/list ([type (in-list parameter-types)])
            (match type
              [`(Owned ,payload) payload]
              [_ type]))))

;; 項のどこかにその記号が現れるかを見る。束縛の位置も数える。
(define (core-mentions? core name)
  (let walk ([t (erase-core core)])
    (cond
      [(eq? t name) #t]
      [(pair? t) (or (walk (car t)) (walk (cdr t)))]
      [else #f])))

;; G5c5b1 spec §8。Owned の仮引数を本体の形で符号化した Typed Core を
;; 検査する。parameters は Lam または Recur の仮引数列であり、Owned の位置
;; には生名が入っている。inner は本体を包む Scope の直下の計算である。
;;
;; 条件を満たさない Typed Core は拒否する。値の形から生名を推測して救う
;; ことはしない。手で書いた不正な Core をここで止める。
(define (check-owned-encoding parameters parameter-types inner node fail)
  (define owned-positions
    (for/list ([name (in-list parameters)]
               [type (in-list parameter-types)]
               #:when (owned-type? type))
      (list name type)))
  (define reserved (list->set parameters))
  (define body
    (let loop ([pending owned-positions] [core inner] [seen '()])
      (cond
        [(null? pending) core]
        [else
         (match-define (list raw declared) (first pending))
         (match (peel-node core)
           [`(Let (,binder-node ,binding-mode ,type-node) ,bound-node ,next)
            (define binder (peel-bind binder-node))
            ;; binder は仮引数のどの名前とも衝突せず、連なりの中で一意で
            ;; ある。衝突を許すと、生名を握り直す形や同じ名前を二度束縛
            ;; する形が通ってしまう。
            (unless (and (eq? (peel-node bound-node) raw)
                         (eq? binding-mode 'let)
                         (type-equiv? (peel-ty type-node) declared)
                         (not (set-member? reserved binder))
                         (not (memq binder seen)))
              (fail 'owned-parameter-missing-binding node))
            (loop (cdr pending) next (cons binder seen))]
           [_ (fail 'owned-parameter-missing-binding node)])])))
  ;; 生名は対応する Let の右辺にちょうど 1 回だけ現れる。外したあとの本体
  ;; に 1 度でも現れれば符号化が壊れている。自由出現だけを数えると、内側の
  ;; Let が生名を shadow する形を見逃す。束縛の位置も数える。
  ;; elab 全体で共有する連番と生成側の予約集合が本体の記号を避けるため、
  ;; 正しく生成した Core がこの検査に当たることはない。
  (for ([entry (in-list owned-positions)])
    (when (core-mentions? body (first entry))
      (fail 'owned-raw-parameter-misuse node)))
  body)

(define (check-many/full cores types Λ Ψ environment places callables node fail
                         [start-index 0]
                         #:adopt? [adopt? #t])
  (unless (= (length cores) (length types))
    (fail 'arity-mismatch node (length types) (length cores)))
  (let loop ([cores cores]
             [types types]
             [i start-index]
             [current-psi Ψ]
             [rows '()]
             [actuals '()])
    (if (null? cores)
        (list (reverse rows) current-psi (reverse actuals))
        (match (check-as/full (first cores)
                              (first types)
                              (enter-child Λ i)
                              current-psi
                              environment places callables fail
                              #:adopt? adopt?)
          [(list row next-psi actual)
           (loop (rest cores)
                 (rest types)
                 (add1 i)
                 next-psi
                 (cons row rows)
                 (cons actual actuals))]))))

;; 既存の呼び出しは実引数の型を要らない。第 3 要素を落として渡す。
(define (check-many cores types Λ Ψ environment places callables node fail
                    [start-index 0])
  (match (check-many/full cores types Λ Ψ environment places callables node fail
                          start-index)
    [(list rows psi _) (list rows psi)]))

;; config の型導出のときだけ、runtime の leaf をそのまま欄へ許す。
;; Rec の欄は既存の deriving-config? 節が同じ役目を別に持つ。
(define (config-runtime-leaf? core)
  (and (deriving-config?)
       (match (peel-node core)
         [`(OwnedLeaf ,_ ,_) #t]
         [_ #f])))

(define (check-construct constructor fields data-type
                         Λ Ψ environment places callables node fail)
  ;; 呼び出し側は G2+ の ts、つまり (#:ty τ s) を包みのまま渡す。
  ;; 剥がす位置をここに 1 つだけ置き、以降は実型だけを使う。
  (define actual-type (peel-ty data-type))
  (define schema (constructor-schema actual-type))
  (unless schema (fail 'unknown-data-type node actual-type))
  (define field-types (lookup schema constructor))
  (unless field-types (fail 'unknown-constructor node constructor))
  ;; Owned な欄は producer の根として OwnLeaf を必須にする。包んでいない欄は
  ;; 従来と同じ owned-constructor-field で落とす。config の runtime leaf だけは
  ;; deriving-config? の検査範囲で既に OwnedLeaf になっているため通す。
  (define permitted
    (for/list ([field-type (in-list field-types)]
               [field (in-list fields)]
               #:when (owned-type? field-type))
      (unless (config-runtime-leaf? field)
        (require-ownleaf-root field 'owned-constructor-field node fail))
      field))
  (match (parameterize ([ownleaf-permitted permitted])
           (check-many fields field-types Λ Ψ environment places callables node fail))
    [(list rows next-psi)
     (list (rows-union rows) next-psi)]))

(define (peel-eliminate-wrapper data-type)
  ;; 借用と所有は data 型を包むだけで構成子を変えない。
  ;; 包みを剥がして schema を引き、包みごとに決まる rewrap を欄の型へ配る。
  ;; Borrowed は欄の型を同じ region で包み直す。Owned は欄が宣言どおりの型を
  ;; 保つため rewrap は恒等である。
  ;; BorrowedMut は構成子の欄に mode が無く、可変の欄と不変の欄を区別できない
  ;; ため節を置かない。節が無ければ包みが剥がれず、constructor-schema が偽を
  ;; 返して non-data-eliminate で落ちる。
  (match data-type
    [`(Borrowed ,τ ,ρ) (values τ (lambda (t) `(Borrowed ,t ,ρ)))]
    [`(Owned ,τ) (values τ values)]
    [_ (values data-type values)]))

(define (branch-contexts branches data-type Λ environment node scrutinee fail)
  (define-values (data-core rewrap) (peel-eliminate-wrapper data-type))
  (define schema-core (constructor-schema data-core))
  (unless schema-core (fail 'non-data-eliminate scrutinee))
  (define schema
    (for/list ([row (in-list schema-core)])
      (list (first row) (map rewrap (second row)))))
  (unless (= (length branches) (length schema))
    (fail 'non-exhaustive-eliminate node))
  (define plain-branches (map peel-branch branches))
  (for ([branch (in-list branches)]
        [plain (in-list plain-branches)])
    ;; 枝の形だけを spanless な文法で検査し、本文は spanful のまま子へ渡す。
    ;; 本文までそのまま G2m へ照合すると、子の span が理由なく不一致になる。
    (unless (redex-match? G2m br (erase-core plain))
      (fail 'ill-typed branch)))
  (define expected-constructors (map first schema))
  (define actual-constructors (map first plain-branches))
  (when (check-duplicates actual-constructors)
    (fail 'duplicate-branch-constructor node))
  (for ([constructor (in-list expected-constructors)])
    (unless (member constructor actual-constructors)
      (fail 'non-exhaustive-eliminate node)))
  (for ([branch (in-list branches)]
        [plain (in-list plain-branches)])
    (match-define `(,constructor (,parameters ...) -> ,_) plain)
    (define field-types (lookup schema constructor))
    (unless field-types (fail 'unknown-constructor branch constructor))
    (unless (= (length parameters) (length field-types))
      (fail 'branch-binder-arity branch (length field-types) (length parameters)))
    (when (check-duplicates (map peel-bind parameters))
      (fail 'duplicate-branch-binder branch)))
  ;; scrutinee の型も schema の欄の型も capability を運ばないときは表を引かない。
  ;; いま通る programme はここを通る。
  (define carries?
    (or (type-carries-capability? data-type)
        (ormap type-carries-capability? (append* (map second schema)))))
  ;; capability を運ぶのに表が作れない scrutinee は所有者を辿れない。
  ;; 現行は infer-eliminate だけが capability-in-eliminate で落としており、
  ;; 期待型を与える check-eliminate は診断も受け渡しも無しに受理していた。
  ;; この 3 分岐を branch-contexts へ置くことで、その非対称が消える。
  (define field-table
    (and carries? (capability-field-table Λ scrutinee)))
  ;; 表が無い scrutinee でも、借用そのものが所有者を運んでいれば欄へ辿れる。
  ;; その場合は capability の path の末尾へ欄の位置を積む。
  (define scrutinee-ws
    (and carries? (not field-table) (borrow-token-key Λ scrutinee)))
  (when (and carries?
             (not field-table)
             (or (not scrutinee-ws) (set-empty? scrutinee-ws)))
    (fail 'unresolved-borrow-owner scrutinee))
  (for/list ([branch (in-list plain-branches)]
             [i (in-naturals 1)])
    (match-define `(,constructor (,parameters ...) -> ,body) branch)
    (define field-types (lookup schema constructor))
    (define binders (map peel-bind parameters))
    ;; 分配の規則は capability-of と共有する。鍵が表に無い分岐は
    ;; その label の値が来ないことを意味するため、空の token を張る。
    (define bindings
      (cond
        [field-table
         (capability-branch-bindings field-table constructor binders)]
        [carries?
         (capability-projection-bindings scrutinee-ws binders)]
        [else
         (capability-branch-bindings #f constructor binders)]))
    (define Λ_branch
      (for/fold ([Λ_acc Λ])
                ([x (in-list binders)] [τ (in-list field-types)]
                 [entry (in-list bindings)])
        (region-ctx-add-token (register-owner Λ_acc x τ)
                              x
                              (car entry)
                              #f
                              #f
                              (cdr entry))))
    (list body
          (extend environment
                  binders
                  field-types)
          (enter-child Λ_branch i))))

(define (check-eliminate scrutinee branches expected
                         Λ Ψ environment places callables node fail
                         [compatible? type-compatible?])
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define data-type (first scrutinee-result))
  (define contexts
    (branch-contexts branches data-type Λ environment node scrutinee fail))
  (define branch-results
    (for/list ([context (in-list contexts)])
      (check-as/full (first context)
                     expected
                     (third context)
                     (third scrutinee-result)
                     (second context)
                     places
                     callables
                     fail
                     compatible?)))
  (define branch-psi
    (for/fold ([joined (third scrutinee-result)])
              ([result (in-list branch-results)])
      (psi-join joined (second result))))
  ;; 分岐ごとに別の α を持つ借用を 1 本へ合流する。合流しなかったときは
  ;; expected を返し、分岐 0 の型を根拠なく選ばない。
  (define unified
    (parameterize ([merge-position
                    (list (region-ctx-ir Λ) (region-ctx-point Λ) node)])
      (with-lifetime-unify
       (lambda ()
         (unify-borrow-lifetimes
          (map (lambda (result) (normalize-type (third result)))
               branch-results))))))
  (define merged (if (= (length unified) 1) (first unified) expected))
  (list (rows-union
         (cons (second scrutinee-result)
               (map first branch-results)))
        branch-psi
        merged))

;; CMP-001: 2 つの型を Union で合わせ、同値な構成要素を正規化で畳む。
(define (join-types left right)
  (normalize-type `(Union ,left ,right)))

;; §10.1。合流の memo。merge-record-types/impl が 1 回の合流につき 1 つ張る。
;; merge-fields と merge-witness-context が同じ型の並びへ同じ α_m を得るための共有である。
(define lifetime-unify-context (make-parameter #f))

;; 合流の制約の診断位置。分岐を型付けする側が張る（§10.2）。
;; 値は `(list ir point node)` か `#f` である。
;; `#f` のときは制約を立てない。span を引けない節点で診断を出さないためである。
;; ir を持つのは、α_m の下限に合流位置の region を置くためである。
(define merge-position (make-parameter #f))

;; §8.1。合流した α から、その合流が受け取った分岐の ρ の集合への対応。
;; lifetime-counter や alpha-table と同じく、寿命を 1 つの typing の文脈に限る。
(define merge-alpha-sources (make-parameter #f))

(define (with-lifetime-unify thunk)
  (parameterize ([lifetime-unify-context (box (hash))]) (thunk)))

;; 借用の寿命だけを合流する。payload が一致する借用が 2 つ以上あるときに働く。
;; 文脈が無いとき（合流の外から呼ばれたとき）は何もしない。
(define (unify-borrow-lifetimes types)
  (define memo (lifetime-unify-context))
  (cond
    [(not memo) types]
    [(hash-ref (unbox memo) types #f) => values]
    [else
     (define result (unify-borrow-lifetimes/fresh types))
     (set-box! memo (hash-set (unbox memo) types result))
     result]))

(define (borrow-shape t)
  (match t
    [`(Borrowed ,payload ,ρ) (list 'Borrowed payload ρ)]
    [`(BorrowedMut ,payload ,ρ) (list 'BorrowedMut payload ρ)]
    [_ #f]))

(define (unify-borrow-lifetimes/fresh types)
  (define shapes (map borrow-shape types))
  (cond
    ;; 全てが借用であり、構築子と payload が一致し、
    ;; かつ少なくとも 1 つの枝が寿命変数を持つときだけ合流する。
    ;; 全ての枝が具体的な region のときは G5b のままにする（§3.1）。
    [(and (andmap values shapes)
          (> (length shapes) 1)
          (for/and ([s (in-list (rest shapes))])
            (and (eq? (first s) (first (first shapes)))
                 (equal? (second s) (second (first shapes)))))
          (for/or ([s (in-list shapes)]) (lifetime-var? (third s))))
     (define ctor (first (first shapes)))
     (define payload (second (first shapes)))
     (define α_m (fresh-lifetime! (list 'merge (length shapes))))
     ;; §8.1。合流した α が受け取った分岐の ρ を記録する。
     ;; capability-source はこれを葉まで展開する。
     (hash-set! (merge-alpha-sources) α_m
                (for/set ([s (in-list shapes)]) (third s)))
     (define pos (merge-position))
     ;; 位置が無い呼び出しでは制約を立てない。§10.2。
     (when (and pos (first pos))
       (define ir (first pos))
       (define point (second pos))
       (define node (third pos))
       ;; α_m の下限を必ず 1 本立てる。合流した値は合流位置で生きている。
       (emit-constraint!
        (region-constraint 'contains α_m (region-at ir point) point node))
       (for ([s (in-list shapes)])
         (define ρ (third s))
         (if (lifetime-var? ρ)
             ;; 合流した値は両分岐の寿命に収まる。§10.1。
             (emit-constraint!
              (region-constraint 'merge ρ α_m point node))
             ;; 具体の側は下限である。§3.1。
             (emit-constraint!
              (region-constraint 'contains α_m (rho->region ir ρ)
                                 point node)))))
     (list (list ctor payload α_m))]
    [else types]))

;; CMP-001/ROW-005: 同じ label を持つ field を合わせる。
;; 異型があれば可変性を保ったまま Union join する。
;; 可変性が枝の間で食い違う field だけを imm へ落とす。
(define (merge-field left right)
  (merge-fields (list left right)))

(define (presence-binding-name label)
  (string->symbol (format "presence-~a" label)))

(define (field-type-binding-name label index)
  (string->symbol (format "field-type-~a-~a" label index)))

(define (merge-witness-binding name proposition)
  (list name
        (list proposition '(Reserved o-merge)
              name 'root 'default '())))

;; branch 型を正規化し、Union 正規化と同じ順序・同値判定で重複を畳む。
(define (distinct-normal-types types)
  (define normalized (map normalize-type types))
  (and (andmap values normalized)
       (unify-borrow-lifetimes (sort-then-dedup normalized))))

;; RFN-002/CMP-001: merge が立てる局所 witness 文脈。
;; 各 field の Presence に加え、異型 join には branch 型ごとの FieldType を置く。
(define (merge-witness-context types merged-row)
  (append-map
   (lambda (field)
     (define label (first field))
     (define branch-types
       (for/list ([type (in-list types)])
         (first (field-row-lookup (second type) label))))
     (define distinct-types (distinct-normal-types branch-types))
     (define presence-name (presence-binding-name label))
     (cons
      (merge-witness-binding presence-name `(Presence ,label))
      (if (> (length distinct-types) 1)
          (for/list ([type (in-list distinct-types)]
                     [index (in-naturals)])
            (define name (field-type-binding-name label index))
            (merge-witness-binding name `(FieldType ,label ,type)))
          '())))
   merged-row))

(define (merge-fields fields)
  (define first-field (first fields))
  (define label (first first-field))
  ;; 全枝が mut のときにだけ mut を保つ。1 枝でも imm なら、書き込みが
  ;; imm 枝の不変性を破りうるため imm へ落とす。
  (define all-mutable?
    (for/and ([field (in-list fields)]) (eq? (third field) 'mut)))
  (define types (distinct-normal-types (map second fields)))
  (and
   (for/and ([field (in-list fields)])
     (eq? (first field) label))
   types
   (cond
     [(null? (rest types))
      (list label (first types) (if all-mutable? 'mut 'imm))]
     ;; 異型でも可変性は保つ。field の型を Union にしたまま mut で残す
     ;; （spec §9.1、ホワイトペーパー §4.5.3）。書き戻しの安全性は
     ;; Assign の側が受け持ち、Union の全成分と両立しない値を拒む
     ;; （spec §9.2 の infer-assign）。
     [else
      (define joined
        (for/fold ([joined (first types)])
                  ([type (in-list (rest types))])
          (join-types joined type)))
      (and joined (list label joined (if all-mutable? 'mut 'imm)))])))

;; ROW-005: 返り値は 3 状態である。field 行なら合流成功、'absent は「どれかの
;; branch にこの field が無い」正常な脱落、#f は正規化または join の失敗であり
;; merge 全体の fail-closed へ伝播する。
;; 両者を #f で兼ねると、失敗が脱落として黙って握り潰される。
(define (merge-common-field types first-field)
  (define label (first first-field))
  (define fields
    (for/list ([type (in-list types)])
      (assoc label (second type))))
  (if (andmap values fields)
      (merge-fields fields)
      'absent))

;; RFN-002/CMP-001/ROW-005: 全 branch に常在する field を合わせる。異型は
;; 可変性を保ったまま Union join する。どれかの branch に無い field だけが落ちる。
;; types は空でないことを呼び出し側が保証する。
(define (merge-record-types/impl types)
  (with-lifetime-unify
   (lambda ()
     (define merged-fields
       (for/list ([field (in-list (second (first types)))])
         (merge-common-field types field)))
     (cond
       [(memq #f merged-fields) (values #f '())]
       [else
        (define merged-row
          (filter (lambda (field) (not (eq? field 'absent))) merged-fields))
        (define merged-type (normalize-type `(Record ,merged-row)))
        (if merged-type
            (values merged-type
                    (merge-witness-context types (second merged-type)))
            (values #f '()))]))))

;; POL-002/ROW-004: 合流 row の label は一意で昇順、witness 列は wf-context? を
;; 満たし束縛名が重複しない。#f だけが fail-closed 返却である。(Record ()) は
;; 共通 field が残らない正常な合流であり、成功返却として不変条件を適用する。
;; 両者を同じ形と見なすと、正規化失敗が「空 row の合流に成功した」として素通り
;; する。
;; ROW-005 以降、#f は merge-common-field から伝播した正規化・join の失敗と、
;; 合流 row 自身の正規化失敗の 2 経路で立つ。
(define (check-merge-return args returns)
  (match returns
    [(list #f '()) #t]
    [(list `(Record ,row) witnesses)
     (define labels (map first row))
     (define names (map first witnesses))
     (and (field-row-unique? row)
          (equal? labels (sort labels symbol<?))
          (wf-context? witnesses)
          (= (length names) (length (remove-duplicates names))))]
    [_ #f]))

(define merge-record-types
  (policy-wrap 'RowPolicy 'merge-record-types
               merge-record-types/impl
               check-merge-return))

;; RFN-002: merge の局所検査。その merge が立てた W だけを候補文脈として、
;; 要求された常在性の義務が充足できるかを見る。型付けの受理条件ではなく、
;; merge ごとに成り立つ性質として検査する。
(define (merge-witnesses-dischargeable? types obligations)
  (define-values (merged witnesses) (merge-record-types/impl types))
  (and merged
       (obligations-dischargeable? obligations witnesses)))

(define (infer-eliminate scrutinee branches Λ Ψ environment places callables node fail)
  (define scrutinee-result
    (infer scrutinee (enter-child Λ 0) Ψ environment places callables fail))
  (define data-type (first scrutinee-result))
  (define contexts
    (branch-contexts branches data-type Λ environment node scrutinee fail))
  (define attempts
    (for/list ([context (in-list contexts)])
      (infer (first context)
             (third context)
             (third scrutinee-result)
             (second context)
             places
             callables
             fail)))
  (define non-never
    (filter (lambda (result)
              (not (eq? (first result) 'Never)))
            attempts))
  (define types (map first non-never))
  (define result-type
    (cond
      [(null? types) 'Never]
      [(andmap record-type? types)
       ;; RFN-002: W は merge の局所検査だけで使う。型へは載せない。
       (define-values (merged _witnesses)
         (parameterize ([merge-position
                         (list (region-ctx-ir Λ) (region-ctx-point Λ) node)])
           (merge-record-types/impl types)))
       (unless merged (fail 'unmergeable-branch-records node))
       merged]
      [(ormap record-type? types)
       (fail 'incompatible-branch-types node)]
      [else (first types)]))
  (define branch-rows
    (for/list ([context (in-list contexts)])
      (check-as (first context)
                result-type
                (third context)
                (third scrutinee-result)
                (second context)
                places
                callables
                fail
                merge-branch-compatible?)))
  (define branch-psi
    (for/fold ([joined (third scrutinee-result)])
              ([result (in-list branch-rows)])
      (psi-join joined (second result))))
  (list result-type
        (rows-union
         (cons (second scrutinee-result)
               (map first branch-rows)))
        branch-psi))

;; [REQ: BOR-001] spec §14。関数境界で Borrowed と BorrowedMut を禁じる。
;; 仮引数、結果、証明義務の Q、捕捉を同じ入口で検査する。
(define (check-function-boundary parameter-types return-type obligations body
                                 bound-names environment node fail)
  (when (ormap unbound-borrowed-type? parameter-types)
    (fail 'borrowed-function-parameter node))
  (when (unbound-borrowed-type? return-type)
    (fail 'borrowed-function-result node))
  (when (unbound-borrowed-type? obligations)
    (fail 'borrowed-function-result node obligations))
  ;; 関数自身の束縛子は同名の外側の項目を遮蔽するため、自由変数から引く。
  (define free
    (set-subtract (core-free-vars body) (list->set bound-names)))
  ;; environment は連想リストであり、前方の項目が遮蔽後の有効な項目である。
  (define visible
    (for/fold ([entries '()]) ([entry (in-list environment)])
      (if (assoc (first entry) entries)
          entries
          (cons entry entries))))
  (for ([entry (in-list visible)])
    (when (and (unbound-borrowed-type? (second entry))
               (set-member? free (first entry)))
      (fail 'borrowed-function-capture node))))

(define (infer-lam callable parameters body Λ Ψ
                   environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  ;; ForallRegion は直上の RegionLam が渡した binder 文脈で 1 段だけ剥がす。
  ;; 文脈が無い形や束縛数が合わない形は下の既存の fail-closed へ落とす。
  (define expanded
    (or (unwrap-forall-region signature (region-binder-context)) signature))
  (match expanded
    [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates parameters)
       (fail 'duplicate-parameter node))
     ;; 境界では、この callable の署名に現れる region parameter だけを使う。
     ;; とくに内側の素の Lam は、捕捉検査で外側の RegionLam の parameter を
     ;; 引き継いではならない。
     (define signature-region-params
       (set-intersect (bound-region-params)
                      (region-free-params expanded)))
     (parameterize ([bound-region-params signature-region-params])
       (check-function-boundary parameter-types return-type obligations
                                body parameters environment node fail))
     ;; 署名が Owned の仮引数を持つなら、本体は生名と Let の連なりで
     ;; 符号化されている。仮引数の位置ではなく本体の形で検査する。
     (when (ormap owned-type? parameter-types)
       (match (peel-node body)
         [`(Handle ,_ ,_ ,scope)
          (match (peel-node scope)
            [`(Scope () ,inner)
             (check-owned-encoding parameters parameter-types inner node fail)]
            [_ (fail 'owned-parameter-missing-binding node)])]
         [_ (fail 'owned-parameter-missing-binding node)]))
     (define body-environment
       (function-body-environment environment parameters parameter-types))
     ;; §5.4。借用の仮引数の位置ごとに文脈局所の formal 鍵を採る。
     ;; 借用でない位置は #f を置き、位置の対応を崩さない。
     (define formals
       (for/list ([τ (in-list parameter-types)] [i (in-naturals)])
         (and (borrow-typed? τ) (formal-designator Λ node i))))
     ;; formal 鍵は token へ登録する。本体の Reborrow と使用はこの登録を
     ;; 通じて親を引く。普通の借用の要求へは入れない。仮引数は呼出し側の
     ;; 借用の別名であり、定義位置で新しい借用を立てるわけではない。
     (define body-context
       (for/fold ([Λ_body (enter-child Λ 0)])
                 ([x (in-list parameters)] [w (in-list formals)] #:when w)
         (region-ctx-add-token Λ_body x (set (cons w '())))))
     (define collector (box '()))
     (define frame
       (template-frame (for/set ([w (in-list formals)] #:when w) w)
                       collector))
     ;; Lam が転送できるのは自身の署名に自由に現れる region parameter だけ。
     ;; 外側の callable にしか属さない parameter を境界の外へ出すと、閉包の
     ;; ような Lam が証明の終わった lexical region を保持できてしまう。
     ;; expanded は外側の ForallRegion を 1 段剥がした NFn なので、
     ;; region-free-params が署名の自由な RParam だけを返す。
     (define body-result
       (parameterize ([region-binder-context #f]
                      ;; formal の RParam はこの Lam の境界に属する。
                      ;; 内側の Lam が外側の RegionLam の束縛をそのまま
                      ;; 引き継ぐと、formal 借用の capture を見逃す。
                      [bound-region-params signature-region-params]
                      [template-collectors
                       (cons frame (template-collectors))])
         (check-as body return-type body-context Ψ body-environment
                   places callables fail)))
     (unless (row-subset? (first body-result) latent-row)
       (fail 'undeclared-function-effect body latent-row (first body-result)))
     ;; §5.4。出現局所の要約を登録する。Apply はこの要約を引いて実体化する。
     (record-callable-summary!
      Λ node
      (callable-summary formals (reverse (unbox collector))
                        (forwarding-index parameter-types return-type)
                        (hash))
      fail)
     (list expanded '() Ψ)]
    ;; 表の行が ForallRegion に包まれた署名で、binder 文脈が無い形はここへ来る。
    ;; 囲う RegionLam があるはずという仮定を置かず、表に無い場合と key を
    ;; 共有して fail-closed にする（spec §5.7）。
    [_ (fail 'unknown-callable node)]))

(define (infer-recur-value callable function parameters body Λ Ψ
                           environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates (cons function parameters))
       (fail 'duplicate-parameter node))
     (check-function-boundary parameter-types return-type obligations
                              body (cons function parameters) environment node fail)
     (when (ormap owned-type? parameter-types)
       (match (peel-node body)
         [`(Scope () ,inner)
          (check-owned-encoding parameters parameter-types inner node fail)]
         [_ (fail 'owned-parameter-missing-binding node)]))
     ;; §5.1。再帰の呼出し位置ごとに実引数が変わり、formal 鍵の実体化が
     ;; 呼出しの出現をまたぐ。本サイクルでは受けない。
     (when (ormap borrow-typed? parameter-types)
       (fail 'borrowed-function-parameter node))
     (define body-environment
       (extend (function-body-environment environment
                                          parameters parameter-types)
               (list function)
               (list signature)))
     (define body-result
       ;; RecurVal の本体も Lam と同じ関数境界である。RegionLam の
       ;; binder 文脈を値として持ち出さないよう、外側の束縛をここで閉じる。
       (parameterize ([region-binder-context #f]
                      [bound-region-params (set)])
         (check-as body return-type (enter-child Λ 0) Ψ body-environment
                   places callables fail)))
     (unless (row-subset? (first body-result) latent-row)
       (fail 'undeclared-function-effect body latent-row (first body-result)))
     (list signature '() Ψ)]
    ;; 表の行は (NFn ...) と (ForallRegion (rp ...) (NFn ...)) の 2 つである。
    ;; RecurVal と Recur は署名の ForallRegion を剥がさない。
    ;; region 多相な再帰関数は G5c5c で扱う。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

(define (recur-context callable function parameters body Λ Ψ
                       environment places callables node fail)
  (define signature (lookup callables callable))
  (unless signature (fail 'unknown-callable node))
  (match signature
    [`(NFn ,parameter-types ,return-type ,latent-row ,obligations)
     (unless (= (length parameters) (length parameter-types))
       (fail 'parameter-arity-mismatch node
             (length parameter-types)
             (length parameters)))
     (when (check-duplicates (cons function parameters))
       (fail 'duplicate-parameter node))
     (check-function-boundary parameter-types return-type obligations
                              body (cons function parameters) environment node fail)
     (when (ormap owned-type? parameter-types)
       (match (peel-node body)
         [`(Scope () ,inner)
          (check-owned-encoding parameters parameter-types inner node fail)]
         [_ (fail 'owned-parameter-missing-binding node)]))
     ;; §5.1。再帰の呼出し位置ごとに実引数が変わり、formal 鍵の実体化が
     ;; 呼出しの出現をまたぐ。本サイクルでは受けない。
     (when (ormap borrow-typed? parameter-types)
       (fail 'borrowed-function-parameter node))
     (define function-environment
       (extend environment
               (list function)
               (list signature)))
     (define body-environment
       (function-body-environment function-environment
                                  parameters parameter-types))
     ;; body は Recur の子 0 である（region.md §3）。
     ;; 環境は既存の body-environment をそのまま使う。
     ;; 仮引数は owners へ入れないため（spec §3.1）、Λ は enter-child だけを掛ける。
     (define Λ_body (enter-child Λ 0))
     ;; 本体を Ψ が動かなくなるまで解析し直す。集合は単調に増えるため停止する。
     (define (fixpoint Ψ_in)
       (match (parameterize ([region-binder-context #f]
                             [bound-region-params (set)])
               (check-as body return-type Λ_body Ψ_in body-environment
                         places callables fail))
         [(list body-row Ψ_1)
          (define Ψ_next (psi-join Ψ_in Ψ_1))
          (if (equal? Ψ_next Ψ_in)
              (list body-row Ψ_next)
              (fixpoint Ψ_next))]))
     (match-define (list body-row Ψ_body) (fixpoint Ψ))
     (unless (row-subset? body-row latent-row)
       (fail 'undeclared-function-effect body latent-row body-row))
     (list function-environment Ψ_body)]
    ;; 表の行は (NFn ...) と (ForallRegion (rp ...) (NFn ...)) の 2 つである。
    ;; RecurVal と Recur は署名の ForallRegion を剥がさない。
    ;; region 多相な再帰関数は G5c5c で扱う。表に無い場合と key を共有する。
    [_ (fail 'unknown-callable node)]))

;; spec §3.1。宣言型の借用の region 欄は書き手が書いた起点であり、
;; 推論した型のそれは寿命である。語彙が違うので照合しない。
;; 両方が同じ構成子の借用である位置だけ、宣言型の欄を推論した欄へ写す。
;; 形が食い違う位置は宣言型のまま残し、後段の type-compatible? に落とさせる。
(define (adopt-inferred-lifetimes declared actual)
  (match* (declared actual)
    [(`(Borrowed ,d-payload ,_) `(Borrowed ,a-payload ,a-rho))
     `(Borrowed ,(adopt-inferred-lifetimes d-payload a-payload) ,a-rho)]
    [(`(BorrowedMut ,d-payload ,_) `(BorrowedMut ,a-payload ,a-rho))
     `(BorrowedMut ,(adopt-inferred-lifetimes d-payload a-payload) ,a-rho)]
    [((? list?) (? list?))
     #:when (= (length declared) (length actual))
     (for/list ([d (in-list declared)] [a (in-list actual)])
       (adopt-inferred-lifetimes d a))]
    [(_ _) declared]))

;; §12。宣言型が Owned のときだけ使う比較。推論した型が Owned でなければ
;; Owned で包んでから比べる。包んで比べる形を type-compatible? そのものへ
;; 入れない。入れると、関数の実引数や分岐の合流でも暗黙の持ち上げが起きる。
(define (owned-lift-compatible? actual expected)
  (or (type-compatible? actual expected)
      (and (not (owned-type? actual))
           (type-compatible? `(Owned ,actual) expected))))

;; 固定引数と関数のどちらかが Owned なら、結果の関数型も Owned で包む。
;; 包んだ型は Move を経由してのみ関数の位置へ置ける（§5.4）。
(define (curry-result-type remaining-types return-type latent-row obligations owned?)
  (define bare `(NFn ,remaining-types ,return-type ,latent-row ,obligations))
  (if owned? `(Owned ,bare) bare))

;; 関数の位置に置かれた Owned<NFn ...> を一段だけ剥がす。
;; Move と CurryVal は place を経由するため許し、それ以外の根は拒む。
(define owned-function-roots '(Move CurryVal))

(define (owned-function-type? type)
  (match type
    [`(Owned (NFn ,_ ...)) #t]
    [_ #f]))

(define (peel-owned-function type core fail)
  (cond
    [(not (owned-function-type? type)) (values type #f)]
    [else
     (define worn (peel-node core))
     (unless (and (pair? worn)
                  (memq (car worn) owned-function-roots))
       (fail 'owned-function-requires-move core))
     (values (second type) #t)]))

(define (binding-context binding-mode declared-type bound Λ Ψ
                         environment places callables node fail)
  (match declared-type
    [`(Record ,declared-row)
     (match (infer bound (enter-child Λ 0) Ψ environment places callables fail)
       [(list 'Never bound-row bound-psi)
        (list bound-row declared-type bound-psi)]
       [(list `(Record ,actual-row) bound-row bound-psi)
        (unless (compat? `(Record ,actual-row) declared-type Γ-pc0
                         (current-region-relation))
          (fail 'record-binding-incompatible bound))
        (define residual
          (field-row-residual actual-row declared-row))
        (define binding-row
          (case binding-mode
            [(const)
             (if (null? residual)
                 declared-row
                 (fail 'const-record-residual bound residual))]
            [(let)
             (field-row-⊕ declared-row residual)]
            [else (fail 'ill-typed node)]))
        ;; field-row-residual は declared-row のラベルを除いた残余を返すため、
        ;; field-row-⊕ の重複検査はここでは破れない。表の整合を保つため、
        ;; 到達しないこの位置は先の compat? 検査と key を共有する。
        (unless binding-row (fail 'record-binding-incompatible bound))
        (list bound-row `(Record ,binding-row) bound-psi)]
       [(list actual-type _ _)
        (fail 'type-mismatch bound declared-type actual-type)])]
    [`(Owned ,payload)
     ;; §12。計算した値を Owned へ載せる経路。宣言型が Owned のとき、
     ;; bound が計算した値をそのまま place へ載せる。
     ;; resource と Move が作った値は最初の比較で通るため、既存の経路は変わらない。
     ;; payload に借用が入る形は落とす。place へ載せた後は借用の所有者が
     ;; どこにいるのかを追う手立てが無く、所有者より長生きする借用を作れる。
     ;; 束縛の集合は空にする。この位置では region 多相の束縛の下でも、
     ;; 借用そのものを payload に置けない。
     (when (borrowed-type-anywhere? payload)
       (fail 'own-binding-borrowed-payload node))
     (match (check-as/full bound declared-type (enter-child Λ 0)
                           Ψ environment places callables fail
                           owned-lift-compatible?)
       [(list row bound-psi _)
        ;; 宣言型をそのまま束縛の型にする。payload に借用が無いことを
        ;; 直前に確かめたので、寿命を写す先が無い。
        (list row declared-type bound-psi)])]
    [_
     (match (check-as/full bound declared-type (enter-child Λ 0)
                           Ψ environment places callables fail)
       [(list row bound-psi actual)
        ;; 束縛の型には推論した寿命を持つ側を置く。
        ;; 宣言型を置くと spec §5.1 の下限収集が (RVar k) を見つけられず、
        ;; 束縛した名前を使う位置の region が σ に入らない。
        (list row (adopt-inferred-lifetimes declared-type actual) bound-psi)])]))

;; PRF-004: Discharge の連なりを外側から剥がし、(φ 列, 基底) を返す。
;; 型付けを連なりの全体で見るため、節の側では再帰しない。
(define (peel-discharge core)
  (let loop ([core core] [propositions '()])
    (match (peel-node core)
      [`(Discharge ,proof-rep ,inner)
       (match (peel-node proof-rep)
         [`(ProofRep ,_ ,phi)
          (loop inner (cons phi propositions))]
         [_ (values (reverse propositions) core)])]
      [_ (values (reverse propositions) core)])))

;; spec §6: 失敗は返り値ではなく脱出継続で運ぶ。struct を返すと真値になり、
;; 既存の and と andmap と for/and の短絡が失敗を成功として通す。
;; lowering.rkt:88 の with-diagnostics と同じ機構である。
;; 局所回復の callback も同じ検査を通すため、key 検査を単独の手続きにする。
;; callback の中へ書き写すと、片方だけ直したときに未登録 key が素通りする。
(define (assert-typing-key key)
  (unless (diagnostic-code-of 'typing key)
    (error 'fail "registry に無い typing の key である: ~s" key)))

(define (with-typing proc)
  (let/ec escape
    (define (fail key node . details)
      (assert-typing-key key)
      (escape (list 'fail key node details)))
    (list 'ok (proc fail))))

;; 脱出を捕まえて従来の #f へ潰す。core-check-row と config-ok? が使う。
;; spec §4.1。段 1 だけでなく段 3 まで通す。段 2 と段 3 の fail も #f へ潰す。
;; 返り値は成功時の段 1 の row を σ で解決したものであり、σ 自体は外へ出さない。
;; 段 1 の fail は with-typing の脱出で段 2 へ進まないため、段 1 で棄却した形が
;; 制約違反として報告されることはない。type-of/raw* と同じ契約である。
(define (check-as/boolean core expected environment places callables
                          [Λ (empty-region-ctx)]
                          #:compatible? [compatible? type-compatible?])
  (define cs (box '()))
  (define rs (box '()))
  (define ras (box '()))
  (define ir (region-ctx-ir Λ))
  (match (parameterize ([lifetime-collector cs]
                        [request-collector rs]
                        [region-arg-collector ras]
                        [lifetime-counter (box 0)]
                        [alpha-table (box (hash))]
                        [merge-alpha-sources (make-hash)]
                        [callable-summaries (make-hash)]
                        [forwarding-summaries (make-hash)]
                        [template-collectors '()])
           (with-typing
            (lambda (fail)
              ;; 束縛名を入口で 1 度だけ付け替える。関係の表も同じ項から作る。
              (define renamed
                (call-with-region-params
                 (lambda () (alpha-rename-all-region-lams core))))
              (define relation
                (if ir (make-region-relation ir (erase-core renamed)) equal?))
              (parameterize ([current-region-relation relation])
                ;; 段 1。
                (match-define (list row Ψ)
                  (check-as renamed expected Λ (empty-psi)
                            environment places callables fail
                            compatible?))
                ;; 段 2。
                (match (typing-solve ir (reverse (unbox cs)))
                  [(list 'error broken)
                   (define c (first broken))
                   (fail (constraint-key c) (constraint-node c))]
                  [(list 'ok σ)
                   ;; 段 3。ir が無い Λ では emit-use-request! が要求を作らない
                   ;; ため、届くのは RegionApp の要求だけである。
                   (check-region-args ir σ (collected-region-args) relation fail)
                   (check-borrows ir σ Ψ (reverse (unbox rs)) sigma-ref fail)
                   (subst-type-regions row σ ir)])))))
    [(list 'ok row) row]
    [_ #f]))

;; spec §3.1。所有値の束縛子だけを owners へ入れる。
;; ρ は束縛子の節点で有効な region である。Λ.point がその節点を指すため、
;; enter-child を掛ける前の Λ をここへ渡す。
;; ir が無い Λ、すなわち公開入口の既定の空 Λ では何もしない。
(define (register-owner Λ w binding-type)
  (define ir (region-ctx-ir Λ))
  (cond
    [(not ir) Λ]
    [(match (normalize-type binding-type)
       [`(Owned ,_) #t]
       [_ #f])
     (region-ctx-add-owner Λ w (region-at ir (region-ctx-point Λ)))]
    [else Λ]))

;; 借用の対象の payload を引く。p は places が直接 τ を与え、
;; x は environment が (Owned τ) を与える。
(define (borrow-target-payload w environment places node fail)
  (cond
    [(exact-nonnegative-integer? w)
     (define type (lookup places w))
     (unless type (fail 'unknown-place node))
     type]
    [else
     (define type (lookup environment (peel-node w)))
     (unless type (fail 'unbound-variable node))
     (match type
       [`(Owned ,payload) payload]
       [_ (fail 'borrow-non-owned node)])]))

;; [REQ: BOR-001] 借用の region は owner の region に含まれていなければならない。
;; [REQ: BOR-002] 可変借用の有効期間中、競合する alias を作れない。
;;
;; G5c1 では判定を行わない。α を作り、制約と判定の要求だけを記録する。
;; 判定は解決の後、検査の段が行う（spec §7.3）。
(define (infer-borrow core w mutable? Λ Ψ environment places callables fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-unknown-owner-region core))
  (define payload (borrow-target-payload w environment places core fail))
  (define key (if (exact-nonnegative-integer? w) w (peel-node w)))
  (define ρ_owner (region-ctx-owner Λ key))
  ;; 所有者の region が引けないのは制約の違反ではなく入力の情報不足である。
  ;; 解決を待つ理由が無いため、ここで落とす（spec §8.1）。
  (unless ρ_owner (fail 'borrow-unknown-owner-region core))
  (define point (region-ctx-point Λ))
  (define ρ_borrow (region-at ir point))
  (define α (fresh-lifetime! point))
  ;; 借用の起点は α の下限である。使わない借用の解はこの 1 本で決まり、
  ;; G5b の ρ_borrow と一致する（spec §5.3）。
  (emit-constraint!
   (region-constraint 'contains α ρ_borrow point #f))
  ;; BOR-001 は上限制約になる（spec §8.1）。
  (emit-constraint!
   (region-constraint 'outlives ρ_owner α point core))
  (emit-request!
   (borrow-request key '() (if mutable? 'mut 'shared) α core))
  (define Ψ_out
    (if mutable?
        (psi-add-mut Ψ key '() α)
        (psi-add-shared Ψ key '() α)))
  (list (list (if mutable? 'BorrowedMut 'Borrowed)
              payload
              α)
        '()
        Ψ_out))

;; [REQ: BOR-002] Reborrow は可変借用を子 region の共有借用へ落とし、
;; 親 capability を子の生存期間だけ停止する。判定は段 3 で行う。
(define (infer-reborrow core operand Λ Ψ environment places callables fail)
  (match-define (list τ_operand ε_operand Ψ_1)
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'borrow-unknown-owner-region core))
  (match (normalize-type τ_operand)
    [`(BorrowedMut ,τ ,α_parent)
     (define point (region-ctx-point Λ))
     (define α_child (fresh-lifetime! point))
     ;; 型の region 欄は未解決の RVar または concrete な ρ を運ぶ。
     ;; RVar はそのまま制約へ渡し、concrete な欄だけ per-IR bridge で
     ;; region 項へ戻して、制約の寿命項の表現を揃える。
     (define parent-term
       (if (or (lifetime-var? α_parent) (rparam-term? α_parent))
           α_parent
           (rho->region ir α_parent)))
     (define tokens (borrow-token-key Λ operand #:fail fail))
     (when (set-empty? tokens)
       (error 'infer-reborrow
              "親の token を特定できない operand: ~s"
              operand))
     (define parent-designator
       (uniform-token-designator tokens core fail))
     ;; concrete な親でも、core 内の BorrowMut がすでに同じ capability の
     ;; mut 項目を Ψ へ登録している場合がある。そこでは元の α を使い、
     ;; 外部由来の親だけを synthetic request として補う。
     (define (existing-mut cap)
       (for/first ([entry (in-set (psi-mut Ψ_1))]
                   #:when (and (equal? (first entry) (car cap))
                               (equal? (second entry) (cdr cap))))
         entry))
     (define parent-terms
       (for/hash ([cap (in-set tokens)])
         (define existing (existing-mut cap))
         (values cap
                 (if (and existing
                          (not (lifetime-var? α_parent))
                          (not (rparam-term? α_parent)))
                     (third existing)
                     parent-term))))
     (route-constraint!
      (region-constraint 'contains α_child (region-at ir point) point core)
      parent-designator core fail)
     (for ([cap (in-set tokens)])
       (define w (car cap))
       (define fp (cdr cap))
       (route-constraint!
        (region-constraint 'reborrow (hash-ref parent-terms cap)
                           α_child point core)
        parent-designator core fail)
       ;; 外部から渡された concrete な可変借用は、借用要求を core 内で
       ;; 生成していない。各 token を親の要求として記録し、境界の先でも
       ;; Move/Drop の判定へ届かせる。core 内ですでに Ψ にある要求は
       ;; synthetic request を重ねない。
       (unless (or (lifetime-var? α_parent)
                   (rparam-term? α_parent)
                   (existing-mut cap))
         (route-request! (borrow-request w fp 'mut parent-term core)
                         core fail)))
     ;; Reborrow の結果そのものも共有借用として判定要求へ記録する。
     ;; 親を停止窓から除いたあとも、子と別の可変借用との衝突は残す必要がある。
     (for ([cap (in-set tokens)])
       (define w (car cap))
       (define fp (cdr cap))
       (route-request! (borrow-request w fp 'shared α_child core)
                       core fail))
     ;; concrete な親は Ψ に元の mut 項目が無い環境由来の借用である。
     ;; synthetic request と親子除外を同じ規則へ揃えるため、判定用の
     ;; suspension tuple だけは実在する mut capability として張る。
     (define Ψ_seed
       (if (or (lifetime-var? α_parent)
               (rparam-term? α_parent))
           Ψ_1
           (for/fold ([Ψ_acc Ψ_1]) ([cap (in-set tokens)])
             (if (existing-mut cap)
                 Ψ_acc
                 (psi-add-mut Ψ_acc (car cap) (cdr cap) parent-term)))))
     (define Ψ_2
       (for/fold ([Ψ_acc Ψ_seed]) ([cap (in-set tokens)])
         (psi-suspend Ψ_acc
                      (car cap)
                      (cdr cap)
                      (hash-ref parent-terms cap)
                      α_child)))
     (list `(Borrowed ,τ ,α_child) ε_operand Ψ_2)]
    [_ (fail 'reborrow-non-mutable core)]))

;; §8.1。合流した α を、借用の項が直接採番した α だけの集合へ展開する。
;; 中間の合流 α を残してはならない。循環は不変条件の破れとして error にする。
(define (alpha-set ρ)
  (cond
    [(not (lifetime-var? ρ)) (set)]
    [else
     (let expand ([α ρ] [seen (set)])
       (cond
         [(set-member? seen α)
          (error 'alpha-set "合流した α の対応が循環している: ~s" α)]
         [(hash-ref (merge-alpha-sources) α #f)
          => (lambda (branches)
               (for/fold ([acc (set)]) ([β (in-set branches)])
                 (if (lifetime-var? β)
                     (set-union acc (expand β (set-add seen α)))
                     acc)))]
         [else (set α)]))]))

;; §8.1。capability の起点となる借用の α の集合を返す。
;; 具体的な ρ と借用でない型は起点の寿命を運ばないので空集合である。
(define (capability-source type)
  (match (normalize-type type)
    [`(Borrowed ,_ ,ρ) (alpha-set ρ)]
    [`(BorrowedMut ,_ ,ρ) (alpha-set ρ)]
    [_ (set)]))

;; [REQ: BOR-004] 借用の field 射影。親の α をそのまま使い、
;; 新しい α と borrow-request は作らない（spec §5.1）。
(define (infer-projborrow core operand label Λ Ψ environment places callables fail)
  (match-define (list τ_operand ε_operand Ψ_1)
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define-values (m_parent τ_inner α)
    (match (normalize-type τ_operand)
      [`(Borrowed ,τ ,α) (values 'Borrowed τ α)]
      [`(BorrowedMut ,τ ,α) (values 'BorrowedMut τ α)]
      [_ (fail 'projborrow-non-record core)]))
  (define row
    (match (normalize-type τ_inner)
      [`(Record ,r) r]
      [_ (fail 'projborrow-non-record core)]))
  (define field
    (or (assoc label row)
        (fail 'projborrow-unknown-field core)))
  (match-define (list _ τ_f m_f) field)
  ;; spec §5.4 の例外。直接の Owned payload は Borrowed の禁止形になる。
  (when (match (normalize-type τ_f) [`(Owned ,_) #t] [_ #f])
    (fail 'borrowed-owned-payload core))
  (define source (use-source Λ operand τ_operand))
  (for ([cap (in-set (borrow-token-key Λ operand #:fail fail))])
    (emit-use-request! Λ (car cap) (append (cdr cap) (list label)) 'read source
                       core 'borrow-conflicting-use #f fail))
  (list `(,(proj-borrow-mode m_parent m_f) ,τ_f ,α) ε_operand Ψ_1))

;; spec §4 分岐 2。α から所有者の region を引く。
;; 借用の生成は BOR-001 の上限制約 (outlives ρ_owner α) を必ず出すため、
;; 収集器の中に α を右辺とする outlives があれば、その左辺が所有者の region である。
(define (lifetime-owner-region alpha)
  (for/first ([c (in-list (collected-constraints))]
              #:when (and (eq? (region-constraint-kind c) 'outlives)
                          (equal? (region-constraint-right c) alpha)))
    (region-constraint-left c)))

;; copy-out-scan は借用の payload 内の lifetime を収集しないため、
;; 内側に別の借用を持つ payload はこの段で複製を拒否する。
(define (borrow-payload-borrow-free? type)
  (let walk ([t type])
    (match t
      [`(Borrowed ,payload ,_) (not (borrowed-type-anywhere? payload))]
      [`(BorrowedMut ,payload ,_) (not (borrowed-type-anywhere? payload))]
      [(? list? terms) (andmap walk terms)]
      [_ #t])))

;; 型の中の借用がすべて所有者を追えることを確かめ、α の列を返す。
;; 借用以外の複製できない構成子は reason で落とす。
;; 所有者が引けない借用は関数の境界を越えて入ってきたものであり、
;; borrow.md 14 節 2 項により本サイクルでは受け取らない。
(define (payload-borrows-traceable? type reason core fail)
  (define scanned (copy-out-scan type))
  (unless scanned (fail reason core))
  (unless (borrow-payload-borrow-free? type)
    (fail reason core))
  (for ([alpha (in-list scanned)])
    (unless (lifetime-owner-region alpha)
      (fail 'borrow-unknown-owner-region core)))
  scanned)

;; [REQ: BOR-005] 借用が指す先の値を複製する。結果は借用でも所有値でもない。
;; ρ は結果の型に現れない（spec §6.1）。
(define (infer-read core operand Λ Ψ environment places callables fail)
  (match-define (list τ_operand ε_operand Ψ_1)
    (infer operand (enter-child Λ 0) Ψ environment places callables fail))
  (define-values (τ_payload α_view)
    (match (normalize-type τ_operand)
      [`(Borrowed ,τ ,α) (values τ α)]
      [`(BorrowedMut ,τ ,α) (values τ α)]
      [_ (fail 'read-non-borrow core)]))
  (define α_inner
    (payload-borrows-traceable? τ_payload 'read-uncopyable-payload core fail))
  ;; borrow.md 14 節 3 項。読み出した値の中の借用は view の region を超えない。
  ;; BOR-001 と同じ形の上限制約であり、違反は borrow-escapes-owner で報告される。
  (for ([α (in-list α_inner)])
    (emit-constraint!
     (region-constraint 'outlives α_view α (region-ctx-point Λ) core)))
  (define source (use-source Λ operand τ_operand))
  (for ([cap (in-set (borrow-token-key Λ operand #:fail fail))])
    (emit-use-request! Λ (car cap) (cdr cap) 'read source
                       core 'borrow-conflicting-use #f fail))
  (list τ_payload ε_operand Ψ_1))

;; [REQ: BOR-004] 可変借用 capability を通じた代入だけを許す。
;; target の payload が Union のときは、実行時の全成分と互換でなければならない。
(define (infer-assign core target value Λ Ψ environment places callables fail)
  (match-define (list τ_target ε_target Ψ_1)
    (infer target (enter-child Λ 0) Ψ environment places callables fail))
  (define τ_target* (normalize-type τ_target))
  (define-values (τ_payload α_target)
    (match τ_target*
      [`(BorrowedMut ,τ ,α) (values τ α)]
      [`(Borrowed ,_ ,_) (fail 'assign-through-shared core)]
      [_ (fail 'assign-non-borrow core)]))
  (payload-borrows-traceable? τ_payload 'assign-owned-payload core fail)
  (match-define (list τ_value ε_value Ψ_2)
    (infer value (enter-child Λ 1) Ψ_1 environment places callables fail))
  ;; 書き込む値の借用は、書き込み先の view より長く生きなければならない。
  ;; 短ければ view を通じて解放済みの借用を読み出せる。
  (define α_value
    (payload-borrows-traceable? τ_value 'assign-owned-payload core fail))
  (for ([α (in-list α_value)])
    (emit-constraint!
     (region-constraint 'outlives α α_target (region-ctx-point Λ) core)))
  (for ([τ_i (in-list (union-members τ_payload))])
    (unless (type-compatible? τ_value τ_i)
      (fail 'assign-union-variant core)))
  (define source (use-source Λ target τ_target))
  (for ([cap (in-set (borrow-token-key Λ target #:fail fail))])
    (emit-use-request! Λ (car cap) (cdr cap) 'assign source
                       core 'borrow-conflicting-use #f fail))
  (list 'Unit (row-union ε_target ε_value) Ψ_2))

(define (infer core Λ Ψ environment places callables fail)
  ((typing-point-probe) (region-ctx-point Λ))
  (define result
    (infer/body core Λ Ψ environment places callables fail))
  (collect-use-regions! (first result)
                        (region-ctx-ir Λ)
                        (region-ctx-point Λ))
  result)

;; producer 位置から入ったときだけ OwnLeaf を許す。許可は節点そのものを
;; memq で保持するため、兄弟の位置へ漏れない。既定は拒否である。
(define ownleaf-permitted (make-parameter '()))

;; span 付きの core も受けるため peel-node を通す。
(define (ownleaf-root? core)
  (match (peel-node core)
    [`(OwnLeaf ,_) #t]
    [_ #f]))

;; producer 位置の共通 gate。追跡されていない raw Owned payload を通さない
;; ため、根の OwnLeaf を必須にする。診断 key は producer ごとに異なるため
;; 引数で受ける。
(define (require-ownleaf-root core key node fail)
  (unless (ownleaf-root? core)
    (fail key node)))

(define (infer/body core Λ Ψ environment places callables fail)
  (match (peel-node core)
    [(? integer?) (list 'Int '() Ψ)]
    [(? string?) (list 'String '() Ψ)]
    ['unit (list 'Unit '() Ψ)]

    [`(Lam ,_ ,callable (,parameters ...) ,body)
     (infer-lam callable (map peel-bind parameters) body Λ
                Ψ
                environment places callables core fail)]

    [`(RegionLam (,rps ...) ,body)
     (match-define (list body-type body-row body-psi)
       (parameterize ([region-binder-context rps]
                      [bound-region-params
                       (set-union (bound-region-params) (list->set rps))])
         (infer body (enter-child Λ 0) Ψ environment places callables fail)))
     (list `(ForallRegion ,rps ,body-type) body-row body-psi)]

    [`(PrimVal ,_ ,name)
     (match (assoc name Γ0)
       [(list _ (list type canonical-value))
        (unless (equal? canonical-value (peel-node core))
          (fail 'non-canonical-primitive core))
        (list type '() Ψ)]
       [_ (fail 'unknown-primitive core)])]

    [`(CurryVal ,_ ,function ,argument)
     (match-define (list function-type function-row function-psi)
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (define-values (peeled function-owned?)
       (peel-owned-function function-type function fail))
     (match (list peeled function-row function-psi)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              _ _)
        (define summary
          (or (lookup-callable-summary (enter-child Λ 0) function)
              (let ([w (peel-node function)])
                (and (borrow-designator? w)
                     (region-ctx-summary Λ w)))))
        (define borrowed-parameter?
          (or (borrowed-type-anywhere? first-type)
              (ormap borrowed-type-anywhere? remaining-types)))
        (define borrowed-result?
          (borrowed-type-anywhere? return-type))
        (define borrowed-obligations?
          (borrowed-type-anywhere? obligations))
        (cond
          [(and summary
                (or borrowed-parameter? borrowed-result?
                    borrowed-obligations?))
           (fail 'unresolved-borrow-owner function)]
          [borrowed-parameter?
           ;; 具体 NFn の従来の診断を保つ。summary が無い場合でも、部分適用
           ;; は型木の内側にある借用の provenance を運べないため落とす。
           (fail 'borrowed-function-parameter function)]
          [borrowed-result?
           (fail 'borrowed-function-result function)]
          [borrowed-obligations?
           (fail 'borrowed-function-result function obligations)])
        (unless (null? function-row)
          (fail 'effectful-curry-operand function))
        (when (and (owned-type? first-type)
                   (not (config-runtime-leaf? argument)))
          (require-ownleaf-root argument 'missing-ownleaf-root argument fail))
        (define argument-row
          (parameterize ([ownleaf-permitted
                          (if (owned-type? first-type) (list argument) '())])
            (check-as argument first-type (enter-child Λ 1)
                      function-psi
                      environment places callables fail
                      (if (owned-type? first-type)
                          owned-lift-compatible?
                          type-compatible?))))
        (unless (null? (first argument-row))
          (fail 'effectful-curry-operand argument))
        (list (curry-result-type remaining-types return-type latent-row obligations
                                 (or function-owned? (owned-type? first-type)))
              (row-union function-row (first argument-row))
              (second argument-row))]
       [_ (fail 'curry-non-function function)])]

    [`(RecurVal ,callable ,function (,parameters ...) ,body)
     (infer-recur-value callable (peel-bind function)
                        (map peel-bind parameters) body Λ
                        Ψ
                        environment places callables core fail)]

    [`(TypeRep ,_ ,_ ,kind)
     (list `(TypeInfo ,kind) '() Ψ)]

    [`(ProofRep ,_ ,proposition)
     (list `(Proof ,proposition) '() Ψ)]

    [`(Construct ,data-type ,constructor ,fields ...)
     (define result
       (check-construct constructor fields data-type Λ
                        Ψ
                        environment places callables core fail))
     (list (peel-ty data-type) (first result) (second result))]

    [`(resource ,_) (list '(Owned Res) '() Ψ)]

    ;; producer 位置から入ったときだけ OwnLeaf を許す。payload の再帰は
    ;; 通常の infer へ戻すため、入れ子の producer は親位置で個別に許可される。
    [`(OwnLeaf ,payload)
     (unless (memq core (ownleaf-permitted))
       (fail 'unexpected-ownleaf core))
     (parameterize ([ownleaf-permitted '()])
       (infer payload (enter-child Λ 0)
              Ψ environment places callables fail))]

    [`(OwnedLeaf ,_tk ,payload)
     (match-define (list payload-type payload-row payload-psi)
       (infer payload (enter-child Λ 0) Ψ environment places callables fail))
     (unless (owned-type? payload-type)
       (fail 'ill-typed core))
     (list payload-type payload-row payload-psi)]

    [`(Rec (,fields ...))
     (define plain-fields
       (for/list ([field (in-list fields)])
         (list (peel-lbl (first field))
               (second field)
               (third field))))
     (unless (field-row-unique? plain-fields)
       (fail 'duplicate-record-label core))
     (define-values (results final-psi)
       (for/fold ([results '()] [current-psi Ψ])
                 ([field (in-list plain-fields)]
                  [i (in-naturals)])
         (define result
           (infer (third field) (enter-child Λ i)
                  current-psi environment places callables fail))
         (values (append results (list result)) (third result))))
     (for ([field (in-list plain-fields)]
           [result (in-list results)])
       (when (and (owned-type? (first result))
                  (not (and (deriving-config?)
                            (match (peel-node (third field))
                              [`(OwnedLeaf ,_ ,_) #t]
                              [_ #f]))))
         (fail 'owned-record-field (third field))))
     (list
      `(Record
        ,(for/list ([field (in-list plain-fields)]
                    [result (in-list results)])
           `(,(first field) ,(first result) ,(second field))))
      (rows-union (map second results))
      final-psi)]

    ;; RFN-001: 未検証の値。ペイロードの型をそのまま Untrusted で包む。
    ;; effect row はペイロードのものを引き継ぐ。
    [`(UVal ,value)
     (match (infer value (enter-child Λ 0)
                    Ψ
                    environment places callables fail)
       [(list value-type value-row value-psi)
        (unless (owned-free? value-type)
          (fail 'owned-untrusted-payload value))
        (list `(Untrusted ,value-type) value-row value-psi)])]

    ;; RFN-001: 検証済みの値。witness の命題を型へ持ち上げる。発行者が正当か
    ;; どうかは成果物検証（verify-origins）の担当であり、ここでは見ない。
    [`(RVal ,proof-rep ,value)
     (match (peel-node proof-rep)
       [`(ProofRep ,_ ,proposition)
        (match (infer value (enter-child Λ 0)
                       Ψ
                       environment places callables fail)
          [(list value-type value-row value-psi)
           (unless (owned-free? value-type)
             (fail 'owned-refined-payload value))
           (list `(Refined ,value-type ,proposition) value-row value-psi)])]
       [_ (fail 'ill-typed core)])]

    [`(Proj ,record ,label)
     (match (infer record (enter-child Λ 0)
                    Ψ environment places callables fail)
       [(list `(Record ,row) record-row record-psi)
        (match (field-row-lookup row (peel-lbl label))
          [(list field-type _) (list field-type record-row record-psi)]
          [_ (fail 'unknown-record-label core)])]
       [_ (fail 'project-non-record record)])]

    [`(RegionApp ,function (,rhos ...))
     (match-define (list function-type function-row function-psi)
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (match function-type
       [`(ForallRegion (,rps ...) ,body-type)
        (unless (= (length rps) (length rhos))
          (fail 'region-app-arity core (length rps) (length rhos)))
        (for ([rho (in-list rhos)])
          (emit-region-arg-request! rho (region-ctx-point Λ) core))
        ;; subst-region-params は capture-avoiding ではない。両入口で infer の
        ;; 前に alpha-rename-all-region-lams を通すため、全 binder 名が一意になり、
        ;; region-param.rkt の前提 (2) をここでも満たす。
        (define actual-regions
          (for/hash ([rp (in-list rps)] [rho (in-list rhos)])
            (values rp rho)))
        (define substituted-body
          (subst-region-params body-type actual-regions))
        ;; §5.4。RegionApp の実引数の代入も、alpha-rename-all-region-lams が
        ;; 入口で全 binder 名を一意にした前提に依る。これにより代入値の自由な
        ;; RParam が対象の項の同名 binder に捕獲されない。
        (define inner
          (lookup-callable-summary
           (enter-child (enter-child Λ 0) 0)
           (match (peel-node function)
             [`(RegionLam ,_ ,body) body]
             [_ function])))
        (when inner
          (record-callable-summary!
           Λ core
           (struct-copy callable-summary inner
                        [region-subst actual-regions])
           fail))
        (list substituted-body function-row function-psi)]
       [_ (fail 'region-app-non-forall core function-type)])]

    [`(Apply ,function ,arguments ...)
     (match-define (list function-type function-row function-psi)
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (define-values (peeled _function-owned?)
       (peel-owned-function function-type function fail))
     (match (list peeled function-row function-psi)
       [(list `(NFn ,parameter-types
                    ,return-type ,latent-row ,obligations)
              _ _)
        (define summary
          (or (lookup-callable-summary (enter-child Λ 0) function)
              (let ([w (peel-node function)])
                (and (borrow-designator? w)
                     (region-ctx-summary Λ w)))))
        ;; 義務は呼出しの出現へ provenance を結び付けられるため、束縛済みの
        ;; RParam は呼出し側で運べる。ここでは既定の bound-region-params を
        ;; 尊重し、未束縛の借用だけを借用結果として拒む。
        (when (unbound-borrowed-type? obligations)
          (fail 'borrowed-function-result function obligations))
        ;; summary の無い concrete NFn は、従来の関数境界の診断を引数の
        ;; 照合より先に返す。summary のある callable だけ実体化へ進む。
        (when (and (not summary)
                   (ormap unbound-borrowed-type? parameter-types))
          (fail 'borrowed-function-parameter function))
        (when (and (not summary)
                   (unbound-borrowed-type? return-type))
          (fail 'borrowed-function-result function))
        (define argument-result
          (check-many/full arguments parameter-types Λ function-psi
                           environment places callables core fail 1
                           #:adopt? #f))
        (define actuals (third argument-result))
        (define borrow-parameters?
          (ormap borrow-typed? parameter-types))
        ;; 既存の concrete NFn は本体の出現要約を持たないため、従来の
        ;; unbound 診断を保つ。ForallRegion の要約欠落だけを fail-closed にする。
        (when (and (not summary) borrow-parameters?)
          (unless (or (not (borrow-region return-type))
                      (forwarding-index parameter-types return-type))
            (fail 'unresolved-borrow-owner core)))
        (define argument-caps
          (for/list ([a (in-list arguments)]
                     [τ (in-list parameter-types)]
                     [i (in-naturals 1)])
            (if (borrow-typed? τ)
                (argument-capabilities Λ a i fail)
                (set))))
        (define next-psi (second argument-result))
        (when summary
          (define formals (callable-summary-formals summary))
          (define subst
            (for/hash ([w (in-list formals)] [caps (in-list argument-caps)]
                       #:when w)
              (when (set-empty? caps)
                (fail 'unresolved-borrow-owner core))
              (values w caps)))
          (define sources
            (for/hash ([w (in-list formals)]
                       [a (in-list arguments)]
                       [τ (in-list actuals)]
                       [i (in-naturals 1)]
                       #:when w)
              (values w (argument-source Λ a τ i))))
          (set! next-psi
                (instantiate-deferred! summary Λ core subst sources
                                        next-psi fail)))
        (when (borrow-region return-type)
          (define i (forwarding-index parameter-types return-type))
          (unless i (fail 'unresolved-borrow-owner core))
          (define keys (list-ref argument-caps i))
          (when (set-empty? keys)
            (fail 'unresolved-borrow-owner core))
          (record-forwarding-summary!
           Λ core
           (forwarding-summary i keys
                               (argument-source Λ (list-ref arguments i)
                                                (list-ref actuals i)
                                                (add1 i)))
           fail))
        (unless (obligations-dischargeable? obligations Γ-pc0)
          (fail 'unsatisfied-proof-obligation core))
        (list return-type
              (rows-union
               (append (list function-row)
                       (first argument-result)
                       (list latent-row)))
              next-psi)]
       [_ (fail 'apply-non-function function)])]

    [`(Discharge ,_ ,_)
     ;; 包み先を直接の Apply に限る形は採れない。複数義務では外側の Discharge
     ;; の包み先が Discharge になり、生成する形を自分で拒否してしまう。
     ;; 素通しの規則も採れない。当該の Apply と無関係な正当な ProofRep を手書き
     ;; で包んだ項が検証を通る。PRF-004 が要求するのは選択した Proof の
     ;; provenance であるから、φ 列と義務列の対応をここで固定する。
     (define-values (propositions base) (peel-discharge core))
     (define base-Λ
       (let loop ([node (peel-node core)] [ctx Λ])
         ;; Discharge の proof 欄は子ではないが、各包みの inner は child 0
         ;; である。base へ跳ぶ前に中間層も観測して point 集合を欠かさない。
         ((typing-point-probe) (region-ctx-point ctx))
         (match node
           [`(Discharge ,_ ,inner)
            (loop (peel-node inner) (enter-child ctx 0))]
           [_ ctx])))
     (match (peel-node base)
       [`(Apply ,function ,_ ...)
        (match (infer function (enter-child base-Λ 0)
                       Ψ environment places callables fail)
          [(list `(NFn ,_ ,_ ,_ ,obligations) _ function-psi)
           (unless (= (length propositions) (length obligations))
             (fail 'discharge-obligation-count core))
           (for ([phi (in-list propositions)]
                 [obligation (in-list obligations)])
             (unless (proposition-equiv? phi obligation)
               (fail 'discharge-proposition-mismatch core)))
           ;; 型と Effect 行は基底の Apply のものを返す。
           (infer base base-Λ function-psi environment places callables fail)]
          [_ (fail 'apply-non-function function)])]
       [_ (fail 'discharge-target-not-apply base)])]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound Λ
                             Ψ environment places callables core fail)
       [(list bound-row binding-type bound-psi)
        (define x (peel-bind name))
        (define Λ_owner (register-owner Λ x binding-type))
        (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
        (define callable (lookup-callable-summary (enter-child Λ 0) bound))
        (define borrowed? (borrow-typed? (normalize-type binding-type)))
        (define token
          (cond
            [(not borrowed?) (set)]
            [summary (forwarding-summary-keys summary)]
            [else (borrow-token-key Λ bound #:fail fail)]))
        (when (and summary borrowed? (set-empty? token))
          (fail 'unresolved-borrow-owner bound))
        ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
        ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
        ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
        ;; ため、表の側で fail を落としても未知の designator を見逃さない。
        (define fields (capability-field-table Λ bound))
        (define Λ_token
          (region-ctx-add-token Λ_owner x token
                                (and summary (forwarding-summary-source summary))
                                callable
                                fields))
        (define Λ_body (enter-child Λ_token 1))
        (match (infer body
                      Λ_body
                      bound-psi
                      (extend environment (list x)
                              (list binding-type))
                      places
                      callables
                      fail)
          [(list body-type body-row body-psi)
           (list body-type (row-union bound-row body-row) body-psi)])])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-result
       (check-as bound (peel-ty type) (enter-child Λ 0)
                 Ψ environment places callables fail))
     (define x (peel-bind name))
     (define binding-type (peel-ty type))
     (define Λ_owner (register-owner Λ x binding-type))
     (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
     (define callable (lookup-callable-summary (enter-child Λ 0) bound))
     (define borrowed? (borrow-typed? (normalize-type binding-type)))
     (define token
       (cond
         [(not borrowed?) (set)]
         [summary (forwarding-summary-keys summary)]
         [else (borrow-token-key Λ bound #:fail fail)]))
     (when (and summary borrowed? (set-empty? token))
       (fail 'unresolved-borrow-owner bound))
     ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
     ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
     ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
     ;; ため、表の側で fail を落としても未知の designator を見逃さない。
     (define fields (capability-field-table Λ bound))
     (define Λ_token
       (region-ctx-add-token Λ_owner x token
                             (and summary (forwarding-summary-source summary))
                             callable
                             fields))
     (define Λ_body (enter-child Λ_token 1))
     (match (infer body
                   Λ_body
                   (second bound-result)
                   (extend environment
                           (list x)
                           (list binding-type))
                   places
                   callables
                   fail)
       [(list body-type body-row body-psi)
        (list body-type
              (row-union (first bound-result) body-row)
              body-psi)])]

    [`(Eliminate ,scrutinee (,branches ...))
     (infer-eliminate scrutinee branches Λ
                      Ψ
                      environment places callables core fail)]

    [`(Perform (Return ,boundary ,type) ,argument)
     (define type* (peel-ty type))
     (define argument-row
       (check-as argument type* (enter-child Λ 0)
                 Ψ environment places callables fail))
     (list 'Never
           (row-union (first argument-row)
                      `((Return ,boundary ,type*)))
           (second argument-row))]

    [`(Handle (Return ,boundary ,type) ,handler-clause ,body)
     (define type* (peel-ty type))
     (define body-result
       (check-as body type* (enter-child Λ 1)
                 Ψ environment places callables fail))
     (define handler-result
       (match (peel-branch handler-clause)
         [`(,name -> ,handler)
          (check-as handler
                    type*
                    (enter-child Λ 0)
                    (psi-join Ψ (second body-result))
                    (extend environment (list (peel-bind name)) (list type*))
                    places
                    callables
                    fail)]
         [_ (fail 'ill-typed core)]))
     (list type*
           (row-union
            (row-difference (first body-result)
                            `((Return ,boundary ,type*)))
            (first handler-result))
           (psi-join (second body-result) (second handler-result)))]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (infer body (enter-child Λ 0) Ψ environment places callables fail)]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      Λ
                      Ψ
                      environment places callables core fail))
     (infer continuation (enter-child Λ 1)
           (second continuation-environment)
           (first continuation-environment)
           places callables fail)]

    [`(Yield ,observed ,next)
      (define observed-result
       (parameterize ([ownleaf-permitted (list observed)])
         (infer observed (enter-child Λ 0)
               Ψ environment places callables fail)))
      (define observed-owned? (owned-type? (first observed-result)))
      (cond
        [(and observed-owned?
              (not (ownleaf-root? observed))
              (not (config-runtime-leaf? observed)))
         (fail 'missing-ownleaf-root observed)]
        [(and (not observed-owned?) (ownleaf-root? observed))
         (fail 'unexpected-ownleaf observed)])
      (define next-result
       (infer next (enter-child Λ 1)
             (third observed-result)
             environment places callables fail))
     (list (first next-result)
           (rows-union
            (list (second observed-result)
                  (second next-result)
                  `((Yield ,(first observed-result)))))
           (third next-result))]

    [`(Suspend ,body)
     (define result (infer body (enter-child Λ 0)
                               Ψ
                               environment places callables fail))
     (list (first result) (row-union (second result) '(Suspend))
           (third result))]

    [`(Move ,place)
     #:when (exact-nonnegative-integer? place)
     (define type (lookup places place))
     (unless type (fail 'unknown-place core))
     (emit-use-request! Λ place '() 'move (set) core 'move-borrowed)
     (list `(Owned ,type) '(Own) Ψ)]

    [`(Move ,name)
     (define w (peel-node name))
     (define type (lookup environment w))
     (unless type (fail 'unbound-variable core))
     (emit-use-request! Λ w '() 'move (set) core 'move-borrowed)
     (when (borrow-typed? type) (fail 'move-borrowed core))
     (match type
       [`(Owned ,inner-type) (list `(Owned ,inner-type) '(Own) Ψ)]
       [_ (fail 'move-non-owned core)])]

    [`(Drop ,argument)
     (define dropped
       (match (peel-node argument)
         [`(Move ,w) (peel-node w)]
         [(? symbol? w) w]
         [_ #f]))
     ;; spec §7.5。Move を通さない裸の名前で、型が Owned のとき、
     ;; 段 1 は答えを決められない。借用が生きていれば drop-borrowed、
     ;; 生きていなければ owned-variable-requires-move である。
     ;; 段 1 で後者を出すと段 3 の判定を潰すので、両方を段 3 へ渡す。
     ;; ir が無いときは借用が無いので答えが段 1 で確定する。
     ;; そのとき渡してしまうと要求が記録されず、どちらも出ずに受理してしまう。
     (define dropped-type (and dropped (lookup environment dropped)))
     (define bare-owned?
       (and dropped
            (region-ctx-ir Λ)
            (symbol? (peel-node argument))
            dropped-type
            (owned-type? dropped-type)))
     (when dropped
       (emit-use-request! Λ dropped '() 'move (set) argument 'drop-borrowed
                          (and bare-owned? 'owned-variable-requires-move)))
     (when (and dropped
                (borrow-typed? (or (lookup environment dropped) '())))
       (fail 'drop-borrowed argument))
     (define argument-Λ (enter-child Λ 0))
     (define argument-result
       (if bare-owned?
           (list dropped-type '() Ψ)
           (let/ec recover
             (infer argument argument-Λ Ψ environment places callables
                    (lambda (key node . details)
                      (assert-typing-key key)
                      (recover #f))))))
     (cond
       [(and argument-result
             (owned-type? (first argument-result)))
        (list 'Unit
              (row-union (second argument-result) '(Own))
              (third argument-result))]
       [else
        (define argument-row
          (check-as argument '(Owned Res) argument-Λ
                    Ψ
                    environment places callables
                    (lambda (key node . details)
                      (assert-typing-key key)
                      (if (and (eq? key 'type-mismatch)
                               (eq? node argument))
                          (fail 'drop-non-owned argument)
                          (apply fail key node details)))))
        (list 'Unit (row-union (first argument-row) '(Own))
              (second argument-row))])]

    [`(Curry ,function ,argument)
     (match-define (list function-type function-row function-psi)
       (infer function (enter-child Λ 0)
              Ψ environment places callables fail))
     (define-values (peeled function-owned?)
       (peel-owned-function function-type function fail))
     (match (list peeled function-row function-psi)
       [(list `(NFn (,first-type ,remaining-types ...)
                    ,return-type ,latent-row ,obligations)
              _ _)
        (define summary
          (or (lookup-callable-summary (enter-child Λ 0) function)
              (let ([w (peel-node function)])
                (and (borrow-designator? w)
                     (region-ctx-summary Λ w)))))
        (define borrowed-parameter?
          (or (borrowed-type-anywhere? first-type)
              (ormap borrowed-type-anywhere? remaining-types)))
        (define borrowed-result?
          (borrowed-type-anywhere? return-type))
        (define borrowed-obligations?
          (borrowed-type-anywhere? obligations))
        (cond
          [(and summary
                (or borrowed-parameter? borrowed-result?
                    borrowed-obligations?))
           (fail 'unresolved-borrow-owner function)]
          [borrowed-parameter?
           (fail 'borrowed-function-parameter function)]
          [borrowed-result?
           (fail 'borrowed-function-result function)]
          [borrowed-obligations?
           (fail 'borrowed-function-result function obligations)])
        (when (and (owned-type? first-type)
                   (not (config-runtime-leaf? argument)))
          (require-ownleaf-root argument 'missing-ownleaf-root argument fail))
        (define argument-row
          (parameterize ([ownleaf-permitted
                          (if (owned-type? first-type) (list argument) '())])
            (check-as argument first-type (enter-child Λ 1)
                      function-psi
                      environment places callables fail)))
        (list (curry-result-type remaining-types return-type latent-row obligations
                                 (or function-owned? (owned-type? first-type)))
              (row-union function-row (first argument-row))
              (second argument-row))]
       [_ (fail 'curry-non-function function)])]

    [`(Error ,_) (fail 'error-needs-expected-type core)]

    [(? symbol? name)
     (define type (lookup environment name))
     (unless type (fail 'unbound-variable core))
     (when (owned-type? type) (fail 'owned-variable-requires-move core))
     (list type '() Ψ)]

    [`(Borrow ,w)
     (infer-borrow core w #f Λ Ψ environment places callables fail)]
    [`(BorrowMut ,w)
     (infer-borrow core w #t Λ Ψ environment places callables fail)]
    [`(BorrowAt ,ρ ,_ ,w)
     (check-region-annotation Λ ρ core fail)
     (infer-borrow core w #f Λ Ψ environment places callables fail)]
    [`(BorrowMutAt ,ρ ,_ ,w)
     (check-region-annotation Λ ρ core fail)
     (infer-borrow core w #t Λ Ψ environment places callables fail)]
    [`(Reborrow ,c_operand)
     (infer-reborrow core c_operand Λ Ψ environment places callables fail)]
    [`(ReborrowAt ,ρ ,_ ,c_operand)
     (check-region-annotation Λ ρ core fail)
     (infer-reborrow core c_operand Λ Ψ environment places callables fail)]
    [`(ProjBorrowAt ,_ ,_ ,operand ,label)
     (infer-projborrow core operand label Λ Ψ environment places callables fail)]
    [`(Read ,operand)
     (infer-read core operand Λ Ψ environment places callables fail)]
    [`(Assign ,target ,value)
     (infer-assign core target value Λ Ψ environment places callables fail)]

    [_ (fail 'ill-typed core)]))

;; 段 1 だけを走らせる。試験と、Task 7 の解決の段が使う。
;; with-typing は成功を (list 'ok <本体の返り値>) で包むので、ここで剥がす。
;; 返すのは裸の 6 つ組で、末尾は RegionApp の実引数要求と callable 要約である。
;; 段 1 で棄却されたときは error を上げる。
(define (typing-inference core-in places callables [environment '()]
                          [Λ (empty-region-ctx)])
  (define cs (box '()))
  (define rs (box '()))
  (define ras (box '()))
  (define tbl (box (hash)))
  (define ir (region-ctx-ir Λ))
  (define result
    (parameterize ([lifetime-collector cs]
                   [request-collector rs]
                   [region-arg-collector ras]
                   [lifetime-counter (box 0)]
                   [alpha-table tbl]
                   [merge-alpha-sources (make-hash)]
                   [callable-summaries (make-hash)]
                   [forwarding-summaries (make-hash)]
                   [template-collectors '()])
      (with-typing
       (lambda (fail)
         (define renamed
           (call-with-region-params
            (lambda () (alpha-rename-all-region-lams core-in))))
         (parameterize ([current-region-relation
                         (if ir
                             (make-region-relation ir (erase-core renamed))
                             equal?)])
           (match-define (list type _row _Ψ)
             (infer renamed Λ (empty-psi) environment places callables fail))
           (list type (unbox tbl) (reverse (unbox cs)) (reverse (unbox rs))
                 (collected-region-args)
                 (collected-callable-summaries)))))))
  (match result
    [(list 'ok value) value]
    [(list 'fail key _node details)
     (error 'typing-inference "段 1 が棄却した: ~a ~a" key details)]))

;; 呼出し位置の実引数を照合する。借用の region 欄は、宣言側では呼出しの
;; 起点、推論側では寿命を表すため、その欄同士を adopt で一致させない。
;; まず実引数の capability を use-source と同じ起点解決で取り、各 owner の
;; region が宣言側の region と一致することを確認する。その後は region 欄を
;; 推論側へ揃えた一時型で payload と mode だけを比較する。owner が解けない
;; 形は type-mismatch ではなく unresolved-borrow-owner で閉じる。
(define (argument-owner-rhos Λ core fail)
  (define ir (region-ctx-ir Λ))
  (unless ir (fail 'unresolved-borrow-owner core))
  (define caps (argument-capabilities Λ core 0 fail))
  (for/list ([cap (in-set caps)])
    (define owner (region-ctx-owner Λ (car cap)))
    (unless owner (fail 'unresolved-borrow-owner core))
    (region->rho ir owner)))

(define (call-argument-compatible? actual expected core Λ compatible? fail)
  (define actual* (normalize-type actual))
  (define expected* (normalize-type expected))
  (match* (actual* expected*)
    [((list ctor actual-payload actual-rho)
      (list same-ctor _ expected-rho))
     #:when (and (memq ctor '(Borrowed BorrowedMut))
                 (eq? ctor same-ctor))
     (if (equal? actual-rho expected-rho)
         (compatible? actual expected)
         (and (for/or ([owner-rho (in-list (argument-owner-rhos Λ core fail))])
                (equal? owner-rho expected-rho))
              (compatible? actual
                           (adopt-inferred-lifetimes expected actual))))]
    [(_ _) (compatible? actual expected)]))

(define (check-as/full core expected Λ Ψ environment places callables fail
                       [compatible? type-compatible?]
                       #:adopt? [adopt? #t])
  ((typing-point-probe) (region-ctx-point Λ))
  (match (peel-node core)
    [`(Construct ,data-type ,constructor ,fields ...)
     (define actual (peel-ty data-type))
     (unless (compatible? actual expected)
       (fail 'type-mismatch core expected actual))
     (match (check-construct constructor fields data-type
                              Λ
                              Ψ
                              environment places callables core fail)
       [(list row psi) (list row psi actual)])]

    [`(Error ,place)
     (unless (and (exact-nonnegative-integer? place)
                  (assoc place places))
       (fail 'unknown-place core))
     (list '() Ψ expected)]

    [`(Let (,name ,binding-mode ,type) ,bound ,body)
     (match (binding-context binding-mode (peel-ty type) bound
                             Λ
                             Ψ environment places callables core fail)
       [(list bound-row binding-type bound-psi)
        (define x (peel-bind name))
        (define Λ_owner (register-owner Λ x binding-type))
        (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
        (define callable (lookup-callable-summary (enter-child Λ 0) bound))
        (define borrowed? (borrow-typed? (normalize-type binding-type)))
        (define token
          (cond
            [(not borrowed?) (set)]
            [summary (forwarding-summary-keys summary)]
            [else (borrow-token-key Λ bound #:fail fail)]))
        (when (and summary borrowed? (set-empty? token))
          (fail 'unresolved-borrow-owner bound))
        ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
        ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
        ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
        ;; ため、表の側で fail を落としても未知の designator を見逃さない。
        (define fields (capability-field-table Λ bound))
        (define Λ_token
          (region-ctx-add-token Λ_owner x token
                                (and summary (forwarding-summary-source summary))
                                callable
                                fields))
        (define Λ_body (enter-child Λ_token 1))
        (define body-result
          (check-as/full body
                        expected
                        Λ_body
                        bound-psi
                        (extend environment (list x)
                                (list binding-type))
                        places
                        callables
                        fail
                        compatible?))
        (list (row-union bound-row (first body-result))
              (second body-result)
              (third body-result))])]

    [`(Let (,name ,type) ,bound ,body)
     (define bound-result
       (check-as/full bound (peel-ty type) (enter-child Λ 0)
                      Ψ environment places callables fail compatible?))
     (define x (peel-bind name))
     (define binding-type (peel-ty type))
     (define Λ_owner (register-owner Λ x binding-type))
     (define summary (lookup-forwarding-summary (enter-child Λ 0) bound))
     (define callable (lookup-callable-summary (enter-child Λ 0) bound))
     (define borrowed? (borrow-typed? (normalize-type binding-type)))
     (define token
       (cond
         [(not borrowed?) (set)]
         [summary (forwarding-summary-keys summary)]
         [else (borrow-token-key Λ bound #:fail fail)]))
     (when (and summary borrowed? (set-empty? token))
       (fail 'unresolved-borrow-owner bound))
     ;; 表は #:fail なしで取る。fail を渡すと (Let (y let Int) 1 y) の 1 が
     ;; designator の枝へ落ち、表を引くだけの呼出しが E-BOR-020 を出す。
     ;; ws の側は同じ位置で borrow-token-key が #:fail fail 付きに計算している
     ;; ため、表の側で fail を落としても未知の designator を見逃さない。
     (define fields (capability-field-table Λ bound))
     (define Λ_token
       (region-ctx-add-token Λ_owner x token
                             (and summary (forwarding-summary-source summary))
                             callable
                             fields))
     (define Λ_body (enter-child Λ_token 1))
     (define body-result
       (check-as/full body
                     expected
                     Λ_body
                     (second bound-result)
                     (extend environment
                             (list x)
                             (list binding-type))
                     places
                     callables
                     fail
                     compatible?))
     (list (row-union (first bound-result) (first body-result))
           (second body-result)
           (third body-result))]

    [`(Eliminate ,scrutinee (,branches ...))
     (check-eliminate scrutinee branches expected
                      Λ
                      Ψ
                      environment places callables core fail
                      compatible?)]

    [`(Scope (,managed-places ...) ,body)
     (unless (andmap (λ (place) (assoc place places))
                     managed-places)
       (fail 'unmanaged-place core))
     (check-as/full body expected (enter-child Λ 0)
                    Ψ environment places callables fail compatible?)]

    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define continuation-environment
       (recur-context callable
                      (peel-bind function)
                      (map peel-bind parameters)
                      body
                      Λ
                      Ψ
                      environment places callables core fail))
     (check-as/full continuation
                    expected
                    (enter-child Λ 1)
                    (second continuation-environment)
                    (first continuation-environment)
                    places
                    callables
                    fail
                    compatible?)]

    [`(Yield ,observed ,next)
      (define observed-result
       (parameterize ([ownleaf-permitted (list observed)])
         (infer observed (enter-child Λ 0)
               Ψ environment places callables fail)))
      (define observed-owned? (owned-type? (first observed-result)))
      (cond
        [(and observed-owned?
              (not (ownleaf-root? observed))
              (not (config-runtime-leaf? observed)))
         (fail 'missing-ownleaf-root observed)]
        [(and (not observed-owned?) (ownleaf-root? observed))
         (fail 'unexpected-ownleaf observed)])
      (define next-result
       (check-as/full next expected (enter-child Λ 1)
                      (third observed-result)
                      environment places callables fail compatible?))
     (list (rows-union
            (list (second observed-result)
                  (first next-result)
                  `((Yield ,(first observed-result)))))
           (second next-result)
           (third next-result))]

    [`(Suspend ,body)
     (define body-result
       (check-as/full body expected (enter-child Λ 0)
                      Ψ environment places callables fail compatible?))
     (list (row-union (first body-result) '(Suspend))
           (second body-result)
           (third body-result))]

    [_
     (match (infer core Λ Ψ environment places callables fail)
       [(list actual row result-psi)
        (unless (if adopt?
                   (compatible?
                    actual
                    (adopt-inferred-lifetimes expected actual))
                   (call-argument-compatible? actual expected core Λ
                                              compatible? fail))
          (fail 'type-mismatch core expected actual))
        (list row result-psi actual)])]))

;; 既存の呼び出しは結果の型を要らない。第 3 要素を落として渡す。
(define (check-as core expected Λ Ψ environment places callables fail
                  [compatible? type-compatible?]
                  #:adopt? [adopt? #t])
  (match (check-as/full core expected Λ Ψ environment places callables fail
                        compatible?
                        #:adopt? adopt?)
    [(list row psi _) (list row psi)]))

;; 入口検査は type-of/raw と core-check-row が共有する。片方だけ直す事故を
;; 避けるため、検査の順と key をここへ寄せる。
;; core は投影済みの項を受け取る。返り値は最初に破れた検査の
;; (list key details ...) か、すべて通ったときの #f である。
(define (borrowed-owned-payload-type subject)
  ;; core の型注釈を走査し、Borrowed または BorrowedMut の payload が直接
  ;; Owned である最初の型を返す。無ければ #f。
  (let search ([t subject])
    (match t
      [`(Borrowed (Owned ,_) ,_) t]
      [`(BorrowedMut (Owned ,_) ,_) t]
      [(? list?) (for/or ([e (in-list t)]) (search e))]
      [_ #f])))

(define (entry-violation core places callables environment)
  (cond
    [(not (redex-match? G2m c core)) '(not-core-term)]
    [(own-annotation-violation core)
     => (lambda (found) (list 'own-designator-mismatch found))]
    [(borrowed-owned-payload-type core)
     => (lambda (found) (list 'borrowed-owned-payload found))]
    [(not (core-types-normal? core)) '(non-normal-type)]
    [(not (valid-environment? environment))
     (list 'invalid-environment environment)]
    [(not (valid-places? places)) (list 'invalid-places places)]
    [(not (valid-callables? callables)) (list 'invalid-callables callables)]
    [else #f]))

(define (type-of/raw* core-in places callables environment Λ)
  (define cs (box '()))
  (define rs (box '()))
  (define ras (box '()))
  (define tbl (box (hash)))
  (define ir (region-ctx-ir Λ))
  (define result
    (parameterize ([lifetime-collector cs]
                   [request-collector rs]
                   [region-arg-collector ras]
                   [lifetime-counter (box 0)]
                   [alpha-table tbl]
                   [merge-alpha-sources (make-hash)]
                   [callable-summaries (make-hash)]
                   [forwarding-summaries (make-hash)]
                   [template-collectors '()])
      (with-typing
       (lambda (fail)
         ;; span.md §7.3: 入口検査だけ投影し、走査は spanful な項へ行う。
         (define core (erase-core core-in))
         (define violation (entry-violation core places callables environment))
         (when violation
           (apply fail (first violation) core-in (rest violation)))
         ;; 束縛名を入口で 1 度だけ付け替える。関係の表も同じ core から作る。
         (define renamed
           (call-with-region-params
            (lambda () (alpha-rename-all-region-lams core-in))))
         (define relation
           (if ir (make-region-relation ir (erase-core renamed)) equal?))
         (parameterize ([current-region-relation relation])
           ;; 段 1。
           (match-define (list type row Ψ)
             (infer renamed Λ (empty-psi) environment places callables fail))
           ;; 段 2。
           (define solved (typing-solve ir (reverse (unbox cs))))
           (match solved
             [(list 'error broken)
              (define c (first broken))
              (fail (constraint-key c) (constraint-node c))]
             [(list 'ok σ)
              ;; 段 3。
              (check-region-args ir σ (collected-region-args) relation fail)
              (check-borrows ir σ Ψ (reverse (unbox rs)) sigma-ref fail)
              ;; 型の中の α を σ で解いてから正規化する。materialize が core の
              ;; 注釈へ行う置換と同じ σ を、型の側へも行う（spec §6.3）。
              ;; 置換を正規化より先に置くのは、Union の重複除去が置換の後で
              ;; なければ効かないためである。σ(α_1) と σ(α_2) が同じ region に
              ;; なる形では、正規化を先に置くと正規形の不変が破れる。
              (define substituted (subst-type-regions type σ ir))
              (define normalized (normalize-type substituted))
              (unless normalized
                (fail 'non-normalizable-result-type core-in substituted))
              ;; row も同じ σ で解く。Yield は観測値の型を (Yield τ) として、
              ;; Perform は (Return boundary τ) として row へ入れるため、
              ;; 借用をこれらで返すと row が α を運ぶ。
              (list normalized
                    (subst-type-regions row σ ir)
                    (unbox tbl)
                    σ
                    renamed)]))))))
  ;; 失敗の details も同じ σ の下へ置く。段 1 の fail は脱出継続で
  ;; with-typing の外へ出るため、σ を掛ける位置はここしかない。
  (materialize-fail-result (region-ctx-ir Λ) (reverse (unbox cs)) result))

;; 既存の呼び出しは結果の型を要らない。第 3 要素以降を落として渡す。
(define (type-of/raw core-in places callables [environment '()]
                     [Λ (empty-region-ctx)])
  (match (type-of/raw* core-in places callables environment Λ)
    [(list 'ok (list type row _table _σ _renamed)) (list 'ok (list type row))]
    [other other]))

;; 機械へ渡すため、型付けと同じ σ で core の注釈を materialize する。
(define (core-type-of/materialized core-in places callables
                                   [environment '()]
                                   [Λ (empty-region-ctx)])
  (match (type-of/raw* core-in places callables environment Λ)
    [(list 'ok (list type _row table σ renamed))
     (define ir (region-ctx-ir Λ))
     (list 'ok type (if ir (materialize-regions ir renamed table σ) renamed))]
    [other other]))

;; 失敗の details は、型と effect row に続く 3 つ目の σ の経路である（spec §6.3）。
;; 段 1 の fail は推論の途中の型を details へ入れる。typing.rkt:1346 の
;; typing-expected/found がそれを diagnostic-of の expected と found へ
;; そのまま渡すので、α が残ると Task 3 の寿命変数の検査が型検査を
;; 異常終了させる。返す前に必ず解くか捨てるかする。
(define (materialize-fail-result ir cs result)
  (match result
    [(list 'fail key node details)
     (match (and ir (pair? cs) (typing-solve ir cs))
       [(list 'ok σ)
        (list 'fail key node
              (map (lambda (d) (subst-type-regions d σ ir)) details))]
       ;; ir が無い形と制約が空の形では α を採らない。details はそのままでよい。
       [#f result]
       ;; 段 1 が棄却した時点の制約集合は不完全である。出口の下限が欠けると
       ;; σ(α) は本来より狭くなり、α を左辺に持つ Reborrow と分岐合流の制約が
       ;; 偽に破れる。左辺が具体的な region の BOR-001 だけは向きが逆になるが、
       ;; 制約の種別で健全性が変わる規則は置かない。段 1 の key と node を保ち、
       ;; 解けない details だけを捨てる。失われるのは expected と found であり、
       ;; 診断の分類と位置は残る（spec §6.3）。
       [_ (list 'fail key node '())])]
    [_ result]))

;; 破れた上限制約から診断の key と節点を引く。
;; Task 12 が合流の制約を足すとき、ここに 1 行足せば済む形にする。
(define (constraint-key c)
  (case (region-constraint-kind c)
    [(outlives) 'borrow-escapes-owner]
    [(reborrow) 'reborrow-region-escapes]
    [else
     (error 'constraint-key "未知の region constraint kind: ~s"
            (region-constraint-kind c))]))

(define (constraint-node c) (region-constraint-node c))

;; 型の中の `(RVar k)` を σ の解へ置き換える（spec §6.3）。
;; α が現れるのは借用の 3 つ目の欄だけだが、Union や Record や NFn の中へ
;; 入れ子になるため木全体を歩く。
;; これを通さないと、`type-of` の返り値に α が残り、spec §11 の不変性が破れる。
;; effect row も同じ関数で解く。row の要素は (Return boundary τ) と (Yield τ) と
;; 記号であり、型を運ぶ欄はこの走査で覆える。validators.rkt の
;; effect-owned-free? が row の同じ 2 形から型を取り出しているのと対応する。
(define (subst-type-regions t σ ir)
  (match t
    [`(RVar ,_) (region->rho ir (sigma-ref σ t))]
    [(? list? ts) (map (lambda (x) (subst-type-regions x σ ir)) ts)]
    [_ t]))

;; 段 3 の出口で α が残っていないことを試験が見るための述語。
(define (contains-lifetime-var? t)
  (cond
    [(lifetime-var? t) #t]
    [(list? t) (ormap contains-lifetime-var? t)]
    [else #f]))

;; 段 1 の試験専用。typing の走査が訪れた point を集める。
;; 型検査の成否は問わず、走査の網羅だけを観測する。
(define (typing-visited-points core places callables [environment '()])
  (define seen (box '()))
  (parameterize ([typing-point-probe
                  (lambda (point)
                    (set-box! seen (cons point (unbox seen))))])
    (with-typing
     (lambda (fail)
       (infer core (empty-region-ctx) (empty-psi)
              environment places callables fail))))
  (unbox seen))

(define (core-type-of core-in places callables [environment '()]
                      [Λ (empty-region-ctx)])
  (match (type-of/raw core-in places callables environment Λ)
    [(list 'ok result) result]
    [_ 'ill-typed]))

;; spec §8: Diagnostic を組む位置はここ 1 箇所だけである。
;; producer は details の先頭へ expected、次へ actual を渡す
;; （G4e2 spec §3）。elaborate.rkt の distribute-details と同じ規則である。
;; key の allowlist は残す。表に無い key の details 2 件は
;; expected と actual の対ではない。
(define (typing-expected/found key details)
  (match* (key details)
    [((or 'type-mismatch
          'arity-mismatch
          'parameter-arity-mismatch
          'branch-binder-arity
          'undeclared-function-effect)
      (list expected actual))
     (values expected actual)]
    [(_ '()) (values #f #f)]
    [(_ (list only)) (values #f only)]
    [(_ _) (values #f details)]))

(define (typing-diagnostic key node details)
  (define-values (expected found) (typing-expected/found key details))
  (diagnostic-of 'typing key
                #:primary-span (entry-span node)
                #:expected expected
                #:found found))

;; spec §3: G4d2 の公開 Diagnostic 境界はこの adapter である。
;; core-type-of は 'ill-typed を返す低レベルの判定として残し、判定 API と診断 API
;; を混ぜない。
;; primary-span は fail が運ぶ棄却節点から取る。entry-span が span を取れないときだけ
;; synthetic fallback へ落ちる。
(define (core-type-of/diagnostic core-in places callables [environment '()]
                                 [Λ (empty-region-ctx)])
  (match (type-of/raw core-in places callables environment Λ)
    [(list 'ok (list type row)) (list type row)]
    [(list 'fail key node details) (typing-diagnostic key node details)]))

(define (core-check-row core-in places callables expected [environment '()]
                        [Λ (empty-region-ctx)])
  ;; span.md §7.3: core-type-of と同じく、既存の型走査へ渡す前に投影する。
  (define core (erase-core core-in))
  (and (not (entry-violation core places callables environment))
       (type? expected)
       (check-as/boolean core-in expected environment places callables Λ)))

(define (core-check core places callables expected row [environment '()]
                    [Λ (empty-region-ctx)])
  (and (row? row)
       (let ([actual-row
              (core-check-row core places callables expected environment Λ)])
         (and actual-row (row=? actual-row row)))))

;; Ξ の第 1 段。place を直接含む値は BorrowRef と BorrowMutRef だけだが、
;; typing.rkt にその値の節はないため type-of/raw が拒否する。OwnedLeaf を
;; 含む Rec 欄は config 専用の with-config-typing でだけ許されるが、heap を
;; place の番号順に畳み込むため、前方参照を含む値は依然として拒否される。
;; 閉包の捕捉先もこの順序に従うため、R-Assign の後に再検査しても前方参照の
;; 拒否は同じように効く。
;; H の entry の並びは規定されないため、先に番号で整列する。
(define (derive-places heap callables)
  (for/fold ([acc '()] #:result (and acc (reverse acc)))
            ([entry (in-list (sort heap < #:key first))])
    #:break (not acc)
    (match (type-of/raw (second entry) (reverse acc) callables)
      [(list 'ok (list type _row))
       (cons (list (first entry) (strip-owned type)) acc)]
      [_ #f])))

;; Ξ は place の指す値そのものの型を持ち、Owned の包みは place 側が担う。
;; heap の値の型が常に Owned で始まるとは仮定しない。
(define (strip-owned type)
  (match type
    [`(Owned ,inner) inner]
    [_ type]))

;; Ω[p]=Available の root の値だけを live 集合へ入れる。Moved root の H entry
;; は R-Move 後も stale value を保持するため、ここへ含めない。
(define (available-root-values heap states)
  (for/list ([entry (in-list heap)]
             #:when (match (assoc (first entry) states)
                       [(list _ 'Available) #t]
                       [_ #f]))
    (second entry)))

;; θ の (obs v) の payload を出現順に返す。観測は履歴であるが、観測した値
;; そのものは回収前の live な値として残るため、token 検査の対象に含める。
(define (observed-values trace)
  (for/list ([event (in-list trace)]
             #:when (match event
                      [`(obs ,_) #t]
                      [_ #f]))
    (second event)))

;; 制御項、Available な root の値、θ の obs の payload を token 検査の対象に
;; する。Moved/Dropped の root の heap entry は R-Move 後の stale value なので
;; 含めない。
(define (live-roots core heap states trace)
  (append (cons core (available-root-values heap states))
          (observed-values trace)))

(define (live-tokens core heap states trace)
  (append-map collect-tokens (live-roots core heap states trace)))

;; 値である最大の部分項へ leaf-positions-ok? を課し、値でない構成子はその子を
;; 透過して見る。Drop (Rec ((f mut leaf))) のような制御項は許す一方、値の位置へ
;; leaf を隠す構成子は拒否する。
(define (control-leaf-positions-ok? core)
  (define (value-position-ok? candidate)
    (if (redex-match? G2m v candidate)
        (observed-leaf-positions-ok? candidate)
        (control-leaf-positions-ok? candidate)))
  (match (peel-node core)
    ;; Yield の観測 payload と Curry の固定引数は producer が作る値位置
    ;; なので、根の leaf を許しつつ値内部の走査規則を適用する。
    [`(Yield ,observed ,continuation)
     (and (value-position-ok? observed)
          (control-leaf-positions-ok? continuation))]
    [`(Curry ,function ,argument)
     (and (control-leaf-positions-ok? function)
          (value-position-ok? argument))]
    ;; CurryVal の固定引数は β 縮約で Apply の実引数や Drop の引数へ
    ;; 移るため、評価途中のこれらの値位置では根 leaf を許す。
    [`(Apply ,function ,arguments ...)
     (and (control-leaf-positions-ok? function)
          (andmap value-position-ok? arguments))]
    [`(Let ,_binding ,bound ,body)
     (and (value-position-ok? bound)
          (control-leaf-positions-ok? body))]
    [`(Drop ,argument)
     (value-position-ok? argument)]
    [_
     (cond
       [(redex-match? G2m v core) (leaf-positions-ok? core)]
       [(list? core) (andmap control-leaf-positions-ok? core)]
       [else #t])]))

;; finLeaf は所有値の走査が作る owner path を記録する。Construct の欄は
;; positional segment を使うため、空 path だけを拒否する。
(define (trace-paths-ok? trace)
  (andmap
   (lambda (event)
     (match event
       [`(finLeaf ,_ ,fp) (and (pair? fp) (owner-path? fp))]
       [_ #t]))
   trace))

(define (config-ok? configuration callables expected row)
  ;; entry-violation と共通の型・形状検査に加え、config-ok? は構成固有の
  ;; root/leaf 位置と token 状態も検査する。G2m config を見る別の入口なので、
  ;; places を heap から導出する entry-violation はそのまま呼ばない。
  (with-config-typing (lambda ()
    (and (redex-match? G2m config configuration)
         (core-types-normal? configuration)
         (valid-callables? callables)
         (type? expected)
         (row? row)
         (match configuration
           [`(cfg ,core ,heap ,states ,token-states ,trace)
            (and (unique-table? heap)
                 (unique-table? states)
                 (equal? (sort (map first heap) <)
                         (sort (map first states) <))
                 (unique-table? token-states)
                 (trace-paths-ok? trace)
                 ;; G5 derives Ξ from each heap value rather than assuming Res.
                 (let ([places (derive-places heap callables)])
                   (and
                    places
                    (for/and ([entry (in-list heap)])
                      (define declared
                        (second (assoc (first entry) places)))
                      (define value-row
                        (check-as/boolean (second entry)
                                          (list 'Owned declared)
                                          '()
                                          places
                                          callables
                                          #:compatible?
                                          ;; Rec の leaf は payload の bare Record を
                                          ;; 推論するため、place の Owned 宣言へ持ち上げる。
                                          ;; leaf を含まない通常の値は旧来の厳密比較を保つ。
                                          (if (contains-owned-leaf? (second entry))
                                              owned-lift-compatible?
                                              type-compatible?)))
                      (and value-row (null? value-row)))
                    (let ([actual-row
                           (check-as/boolean core expected '()
                                             places callables)])
                      (and actual-row
                           (row=? actual-row row)
                           ;; 根の位置に leaf は置かない。
                           (not (owned-leaf? core))
                           ;; H の leaf は走査で辿れる位置に限る。
                           (andmap (lambda (entry)
                                     (leaf-positions-ok? (second entry)))
                                   heap)
                           (andmap observed-leaf-positions-ok?
                                   (observed-values trace))
                           (control-leaf-positions-ok? core)
                           ;; token の live 出現と Λtok の状態を突き合わせる。
                           (let ([tokens (live-tokens core heap states trace)])
                             (and
                              (= (length tokens)
                                 (length (remove-duplicates tokens)))
                              (for/and ([tk (in-list tokens)])
                                (assoc tk token-states))
                              (for/and ([entry (in-list token-states)])
                                (define occurrences
                                  (length
                                   (filter (lambda (tk)
                                             (equal? tk (first entry)))
                                           tokens)))
                                (case (second entry)
                                  [(Available Moved) (= occurrences 1)]
                                  [(Dropped) (= occurrences 0)]
                                  [else #f])))))))))]
           [_ #f])))))

(module+ test
  (require rackunit)

  ;; fail は key ill-typed を未登録として error にしない。
  (check-equal? (with-typing (lambda (fail) (fail 'ill-typed 1)))
                '(fail ill-typed 1 ()))

  ;; registry に無い key は error になる。
  (check-exn #px"registry に無い typing の key"
             (lambda ()
               (with-typing (lambda (fail) (fail 'no-such-key 1))))))

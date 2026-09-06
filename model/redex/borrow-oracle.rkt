#lang racket

(require racket/match
         racket/set)

(provide control-diff
         borrow-form-candidates
         borrow-value?
         rule-bucket
         (struct-out provenance)
         empty-provenance
         provenance-extend
         resolve-designator)

;; spec §4.5。oracle は typing.rkt と borrow.rkt の判定を一切呼ばない。
;; 呼ぶと静的な借用検査の言い換えになり、独立な照合の意味が消える。

(define (borrow-value? v)
  (match v
    [`(BorrowRef ,_ ,_ ,_) #t]
    [`(BorrowMutRef ,_ ,_ ,_) #t]
    [_ #f]))

;; 簡約前後の制御項について、差分をすべて含む最小の位置を求め、その位置の
;; 部分項の対を返す。制御項が等しいときだけ #f を返す。
;; 子が 2 つ以上異なる節点は、その節点自体が差分を含む最小の位置である。
;; 位置が根まで戻る場合も対は返す。構造が食い違う位置も、それ自体が最小の
;; 位置である。
(define (control-diff pre post)
  (cond
    [(equal? pre post) #f]
    [(and (list? pre) (list? post)
          (= (length pre) (length post)))
     (define differing
       (for/list ([a (in-list pre)]
                  [b (in-list post)]
                  [i (in-naturals)]
                  #:unless (equal? a b))
         i))
     (if (= (length differing) 1)
         (control-diff (list-ref pre (first differing))
                       (list-ref post (first differing)))
         (cons pre post))]
    [else (cons pre post)]))

;; spec §4.6。承認済みの redex と contractum の対の表。
;; 分類は根、派生、再借用、使用、未検証のいずれかである。
(define (approved-forms redex contractum)
  (match (list redex contractum)
    [(list `(BorrowAt ,ρ (Own ,p ,fp) ,w)
           `(BorrowRef ,p2 ,fp2 ,ρ2))
     #:when (and (equal? p p2) (equal? fp fp2) (equal? ρ ρ2))
     (list (list 'root 'shared p fp ρ w))]
    [(list `(BorrowMutAt ,ρ (Own ,p ,fp) ,w)
           `(BorrowMutRef ,p2 ,fp2 ,ρ2))
     #:when (and (equal? p p2) (equal? fp fp2) (equal? ρ ρ2))
     (list (list 'root 'mut p fp ρ w))]
    [(list `(ReborrowAt ,ρ (Own ,p ,fp)
                         (BorrowMutRef ,pp ,fpp ,ρp))
           `(BorrowRef ,p2 ,fp2 ,ρ2))
     #:when (and (equal? p p2) (equal? fp fp2) (equal? ρ ρ2)
                 (equal? p pp) (equal? fp fpp))
     (list (list 'reborrow p fp ρ ρp))]
    [(list `(ProjBorrowAt ,ρ (Own ,p ,fp-result)
                           (,tag ,pp ,fpp ,ρp) ,label)
           `(,tag2 ,p2 ,fp2 ,ρ2))
     #:when (and (memq tag '(BorrowRef BorrowMutRef))
                 (memq tag2 '(BorrowRef BorrowMutRef))
                 (not (and (eq? tag 'BorrowRef)
                           (eq? tag2 'BorrowMutRef)))
                 (equal? p pp) (equal? p p2)
                 (equal? fp-result (append fpp (list label)))
                 (equal? fp2 fp-result)
                 (equal? ρ ρ2))
     (list (list 'derived
                 (if (eq? tag2 'BorrowMutRef) 'mut 'shared)
                 p fp2 ρ pp fpp ρp))]
    [(list `(Eliminate (BorrowRef ,p ,fp ,ρ) ,_ ...) contractum)
     (define children (collect-borrow-values contractum))
     (define expected
       (for/list ([child (in-list children)])
         (match child
           [`(BorrowRef ,cp ,cfp ,cρ)
            #:when (and (equal? cp p) (equal? cρ ρ)
                        (= (length cfp) (add1 (length fp)))
                        (equal? (take cfp (length fp)) fp)
                        (exact-nonnegative-integer? (last cfp)))
            (list 'derived 'shared p cfp ρ p fp ρ)]
           [_ (list 'unverified)])))
     (if (null? expected) (list (list 'unverified)) expected)]
    [(list `(Read (,tag ,p ,fp ,ρ)) _)
     #:when (memq tag '(BorrowRef BorrowMutRef))
     (list (list 'use (if (eq? tag 'BorrowMutRef) 'mut 'shared) p fp ρ))]
    [(list `(Assign (BorrowMutRef ,p ,fp ,ρ) ,_) 'unit)
     (list (list 'use 'mut p fp ρ))]
    [_ #f]))

;; contractum の中の借用値をすべて拾う。
(define (collect-borrow-values t)
  (cond
    [(borrow-value? t) (list t)]
    [(list? t) (append* (map collect-borrow-values t))]
    [else '()]))

;; spec §4.6。照合できず、しかも redex か contractum に借用値が現れるなら
;; unverified を返して失敗させる。借用値が無い遷移は非借用遷移として扱う。
(define (borrow-form-candidates redex contractum)
  (define matched (approved-forms redex contractum))
  (cond
    [(and matched (pair? matched)) matched]
    [(or (pair? (collect-borrow-values redex))
         (pair? (collect-borrow-values contractum)))
     (list (list 'unverified))]
    [else '()]))

;; spec §4.6。置換を行う規則。ここから記号と place の対応を取る。
;; -->g2/rules は -->g1/rules を extend-reduction-relation で拡張しており、
;; G1 側の名前も発火しうるので両方を挙げる。
(define substituting-rule-names
  (seteq 'R-Beta 'R-Let 'R-LetB 'R-LetOwned 'R-LetOwnedB
         'R-Eliminate 'R-EliminateRef
         'R-RecurUnfold 'R-HandleReturn))

;; spec §4.6。置換を行わない規則。名前が増えたときに黙って取りこぼさないよう
;; 明示的に挙げ、どちらにも無い名前は unknown として検査を失敗させる。
;; 二つの集合の和は -->g2/rules の 41 名と一致する。Step の回帰がこれを検査する。
(define non-substituting-rule-names
  (seteq 'R-Delta 'R-Proj 'R-Drop 'R-Borrow 'R-BorrowError
         'R-BorrowMut 'R-BorrowMutError 'R-Reborrow
         'R-ProjBorrow 'R-ProjBorrowMut 'R-Read 'R-ReadMut 'R-Assign
         'R-Move 'R-MoveError 'R-ScopeValue 'R-ScopeError 'R-ScopeAbort
         'R-RecurBind 'R-RegionApp 'R-Yield 'R-Suspend 'R-Discharge 'R-OwnLeaf
         'R-CurryVal 'R-ApplyCurry
         'R-HandleValue 'R-HandleSkip 'R-HandleError
         'R-RetireValue 'R-RetireError 'R-RetirePerform))

(define (rule-bucket name)
  (cond [(set-member? substituting-rule-names name) 'substituting]
        [(set-member? non-substituting-rule-names name) 'non-substituting]
        [else 'unknown]))

;; spec §4.6。記号から place への多価の対応。
(struct provenance (table) #:transparent)

(define (empty-provenance) (provenance (hash)))

(define (provenance-add prov name place)
  (provenance
   (hash-update (provenance-table prov) name
                (lambda (s) (set-add s place))
                (set))))

(define (resolve-designator prov w)
  (cond
    [(exact-nonnegative-integer? w) (list w)]
    [(symbol? w)
     (set->list (hash-ref (provenance-table prov) w (set)))]
    [else '()]))

(define (cfg-parts config)
  (match config
    [`(cfg ,core ,H ,Ω ,Λtok ,θ) (list core H Ω Λtok θ)]
    [_ #f]))

(define (table-keys tbl)
  (for/set ([entry (in-list tbl)]) (first entry)))

;; 裸の自然数は整数リテラルとも place とも読める。Ω の鍵に現れる値だけを
;; place の候補として扱う。取りこぼしは起きず、余分な対応が入りうるだけ。
(define (place-candidates v known-places)
  (cond
    [(and (exact-nonnegative-integer? v) (set-member? known-places v))
     (list v)]
    [(borrow-value? v) (list (second v))]
    [else '()]))

;; branch の形は (K (x ...) -> c) である。
(define (branches-for K branches)
  (for/list ([br (in-list branches)]
             #:when (equal? (first br) K))
    br))

(define (branch-binders K branches)
  (define found (branches-for K branches))
  ;; 同じ K の枝が 2 つ以上あると枝が一意に定まらないので #f を返し、
  ;; 呼び出し側が fail させる。
  (and (= (length found) 1) (second (first found))))

;; spec §4.6。置換規則の redex から (記号 . 値) の対を取り出す。
;; 取り出せない形なら #f を返し、呼び出し側が fail させる。
(define (substitution-pairs name redex contractum)
  (match (list name redex)
    [(list (or 'R-Let 'R-LetB) `(Let (,x ,_bmode ,_τ) ,v-bound ,_body))
     (list (cons x v-bound))]
    [(list 'R-Beta `(Apply (Lam ,_O ,_cid (,x ...) ,_body) ,v ...))
     #:when (= (length x) (length v))
     (map cons x v)]
    [(list 'R-RecurUnfold
           `(Apply (RecurVal ,_cid ,f (,x ...) ,_body) ,v ...))
     #:when (= (length x) (length v))
     ;; f へ束縛されるのは RecurVal 自身であり place ではない。
     (cons (cons f 'not-a-place) (map cons x v))]
    [(list 'R-Eliminate `(Eliminate (Construct ,_τ ,K ,v ...) ,branches))
     (define binders (branch-binders K branches))
     (and binders (= (length binders) (length v)) (map cons binders v))]
    [(list 'R-EliminateRef
           `(Eliminate (BorrowRef ,p ,fp ,ρ) ,branches))
     ;; 束縛子へ渡るのは欄を指す借用参照であり、規則が組み立てる。
     ;; contractum は本体が実際に使った欄しか含まないため、出現した参照の
     ;; arity だけでは未使用の束縛子を復元できない。各枝の本体へ位置順の
     ;; 参照を同時置換して contractum と比較し、合致した全候補を合併する。
     (define (child-ref i) (list 'BorrowRef p (append fp (list i)) ρ))
     (define matching
       (for/list ([b (in-list branches)]
                  #:when (and (list? b)
                               (= (length b) 4)
                               (list? (second b))
                               (eq? (third b) '->))
                  #:do [(define binders (second b))]
                  #:when (equal? (substitute-branch-body
                                  (fourth b)
                                  binders
                                  (for/list ([i (in-range (length binders))])
                                    (child-ref i)))
                                contractum))
         (for/list ([x (in-list (second b))]
                    [i (in-naturals 0)])
           (cons x (child-ref i)))))
     (if (null? matching) #f (apply append matching))]
    [(list 'R-HandleReturn
           `(Handle ,_op (,x -> ,handler) ,_inner))
     (define inferred (infer-substituted-value handler x contractum))
     (cond
       [(not inferred) #f]
       [(null? inferred) '()]
       [else (list (cons x (first inferred)))])]
    [_ #f]))

;; R-HandleReturn は handler 本体へ payload を置換した結果を返す。
;; F の走査を再現すると値の内部の Perform を誤って拾うため、redex 内の
;; handler 本体と contractum を逆向きに照合して実際の payload を復元する。
(define (infer-substituted-value body binder contractum)
  (define found? (box #f))
  (define payload (box #f))
  (define (walk source result)
    (cond
      [(and (symbol? source) (eq? source binder))
       (cond
         [(unbox found?) (equal? (unbox payload) result)]
         [else (set-box! found? #t) (set-box! payload result) #t])]
      [(and (pair? source) (pair? result)
            (= (length source) (length result)))
       (andmap walk source result)]
      [else (equal? source result)]))
  (and (walk body contractum)
       (if (unbox found?) (list (unbox payload)) '())))

;; 枝本体の束縛子を同じ位置の借用参照へ置き換える。
;; 生成域は unique binders を満たすため、ここでは構文木の全ての葉を
;; 走査する。未知の枝形は呼び出し側の候補から除外される。
(define (substitute-branch-body body binders values)
  (define substitutions (make-hash (map cons binders values)))
  (define (walk t)
    (cond
      [(symbol? t) (hash-ref substitutions t t)]
      [(pair? t) (map walk t)]
      [else t]))
  (walk body))

;; spec §4.6。規則名で仕分け、置換規則なら記号と place の対応を足す。
;; 未知の規則、形が取り出せない置換規則、R-LetOwned 系の増分が想定外の場合は
;; fail を返し、その trace の検査を失敗させる。
(define (provenance-extend prov name pre post)
  (define pre-parts (cfg-parts pre))
  (define post-parts (cfg-parts post))
  (cond
    [(or (not pre-parts) (not post-parts)) 'fail]
    [else
     (define known-places (table-keys (third pre-parts)))
     (case (rule-bucket name)
       [(non-substituting) prov]
       [(unknown) 'fail]
       [(substituting)
        (cond
          [(memq name '(R-LetOwned R-LetOwnedB))
           (extend-let-owned prov pre-parts post-parts)]
          [else
           (define diff (control-diff (first pre-parts) (first post-parts)))
           ;; 空の対応（束縛子を持たない枝）は正しい結果なので、#f とだけ区別する。
           (define pairs
             (and diff (substitution-pairs name (car diff) (cdr diff))))
           (cond
             [(not pairs) 'fail]
             [else
              (for/fold ([acc prov]) ([pair (in-list pairs)])
                (for/fold ([acc acc])
                          ([place (in-list
                                   (place-candidates (cdr pair)
                                                     known-places))])
                  (provenance-add acc (car pair) place)))])])]
       [else 'fail])]))

;; spec §4.6。所有束縛は H の増分から fresh place を取る。
;; 増分がちょうど 1 件で、同じ place が Ω にも増えている場合だけ採る。
(define (extend-let-owned prov pre-parts post-parts)
  (define pre-H (table-keys (second pre-parts)))
  (define post-H (table-keys (second post-parts)))
  (define pre-Ω (table-keys (third pre-parts)))
  (define post-Ω (table-keys (third post-parts)))
  (define added-H (set-subtract post-H pre-H))
  (define added-Ω (set-subtract post-Ω pre-Ω))
  (cond
    [(not (= (set-count added-H) 1)) 'fail]
    [(not (equal? added-H added-Ω)) 'fail]
    [else
     (define p-new (set-first added-H))
     (define diff (control-diff (first pre-parts) (first post-parts)))
     (match (and diff (car diff))
       [`(Let (,x ,_bmode ,_τ) ,_v ,_body) (provenance-add prov x p-new)]
       ;; R-LetOwnedB の redex は Scope ごと入れ替わるので、Let を内側から探す。
       [(? list? redex)
        (define found (find-let-binder redex))
        (if found (provenance-add prov found p-new) 'fail)]
       [_ 'fail])]))

(define (find-let-binder t)
  (match t
    [`(Let (,x ,_bmode ,_τ) ,_v ,_body) x]
    [(? list?) (for/or ([sub (in-list t)]) (find-let-binder sub))]
    [_ #f]))

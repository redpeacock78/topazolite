#lang racket/base

(require racket/match
         racket/set
         racket/format)

(provide region-free-params
         region-param-counter
         bound-region-params
         region-binder-context
         current-region-relation
         call-with-region-params
         fresh-region-param
         fresh-region-param/avoiding
         region-lam-parts
         rebuild-region-lam
         alpha-rename-region-lam
         rename-region-params
         subst-region-params
         alpha-rename-all-region-lams
         term-symbols)

;; 型木を下って自由な rp の集合を返す。Core を受けた場合も RegionLam の
;; 束縛を除く。RegionApp の実引数は静的な region 出現として列を下る。
(define (region-free-params type)
  (let walk ([t type])
    (match t
      [`(RParam ,rp) (set rp)]
      [`(ForallRegion (,rps ...) ,body)
       (set-subtract (walk body) (list->set rps))]
      [(app region-lam-parts (list _ rps body))
       (set-subtract (walk body) (list->set rps))]
      [(? list?)
       (for/fold ([free (set)]) ([element (in-list t)])
         (set-union free (walk element)))]
      [_ (set)])))

;; 付け替えに使う名前の供給元。typing または IR の文脈ごとに初期化する。
(define region-param-counter (make-parameter #f))

;; 現在の項を囲む RegionLam が束縛している rp の集合。
;; Apply と Curry の境界検査は infer の深い位置にあり、引数で運ぶと infer の
;; 全経路へ引数が増える。既定は空集合であり、既定のままでは借用型がすべて
;; 違反になる。つまり region 引数を書かない programme の判定は変わらない。
(define bound-region-params (make-parameter (set)))

;; 直上の RegionLam が束縛した rp の並び。
;; #f は直上に RegionLam が無いこと、空の並びは束縛 0 個の
;; RegionLam が直上にあることを表す。
(define region-binder-context (make-parameter #f))

;; compat? へ渡す region どうしの関係。既定は equal? である。
;; typing の funnel は type-compatible? であり、merge-branch-compatible? は
;; 引数 2 つの callback として渡るため、引数ではなく parameter で供給する。
(define current-region-relation (make-parameter equal?))

(define (call-with-region-params thunk)
  (parameterize ([region-param-counter (box 0)])
    (thunk)))

(define (fresh-region-param base)
  (define counter (region-param-counter))
  (unless (box? counter)
    (error 'fresh-region-param
           "region-param-counter が parameterize されていない: ~s" base))
  (define index (unbox counter))
  (set-box! counter (add1 index))
  (string->symbol (~a base "." index)))

;; forbidden に載らない名前が出るまで採り直す。
(define (fresh-region-param/avoiding base forbidden)
  (let loop ()
    (define candidate (fresh-region-param base))
    (if (set-member? forbidden candidate) (loop) candidate)))

;; RegionLam の spanless/spanful な形を共通の三要素へ剥がす。
(define (region-lam-parts term)
  (match term
    [(list 'RegionLam (list (? symbol? rps) ...) body) (list #f rps body)]
    [(list 'RegionLam (and s (list '#:span _ _ _))
           (list (? symbol? rps) ...) body)
     (list s rps body)]
    [_ #f]))

(define (rebuild-region-lam s rps body)
  (if s (list 'RegionLam s rps body) (list 'RegionLam rps body)))

;; RegionLam の束縛名を capture-avoiding に付け替える。
(define (alpha-rename-region-lam term)
  (match (region-lam-parts term)
    [(list s rps body)
     (define forbidden (set-union (term-symbols body) (list->set rps)))
     (define renaming
       (for/hash ([rp (in-list rps)])
         (values rp (fresh-region-param/avoiding rp forbidden))))
     (rebuild-region-lam
      s
      (for/list ([rp (in-list rps)]) (hash-ref renaming rp))
      (rename-region-params body renaming))]
    [#f (error 'alpha-rename-region-lam "RegionLam ではない: ~s" term)]))

;; renaming に載る rp だけを付け替え、内側の束縛で shadow する。
(define (rename-region-params term renaming)
  (let walk ([t term] [ren renaming])
    (define (shadow binders)
      (for/fold ([narrowed ren]) ([binder (in-list binders)])
        (hash-remove narrowed binder)))
    (match t
      [`(RParam ,rp) `(RParam ,(hash-ref ren rp rp))]
      [(app region-lam-parts (list s rps body))
       (rebuild-region-lam s rps (walk body (shadow rps)))]
      [`(ForallRegion (,rps ...) ,body)
       `(ForallRegion ,rps ,(walk body (shadow rps)))]
      [(? list?)
       (for/list ([element (in-list t)]) (walk element ren))]
      [_ t])))

;; (RParam rp) を表の値そのものへ置き換える。
;; rename-region-params は (RParam rp) の中の名前だけを替えるため、region の項
;; そのものへ置き換える RegionApp の実引数の代入には使えない。
;; 2 つを 1 つの関数へ寄せないのは、置換の値域が違うためである。
;; 内側の RegionLam と ForallRegion が同じ名前を束縛していれば、その名前を表から
;; 外して降りる。外さないと内側の束縛が外側の代入で捕獲される。
;;
;; 前提。この関数は捕獲を避けない。shadow が表から外すのは鍵の側の名前だけで
;; あり、表の値の中に現れる自由な rp は守らない。値の中の rp と同じ名前を束縛
;; する RegionLam または ForallRegion が term の内側にあれば、その値はその束縛
;; へ捕獲される。呼ぶ側は、次のどちらかを満たしてから呼ぶ。
;; (1) 表の値に自由な (RParam rp) が現れない。
;; (2) 値に現れる rp と同じ名前を束縛する binder が term の内側に無い。
;; unwrap-forall-region は値の側が (RParam name) なので (1) を満たさない。
;; (2) を保つのは valid-callables? の入れ子の禁止である。RegionApp の実引数の
;; 代入も同じ前提を要る（Task 4b）。
(define (subst-region-params term substitution)
  (let walk ([t term] [sub substitution])
    (define (shadow binders)
      (for/fold ([narrowed sub]) ([binder (in-list binders)])
        (hash-remove narrowed binder)))
    (match t
      [`(RParam ,rp)
       (if (hash-has-key? sub rp) (hash-ref sub rp) t)]
      [(app region-lam-parts (list s rps body))
       (rebuild-region-lam s rps (walk body (shadow rps)))]
      [`(ForallRegion (,rps ...) ,body)
       `(ForallRegion ,rps ,(walk body (shadow rps)))]
      [(? list?)
       (for/list ([element (in-list t)]) (walk element sub))]
      [_ t])))

;; term に現れるすべての RegionLam の束縛名を一意な名前へ付け替える。
;; 外側から内側へ降りる。alpha-rename-region-lam の付け替えは本体の全体へ
;; 届くため、その後で内側を見れば、内側の本体に残る外側の名前も付け替え後の
;; 名前になっている。付け替えを終えた項では、すべての束縛名が一意であり、
;; 同じ名前による遮蔽は残らない。
(define (alpha-rename-all-region-lams term)
  (let walk ([t term])
    (match t
      [(app region-lam-parts (list _ _ _))
       (match-define (list s renamed renamed-body)
         (region-lam-parts (alpha-rename-region-lam t)))
       (rebuild-region-lam s renamed (walk renamed-body))]
      [(? list?)
       (for/list ([element (in-list t)]) (walk element))]
      [_ t])))

;; 項に現れる記号の集合。束縛名の衝突を避けるために使う。
(define (term-symbols term)
  (let walk ([t term])
    (cond
      [(symbol? t) (set t)]
      [(list? t)
       (for/fold ([used (set)]) ([element (in-list t)])
         (set-union used (walk element)))]
      [else (set)])))

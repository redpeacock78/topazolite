#lang racket/base

(require racket/match
         racket/set
         racket/format)

(provide region-free-params
         region-param-counter
         bound-region-params
         call-with-region-params
         fresh-region-param
         fresh-region-param/avoiding
         region-lam-parts
         rebuild-region-lam
         alpha-rename-region-lam
         rename-region-params
         term-symbols)

;; 型木を下って自由な rp の集合を返す。Core を受けた場合も RegionLam の
;; 束縛を除く。RegionApp の実引数は静的な region 出現として列を下る。
(define (region-free-params type)
  (let walk ([t type])
    (match t
      [`(RParam ,rp) (set rp)]
      [`(ForallRegion (,rps ...) ,body)
       (set-subtract (walk body) (list->set rps))]
      [`(RegionLam (,rps ...) ,body)
       (set-subtract (walk body) (list->set rps))]
      [`(RegionLam ,_ (,rps ...) ,body)
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

;; 項に現れる記号の集合。束縛名の衝突を避けるために使う。
(define (term-symbols term)
  (let walk ([t term])
    (cond
      [(symbol? t) (set t)]
      [(list? t)
       (for/fold ([used (set)]) ([element (in-list t)])
         (set-union used (walk element)))]
      [else (set)])))

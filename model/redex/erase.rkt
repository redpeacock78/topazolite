#lang racket

(provide erase-core erase-core/region-annotations erase-surface erase-origin-core
         metadata-form? check-spanless! check-spanless/deep!)

;; span 機構の包みかどうかを head だけで判定する。
;; 型・表・semantic origin は spanless であり、head に keyword を取る形を持たない。
(define (metadata-form? t)
  (and (pair? t) (keyword? (car t))))

;; spanless を要求する位置へ包みが渡ったことを、その場で落とす。
;; 黙って通すと、包みが型として比較され、型同一性や正規形の判定が偽の成立をする。
(define (check-spanless! who t)
  (when (metadata-form? t)
    (error who "spanless な位置へ span 機構の包みが渡った: ~s" t)))

;; span.md §7.3: 命題を受け取る入口は、内側の包みも拒否する。
;; head だけを見ると (Implements (#:ty Int s) Printable) が通り、命題の
;; 一致が包みごと比較されて偽に成立する。
(define (check-spanless/deep! who t)
  (check-spanless! who t)
  (when (list? t)
    (for-each (lambda (u) (check-spanless/deep! who u)) t)))

;; 列の要素として現れた span を判定する。
(define (span-element? t)
  (and (list? t)
       (= 4 (length t))
       (eq? (car t) '#:span)))

;; span 機構の 7 つの包みを開き、構成子の直後にある span を落とす。
;; production ごとの節を書かない。span 機構の head は 8 つに固定されており、
;; 構造の再帰 1 本で UCore+ と G1+ と G2+ の全 production を覆える。
;; spanless な入力に対しては恒等写像になる。
;;
;; 再帰は閉世界である。head が keyword の list は、上の 8 節のいずれかに
;; 一致しなければ誤りとして落とす。head を将来足したときに、span が出力へ残る、
;; あるいは意図せず落ちる境界を、黙って通さずここで検出する。
(define (erase-term t preserve-region-annotations?)
  (match t
    [`(EliminateAt ,scrutinee (,branches ...))
     (define branches*
       (for/list ([branch (in-list branches)])
         (match (erase-term branch preserve-region-annotations?)
           [`(,tag (,binders ...) (,regions ...) -> ,body)
            (if preserve-region-annotations?
                `(,tag ,binders ,regions -> ,body)
                `(,tag ,binders -> ,body))]
           [other
            (error 'erase-term "注釈付き Eliminate の枝が不正: ~s" other)])))
     (if preserve-region-annotations?
         `(EliminateAt ,(erase-term scrutinee preserve-region-annotations?)
                       ,branches*)
         `(Eliminate ,(erase-term scrutinee preserve-region-annotations?)
                     ,branches*))]
    [`(UnionEliminateAt ,scrutinee (,branches ...))
     (define branches*
       (for/list ([branch (in-list branches)])
         (match (erase-term branch preserve-region-annotations?)
           [`(,type ,binder ,region -> ,body)
            (if preserve-region-annotations?
                `(,type ,binder ,region -> ,body)
                `(,type ,binder -> ,body))]
           [other
            (error 'erase-term "注釈付き UnionEliminate の枝が不正: ~s"
                   other)])))
     (if preserve-region-annotations?
         `(UnionEliminateAt ,(erase-term scrutinee preserve-region-annotations?)
                            ,branches*)
         `(UnionEliminate ,(erase-term scrutinee preserve-region-annotations?)
                          ,branches*))]
    [(list '#:var x _) x]
    [(list '#:lit l _) l]
    [(list '#:bind x _) x]
    [(list '#:lbl label _) label]
    [(list '#:ty type _) (erase-term type preserve-region-annotations?)]
    [(list '#:ef row _) (erase-term row preserve-region-annotations?)]
    ;; SUR-008。省略した戻り型は span を落とし、裸の標識として残す。
    [(list '#:infer _) '#:infer]
    [(list '#:span _ _ _)
     (error 'erase-term "span が項の位置に現れた: ~a" t)]
    [(? pair?)
     #:when (keyword? (car t))
     (error 'erase-term "span 機構が知らない keyword head である: ~a" t)]
    [(? list?) (map (lambda (u) (erase-term u preserve-region-annotations?))
                    (filter (λ (u) (not (span-element? u))) t))]
    [_ t]))

(define (erase-core t) (erase-term t #f))
(define (erase-core/region-annotations t) (erase-term t #t))
(define (erase-surface t) (erase-term t #f))

;; Curry の origin payload は erased core の比較キーである。
;; uniquify-binders と substitute が付ける ⟨N⟩ / «N» は実装上の識別子なので
;; 構造を保ったまま剥がすが、元の束縛名そのものは保持する。型同値の O は
;; source-level の provenance を正確に比較し、実装上の添字だけに依存しない。
(define (erase-origin-core t)
  (define generated-id-rx (pregexp "(⟨[0-9]+⟩|«[0-9]+»)+$"))
  (define (normalize-symbol value)
    (if (symbol? value)
        (string->symbol
         (regexp-replace generated-id-rx (symbol->string value) ""))
        value))
  (define (normalize value)
    (cond
      [(symbol? value) (normalize-symbol value)]
      [(list? value) (map normalize value)]
      [else value]))
  (normalize (erase-core t)))

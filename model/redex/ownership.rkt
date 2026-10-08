#lang racket/base

;; OWN-004。構造型 narrowing が余剰 Owned field を失う場合の拒否。
;; 引き金は余剰欄が在ることではなく、余剰の affine 資源を失うことである。
;; compat? が成功した後にだけ呼ぶ。構造の一致は呼び出し側が保証しており、
;; 形の合わない節は検査対象なしとして 'ok を返す。
;; 正典の narrative 名は OwnershipPolicyNarrative.narrow である。
;; owned-narrowing-kind は正典 §4.5.2 の narrow の実装である。narrow は
;; 借用 view と明示 projection と残余 drop の Proof と拒否の 4 つを返しうる。
;; この関数はそのうち 3 つを担う。'ok は narrowing がそのまま通る場合、
;; (drop-obligation τ_actual τ_expected) は RemainderSafelyDropped の Proof を
;; 求める場合、'reject は救済できない場合である。借用 view は SUR-004 で扱う。
;; compat.rkt へは依存しない。互換性述語は呼び出し側から受け取る。
;; 呼び出し側の値互換性述語は Union の候補選択にも使われ、判定の食い違いが起きない。

(require racket/list
         racket/match
         redex/reduction-semantics
         "lang.rkt"
         "policy.rkt"
         "rows.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide owned-narrowing-kind owned-narrowing-kind/for-elaboration
         check-narrowing-return
         remainder-removal-shape remainder-target-type)

(define (union-type? type)
  (and (pair? type) (eq? (car type) 'Union)))

(define (kind-max a b)
  (cond
    [(or (eq? a 'reject) (eq? b 'reject)) 'reject]
    [(eq? a 'ok) b]
    [(eq? b 'ok) a]
    [else 'reject]))

(define (drop-obligation? kind)
  (match kind [`(drop-obligation ,_ ,_) #t] [_ #f]))

(define (kind-max/nested a b)
  (cond
    [(or (eq? a 'reject) (eq? b 'reject)) 'reject]
    [(eq? a 'ok) b]
    [(eq? b 'ok) a]
    [(and (eq? a 'nested-drop) (eq? b 'nested-drop)) 'nested-drop]
    [(and (drop-obligation? a) (eq? b 'nested-drop)) a]
    [(and (eq? a 'nested-drop) (drop-obligation? b)) b]
    [else 'reject]))

(define (kind-all/nested kinds)
  (for/fold ([acc 'ok]) ([kind (in-list kinds)])
    (kind-max/nested acc kind)))

(define (kind-all kinds)
  (for/fold ([acc 'ok]) ([k (in-list kinds)]) (kind-max acc k)))

;; Core の判定を変えず、elaboration が Union の成分ごとの判定へ委ねる。
(define elaboration-union-mode (make-parameter #f))

;; compat?/impl と同型の再帰。Union の分岐位置も compat?/impl に合わせる。
(define (owned-narrowing-kind/impl actual expected compatible? [ctx 'top])
  (cond
    ;; Heap root の Owned へ Union 値を持ち上げる比較は tag を狭めない。
    ;; compatible? が持ち上げを認めた組だけ OWN-004 の追加検査を通す。
    [(and (union-type? actual)
          (match expected [`(Owned ,_) #t] [_ #f])
          (compatible? actual expected))
     'ok]
    [(and (elaboration-union-mode)
          (memq ctx '(top chain))
          (not (union-type? actual))
          (union-type? expected))
     (if (for/or ([expected-member (in-list (union-members expected))])
           (and (compatible? actual expected-member)
                (let ([kind
                       (owned-narrowing-kind/impl actual expected-member
                                                  compatible? 'top)])
                  (or (eq? kind 'ok)
                      (eq? kind 'nested-drop)
                      (drop-obligation? kind)))))
         'ok
         'reject)]
    [(or (union-type? actual) (union-type? expected))
     (if (for/and ([actual-member (in-list (union-members actual))])
           (for/or ([expected-member (in-list (union-members expected))])
             (and (compatible? actual-member expected-member)
                  (eq? (owned-narrowing-kind/impl actual-member expected-member
                                                  compatible? 'inner)
                       'ok))))
         'ok
         'reject)]
    [else (narrowing-kind/non-union actual expected compatible? ctx)]))

(define (narrowing-kind/non-union actual expected compatible? ctx)
  (match* (actual expected)
    [(`(Record ,actual-row) `(Record ,expected-row))
     (kind-max/nested
      (residual-kind actual-row expected-row actual expected ctx)
      (common-imm-fields-kind actual-row expected-row compatible? ctx))]
    [(`(Owned ,actual-payload) `(Owned ,expected-payload))
     (owned-narrowing-kind/impl actual-payload expected-payload
                                compatible? 'inner)]
    [(`(Untrusted ,actual-payload) `(Untrusted ,expected-payload))
     (owned-narrowing-kind/impl actual-payload expected-payload
                                compatible? 'inner)]
    [(`(Refined ,actual-payload ,_) `(Refined ,expected-payload ,_))
     (owned-narrowing-kind/impl actual-payload expected-payload
                                compatible? 'inner)]
    [(`(NFn ,actual-parameters ,actual-return ,_ ,_ ,_ ,_)
      `(NFn ,expected-parameters ,expected-return ,_ ,_ ,_ ,_))
     (if (= (length actual-parameters) (length expected-parameters))
         (kind-all
          (cons (owned-narrowing-kind/impl actual-return expected-return
                                           compatible? 'inner)
                ;; 引数は反変。expected の引数型が actual の引数型へ narrowing
                (for/list ([actual-parameter (in-list actual-parameters)]
                           [expected-parameter (in-list expected-parameters)])
                  (owned-narrowing-kind/impl expected-parameter actual-parameter
                                             compatible? 'inner))))
         'reject)]
    ;; 借用した view は正典が挙げる救済策そのものであり、所有者は動かない。
    [(`(Borrowed ,_ ,_) `(Borrowed ,_ ,_)) 'ok]
    ;; BorrowedMut と Owned と List などは compat? が type-equiv? を要求するため
    ;; narrowing が起きない。既定節は検査対象なしとして通す。
    [(_ _) 'ok]))

;; 残余に Owned があるとき、最上位なら義務を返す。
;; imm Record の共通欄の鎖では内部印を返し、最上位で呼び出し全体の対へ戻す。
(define (residual-kind actual-row expected-row actual expected ctx)
  (cond
    [(for/and ([field (in-list (field-row-residual actual-row expected-row))])
       (owned-free? (second field)))
     'ok]
    [(eq? ctx 'top) `(drop-obligation ,actual ,expected)]
    [(eq? ctx 'chain) 'nested-drop]
    [else 'reject]))

;; compat? が共変に再帰する欄と同じ組を辿る。mut 欄は type-equiv? で閉じる。
(define (common-imm-fields-kind actual-row expected-row compatible? ctx)
  (define child-ctx (if (memq ctx '(top chain)) 'chain 'inner))
  (kind-all/nested
   (for/list ([field (in-list expected-row)])
     (match field
       [(list label expected-type 'imm _ ...)
        (match (field-row-lookup actual-row label)
          [(list actual-type _)
           (owned-narrowing-kind/impl actual-type expected-type
                                      compatible? child-ctx)]
          [_ 'ok])]
       [_ 'ok]))))

;; RemainderSafelyDropped が実行時に除去する欄を型対から得る。
;; `drop` はこの欄を値ごと取り除き、`nested` は共通する imm Record 欄へ潜る。
;; `#f` は対応する型構造でない場合、空リストは除去欄が無い場合である。
(define (remainder-removal-shape actual expected)
  (define (shape-for-type actual-type expected-type)
    (cond
      [(type-equiv? actual-type expected-type) '()]
      [else
       (match* (actual-type expected-type)
         [(`(Record ,actual-row) `(Record ,expected-row))
          (and (field-row-unique? actual-row)
               (field-row-unique? expected-row)
               (let ([removed
                      (for/list ([field
                                  (in-list
                                   (field-row-residual actual-row expected-row))]
                                 #:unless (owned-free? (second field)))
                        (list (first field) 'drop (field-optional? field)))])
                 (let loop ([remaining expected-row] [nested '()])
                   (cond
                     [(null? remaining) (append removed (reverse nested))]
                     [else
                      (define expected-field (car remaining))
                      (define actual-field
                        (assoc (first expected-field) actual-row))
                      (define recurse?
                        (and actual-field
                             (eq? (third actual-field) 'imm)
                             (eq? (third expected-field) 'imm)
                             ;; actual の必須欄は expected の optional 欄として扱える。
                             ;; 値は存在するため、その値の入れ子へ安全に降りられる。
                             (or (not (field-optional? actual-field))
                                 (field-optional? expected-field))
                             (match* ((second actual-field)
                                      (second expected-field))
                               [(`(Record ,_) `(Record ,_)) #t]
                               [(_ _) #f])))
                      (if recurse?
                          (let ([child-shape
                                 (shape-for-type (second actual-field)
                                                 (second expected-field))])
                            (and child-shape
                                 (loop
                                  (cdr remaining)
                                  (if (null? child-shape)
                                      nested
                                      (cons (list (first expected-field)
                                                  'nested
                                                  (field-optional? actual-field)
                                                  child-shape)
                                            nested)))))
                          (loop (cdr remaining) nested))]))))]
         [(_ _) #f])]))
  (shape-for-type actual expected))

;; remainder-removal-shape が示す Owned 欄を actual から除いた型を返す。
;; nested はその欄の型へ再帰的に適用し、残す欄の順序と印は actual のまま保つ。
(define (remainder-target-type actual expected)
  (define shape (remainder-removal-shape actual expected))
  (define (apply-shape type shape)
    (if (null? shape)
        type
        (match type
          [`(Record ,row)
           (let loop ([fields row] [result '()])
             (cond
               [(null? fields) `(Record ,(reverse result))]
               [else
                (define field (car fields))
                (define entry (assoc (first field) shape))
                (match entry
                  [(list _ 'drop _)
                   (loop (cdr fields) result)]
                  [(list _ 'nested _ child-shape)
                   (define child-type
                     (apply-shape (second field) child-shape))
                   (and child-type
                        (loop (cdr fields)
                              (cons (list* (first field) child-type
                                           (cddr field))
                                    result)))]
                  [_ (loop (cdr fields) (cons field result))])]))]
          [_ #f])))
  (and shape (apply-shape actual shape)))

(define (type-value? v)
  (redex-match? G2m τ v))

(define (check-narrowing-return args returns)
  (match* (args returns)
    [((list actual expected _) (list result))
     (match result
       ['ok #t]
       ['reject #t]
       [`(drop-obligation ,residual-actual ,residual-expected)
        (and (type-value? residual-actual)
             (type-value? residual-expected)
             (equal? residual-actual actual)
             (equal? residual-expected expected))]
       [_ #f])]
    [(_ _) #f]))

(define (owned-narrowing-kind/adapter actual expected compatible?)
  (define kind (owned-narrowing-kind/impl actual expected compatible? 'top))
  (if (eq? kind 'nested-drop)
      `(drop-obligation ,actual ,expected)
      kind))

(define owned-narrowing-kind
  (policy-wrap 'OwnershipPolicy 'owned-narrowing-kind
               owned-narrowing-kind/adapter
               check-narrowing-return))

(define (owned-narrowing-kind/for-elaboration actual expected compatible?)
  (parameterize ([elaboration-union-mode #t])
    (owned-narrowing-kind actual expected compatible?)))

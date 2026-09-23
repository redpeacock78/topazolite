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
;; 呼び出し側が merge-branch-compatible? を使った位置では Union の候補選択も
;; 同じ述語で行われ、判定の食い違いが起きない。

(require racket/list
         racket/match
         redex/reduction-semantics
         "lang.rkt"
         "policy.rkt"
         "rows.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide owned-narrowing-kind check-narrowing-return)

(define (union-type? type)
  (and (pair? type) (eq? (car type) 'Union)))

(define (kind-max a b)
  (cond
    [(or (eq? a 'reject) (eq? b 'reject)) 'reject]
    [(eq? a 'ok) b]
    [(eq? b 'ok) a]
    [else 'reject]))

(define (kind-all kinds)
  (for/fold ([acc 'ok]) ([k (in-list kinds)]) (kind-max acc k)))

;; compat?/impl と同型の再帰。Union の分岐位置も compat?/impl に合わせる。
(define (owned-narrowing-kind/impl actual expected compatible? [top? #t])
  (cond
    [(or (union-type? actual) (union-type? expected))
     (if (for/and ([actual-member (in-list (union-members actual))])
           (for/or ([expected-member (in-list (union-members expected))])
             (and (compatible? actual-member expected-member)
                  (eq? (owned-narrowing-kind/impl actual-member expected-member
                                                  compatible? #f)
                       'ok))))
         'ok
         'reject)]
    [else (narrowing-kind/non-union actual expected compatible? top?)]))

(define (narrowing-kind/non-union actual expected compatible? top?)
  (match* (actual expected)
    [(`(Record ,actual-row) `(Record ,expected-row))
     (kind-max (residual-kind actual-row expected-row actual expected top?)
               (common-imm-fields-kind actual-row expected-row compatible?))]
    [(`(Untrusted ,actual-payload) `(Untrusted ,expected-payload))
     (owned-narrowing-kind/impl actual-payload expected-payload compatible? #f)]
    [(`(Refined ,actual-payload ,_) `(Refined ,expected-payload ,_))
     (owned-narrowing-kind/impl actual-payload expected-payload compatible? #f)]
    [(`(NFn ,actual-parameters ,actual-return ,_ ,_ ,_ ,_)
      `(NFn ,expected-parameters ,expected-return ,_ ,_ ,_ ,_))
     (if (= (length actual-parameters) (length expected-parameters))
         (kind-all
          (cons (owned-narrowing-kind/impl actual-return expected-return
                                           compatible? #f)
                ;; 引数は反変。expected の引数型が actual の引数型へ narrowing
                (for/list ([actual-parameter (in-list actual-parameters)]
                           [expected-parameter (in-list expected-parameters)])
                  (owned-narrowing-kind/impl expected-parameter actual-parameter
                                             compatible? #f))))
         'reject)]
    ;; 借用した view は正典が挙げる救済策そのものであり、所有者は動かない。
    [(`(Borrowed ,_ ,_) `(Borrowed ,_ ,_)) 'ok]
    ;; BorrowedMut と Owned と List などは compat? が type-equiv? を要求するため
    ;; narrowing が起きない。既定節は検査対象なしとして通す。
    [(_ _) 'ok]))

;; 残余に Owned があるとき、最上位なら義務を、内側なら拒否を返す。
;; 内側で拒否するのは、Proof が型の対で鍵付くためである。内側の対を
;; 外へ出すと、包んだ項の型と鍵が合わない。
(define (residual-kind actual-row expected-row actual expected top?)
  (cond
    [(for/and ([field (in-list (field-row-residual actual-row expected-row))])
       (owned-free? (second field)))
     'ok]
    [top? `(drop-obligation ,actual ,expected)]
    [else 'reject]))

;; compat? が共変に再帰する欄と同じ組を辿る。mut 欄は type-equiv? で閉じる。
(define (common-imm-fields-kind actual-row expected-row compatible?)
  (kind-all
   (for/list ([field (in-list expected-row)])
     (match field
       [(list label expected-type 'imm)
        (match (field-row-lookup actual-row label)
          [(list actual-type _)
           (owned-narrowing-kind/impl actual-type expected-type compatible? #f)]
          [_ 'ok])]
       [_ 'ok]))))

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

(define owned-narrowing-kind
  (policy-wrap 'OwnershipPolicy 'owned-narrowing-kind
               owned-narrowing-kind/impl
               check-narrowing-return))

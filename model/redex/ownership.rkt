#lang racket/base

;; OWN-004。構造型 narrowing が余剰 Owned field を失うことを拒否する。
;; 引き金は余剰欄が在ることではなく、余剰の affine 資源を失うことである。
;; compat? が成功した後にだけ呼ぶ。構造の一致は呼び出し側が保証しており、
;; 形の合わない節は検査対象なしとして #t を返す。
;; 正典の narrative 名は OwnershipPolicyNarrative.narrow である。
;; owned-narrowing-ok? は boolean を返す narrow の reject-only 実装であり、
;; 救済策を実装するときに返却形を広げる境界がここになる。
;; compat.rkt へは依存しない。互換性述語は呼び出し側から受け取る。
;; 呼び出し側が merge-branch-compatible? を使った位置では Union の候補選択も
;; 同じ述語で行われ、判定の食い違いが起きない。

(require racket/list
         racket/match
         "policy.rkt"
         "rows.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide owned-narrowing-ok?)

(define (union-type? type)
  (and (pair? type) (eq? (car type) 'Union)))

;; compat?/impl と同型の再帰。Union の分岐位置も compat?/impl に合わせる。
(define (owned-narrowing-ok?/impl actual expected compatible?)
  (cond
    [(or (union-type? actual) (union-type? expected))
     (for/and ([actual-member (in-list (union-members actual))])
       (for/or ([expected-member (in-list (union-members expected))])
         (and (compatible? actual-member expected-member)
              (owned-narrowing-ok?/impl actual-member expected-member
                                        compatible?))))]
    [else (narrowing-ok?/non-union actual expected compatible?)]))

(define (narrowing-ok?/non-union actual expected compatible?)
  (match* (actual expected)
    [(`(Record ,actual-row) `(Record ,expected-row))
     (and (residual-owned-free? actual-row expected-row)
          (common-imm-fields-ok? actual-row expected-row compatible?))]
    [(`(Untrusted ,actual-payload) `(Untrusted ,expected-payload))
     (owned-narrowing-ok?/impl actual-payload expected-payload compatible?)]
    [(`(Refined ,actual-payload ,_) `(Refined ,expected-payload ,_))
     (owned-narrowing-ok?/impl actual-payload expected-payload compatible?)]
    [(`(NFn ,actual-parameters ,actual-return ,_ ,_)
      `(NFn ,expected-parameters ,expected-return ,_ ,_))
     (and (= (length actual-parameters) (length expected-parameters))
          (owned-narrowing-ok?/impl actual-return expected-return compatible?)
          ;; 引数は反変。expected の引数型が actual の引数型へ narrowing される。
          (for/and ([actual-parameter (in-list actual-parameters)]
                    [expected-parameter (in-list expected-parameters)])
            (owned-narrowing-ok?/impl expected-parameter actual-parameter
                                      compatible?)))]
    ;; 借用した view は正典が挙げる救済策そのものであり、所有者は値を保つ。
    [(`(Borrowed ,_ ,_) `(Borrowed ,_ ,_)) #t]
    ;; BorrowedMut と Owned と List などは compat? が type-equiv? を要求するため
    ;; narrowing が起きない。既定節は検査対象なしとして通す。
    [(_ _) #t]))

;; expected に無い欄が余剰である。その欄が Owned を含むなら拒否する。
(define (residual-owned-free? actual-row expected-row)
  (for/and ([field (in-list (field-row-residual actual-row expected-row))])
    (owned-free? (second field))))

;; compat? が共変に再帰する欄と同じ組を辿る。mut 欄は type-equiv? で閉じる。
(define (common-imm-fields-ok? actual-row expected-row compatible?)
  (for/and ([field (in-list expected-row)])
    (match field
      [(list label expected-type 'imm)
       (match (field-row-lookup actual-row label)
         [(list actual-type _)
          (owned-narrowing-ok?/impl actual-type expected-type compatible?)]
         [_ #t])]
      [_ #t])))

;; 返却値の検査。narrowing の安全性は同値性から導けないため、boolean である
;; ことだけを要求する。compat? の check-compat-return のような追加条件は置かない。
(define (check-narrowing-return args returns)
  (match* (args returns)
    [((list _ _ _) (list result)) (boolean? result)]
    [(_ _) #f]))

(define owned-narrowing-ok?
  (policy-wrap 'OwnershipPolicy 'owned-narrowing-ok?
               owned-narrowing-ok?/impl
               check-narrowing-return))

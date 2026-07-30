#lang racket

(require racket/match
         "rows.rkt")

(provide effect-equiv?
         row-equiv?
         type-equiv?
         normalize-type
         normalize-proposition
         canonical-proposition-key
         union-members
         type-normal?)

;; 型の外部表現に対する決定的な全順序。
(define (external-key value)
  (format "~s" value))

(define (external<? left right)
  (string<? (external-key left) (external-key right)))

;; Union を左右に潜って要素列へ平坦化する。
(define (union-members type)
  (match type
    [`(Union ,left ,right)
     (append (union-members left) (union-members right))]
    [_ (list type)]))

;; 要素列を右結合の Union へ戻す。1 要素ならそのまま返す。
(define (build-union types)
  (cond
    [(null? types) #f]
    [(null? (cdr types)) (car types)]
    [else `(Union ,(car types) ,(build-union (cdr types)))]))

;; 外部表現で整列してから、保持済みの全要素と type-equiv? で比較して畳む。
(define (sort-then-dedup types)
  (for/fold ([kept '()] #:result (reverse kept))
            ([type (in-list (sort types external<?))])
    (if (for/or ([other (in-list kept)])
          (type-equiv? other type))
        kept
        (cons type kept))))

;; Record の行を label 昇順へ整列する。label は一意である前提。
(define (sort-row row)
  (sort row symbol<? #:key car))

;; 行の各 field 型を正規化する。1 つでも失敗したら #f。
(define (normalize-row row)
  (define normalized
    (for/list ([field (in-list row)])
      (define type (normalize-type (cadr field)))
      (and type (list (car field) type (caddr field)))))
  (and (andmap values normalized) normalized))

;; 作用列を整列して重複を除く。Return/Yield は内包型も正規化する。
(define (normalize-effect-row row)
  (define normalized
    (for/list ([label (in-list row)])
      (match label
        [`(Return ,boundary ,type)
         (define result (normalize-type type))
         (and result `(Return ,boundary ,result))]
        [`(Yield ,type)
         (define result (normalize-type type))
         (and result `(Yield ,result))]
        [_ label])))
  (and (andmap values normalized)
       (remove-duplicates (sort normalized external<?))))

;; 義務列を外部表現順で整列して重複を除く。
(define (sort-obligations obligations)
  (remove-duplicates (sort obligations external<?)))

;; 型を正規形へ写す。正規化できない型には #f を返す。
(define (normalize-type type)
  (match type
    [`(Union ,_ ,_)
     (define members
       (for/list ([member (in-list (union-members type))])
         (normalize-type member)))
     (and (andmap values members)
          (build-union
           (sort-then-dedup (append-map union-members members))))]
    [`(Intersection ,left ,right)
     (define normalized-left (normalize-type left))
     (define normalized-right (normalize-type right))
     (and normalized-left
          normalized-right
          (match* (normalized-left normalized-right)
            [(`(Record ,left-row) `(Record ,right-row))
             (define row (field-row-⊕ left-row right-row))
             (and row `(Record ,(sort-row row)))]
            [(_ _) #f]))]
    [`(Record ,row)
     (define normalized (normalize-row row))
     (and normalized `(Record ,(sort-row normalized)))]
    [`(List ,element)
     (define normalized (normalize-type element))
     (and normalized `(List ,normalized))]
    [`(Option ,element)
     (define normalized (normalize-type element))
     (and normalized `(Option ,normalized))]
    [`(Owned ,inner)
     (define normalized (normalize-type inner))
     (and normalized `(Owned ,normalized))]
    [`(Untrusted ,payload)
     (define normalized (normalize-type payload))
     (and normalized `(Untrusted ,normalized))]
    [`(Result ,ok-type ,error-type)
     (define normalized-ok (normalize-type ok-type))
     (define normalized-error (normalize-type error-type))
     (and normalized-ok
          normalized-error
          `(Result ,normalized-ok ,normalized-error))]
    [`(NFn ,parameters ,return-type ,row ,obligations)
     (define normalized-parameters
       (for/list ([parameter (in-list parameters)])
         (normalize-type parameter)))
     (define normalized-return (normalize-type return-type))
     (define normalized-row (normalize-effect-row row))
     (define normalized-obligations
       (for/list ([proposition (in-list obligations)])
         (normalize-proposition proposition)))
     (and (andmap values normalized-parameters)
          normalized-return
          normalized-row
          (andmap values normalized-obligations)
          `(NFn ,normalized-parameters
                ,normalized-return
                ,normalized-row
                ,(sort-obligations normalized-obligations)))]
    [`(Proof ,proposition)
     (define normalized (normalize-proposition proposition))
     (and normalized `(Proof ,normalized))]
    [`(Refined ,payload ,proposition)
     (define normalized-payload (normalize-type payload))
     (define normalized-proposition (normalize-proposition proposition))
     (and normalized-payload
          normalized-proposition
          `(Refined ,normalized-payload ,normalized-proposition))]
    [_ type]))

;; 命題に埋め込まれた型を正規化する。
(define (normalize-proposition proposition)
  (match proposition
    [`(Implements ,type ,trait)
     (define normalized (normalize-type type))
     (and normalized `(Implements ,normalized ,trait))]
    [`(FieldType ,label ,type)
     (define normalized (normalize-type type))
     (and normalized `(FieldType ,label ,normalized))]
    [`(RequiresBoth ,left ,right)
     (if (symbol<? left right)
         `(RequiresBoth ,left ,right)
         `(RequiresBoth ,right ,left))]
    [_ proposition]))

;; 正規化を通した型について type-equiv? と一致する内部専用の鍵。
(define (canonical-type-key type)
  (define normalized (normalize-type type))
  (and normalized (canonical-key/normal normalized)))

(define (canonical-key/normal type)
  (match type
    [`(Record ,row)
     `(Record
       ,(sort
         (for/list ([field (in-list row)])
           (list (car field)
                 (canonical-key/normal (cadr field))
                 (caddr field)))
         symbol<?
         #:key car))]
    [`(Union ,_ ,_)
     `(Union
       ,(sort
         (for/list ([member (in-list (union-members type))])
           (canonical-key/normal member))
         external<?))]
    [`(List ,element) `(List ,(canonical-key/normal element))]
    [`(Option ,element) `(Option ,(canonical-key/normal element))]
    [`(Owned ,inner) `(Owned ,(canonical-key/normal inner))]
    [`(Untrusted ,payload) `(Untrusted ,(canonical-key/normal payload))]
    [`(Result ,ok-type ,error-type)
     `(Result ,(canonical-key/normal ok-type)
              ,(canonical-key/normal error-type))]
    [`(NFn ,parameters ,return-type ,row ,obligations)
     `(NFn ,(map canonical-key/normal parameters)
           ,(canonical-key/normal return-type)
           ,(canonical-effect-row-key row)
           ,(sort (map canonical-proposition-key obligations) external<?))]
    [`(Proof ,proposition)
     `(Proof ,(canonical-proposition-key proposition))]
    [`(Refined ,payload ,proposition)
     `(Refined ,(canonical-key/normal payload)
               ,(canonical-proposition-key proposition))]
    [_ type]))

;; 作用列は type-equiv? が集合として比べるので、整列と重複除去を行う。
(define (canonical-effect-row-key row)
  (sort
   (remove-duplicates
    (for/list ([label (in-list row)])
      (match label
        [`(Return ,boundary ,type)
         `(Return ,boundary ,(canonical-key/normal type))]
        [`(Yield ,type)
         `(Yield ,(canonical-key/normal type))]
        [_ label])))
   external<?))

;; 命題の正準鍵。探索の候補識別、issuer 検査、義務の包含判定で共有する。
(define (canonical-proposition-key proposition)
  (define normalized (normalize-proposition proposition))
  (and normalized
       (match normalized
         [`(Implements ,type ,trait)
          `(Implements ,(canonical-type-key type) ,trait)]
         [`(FieldType ,label ,type)
          `(FieldType ,label ,(canonical-type-key type))]
         [_ normalized])))

;; 型が正規形であるか。normalize-type が失敗する型は正規形でない。
(define (type-normal? type)
  (equal? (normalize-type type) type))

(define (effect-equiv? left right)
  (match* (left right)
    [(`(Return ,left-boundary ,left-type)
      `(Return ,right-boundary ,right-type))
     (and (equal? left-boundary right-boundary)
          (type-equiv? left-type right-type))]
    [(`(Yield ,left-type) `(Yield ,right-type))
     (type-equiv? left-type right-type)]
    [(_ _) (equal? left right)]))

(define (row-equiv? left right)
  (and (for/and ([left-label (in-list left)])
         (for/or ([right-label (in-list right)])
           (effect-equiv? left-label right-label)))
       (for/and ([right-label (in-list right)])
         (for/or ([left-label (in-list left)])
           (effect-equiv? left-label right-label)))))

(define (types-equiv? left right)
  (and (= (length left) (length right))
       (for/and ([left-type (in-list left)]
                 [right-type (in-list right)])
         (type-equiv? left-type right-type))))

;; 命題の同値。正準鍵が作れない命題は旧来どおり構文で比べる。
(define (proposition-equiv? left right)
  (define left-key (canonical-proposition-key left))
  (define right-key (canonical-proposition-key right))
  (if (and left-key right-key)
      (equal? left-key right-key)
      (equal? left right)))

(define (propositions-equiv? left right)
  (and (= (length left) (length right))
       (for/and ([left-proposition (in-list left)]
                 [right-proposition (in-list right)])
         (proposition-equiv? left-proposition right-proposition))))

;; Union は要素の集合として比べる。
(define (union-type-equiv? left right)
  (define left-members (union-members left))
  (define right-members (union-members right))
  (and (for/and ([left-member (in-list left-members)])
         (for/or ([right-member (in-list right-members)])
           (type-equiv? left-member right-member)))
       (for/and ([right-member (in-list right-members)])
         (for/or ([left-member (in-list left-members)])
           (type-equiv? left-member right-member)))))

(define (type-equiv? left right)
  (match* (left right)
    [(`(Union ,_ ,_) _) (union-type-equiv? left right)]
    [(_ `(Union ,_ ,_)) (union-type-equiv? left right)]
    [(`(List ,left-element) `(List ,right-element))
     (type-equiv? left-element right-element)]
    [(`(Option ,left-element) `(Option ,right-element))
     (type-equiv? left-element right-element)]
    [(`(Result ,left-ok ,left-error) `(Result ,right-ok ,right-error))
     (and (type-equiv? left-ok right-ok)
          (type-equiv? left-error right-error))]
    [(`(Owned ,left-inner) `(Owned ,right-inner))
     (type-equiv? left-inner right-inner)]
    [(`(Untrusted ,left-payload) `(Untrusted ,right-payload))
     (type-equiv? left-payload right-payload)]
    ;; RFN-001: witness の実体は型同一性に関与しない。φ は正準鍵だけを見る。
    [(`(Refined ,left-payload ,left-proposition)
      `(Refined ,right-payload ,right-proposition))
     (and (type-equiv? left-payload right-payload)
          (proposition-equiv? left-proposition right-proposition))]
    [(`(Record ,left-row) `(Record ,right-row))
     (field-row-equiv? left-row right-row type-equiv?)]
    [(`(NFn ,left-parameters ,left-return ,left-row ,left-obligations)
      `(NFn ,right-parameters ,right-return ,right-row ,right-obligations))
     (and (types-equiv? left-parameters right-parameters)
          (type-equiv? left-return right-return)
          (row-equiv? left-row right-row)
          (propositions-equiv? left-obligations right-obligations))]
    [(`(TypeInfo ,left-kind) `(TypeInfo ,right-kind))
     (equal? left-kind right-kind)]
    [(`(Proof ,left-proposition) `(Proof ,right-proposition))
     (proposition-equiv? left-proposition right-proposition)]
    ;; Future type-level computations remain opaque unless their syntax is
    ;; identical. G1 has no reducible type form beyond constructor specs.
    [(_ _) (equal? left right)]))

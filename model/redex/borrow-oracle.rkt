#lang racket

(require racket/match)

(provide control-diff
         borrow-form-candidates
         borrow-value?)

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

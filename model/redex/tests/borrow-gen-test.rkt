#lang racket

(require rackunit
         racket/match
         racket/set
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../gen.rkt"
         "../region.rkt")

(define limits (read-bounds))

(define (binder-names t)
  (match t
    [`(Let (,x ,_bmode ,_τ) ,bound ,body)
     (cons x (append (binder-names bound) (binder-names body)))]
    [`(,K (,x ...) -> ,c) (append x (binder-names c))]
    [(? list?) (append* (map binder-names t))]
    [_ '()]))

(define (contains-borrow-form? t)
  (match t
    [(or `(Borrow ,_) `(BorrowMut ,_) `(Reborrow ,_)) #t]
    [(or `(BorrowRef ,_ ,_ ,_) `(BorrowMutRef ,_ ,_ ,_)) #t]
    [(? list?) (ormap contains-borrow-form? t)]
    [_ #f]))

(define (yield-payloads t)
  (match t
    [`(Yield ,payload ,rest) (cons payload (yield-payloads rest))]
    [(? list?) (append* (map yield-payloads t))]
    [_ '()]))

(define (small-ints t)
  (cond [(and (exact-integer? t) (< t 1000)) (list t)]
        [(and (list? t) (pair? t)) (append* (map small-ints t))]
        [else '()]))

(test-case "生成器は Scope を根に持つ core を返す"
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range 200)])
       (define t (gen-borrow-term 4))
       (check-equal? (first t) 'Scope)))))

(test-case "束縛名は相異なる"
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range 200)])
       (define names (binder-names (gen-borrow-term 4)))
       (check-equal? (length names) (length (remove-duplicates names)))))))

(test-case "Yield の payload に借用形が現れない"
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range 200)])
       (for ([payload (in-list (yield-payloads (gen-borrow-term 4)))])
         (check-false (contains-borrow-form? payload)))))))

(test-case "整数リテラルは 1000 以上である"
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range 200)])
       ;; place 索引でも region 索引でもない、リテラルの位置だけを見る。
       (check-equal? (small-ints (literal-positions (gen-borrow-term 4)))
                     '())))))

(test-case "placeholder が実際の ρ へ置き換わる"
  (define skeleton
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1000)
         (Scope ()
           (Let (y let (Borrowed Res ph)) (Borrow x) 1000)))))
  (define ir (build-region-ir skeleton))
  (define filled (fill-region-placeholders skeleton ir))
  (check-equal? filled
                (list 'Scope '()
                      (list 'Let (list 'x 'let '(Owned Res)) '(resource 1000)
                            (list 'Scope '()
                                  (list 'Let (list 'y 'let
                                                   (list 'Borrowed 'Res
                                                         (region->rho
                                                          ir
                                                          (region-at ir
                                                                     '(0 1 0 0)))))
                                        '(Borrow x) 1000)))))
  (check-false (memq 'ph (flatten filled))))

(test-case "prepare-borrow-term は型検査を通る項で ok を返す"
  (define skeleton
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1000)
         (Scope ()
           (Let (y let (Borrowed Res ph)) (Borrow x) 1000)))))
  (match (prepare-borrow-term skeleton)
    [(list 'ok config sidecar ir)
     (check-equal? (first config) 'cfg)
     (check-true (borrow-sidecar? sidecar))]
    [other (fail (format "unexpected: ~e" other))]))

(test-case "型検査に落ちる項は discard になる"
  (check-equal? (prepare-borrow-term '(Scope () (Read 1000))) 'discard))

;; 生成域へ足した 4 形が型検査を通ることを確かめる。prepare-borrow-term は
;; 型検査に落ちた項を黙って捨てるため、この試験が無いと生成器が作った項が
;; 全て捨てられていても Step 6 は PASS してしまう。
(test-case "射影借用と Eliminate の骨組みは型検査を通る"
  (define rec-skeleton
    '(Scope ()
       (Let (c let (Owned (Record ((f0 Int mut) (f1 Int imm)))))
         (Rec ((f0 mut 1000) (f1 imm 1001)))
         (Scope ()
           (Let (q let (Borrowed Int ph))
             (ProjBorrow (Borrow c) f1)
             1000)))))
  (define rec-mut-skeleton
    '(Scope ()
       (Let (c let (Owned (Record ((f0 Int mut) (f1 Int imm)))))
         (Rec ((f0 mut 1000) (f1 imm 1001)))
         (Scope ()
           (Let (qm let (BorrowedMut Int ph))
             (ProjBorrow (BorrowMut c) f0)
             1000)))))
  (define elim-ref-skeleton
    '(Scope ()
       (Let (d let (Owned (Option Int))) (Construct (Option Int) some 1000)
         (Scope ()
           (Eliminate (Borrow d)
                      ((none () -> 1000)
                       (some (e) -> (Read e))))))))
  (define elim-skeleton
    '(Scope ()
       (Let (d let (Owned (Option Int))) (Construct (Option Int) some 1000)
         (Scope ()
           (Eliminate (Move d)
                      ((none () -> 1000)
                       (some (e) -> e)))))))
  (for ([skeleton (in-list (list rec-skeleton rec-mut-skeleton
                                 elim-ref-skeleton elim-skeleton))])
    (check-true (pair? (prepare-borrow-term skeleton))
                (format "discard: ~e" skeleton))))

;; 生成器が実際に 4 形を作ることを確かめる。乱数は種を固定して再現させる。
(test-case "生成器は射影借用と Eliminate を作る"
  (random-seed 20260906)
  (define heads
    (for*/fold ([acc (set)]) ([_ (in-range 400)])
      (let walk ([t (gen-borrow-term 4)] [acc acc])
        (cond
          [(and (pair? t) (symbol? (first t)))
           (for/fold ([acc (set-add acc (first t))])
                     ([k (in-list (rest t))])
             (walk k acc))]
          [(list? t) (for/fold ([acc acc]) ([k (in-list t)]) (walk k acc))]
          [else acc]))))
  (for ([form (in-list '(Rec ProjBorrow Construct Eliminate))])
    (check-true (set-member? heads form) (format "生成されない: ~a" form))))

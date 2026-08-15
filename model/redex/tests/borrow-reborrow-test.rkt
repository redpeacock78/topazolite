#lang racket

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; spec §12 の静的な形と注釈後の形。
(let ()
  (define Λ_0 (empty-region-ctx))
  (define Λ (region-ctx-add-token Λ_0 'y (set 'x)))
  (check-equal? (borrow-token-key Λ_0 '(Reborrow (BorrowMut x))) (set 'x))
  (check-equal? (borrow-token-key Λ
                                  '(Let (y let (BorrowedMut Int 0))
                                        (BorrowMut x)
                                        (Reborrow y)))
                (set 'x))
  (check-equal? (borrow-token-key Λ_0 '(ReborrowAt 1 (BorrowMutAt 0 7)))
                (set 7))
  (check-equal? (borrow-token-key Λ_0 '(ReborrowAt 1 (BorrowMutRef 7 0)))
                (set 7)))

;; 内側の項の型をそのまま運ぶ形も全欄を合併する。
(let ()
  (define Λ_0 (empty-region-ctx))
  (check-equal? (borrow-token-key Λ_0 '(Proj (Rec ((a imm (BorrowMut x)))) a))
                (set 'x))
  (check-equal? (borrow-token-key Λ_0 '(Suspend (BorrowMut x))) (set 'x))
  (check-equal? (borrow-token-key Λ_0 '(Yield 1 (BorrowMut x))) (set 'x))
  (check-equal? (borrow-token-key Λ_0
                                  '(Handle (Return 0 (BorrowedMut Int 0))
                                           (h -> h)
                                           (BorrowMut x)))
                (set 'x 'h)))

(let ()
  (define Λ_0 (empty-region-ctx))
  (check-equal? (borrow-token-key
                 Λ_0
                 '(Proj (Rec ((a imm (BorrowMut x))
                              (b imm (BorrowMut y)))) b))
                (set 'x 'y))
  (check-equal? (borrow-token-key Λ_0
                                  '(Construct (Option Int) some (BorrowMut x)))
                (set 'x))
  (check-equal? (borrow-token-key Λ_0 '(Rec ((a imm (resource 1))))) (set)))

;; 登録のない designator は自己 fallback で親 capability になる。
(let ()
  (define core '(Scope () (Let (x let (Owned Res)) (resource 1) (Borrow x))))
  (define ir (build-region-ir core))
  (define ρ_root (region->rho ir (region-at ir '())))
  (define environment (list (list 'y `(BorrowedMut Int ,ρ_root))))
  (check-equal? (borrow-token-key (Λ-of ir) 'y) (set 'y))
  (check-equal? (first (type-of/raw '(Reborrow y) '() '() environment (Λ-of ir)))
                'ok))

;; Construct の borrowed field を branch binder で受ける形。
(let ()
  (define skeleton
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Scope ()
           (Let (o let (Option (BorrowedMut Res 0)))
                (Construct (Option (BorrowedMut Res 0)) some (BorrowMut x))
             (Eliminate o
               ((none () -> 0)
                (some (y) ->
                  (Let (z let (Borrowed Res 0)) (Reborrow y) 0)))))))))
  (define ir (build-region-ir skeleton))
  (define ρ_inner (region->rho ir (region-at ir '(0 1))))
  (define core
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Scope ()
           (Let (o let (Option (BorrowedMut Res ρ_hole)))
                (Construct (Option (BorrowedMut Res ρ_hole)) some (BorrowMut x))
             (Eliminate o
               ((none () -> 0)
                (some (y) ->
                  (Let (z let (Borrowed Res ρ_hole)) (Reborrow y) 0)))))))))
  (define core-filled
    (let fill ([t core])
      (cond [(eq? t 'ρ_hole) ρ_inner]
            [(pair? t) (cons (fill (car t)) (fill (cdr t)))]
            [else t])))
  (check-equal? (first (type-of/raw core-filled '() '() '() (Λ-of ir))) 'ok))

;; Reborrow の operand 全体が Let になる形。
(let ()
  (define skeleton
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Scope ()
           (Reborrow (Let (y let (BorrowedMut Res 0)) (BorrowMut x) y))))))
  (define ir (build-region-ir skeleton))
  (define ρ_inner (region->rho ir (region-at ir '(0 1))))
  (define core
    (let fill ([t skeleton])
      (cond [(equal? t '(BorrowedMut Res 0)) `(BorrowedMut Res ,ρ_inner)]
            [(pair? t) (cons (fill (car t)) (fill (cdr t)))]
            [else t])))
  (check-equal? (borrow-token-key (Λ-of ir)
                                  '(Let (y let (BorrowedMut Res 0))
                                        (BorrowMut x) y))
                (set 'x))
  (check-equal? (first (type-of/raw core '() '() '() (Λ-of ir))) 'ok))

;; 正常系。子 region の共有借用を返す。
(let ()
  (define core
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Scope () (Reborrow (BorrowMut x))))))
  (define ir (build-region-ir core))
  (define ρ_inner (region->rho ir (region-at ir '(0 1))))
  (check-equal? (type-of/raw core '() '() '() (Λ-of ir))
                (list 'ok (list `(Borrowed Res ,(region->rho ir (region-at ir '(0 1)))) '()))))

;; Let 経由で停止、子退場後の復帰、Drop の拒否を通す。
(let ()
  (define (core-with ρ_num body)
    `(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Scope ()
           (Let (y let (BorrowedMut Res ,ρ_num)) (BorrowMut x)
             ,body)))))
  (define (prepare body)
    (define skeleton (core-with 0 body))
    (define ir (build-region-ir skeleton))
    (define n-parent (region->rho ir (region-at ir '(0 1))))
    (define core (core-with n-parent body))
    (check-equal? (core-points core) (core-points skeleton))
    (values core ir))
  (define-values (core-plain ir-plain) (prepare '(Scope () (Reborrow y))))
  (define n-child (region->rho ir-plain (region-at ir-plain '(0 1 0 1))))
  (check-not-equal? n-child (region->rho ir-plain (region-at ir-plain '(0 1))))
  (check-equal? (first (type-of/raw core-plain '() '() '() (Λ-of ir-plain))) 'ok)
  (define-values (core-inner ir-inner) (prepare '(Scope () (Yield (Reborrow y) (Move x)))))
  (check-equal? (key-of (type-of/raw core-inner '() '() '() (Λ-of ir-inner)))
                'move-borrowed)
  (define-values (core-move ir-move) (prepare '(Yield (Scope () (Reborrow y)) (Move x))))
  (check-equal? (key-of (type-of/raw core-move '() '() '() (Λ-of ir-move)))
                'move-borrowed)
  (define-values (core-drop ir-drop) (prepare '(Yield (Scope () (Reborrow y)) (Drop x))))
  (check-equal? (key-of (type-of/raw core-drop '() '() '() (Λ-of ir-drop)))
                'drop-borrowed))

;; 親の region まで退場したあとなら Move できる。
(let ()
  (define (core-with ρ_num)
    `(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Yield
          (Scope ()
            (Let (y let (BorrowedMut Res ,ρ_num)) (BorrowMut x)
              (Yield (Scope () (Reborrow y)) 1)))
          (Move x)))))
  (define skeleton (core-with 0))
  (define ir (build-region-ir skeleton))
  (define n-parent (region->rho ir (region-at ir '(0 1 0))))
  (define core (core-with n-parent))
  (check-equal? (core-points core) (core-points skeleton))
  (check-equal? (first (type-of/raw core '() '() '() (Λ-of ir))) 'ok))

(let ()
  (define core '(Scope () (Let (x let (Owned Res)) (resource 1) (Reborrow (Borrow x)))))
  (define ir (build-region-ir core))
  (check-equal? (key-of (type-of/raw core '() '() '() (Λ-of ir)))
                'reborrow-non-mutable))

;; 親の region が子を包まない場合。
(let ()
  (define core '(Scope () (Let (x let (Owned Res)) (resource 1) (Scope () (Borrow x)))))
  (define ir (build-region-ir core))
  (define ρ-inner (region->rho ir (region-at ir '(0 1))))
  (define environment (list (list 'y `(BorrowedMut Int ,ρ-inner))))
  (define Λ (region-ctx ir '() (hash) (hash 'y (set 'x))))
  (check-equal? (key-of (type-of/raw '(Reborrow y) '() '() environment Λ))
                'reborrow-region-escapes))

;; 停止中の親は Move できない。
(let ()
  (define core
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Yield (Reborrow (BorrowMut x)) (Move x)))))
  (define ir (build-region-ir core))
  (check-equal? (key-of (type-of/raw core '() '() '() (Λ-of ir)))
                'move-borrowed))

;; 親子が同時に退場する場合は復帰後の Move が通る。
(let ()
  (define core
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Yield (Scope () (Reborrow (BorrowMut x))) (Move x)))))
  (define ir (build-region-ir core))
  (check-equal? (first (type-of/raw core '() '() '() (Λ-of ir))) 'ok))

;; token が複数なら全要素を停止する。
(let ()
  (define (core-with body)
    `(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Let (z let (Owned Res)) (resource 2)
           (Yield (Reborrow y) ,body)))))
  (for ([body (in-list '((Move x) (Move z)))])
    (define core (core-with body))
    (define ir (build-region-ir core))
    (define ρ-scope (region->rho ir (region-at ir '())))
    (define Λ (region-ctx ir '() (hash) (hash 'y (set 'x 'z))))
    (define environment (list (list 'y `(BorrowedMut Int ,ρ-scope))))
    (check-equal? (key-of (type-of/raw core '() '() environment Λ))
                  'move-borrowed
                  (format "本体: ~s" body))))

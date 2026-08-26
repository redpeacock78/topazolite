#lang racket

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

;; [REQ: BOR-002] reborrow による親の停止と復帰。

(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; spec §12 の静的な形と注釈後の形。
(let ()
  (define Λ_0 (empty-region-ctx))
  (define Λ (region-ctx-add-token Λ_0 'y (set 'x)))
  (check-equal? (borrow-token-key Λ_0 '(Reborrow (BorrowMut x))) (set (list 'x)))
  (check-equal? (borrow-token-key Λ
                                  '(Let (y let (BorrowedMut Int 0))
                                        (BorrowMut x)
                                        (Reborrow y)))
                (set (list 'x)))
  (check-equal? (borrow-token-key Λ_0 '(ReborrowAt 1 (Own 7 ()) (BorrowMutAt 0 (Own 7 ()) 7)))
                (set (list 7)))
  (check-equal? (borrow-token-key Λ_0 '(ReborrowAt 1 (Own 7 ()) (BorrowMutRef 7 () 0)))
                (set (list 7))))

;; 内側の項の型をそのまま運ぶ形も全欄を合併する。
(let ()
  (define Λ_0 (empty-region-ctx))
  (check-equal? (borrow-token-key Λ_0 '(Proj (Rec ((a imm (BorrowMut x)))) a))
                (set (list 'x)))
  (check-equal? (borrow-token-key Λ_0 '(Suspend (BorrowMut x))) (set (list 'x)))
  (check-equal? (borrow-token-key Λ_0 '(Yield 1 (BorrowMut x))) (set (list 'x)))
  (check-equal? (borrow-token-key Λ_0
                                  '(Handle (Return 0 (BorrowedMut Int 0))
                                           (h -> h)
                                           (BorrowMut x)))
                (set (list 'x))))

(let ()
  (define Λ_0 (empty-region-ctx))
  (check-equal? (borrow-token-key
                 Λ_0
                 '(Proj (Rec ((a imm (BorrowMut x))
                              (b imm (BorrowMut y)))) b))
                (set (list 'x) (list 'y)))
  (check-equal? (borrow-token-key Λ_0
                                  '(Construct (Option Int) some (BorrowMut x)))
                (set (list 'x)))
  (check-equal? (borrow-token-key Λ_0 '(Rec ((a imm (resource 1))))) (set)))

;; 登録のない designator は、明示的な fail が無い限り空集合になる。
(let ()
  (define core '(Scope () (Let (x let (Owned Res)) (resource 1) (Borrow x))))
  (define ir (build-region-ir core))
  (define ρ_root (region->rho ir (region-at ir '())))
  (define environment (list (list 'y `(BorrowedMut Int ,ρ_root))))
  (check-equal? (borrow-token-key (Λ-of ir) 'y) (set))
  (check-equal? (second (type-of/raw '(Reborrow y) '() '() environment (Λ-of ir)))
                'unresolved-borrow-owner))

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
  ;; scrutinee の表が some の 0 番の欄へ BorrowMut の親を運ぶ。
  ;; 分岐の束縛子 y はその親を受け取り、Reborrow が親を持つ。
  (check-equal? (first (type-of/raw core-filled '() '() '() (Λ-of ir))) 'ok)
  ;; 期待型を与える check-eliminate の経路も同じ配布を使う。
  (define expected-core
    '(Eliminate o ((none () -> 0) (some (y) -> (Read y)))))
  (define expected-ir (build-region-ir expected-core))
  (define expected-rho
    (region->rho expected-ir (region-at expected-ir '())))
  (define env-o (list (list 'o `(Option (BorrowedMut Int ,expected-rho)))))
  (define tbl-o (hash (cons 'some 0) (cons (set (list 'x)) #f)))
  (define Λ-o (region-ctx-add-token (Λ-of expected-ir) 'o
                                    (set (list 'x)) #f #f tbl-o))
  (check-equal? (core-check-row expected-core '() '() 'Int env-o Λ-o)
                '())
  ;; capability を運ぶのに表が無い scrutinee は unresolved-borrow-owner になる。
  (define negative-core `(Construct (Option Int) some ,expected-core))
  (define negative-ir (build-region-ir negative-core))
  (define negative-rho
    (region->rho negative-ir (region-at negative-ir '())))
  (define negative-env
    (list (list 'o `(Option (BorrowedMut Int ,negative-rho)))))
  (define negative-result
    (type-of/raw negative-core '() '() negative-env
                 (Λ-of negative-ir)))
  (check-equal? (second negative-result) 'unresolved-borrow-owner))

;; 内側の Eliminate の束縛子から作った Construct を外側の Eliminate が辿る。
(let ()
  (define skeleton
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Scope ()
           (Let (o let (Option (BorrowedMut Res 0)))
                (Construct (Option (BorrowedMut Res 0)) some (BorrowMut x))
             (Eliminate
              (Eliminate o
                         ((none () ->
                                (Construct (Option (BorrowedMut Res 0)) none))
                          (some (y) ->
                                (Yield (Reborrow y)
                                       (Construct (Option (BorrowedMut Res 0))
                                                  some y)))))
              ((none () -> 0)
               (some (z) ->
                     (Let (w let (Borrowed Res 0)) (Reborrow z) 0)))))))))
  (define ir (build-region-ir skeleton))
  (define ρ_inner (region->rho ir (region-at ir '(0 1))))
  (define core
    (let fill ([t skeleton])
      (cond [(equal? t '(BorrowedMut Res 0)) `(BorrowedMut Res ,ρ_inner)]
            [(equal? t '(Borrowed Res 0)) `(Borrowed Res ,ρ_inner)]
            [(pair? t) (cons (fill (car t)) (fill (cdr t)))]
            [else t])))
  (define nested-result (type-of/raw core '() '() '() (Λ-of ir)))
  (check-equal? (first nested-result) 'ok))

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
                (set (list 'x)))
  (check-equal? (first (type-of/raw core '() '() '() (Λ-of ir))) 'ok))

;; 正常系。子 region の共有借用を返す。
;; G5c1 では外側で使われる結果の位置が α_child の下限になり、
;; 親子制約の伝播で返り値の寿命は外側の region へ広がる。
(let ()
  (define core
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Scope () (Reborrow (BorrowMut x))))))
  (define ir (build-region-ir core))
  (define ρ_outer (region->rho ir (region-at ir '())))
  (check-equal? (type-of/raw core '() '() '() (Λ-of ir))
                (list 'ok (list `(Borrowed Res ,ρ_outer) '()))))

;; Reborrow の子寿命へ完全に含まれる共有借用は、停止中の親との
;; 対を除いて許す。Reborrow 自身の shared request が別の可変借用との
;; 衝突を見落とさないことも同時に固定する。
(let ()
  (define core
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Yield (Reborrow (BorrowMut x)) (Borrow x)))))
  (define ir (build-region-ir core))
  (check-equal? (first (type-of/raw core '() '() '() (Λ-of ir))) 'ok))

;; 子寿命の外へはみ出す共有借用は、親が復帰する区間で衝突するため
;; 停止窓から除かず、borrow-conflicting-alias を残す。
(let ()
  (define core
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Yield (Scope () (Reborrow (BorrowMut x))) (Borrow x)))))
  (define ir (build-region-ir core))
  (check-equal? (key-of (type-of/raw core '() '() '() (Λ-of ir)))
                'borrow-conflicting-alias))

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

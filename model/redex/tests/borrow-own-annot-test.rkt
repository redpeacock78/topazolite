#lang racket

(require rackunit
         racket/match
         racket/set
         redex/reduction-semantics
         "../lang.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../type-shape.rkt"
         "../typing.rkt"
         "../machine.rkt")

;; place の designator は空の path を持つ capability になる。
(let ()
  (define core '(Scope (1) (Borrow 1)))
  (define ir (build-region-ir core))
  (match-define `(Scope (1) (BorrowAt ,_ ,own 1)) (annotate-regions core ir))
  (check-equal? own '(Own 1 ())))

;; 借用の型を持つ束縛名は、右辺の capability をそのまま引き継ぐ。
(let ()
  (define core
    '(Scope (1) (Let (b let (Borrowed Res 0)) (Borrow 1) (Reborrow b))))
  (define ir (build-region-ir core))
  (match-define `(Scope (1) (Let (b let ,_) ,_ (ReborrowAt ,_ ,own ,_)))
    (annotate-regions core ir))
  (check-equal? own '(Own 1 ())))

;; 借用の型でない束縛名は identity へ落ちる。
(let ()
  (define core '(Scope (1) (Let (b let Int) 0 (Borrow b))))
  (define ir (build-region-ir core))
  (match-define `(Scope (1) (Let (b let Int) 0 (BorrowAt ,_ ,own b)))
    (annotate-regions core ir))
  (check-equal? own '(Own b ())))

;; Reborrow は operand の own をそのまま引き継ぐ。
(let ()
  (define core '(Scope (1) (Reborrow (BorrowMut 1))))
  (define ir (build-region-ir core))
  (match-define `(Scope (1) (ReborrowAt ,_ ,own (BorrowMutAt ,_ ,own-inner 1)))
    (annotate-regions core ir))
  (check-equal? own '(Own 1 ()))
  (check-equal? own-inner '(Own 1 ())))

;; Scope を operand に持つ Reborrow も body の own を引き継ぐ。
(let ()
  (define core '(Scope (1) (Reborrow (Scope () (BorrowMut 1)))))
  (define ir (build-region-ir core))
  (match-define
    `(Scope (1) (ReborrowAt ,_ ,own (Scope () (BorrowMutAt ,_ ,own-inner 1))))
    (annotate-regions core ir))
  (check-equal? own '(Own 1 ()))
  (check-equal? own-inner '(Own 1 ())))

;; own の root が designator と食い違う注釈済みの木は入口で落ちる。
(let ()
  (define core '(Scope (1) (BorrowAt 0 (Own 7 ()) 1)))
  (define result
    (type-of/raw core (list (list 1 'Res)) '() '() (empty-region-ctx)))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'own-designator-mismatch))

;; 束縛名の designator でも同じく落ちる。
(let ()
  (define core '(Scope (1) (Let (b let Int) 0 (BorrowAt 0 (Own 7 ()) b))))
  (define result
    (type-of/raw core (list (list 1 'Res)) '() '() (empty-region-ctx)))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'own-designator-mismatch))

;; 同じ骨格で own を正しく置けば、この検査では落ちない。
(let ()
  (define core '(Scope (1) (BorrowAt 0 (Own 1 ()) 1)))
  (define result
    (type-of/raw core (list (list 1 'Res)) '() '() (empty-region-ctx)))
  (check-not-equal? (second result) 'own-designator-mismatch))

;; own が食い違う configuration は機械の側でどの規則にも当たらない。
(let ()
  (define conf
    '(cfg (Scope () (BorrowAt 0 (Own 7 ()) 1))
          ((1 1))
          ((1 Available))
          ()))
  (check-equal? (length (raw-steps-g2 conf)) 0))

;; E-BOR-020 の producer。型環境だけが designator x を束縛し、owner/token
;; の文脈は空である。同じ骨格で前提を 1 つずつ崩すと別の key になる。
(define (reborrow-status mode)
  (define core '(Scope () (Reborrow x)))
  (define ir (build-region-ir core))
  (define ρ (region->rho ir (region-at ir '(0))))
  (define environment
    (case mode
      [(missing) '()]
      [(shared) (list (list 'x `(Borrowed Res ,ρ)))]
      [(mutable) (list (list 'x `(BorrowedMut Res ,ρ)))]))
  (second
   (type-of/raw core '() '() environment
                (region-ctx ir '() (hash) (hash)))))

(check-equal? (reborrow-status 'missing) 'unbound-variable)
(check-equal? (reborrow-status 'shared) 'reborrow-non-mutable)
(check-equal? (reborrow-status 'mutable)
              'unresolved-borrow-owner)

;; Eliminate の branch binder へ能力を配る形は fail-closed にする。
(define (run-typing core ir places environment)
  (define annotated (annotate-regions core ir))
  (type-of/raw annotated places '() environment
                (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

;; scrutinee 自体が借用を含む形。
(let ()
  (define core
    '(Scope (1)
       (Let (b let (Borrowed Res 0))
            (Borrow 1)
            (Eliminate b ((true () -> 0) (false () -> 0))))))
  (define ir (build-region-ir core))
  (check-equal? (second (run-typing core ir (list (list 1 'Res)) '()))
                'capability-in-eliminate))

;; 分岐の field 型が借用を含む形。Option の schema を使う。
(let ()
  (define core
    '(Scope (1)
       (Let (x let (Owned Res)) (resource 1)
         (Let (o let (Option (Borrowed Res 0)))
              (Construct (Option (Borrowed Res 0)) some (Borrow 1))
              (Eliminate o
                ((none () -> 0) (some (y) -> 0)))))))
  (define ir (build-region-ir core))
  (check-equal? (second (run-typing core ir (list (list 1 'Res)) '()))
                'capability-in-eliminate))

;; 能力を含まない Eliminate は従来どおり通る。
(let ()
  (define core '(Eliminate (Construct Bool true)
                           ((true () -> 0) (false () -> 0))))
  (check-equal? (first (type-of/raw core '() '() '() (empty-region-ctx))) 'ok))

;; own は annotate/materialize/token の経路で変わらない。
(let ()
  (define core '(Scope (1) (Let (b let (Borrowed Res 0)) (Borrow 1) 0)))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (define own-of
    (lambda (t)
      (match t
        [`(Scope ,_ (Let ,_ (BorrowAt ,_ ,own ,_) ,_)) own]
        [_ #f])))
  (check-equal? (own-of annotated) '(Own 1 ()))
  (check-equal? (own-of (materialize-regions ir annotated (hash) (hash)))
                '(Own 1 ())))

(let ()
  (define core
    '(Scope (1) (Let (b let (Borrowed Res 0)) (Borrow 1) (Reborrow b))))
  (define ir (build-region-ir core))
  (define annotated (annotate-regions core ir))
  (match-define `(Scope ,_ (Let ,_ ,bound ,_)) annotated)
  (define Λ (region-ctx ir '() (hash 1 (region-at ir '())) (hash)))
  (check-equal? (borrow-token-key Λ bound) (set (cons 1 '()))))

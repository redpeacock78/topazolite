#lang racket

;; [REQ: BOR-004] Assign の型付けと受理条件。

(require rackunit
         redex/reduction-semantics
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt"
         "../machine.rkt")

(define (run core τ-place)
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ-place))
               '()
               '()
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

(define (run/env core τ-place environment)
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ-place))
               '()
               environment
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

;; Assign は可変借用 capability を通じた書き換えだけを受け入れる。
(let ()
  (define result (run '(Scope (1) (Assign (BorrowMut 1) 7)) 'Int))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

(let ()
  (define result
    (run '(Scope (1) (Assign (ProjBorrow (BorrowMut 1) a) 7))
         '(Record ((a Int mut)))))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

;; shared capability と非借用値は代入できない。
(let ()
  (define result (run '(Scope (1) (Assign (Borrow 1) 7)) 'Int))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-through-shared))

(let ()
  (define result (run '(Scope (1) (Assign 1 7)) 'Int))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-non-borrow))

(let ()
  (define result
    (run '(Scope (1) (Assign (ProjBorrow (Borrow 1) a) 7))
         '(Record ((a Int imm)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-through-shared))

;; 可変借用から imm field を射影すると共有 capability へ落ちるため、
;; field mode 単独でも Assign を拒む。
(let ()
  (define result
    (run '(Scope (1) (Assign (ProjBorrow (BorrowMut 1) a) 7))
         '(Record ((a Int imm)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-through-shared))

;; target の payload に Owned を含める書き換えと、Union の一成分だけに
;; compat? する書き換えは拒む。
(let ()
  (define result (run '(Scope (1) (Assign (BorrowMut 1) 7)) '(Owned Res)))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-owned-payload))

(let ()
  (define result
    (run '(Scope (1) (Assign (BorrowMut 1) 7)) '(Union Bool Int)))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-union-variant))

(define pure-fn '(NFn (Int) Int () () () User))
(define partial-fn '(NFn (Int) Int () (Partial) () User))

(test-case "REC-001: 純粋な callable の BorrowedMut payload への Assign は拒否する"
  (define result
    (run/env '(Scope (1) (Assign (BorrowMut 1) g))
             pure-fn `((g ,pure-fn let))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'mutable-callable-storage-requires-partial))

(test-case "REC-001: Partial の callable の BorrowedMut payload への Assign は受理する"
  (define result
    (run/env '(Scope (1) (Assign (BorrowMut 1) g))
             partial-fn `((g ,partial-fn let))))
  (check-equal? (first result) 'ok))

(test-case "REC-001: Union の全成分との互換検査は storage-ok より先に出る"
  (define result
    (run/env '(Scope (1) (Assign (BorrowMut 1) g))
             `(Union ,pure-fn Bool) `((g ,pure-fn let))))
  (check-equal? (second result) 'assign-union-variant))

(test-case "REC-001: 借用が衝突する Assign では E-TYP-026 が E-BOR-025 より先"
  (define (make ρ_b ρ_c)
    `(Scope (1)
       (Let (b let (BorrowedMut ,pure-fn ,ρ_b)) (BorrowMut 1)
         (Let (c let (Borrowed ,pure-fn ,ρ_c)) (Reborrow b)
           (Assign b g)))))
  (define ir (build-region-ir (make 0 0)))
  (define result
    (run/env (make (region->rho ir (region-at ir '(0 0)))
                   (region->rho ir (region-at ir '(0 1 0))))
             pure-fn `((g ,pure-fn let))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'mutable-callable-storage-requires-partial))

(define assign-heap
  '((1 (Rec ((a mut 0) (b imm 0))))))
(define assign-omega '((1 Available)))

;; 根 capability への Assign は H の値だけを差し替え、Ω と θ は変えない。
(let ()
  (define conf
    (term (cfg (Assign (BorrowMutRef 1 () 0) 9)
               ((1 5))
               ((1 Available))
               () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list (term (cfg unit ((1 9)) ((1 Available)) () ())))))

;; field path の Assign は根の record を関数的に更新する。
(let ()
  (define conf
    (term (cfg (Assign (BorrowMutRef 1 (a) 0) 9)
               ,assign-heap
               ,assign-omega
               () ())))
  (check-equal?
   (apply-reduction-relation -->g2 conf)
   (list
    (term
     (cfg unit
          ((1 (Rec ((a mut 9) (b imm 0)))))
          ((1 Available))
          () ())))))

;; Moved の place は Assign の対象にできず、規則は stuck する。
(let ()
  (define conf
    (term (cfg (Assign (BorrowMutRef 1 () 0) 9)
               ((1 5))
               ((1 Moved))
               () ())))
  (check-equal? (apply-reduction-relation -->g2 conf) '()))

;; core-calculus.md §4.9。Assign は Mutation を出す。
(let ()
  (define result (run '(Scope (1) (Assign (BorrowMut 1) 7)) 'Int))
  (check-equal? (first result) 'ok)
  (check-true (and (memq 'Mutation (second (second result))) #t)
              "Assign の row に Mutation が載る"))

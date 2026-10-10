#lang racket

(require rackunit
         racket/match
         "../elaborate.rkt"
         "../erase.rkt"
         "../typing.rkt")

(define option-owned '(Option (Owned Res)))
(define wide `(Record ((x ,option-owned imm) (y Int imm))))
(define narrow '(Record ((y Int imm))))
(define proof
  `(ProofRep (Reserved o-narrow)
             (RemainderSafelyDropped ,wide ,narrow)))
(define pure-value
  `(Rec ((x imm (Construct ,option-owned some (OwnLeaf (resource 11))))
        (y imm 7))))

(define (contains-rsd? value)
  (match value
    [`(Discharge (ProofRep ,_ (RemainderSafelyDropped ,_ ,_)) ,_) #t]
    [(? list?) (ormap contains-rsd? value)]
    [_ #f]))

(test-case "RSD は純粋な内側の row を変えない"
  (define core `(Discharge ,proof ,pure-value))
  (check-equal? (core-type-of pure-value '() '()) (list wide '()))
  (check-equal? (core-type-of core '() '()) (list narrow '())))

(test-case "RSD 内側の Move が持つ Own は残る"
  (define move-proof
    `(ProofRep (Reserved o-narrow)
               (RemainderSafelyDropped ,wide ,narrow)))
  (define callables
    `((moved-source (NFn (,option-owned) ,wide () (Own) () User))))
  (define source
    `(Apply
      (Lam User moved-source (raw-owned)
        (Handle (Return source-boundary ,wide) (result -> result)
          (Scope ()
            (Let (stored let ,option-owned) raw-owned
              (Let (record let ,wide)
                (Rec ((x imm (Move stored)) (y imm 8)))
                (Move record))))))
      (Construct ,option-owned some (OwnLeaf (resource 12)))))
  (check-equal? (core-type-of `(Discharge ,move-proof ,source)
                               '() callables)
                (list narrow '(Own))))

(test-case "注釈付き const Let の elaborate row は Core row と一致する"
  ;; この式は Task 1 probe の純粋な Record 幅縮小を再現する。
  (define actual
    '(Rec ((owned imm
                  (Construct some (Types (Owned Res))
                             (Apply acquire 41)))
           (kept imm 7))))
  (define result
    (elab `(Let (record const (Record ((kept Int imm)))) ,actual record)))
  (match result
    [(list core type row callables)
     (check-equal? row '())
     (check-true (contains-rsd? (erase-core core)))
     (check-equal? (core-type-of (erase-core core) '() callables)
                   (list type row))]
    [`(err ,diagnostic)
     (fail-check (format "注釈付き const Let が拒否された: ~s" diagnostic))]))

(test-case "関数 body の注釈付き Let は宣言 row が空でも受理される"
  (define actual
    '(Rec ((owned imm
                  (Construct some (Types (Owned Res))
                             (Apply acquire 42)))
           (kept imm 7))))
  (define body
    `(Let (record const (Record ((kept Int imm)))) ,actual record))
  (define result (elab `(Fn () (Record ((kept Int imm))) () ,body)))
  (match result
    [(list core type row callables)
     (check-equal? row '())
     (check-true (contains-rsd? (erase-core core)))
     (check-equal? (core-type-of (erase-core core) '() callables)
                   (list type row))]
    [`(err ,diagnostic)
     (fail-check (format "空 row の関数が拒否された: ~s" diagnostic))]))

(test-case "過大宣言した Own row の既存受理を保つ"
  (define actual
    '(Rec ((owned imm
                  (Construct some (Types (Owned Res))
                             (Apply acquire 43)))
           (kept imm 7))))
  (define body
    `(Let (record const (Record ((kept Int imm)))) ,actual record))
  (match (elab `(Fn () (Record ((kept Int imm))) (Own) ,body))
    [(list _core _type _row _callables) (void)]
    [`(err ,diagnostic)
     (fail-check (format "宣言 row の Own を持つ関数が拒否された: ~s"
                         diagnostic))]))

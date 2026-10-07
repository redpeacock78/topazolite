#lang racket

(require rackunit
         racket/match
         "../elaborate.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define (accepted source)
  (match (elab source)
    [(list core type row callables)
     (check-equal? (core-type-of core '() callables) (list type row))
     (list core type row)]
    [`(err ,diagnostic)
     (fail-check (format "elaborate が拒否した: ~s" diagnostic))]))

(test-case "ROW-005 の join は型の異なる欄を Union にする"
  (check-equal? (row005-join (list '(Record ((a Int imm) (b Int imm)))
                                   '(Record ((a Int imm) (b Bool imm)))))
                (normalize-type '(Record ((a Int imm)
                                          (b (Union Int Bool) imm))))))

(test-case "ROW-005 の join は可変性の食い違う欄を imm にし、片方だけの欄を落とす"
  (check-equal? (row005-join (list '(Record ((a Int mut) (c Int imm)))
                                   '(Record ((a Bool imm)))))
                (normalize-type '(Record ((a (Union Int Bool) imm))))))

(test-case "ROW-005 の join は Owned の payload の上界を取り、無ければ拒否する"
  (check-equal? (row005-join
                 (list '(Record ((o (Owned (Union Int String)) imm)))
                       '(Record ((o (Owned (Union Bool String)) imm)))))
                (normalize-type
                 '(Record ((o (Owned (Union Int (Union Bool String))) imm)))))
  (check-false
   (row005-join (list '(Record ((o (Owned Int) imm)))
                     '(Record ((o (Owned Bool) imm))))))
  (check-false
   (row005-join (list '(Record ((o (Owned Int) imm)))
                     '(Record ((o Int imm)))))))

(test-case "ROW-005 の join は入れ子の Record を Union にする"
  (check-equal?
   (row005-join
    (list '(Record ((r (Record ((x Int imm))) imm)))
          '(Record ((r (Record ((x Bool imm))) imm)))))
   (normalize-type
    '(Record ((r (Union (Record ((x Int imm)))
                       (Record ((x Bool imm)))) imm))))))

(test-case "synth の match は ROW-005 の欄の上界を返す"
  (match-define (list _ type _)
    (accepted
     '(Eliminate (Construct true (Types))
                 ((true () -> (Rec ((a imm 1))))
                  (false () -> (Rec ((a imm (Construct true (Types))))))))))
  (check-equal? type
                (normalize-type '(Record ((a (Union Int Bool) imm))))))

(test-case "Λ なしの合流は寿命変数を含む型を不変条件の違反にする"
  (check-exn #rx"寿命変数を含む型を受けない"
             (lambda ()
               (branch-types-upper-bound
                (list '(Borrowed Int (RVar 0))
                      '(Borrowed Int (RVar 1)))))))

(test-case "Λ なしの合流は Record の欄の寿命変数も不変条件の違反にする"
  (check-exn #rx"寿命変数を含む型を受けない"
             (lambda ()
               (branch-types-upper-bound
                (list '(Record ((r (Borrowed Int (RVar 0)) imm) (b Int imm)))
                      '(Record ((r (Borrowed Int (RVar 1)) imm) (b Bool imm))))))))

(test-case "Λ なしの合流は寿命変数の無い型で lifetime の状態に触れない"
  (parameterize ([lifetime-counter #f]
                 [merge-alpha-sources #f])
    (check-equal? (branch-types-upper-bound
                   (list '(Record ((a Int imm) (b Int imm)))
                         '(Record ((a Int imm) (b Int imm)))))
                  '(Record ((a Int imm) (b Int imm))))))

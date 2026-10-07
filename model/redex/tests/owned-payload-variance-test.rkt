#lang racket

(require rackunit
         "../compat.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define u1 '(Union Int String))
(define u2 '(Union Int (Union String Bool)))

(test-case "compat? は Owned の payload の tag を保つ widening を受理する"
  (check-true (compat? `(Owned ,u1) `(Owned ,u2)))
  (check-false (compat? `(Owned ,u2) `(Owned ,u1))))

(test-case "compat? は NFn の返り値の Owned widening を受理し逆を拒否する"
  (define (thunk payload) `(NFn () (Owned ,payload) () () () User))
  (check-true (compat? (thunk u1) (thunk u2)))
  (check-false (compat? (thunk u2) (thunk u1))))

(test-case "compat? は NFn の引数の Owned を反変に照合する"
  (define (sink payload) `(NFn ((Owned ,payload)) Int () () () User))
  (check-true (compat? (sink u2) (sink u1)))
  (check-false (compat? (sink u1) (sink u2))))

(test-case "compat? は Borrowed の payload の Owned widening を受理する"
  (check-true (compat? `(Borrowed (Owned ,u1) r)
                       `(Borrowed (Owned ,u2) r))))

(test-case "BorrowedMut の payload widening は compat? と tag-compat? が拒否する"
  (check-false (compat? `(BorrowedMut (Owned ,u1) r)
                        `(BorrowedMut (Owned ,u2) r)))
  (check-false (tag-compat? `(BorrowedMut (Owned ,u1) r)
                            `(BorrowedMut (Owned ,u2) r))))

(test-case "tag の無い値を持つ Owned Record の widening は拒否する"
  (define narrow '(Owned (Record ((a Int imm)))))
  (define wide '(Owned (Record ((a (Union Int Bool) imm)))))
  (check-false (compat? narrow wide))
  (check-false (tag-compat? narrow wide)))

(test-case "Core の合流は Owned payload の tag を保つ上界を返す"
  (check-equal?
   (tag-types-upper-bound
    (list '(Owned (Union Int String)) '(Owned (Union Bool String))))
   (normalize-type '(Owned (Union Int (Union Bool String))))))

(test-case "Core の合流は Owned payload の上界が無ければ失敗する"
  (check-true
   (tag-bound-failure?
    (tag-types-upper-bound (list '(Owned Int) '(Owned Bool)))))
  (check-true
   (tag-bound-failure?
    (tag-types-upper-bound
     (list '(Owned (Record ((a Int imm) (b Int imm))))
           '(Owned (Record ((a Int imm)))))))))

(test-case "Record field の Owned も payload の上界へ合流する"
  (check-equal?
   (tag-types-upper-bound
    (list '(Record ((o (Owned (Union Int String)) imm)))
          '(Record ((o (Owned (Union Bool String)) imm)))))
   (normalize-type
    '(Record ((o (Owned (Union Int (Union Bool String))) imm))))))

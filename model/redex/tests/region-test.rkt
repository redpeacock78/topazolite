#lang racket

(require rackunit
         racket/match
         "../elaborate.rkt"
         "../erase.rkt"
         "../region.rkt")

;; [REQ: BOR-003] point は意味的な子の添字の列である。
;; 生の位置で数えると、spanful な項と spanless な項で同じ部分項が別の添字に来る。
(test-case "Apply の子は被適用項に続けて引数である"
  (check-equal? (core-children '(Apply f 1 2)) '(f 1 2)))

(test-case "span、束縛子、型、op は子に数えない"
  (check-equal? (core-children '(Let (x Int) 1 2)) '(1 2))
  (check-equal? (core-children '(Let (x const Int) 1 2)) '(1 2))
  (check-equal? (core-children '(Perform (Return b Int) 1)) '(1))
  (check-equal? (core-children '(Handle (Return b Int) (k -> 1) 2)) '(1 2))
  (check-equal? (core-children '(Scope () 1)) '(1))
  (check-equal? (core-children '(Proj 1 fld)) '(1))
  (check-equal? (core-children '(Lam User c0 (x y) 1)) '(1)))

(test-case "Eliminate は scrutinee に続けて分岐の本体を分岐の順に並べる"
  (check-equal?
   (core-children '(Eliminate 0 ((nil () -> 1) (cons (h t) -> 2))))
   '(0 1 2)))

;; spec §4 の production を 1 件ずつ実データで通す。
;; 未知形の error は落ちた production を見つけない。既定へ落ちず個別の節が
;; 受けていることは、この試験だけが押さえる。
;; Construct と Rec は c 側と v 側の双方に同じ形の production を持つ。
;; G2 は c ::= v なので、子を整数だけにすると v 側の実装でも通ってしまう。
;; c 専用の形である Apply を子に置き、c 側の経路を分けて押さえる。
(test-case "c 側の残る production も子を返す"
  (check-equal? (core-children '(Construct Int Wrap (Apply f 1) 2))
                '((Apply f 1) 2))
  (check-equal? (core-children '(Rec ((fst imm (Apply f 1)) (snd mut 2))))
                '((Apply f 1) 2))
  (check-equal? (core-children '(Recur c0 f (x) 1 2)) '(1 2))
  (check-equal? (core-children '(Yield 1 2)) '(1 2))
  (check-equal? (core-children '(Suspend 1)) '(1))
  (check-equal? (core-children '(Drop 1)) '(1))
  (check-equal? (core-children '(Curry 1 2)) '(1 2))
  (check-equal? (core-children '(Discharge (ProofRep User ValidNarrativeTrait) 1))
                '(1)))

;; Construct と Rec は c 側と v 側で同じ形を持つ。
;; 1 つの節が両方を受けることを、値だけを子に持つ実データで確かめる。
;; 内側に Scope を置くのは、値を葉として扱うと Scope を落とすためである。
(test-case "v 側の Construct と Rec も内側を歩く"
  (check-equal?
   (core-children '(Construct Int Wrap (Lam User c0 (x) (Scope () x))))
   '((Lam User c0 (x) (Scope () x))))
  (check-equal?
   (core-children '(Rec ((fst imm (Lam User c0 (x) (Scope () x))))))
   '((Lam User c0 (x) (Scope () x))))
  (check-equal?
   (core-points '(Rec ((fst imm (Lam User c0 (x) (Scope () x))))))
   '(() (0) (0 0) (0 0 0))))

;; 値の内側も歩く。Lam の本体は Scope を含むため、値を葉として扱うと
;; Scope を 1 つも見つけられない。
(test-case "値の内側も歩く"
  (check-equal? (core-children '(UVal 1)) '(1))
  (check-equal? (core-children '(RVal (ProofRep User ValidNarrativeTrait) 1))
                '(1))
  (check-equal? (core-children '(CurryVal User 1 2)) '(1 2))
  (check-equal? (core-children '(RecurVal c0 f (x) 1)) '(1)))

(test-case "子を持たない形は空を返す"
  (for ([t (in-list (list 3 "s" 'unit 'x '(Move y)
                          '(PrimVal User add)
                          '(TypeRep User Int Type)
                          '(ProofRep User ValidNarrativeTrait)
                          '(resource 0)))])
    (check-equal? (core-children t) '() (format "~s" t))))

;; 既定を空にすると、c の production が増えたときに走査が黙って内側を飛ばし、
;; 内部の Scope を落とした IR が試験を通ってしまう。
(test-case "知らない形は error を出す"
  (check-exn exn:fail? (lambda () (core-children '(NotACoreForm 1)))))

(test-case "core-points は根から前順で全 point を返す"
  (check-equal? (core-points '(Apply f (Suspend 1)))
                '(() (0) (1) (1 0))))

(test-case "core-node は point の指す節点を返し、指せない point で error を出す"
  (define core '(Apply f (Suspend 1)))
  (check-equal? (core-node core '()) core)
  (check-equal? (core-node core '(1 0)) 1)
  (check-exn exn:fail? (lambda () (core-node core '(2))))
  (check-exn exn:fail? (lambda () (core-node core '(0 0)))))

;; erase-core は span と metadata を落とす写像である。
;; point は erase-core を通した項の上で数えるため、spanful な項を渡しても
;; spanless な項を渡しても同じ point の集合になる。
(test-case "core-points は erase-core を入口に通す"
  (match-define (list raw-core _ _ _) (elab '(Apply (Fn ((x Int)) Int () x) 1)))
  (check-equal? (core-points raw-core) (core-points (erase-core raw-core))))

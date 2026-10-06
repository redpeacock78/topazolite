#lang racket

;; [REQ: OWN-008] Owned の固定引数。
;; [REQ: NAR-005] NFn の型成分 O。curry は O を Derived で伸ばす。

(require rackunit
         racket/match
         redex/reduction-semantics
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../lang.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (elaboration-of source)
  (match (elab source)
    [(list core type row callables) (list core type row callables)]
    [other (error 'elaboration-of "elaboration failed: ~s" other)]))

(define (key-of result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

(define owned-curry-surface
  '(Let p
       (Apply acquire 1)
       (Let g
            (Fn ((q (Owned Res))) Unit (Own) (Drop q))
            (Curry g (Move p)))))

(test-case
 "Owned の固定引数を Move 経由で固定でき、結果型が Owned<NFn 残余> になる"
 (match-define (list core type row callables)
   (elaboration-of owned-curry-surface))
 (check-equal? type
               '(Owned (NFn () Unit () (Own) ()
                            (Derived User (Curry (OwnLeaf (Move p)))))))
 (check-equal?
  (core-type-of core '() callables)
  (list type
        row)))

(define plain-curry-surface
  '(Fn ((n Int)) (NFn () Int () ()) ()
       (Let g
            (Fn ((a Int) (b Int)) Int () a)
            (Curry (Curry g n) 1))))

(test-case
 "関数側も固定引数側も Owned でなければ素の NFn を返す"
 (match-define (list core type row callables)
   (elaboration-of plain-curry-surface))
 (check-equal? type '(NFn (Int) (NFn () Int () () () User) () () () User))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; Owned の関数は Move 経由で呼べる。
(define owned-curry-apply-surface
  '(Fn ((p (Owned Res))) Unit (Own)
       (Let g
            (Fn ((q (Owned Res))) Unit (Own) (Drop q))
            (Let h
                 (Curry g (Move p))
                 (Apply (Move h))))))

(test-case
 "Owned の関数を Move 経由で呼べる"
 (match-define (list core type row callables)
   (elaboration-of owned-curry-apply-surface))
 (check-equal? type '(NFn ((Owned Res)) Unit () (Own) () User))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; 中間の place を Move で開く形は関数の位置へ置ける。Task 3 の生成形がこの形を使う。
(define curried-owned-function-core
  '(Curry (Move t) (OwnLeaf (Move r))))

(define owned-curry-environment
  (list (list 't '(Owned (NFn ((Owned Res)) Unit () (Own) () User)))
        (list 'r '(Owned Res))))

(test-case
 "Owned の closure を載せた place を Move で開く入れ子の Curry は通る"
 (check-equal? (type-of/raw curried-owned-function-core '() '()
                             owned-curry-environment)
               '(ok ((Owned (NFn () Unit () (Own) ()
                                (Derived User (Curry (OwnLeaf (Move r))))))
                     (Own)))))

;; Move を経ない形は落ちる。関数式は Apply であり、Move でも CurryVal でもない。
(define owned-function-not-moved-core
  '(Apply (Apply mk)))

(define owned-maker-environment
  (list (list 'mk '(NFn () (Owned (NFn () Unit () (Own) () User)) () (Own) () User))))

(test-case
 "Owned の関数を Move を経ずに関数の位置へ置くと owned-function-requires-move で落ちる"
 (check-equal? (key-of (type-of/raw owned-function-not-moved-core '() '()
                                     owned-maker-environment))
               'owned-function-requires-move))

(define aggregate-resource-type
  '(Record ((n Int imm) (owned (Owned Res) imm))))

(define aggregate-curry-environment
  `((f (NFn (,aggregate-resource-type Int) Int () () () User))
    (x ,aggregate-resource-type)))

(test-case
 "集約資源型の引数を固定した Curry の型は Owned になる"
 (match-define (list 'ok (list result-type '()))
   (type-of/raw '(Curry f x) '() '() aggregate-curry-environment))
 (check-true
  (match result-type
    [`(Owned (NFn (Int) Int () () () (Derived User (Curry x)))) #t]
    [_ #f])))

(test-case
 "集約資源型を固定した CurryVal の型も Owned になる"
 (define argument
   '(Rec ((n imm 7)
         (owned imm (OwnedLeaf (tok 13) (resource 13))))))
 (define function
   `(Lam User aggregate-curry-lam (aggregate n)
        (Handle (Return boundary Int)
                (return-value -> return-value)
                (Scope ()
                  (Let (aggregate-transfer let ,aggregate-resource-type)
                       aggregate
                    n)))))
 (define callables
   `((aggregate-curry-lam
      (NFn (,aggregate-resource-type Int) Int () () () User))))
 (define core
   `(CurryVal (Derived User (Curry ,argument)) ,function ,argument))
 (define expected
   `(Owned (NFn (Int) Int () () () (Derived User (Curry ,argument)))))
 (define config
   `(cfg (Scope () ,core) () () (((tok 13) Available)) ()))
 (check-true (config-ok? config callables expected '())))

(test-case
 "Owned の Curry は Record 欄へ置けず、Int の Curry は二欄へ置ける"
 (define aggregate-closure `(Curry f x))
 (check-equal?
  (key-of
   (type-of/raw `(Rec ((left imm ,aggregate-closure)))
                '() '() aggregate-curry-environment))
  'owned-record-field)
 (check-equal?
  (key-of
   (type-of/raw
    `(Rec ((left imm ,aggregate-closure) (right imm ,aggregate-closure)))
    '() '() aggregate-curry-environment))
  'owned-record-field)
 (define int-curry-environment
   '((f (NFn (Int Int) Int () () () User)) (x Int)))
 (check-true
  (match (type-of/raw
    '(Rec ((left imm (Curry f x)) (right imm (Curry f x))))
          '() '() int-curry-environment)
    [(list 'ok _) #t]
    [_ #f])))

(test-case
 "集約資源型を固定した閉包は裸で二度呼べない"
 (define closure-type
   '(Owned (NFn (Int) Int () () () User)))
  (define core
   `(Let (closure let ,closure-type)
         (Curry f x)
      (Rec ((left imm (Apply closure 1))
            (right imm (Apply closure 1))))))
 (check-equal?
  (key-of (type-of/raw core '() '() aggregate-curry-environment))
  'owned-variable-requires-move))

(test-case
 "elaborate は集約資源型の固定引数で作る Curry の閉包を Owned にする"
 (define source
   `(Fn ((x ,aggregate-resource-type))
        (Owned (NFn (Int) Int () ()))
        (Own)
      (Curry (Fn ((aggregate ,aggregate-resource-type) (n Int)) Int () n)
             (Move x))))
 (match-define (list core type row callables) (elaboration-of source))
 (check-true
  (match type
    [`(NFn (,aggregate-resource-type)
           (Owned (NFn (Int) Int () () () User)) () (Own) () User)
     #t]
    [_ #f]))
 (check-equal? (core-type-of core '() callables) (list type row)))

;; 関数側だけが Owned で固定引数が Int の Curry を踏む。
;; 内側の Fn は自分の仮引数しか使わない。Task 3 まで E-OWN-005 が
;; Owned の捕捉を禁じるため、捕捉のある形はここでは使えない。
(test-case
 "elaborate の E-Curry は関数側の Owned を結果へ引き継ぐ"
 (define surface
   '(Fn ((p (Owned Res))) (Owned (NFn () Unit (Own) ())) (Own)
        (Let g
             (Fn ((q (Owned Res)) (n Int)) Unit (Own) (Drop q))
          (Let f (Curry g (Move p))
               (Curry (Move f) 1)))))
 (match-define (list _core type _row _callables) (elaboration-of surface))
 (check-equal? (third type) '(Owned (NFn () Unit () (Own) () User))))

(test-case
 "Curry の payload は値でない core 項でも step に合う"
 (check-true (redex-match? G1 step '(Curry x)))
 (check-true (redex-match? G1 step '(Curry (Apply f y)))))

(test-case
 "curry の型 payload は erase 済みなら spanless である"
 (define erased
   '(NFn () Unit () () () (Derived User (Curry 1))))
 (check-not-exn (lambda () (check-spanless! 'own-curry-fixed erased)))
 (define spanful
   '(NFn () Unit () () ()
         (Derived User (Curry (#:lit 1 (#:span src 0 1))))))
 (check-exn exn:fail?
            (lambda () (check-spanless/deep! 'own-curry-fixed spanful))))

(test-case
 "curry の origin payload は uniquify と substitute の添字だけを剥がす"
 (check-equal?
  (erase-origin-core '(Curry (Move p⟨1⟩«2»«3»)))
  '(Curry (Move p)))
 (check-equal?
  (erase-origin-core '(Curry (Move q)))
  '(Curry (Move q))))

(test-case
 "curry-payload-erase は Curry の payload だけを消す"
 (check-equal? (curry-payload-erase '(Derived User (Make Int)))
               '(Derived User (Make Int)))
 (check-equal? (curry-payload-erase '(Derived User (Expand Box)))
               '(Derived User (Expand Box)))
 (check-equal? (curry-payload-erase '(Derived User (Policy Safe)))
               '(Derived User (Policy Safe)))
 (check-equal? (curry-payload-erase '(Derived User (Trait Show)))
               '(Derived User (Trait Show)))
 (check-equal?
  (curry-payload-erase
   '(Derived
     (Derived User (Curry (Apply f x)))
     (Compose pair
              (Derived User (Curry y))
              (Derived (Reserved add) (Make Int)))))
  '(Derived
    (Derived User (Curry #:erased))
    (Compose pair
             (Derived User (Curry #:erased))
             (Derived (Reserved add) (Make Int))))))

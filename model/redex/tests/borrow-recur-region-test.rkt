#lang racket

;; [REQ: BOR-005] region 多相な再帰関数の借用。形 i と形 ii。

(require rackunit
         racket/match
         racket/set
         "../region.rkt"
         "../borrow.rkt"
         "../span-core.rkt"
         "../typing.rkt")

(define (raw-result core ir τ_place callables)
  (define actual-ir (if (region-solver? ir) ir (build-region-ir core)))
  (type-of/raw (annotate-regions core actual-ir)
               (list (list 1 τ_place)) callables '()
               (region-ctx actual-ir '() (hash 1 (region-at actual-ir '())) (hash))))

(define (status core ir τ_place callables)
  (first (raw-result core ir τ_place callables)))

(define (failure-key result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

;; 外側の再帰関数の署名が結果型で (RParam a) に触れる。
;; 本体の内側の Lam は借用の仮引数を持つ。
;; 署名は入力側の自然な束縛名で書く。型検査入口の alpha-renaming 表が、
;; RegionLam の fresh 名との対応を解決する。
(define outer-callables
  '((outer (NFn (Int)
                (NFn ((BorrowedMut Int (RParam a))) Int () ())
                () ()))
    (innerb (NFn ((BorrowedMut Int (RParam a))) Int () ()))))

;; 1。署名が言及する region parameter を本体が引き継ぐ。
;; 空集合へ置き換える実装は、内側の Lam を borrowed-function-parameter で落とす。
(test-case
 "再帰の本体が署名の region parameter を引き継ぐ"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Recur outer f (n)
                             (Lam User innerb (y) (Read y))
                             0))))
 (define ir (build-region-ir core))
 (check-equal? (status core ir 'Int outer-callables) 'ok))

;; 2。署名が言及しない region parameter は引き継がない。
;; set-intersect を使わず外側をそのまま渡す実装は、この形を通してしまう。
(test-case
 "署名が言及しない region parameter は本体へ渡らない"
 (define core
   '(Scope (1)
           (RegionLam (a)
                      (Recur plain f (n)
                             (Lam User innerb (y) (Read y))
                             0))))
 (define ir (build-region-ir core))
 (check-equal?
  (failure-key
   (raw-result core ir 'Int
               (cons '(plain (NFn (Int)
                                  (NFn (Int) Int () ())
                                  () ()))
                     outer-callables)))
  'borrowed-function-parameter))

;; 3。lookup-binding は assoc の結果をそのまま返す。
;; 名前や型の equal? へ退行した実装は、同じ名前かつ同じ型の別の対を返す。
(test-case
 "lookup-binding は環境の対そのものを返す"
 (define inner (list 'f '(NFn (Int) Int () ())))
 (define outer (list 'f '(NFn (Int) Int () ())))
 (define environment (list inner outer))
 (check-eq? (lookup-binding environment 'f) inner))

;; §6。段 4 と段 5 の期待値は type-of/raw と core-check-row の両入口で
;; 同じでなければならない。片方の入口だけを直した実装を通さない。
(define (row-result core ir τ_place callables expected)
  (define actual-ir (if (region-solver? ir) ir (build-region-ir core)))
  (core-check-row (annotate-regions core actual-ir)
                  (list (list 1 τ_place)) callables expected '()
                  (region-ctx actual-ir '() (hash 1 (region-at actual-ir '())) (hash))))

;; 正例は type-of/raw が 'ok を返し、core-check-row が row を返す。
(define (check-both-ok core ir τ_place callables expected)
  (check-equal? (status core ir τ_place callables) 'ok)
  (check-equal? (row-result core ir τ_place callables expected) '()))

;; 負例は type-of/raw が期待する鍵で落ち、core-check-row が #f を返す。
(define (check-both-fail core ir τ_place callables expected key)
  (check-equal? (failure-key (raw-result core ir τ_place callables)) key)
  (check-false (row-result core ir τ_place callables expected)))

;; 借用の仮引数を 2 つ取る再帰の署名。位置ごとの鍵が別であることを使う。
(define swap-callables
  '((rec2 (NFn ((BorrowedMut Int (RParam a)) (BorrowedMut Int (RParam a)))
               Int () ()))))

;; 4。本体の再帰呼出しが仮引数をそのままの位置で渡す。
(test-case
 "再帰の本体が借用の仮引数を同じ位置で渡せる"
 (check-both-ok '(Scope (1)
                   (RegionLam (a)
                     (Recur rec2 f (x y) (Apply f x y) 0)))
                '() 'Int swap-callables '(ForallRegion (a) Int)))

;; 5。位置を入れ替えると、位置 0 の実引数の根が位置 1 の鍵になる。
(test-case
 "再帰の本体が借用の仮引数の位置を入れ替えると落ちる"
 (check-both-fail '(Scope (1)
                     (RegionLam (a)
                       (Recur rec2 f (x y) (Apply f y x) 0)))
                  '() 'Int swap-callables '(ForallRegion (a) Int)
                  'unresolved-borrow-owner))

;; 6。RecurVal も定義側で落ちなくなる。
(test-case
 "RecurVal の署名が借用の仮引数を持てる"
 (check-both-ok '(Scope (1)
                   (RegionLam (a)
                     (RecurVal rec2 f (x y) (Apply f x y))))
                '() '(NFn ((BorrowedMut Int (RParam a))
                           (BorrowedMut Int (RParam a)))
                          Int () ())
                swap-callables
                '(ForallRegion (a.0)
                   (NFn ((BorrowedMut Int (RParam a.0))
                         (BorrowedMut Int (RParam a.0)))
                        Int () ()))))

;; 7。Eliminate の tail は仮引数の capability を根に保ったまま位置 1 を
;; path へ積む。仮の要約は path を固定せず、根の一致だけでこの射影を受ける。
(define list-recur-callables
  '((reclist (NFn ((Borrowed (List Int) (RParam a)))
                    Int () ()))))

(test-case
 "再帰の本体が借用した List の tail を同じ根で渡せる"
 (check-both-ok '(Scope (1)
                   (RegionLam (a)
                     (Recur reclist f (xs)
                       (Eliminate xs
                         ((nil () -> 0)
                          (cons (head tail) -> (Apply f tail))))
                       0)))
                '() 'Int list-recur-callables '(ForallRegion (a) Int)))

;; 8。根の制約は射影の path の形を検査しない一方、別根と空 capability は
;; fail-closed にする。直接 helper を叩き、再借用の path と未解決の両方を固定する。
(test-case
 "再帰の根が別または空の capability を拒む"
 (define frame
   (make-recur-frame (list (list 'f 'signature)) (list 'w)
                     #f (box '()) 'tentative 1))
 (define (failure-key-for caps)
   (let/ec escape
     (recur-check-roots frame (list caps) 'node
                        (lambda (key . _) (escape key)))
     #f))
 (check-equal? (failure-key-for (set (cons 'w '(field)))) #f)
 (check-equal? (failure-key-for (set (cons 'other '(field))))
               'unresolved-borrow-owner)
 (check-equal? (failure-key-for (set)) 'unresolved-borrow-owner))

;; 形 ii。署名そのものが ForallRegion である再帰。
(define forall-callables
  '((recf (ForallRegion (a)
            (NFn ((BorrowedMut Int (RParam a))) Int () ())))
    (useb (NFn ((BorrowedMut Int (RParam a))) Int () ()))))

;; 9。dual-cell の回帰。同じ Recur の本体が剥がした NFn を、継続が
;; ForallRegion を見る。片方の環境しか直していない実装はここで落ちる。
(test-case
 "形 ii の本体は素の呼出し、継続は RegionApp を経る呼出しになる"
 (check-both-ok
  '(Scope (1)
     (RegionLam (a)
       (Recur recf f (x)
              (Apply f x)
              (Lam User useb (y) (Apply (RegionApp f ((RParam a))) y)))))
  '() '(NFn ((BorrowedMut Int (RParam a))) Int () ())
  forall-callables
  '(ForallRegion (a.0)
     (NFn ((BorrowedMut Int (RParam a.0))) Int () ())) ))

;; 10。継続で包みを剥がさずに呼ぶと、関数の型が ForallRegion のままである。
(test-case
 "形 ii の継続が RegionApp を経ずに呼ぶと落ちる"
 (check-both-fail
  '(Scope (1)
     (RegionLam (a)
       (Recur recf f (x)
              (Apply f x)
              (Lam User useb (y) (Apply f y)))))
  '() '(NFn ((BorrowedMut Int (RParam a))) Int () ())
  forall-callables
  '(NFn ((BorrowedMut Int (RParam a))) Int () ())
  'apply-non-function))

;; 11。Let を挟まない RegionApp。関数の位置が名前でも RegionLam でもない。
(test-case
 "RecurVal を直接 RegionApp へ渡せる"
 (check-both-ok
  '(Scope (1)
     (RegionLam (a)
       (RegionApp (RecurVal recf f (x) (Read x)) ((RParam a)))))
  '() '(NFn ((BorrowedMut Int (RParam a))) Int () ())
  forall-callables
  '(ForallRegion (a.0)
     (NFn ((BorrowedMut Int (RParam a.0))) Int () ())) ))

;; 12。本体の借用の使用が雛形として溜まり、継続の呼出しで実体化される。
;; 収集器を template-collectors へ積んでいない実装は、route-deferred! が
;; 持ち主の段を見つけられず unresolved-borrow-owner で落ちる。
(test-case
 "形 ii の本体の借用の使用が継続の呼出しで実体化される"
 (check-both-ok
  '(Scope (1)
     (RegionLam (a)
       (Recur recf f (x)
              (Let (t let Int) (Read x) (Apply f x))
              (Lam User useb (y) (Apply (RegionApp f ((RParam a))) y)))))
  '() '(NFn ((BorrowedMut Int (RParam a))) Int () ())
  forall-callables
  '(ForallRegion (a.0)
     (NFn ((BorrowedMut Int (RParam a.0))) Int () ())) ))

;; 13。外側に RegionLam が無い形 ii。rp を束縛するのは署名だけである。
;; 継続は Scope の生きた region を実引数にして包みを剥がす。
;; 外側の RegionLam が rp を束縛していることに頼る実装はここで落ちる。
(test-case
 "外側に RegionLam が無くても形 ii が通る"
 (check-both-ok
  '(Scope (1)
     (Recur recf f (x)
            (Apply f x)
            (Let (g let (NFn ((BorrowedMut Int (RVar 0))) Int () ()))
                 (RegionApp f ((RVar 0)))
                 0)))
 '() 'Int forall-callables 'Int))

;; 14。RegionApp の置換表は region parameter の並びで作る。2 つの binder を
;; 逆順に受ける実装や hash の走査順へ依存する実装は、結果型の順序で落ちる。
(define forall-two-callables
  '((rec2 (ForallRegion (a b)
            (NFn ((BorrowedMut Int (RParam a))
                  (BorrowedMut Int (RParam b)))
                 Int () ())))))

(test-case
 "複数の region parameter を RegionApp の位置順で置換する"
 (check-both-ok
  '(Scope (1)
     (RegionLam (a)
       (RegionLam (b)
         (RegionApp
          (RecurVal rec2 f (x y) (Apply f x y))
          ((RParam a) (RParam b))))))
  '() 'Int forall-two-callables
  '(ForallRegion (a.0)
     (ForallRegion (b.1)
       (NFn ((BorrowedMut Int (RParam a.0))
             (BorrowedMut Int (RParam b.1)))
            Int () ())))))

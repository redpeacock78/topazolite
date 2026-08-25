#lang racket

(require rackunit
         "../typing.rkt"
         "../region-param.rkt"
         "../erase.rkt"
         "../region.rkt"
         "../borrow.rkt")

;; spec §5.7。callables の表は ForallRegion に包まれた署名を受ける。
;; 包みは 1 段だけであり、入れ子は受けない。

(define NFN '(NFn (Int) Int () ()))

(test-case
 "表は ForallRegion に包まれた署名を受ける"
 (check-equal?
  (type-of/raw '(Lam User f (x) x) '() (list (list 'f `(ForallRegion (a) ,NFN))))
  ;; binder 文脈が無いため unknown-callable で閉じる。入口では落とさない。
  '(fail unknown-callable (Lam User f (x) x) ())))

(test-case
 "入れ子の ForallRegion は入口で落ちる"
 (match-define (list 'fail key _node _details)
   (type-of/raw '(Lam User f (x) x) '()
                (list (list 'f `(ForallRegion (a) (ForallRegion (b) ,NFN))))))
 (check-equal? key 'invalid-callables))

(test-case
 "NFn の内側の ForallRegion も入口で落ちる"
 (match-define (list 'fail key _node _details)
   (type-of/raw
    '(Lam User f (x) x) '()
    (list (list 'f '(ForallRegion (a)
                      (NFn ((ForallRegion (b) (Borrowed Int (RParam a))))
                           Int () ()))))))
 (check-equal? key 'invalid-callables)
 ;; 包みが無い署名でも同じである。
 (match-define (list 'fail bare-key _n _d)
   (type-of/raw
    '(Lam User f (x) x) '()
    (list (list 'f '(NFn ((ForallRegion (a) Int)) Int () ())))))
 (check-equal? bare-key 'invalid-callables))

(test-case
 "ForallRegion の中身が NFn でない行は入口で落ちる"
 (match-define (list 'fail key _node _details)
   (type-of/raw '(Lam User f (x) x) '()
                (list (list 'f '(ForallRegion (a) Int)))))
 (check-equal? key 'invalid-callables))

(test-case
 "NFn の行は今日と同じに通る"
 (check-equal?
  (type-of/raw '(Lam User f (x) x) '() (list (list 'f NFN)))
  `(ok (,NFN ()))))

;; spec §5.7。展開補助は束縛の数を検査し、位置で対応させる。

(test-case
 "unwrap-forall-region が binder 文脈へ位置で対応させる"
 (check-equal?
  (unwrap-forall-region
   '(ForallRegion (a b) (NFn ((Borrowed Int (RParam a))) (Borrowed Int (RParam b))
                             () ()))
   '(p.0 p.1))
  '(NFn ((Borrowed Int (RParam p.0))) (Borrowed Int (RParam p.1)) () ())))

(test-case
 "unwrap-forall-region は文脈が無い形と数が合わない形で #f を返す"
 (define signature '(ForallRegion (a) (NFn (Int) Int () ())))
 (check-false (unwrap-forall-region signature #f))
 (check-false (unwrap-forall-region signature '()))
 (check-false (unwrap-forall-region signature '(p.0 p.1)))
 ;; 包まれていない署名も #f である。呼び側が NFn の節で扱う。
 (check-false (unwrap-forall-region '(NFn (Int) Int () ()) '(p.0))))

;; spec §5.3、§5.7。RegionLam の型付けと展開。

(define forall-callables
  '((g (ForallRegion (a) (NFn ((Borrowed Int (RParam a))) Int () ())))))

(define boundary-callables
  '((outer (NFn (Int) Int () ()))
    (g (ForallRegion (b) (NFn (Int) Int () ())))))

;; 段 A では region 多相な再帰関数を扱わない。
;; Recur の 2 つの入口は署名の ForallRegion を剥がさないため、
;; 表に ForallRegion の行を持つ Recur は unknown-callable で落ちる。
;; 落ちる形そのものを固定して、剥がす作りが入るまで素通りしないようにする。
(test-case
 "region 多相な署名を持つ Recur が unknown-callable で落ちる"
 (define callables
   '((g (ForallRegion (a) (NFn (Int) Int () ())))))
 ;; Recur は (Recur cid f (x ...) c c) であり、本体と継続の 2 つを取る。
 (define core
   '(Scope ()
           (Recur g f (n) n 0)))
 (define ir (build-region-ir core))
 (check-equal?
  (match (type-of/raw core '() callables '()
                       (region-ctx ir '() (hash) (hash)))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok])
  'unknown-callable))

(test-case
 "RegionLam の型が本体の型を ForallRegion で包み直す"
 (match-define (list 'ok (list type _row))
   (type-of/raw '(RegionLam (a) (Lam User g (x) 1)) '() forall-callables))
 (match-define `(ForallRegion (,binder)
                  (NFn ((Borrowed Int (RParam ,used))) Int () ()))
   type)
 (check-equal? used binder))

(test-case
 "囲う RegionLam が無い Lam は ForallRegion の署名で unknown-callable になる"
 (match-define (list 'fail key _node _details)
   (type-of/raw '(Lam User g (x) 1) '() forall-callables))
 (check-equal? key 'unknown-callable))

(test-case
 "束縛の数が署名と合わない RegionLam も unknown-callable になる"
 (match-define (list 'fail key _node _details)
   (type-of/raw '(RegionLam (a b) (Lam User g (x) 1)) '() forall-callables))
 (check-equal? key 'unknown-callable))

(test-case
 "入れ子の Lam は外側の binder 文脈を引き継がない"
 (define nested
   '((g (ForallRegion (a) (NFn ((Borrowed Int (RParam a))) Int () ())))
     (h (ForallRegion (a) (NFn (Int) Int () ())))))
 (match-define (list 'fail key _node _details)
   (type-of/raw '(RegionLam (a) (Lam User g (x) (Apply (Lam User h (y) 1) 1)))
                '() nested))
 (check-equal? key 'unknown-callable))

;; spec §5.3。RegionApp の段 1 の 2 つの検査。

(test-case
 "実引数の数が束縛の数と合わない"
 (match-define (list 'fail key _node details)
   (type-of/raw '(RegionApp (RegionLam (a) (Lam User g (x) 1)) (0 0))
                '() forall-callables))
 (check-equal? key 'region-app-arity)
 (check-equal? details '(1 2)))

(test-case
 "関数側が region 多相でない"
 (match-define (list 'fail key _node details)
   (type-of/raw '(RegionApp 1 (0)) '() '()))
 (check-equal? key 'region-app-non-forall)
 (check-equal? details '(Int)))

;; spec §5.6。実引数の生存は段 3 で IR を見て判定する。
(define (region-arg-core-with rho)
  `(Scope ()
          (Yield (Scope () 0)
                 (RegionApp (RegionLam (a) (Lam User g (x) 1)) (,rho)))))
(define region-arg-ir
  (build-region-ir (erase-core (region-arg-core-with 0))))
(define region-arg-ctx
  (region-ctx region-arg-ir '() (hash) (hash)))
(define region-arg-inner-rho
  (region->rho region-arg-ir (region-at region-arg-ir '(0 0))))
(define region-arg-outer-rho
  (region->rho region-arg-ir (region-at region-arg-ir '(0 1))))

(test-case
 "内側の region を外の位置へ渡すと region-arg-not-live になる"
 (match-define (list 'fail key _node details)
   (type-of/raw (region-arg-core-with region-arg-inner-rho)
                '() forall-callables '() region-arg-ctx))
 (check-equal? key 'region-arg-not-live)
 (check-equal? details '()))

(test-case
 "外側の region を同じ位置へ渡すと通り、束縛が実引数へ置き換わる"
 (match-define (list 'ok (list type _row))
   (type-of/raw (region-arg-core-with region-arg-outer-rho)
                '() forall-callables '() region-arg-ctx))
 (check-equal? type
              `(NFn ((Borrowed Int ,region-arg-outer-rho)) Int () ())))

(test-case
 "外側の RParam を内側の RegionApp へ渡す"
 (define nested-core
   '(Scope ()
           (Yield (Scope () 0)
                  (RegionLam (a)
                    (RegionApp (RegionLam (b) (Lam User g (x) 1))
                               ((RParam a)))))))
 (define nested-ir (build-region-ir (erase-core nested-core)))
 (define nested-ctx (region-ctx nested-ir '() (hash) (hash)))
 ;; spec §5.6。実引数が束縛中の rp なら、外側の適用位置で既に生存が
 ;; 検査されている。適用位置はその内側なので生存は保たれる。
 (match-define (list 'ok (list type _row))
   (type-of/raw nested-core '() forall-callables '() nested-ctx))
 (match-define `(ForallRegion (,binder)
                  (NFn ((Borrowed Int (RParam ,used))) Int () ()))
   type)
 (check-equal? used binder))

(test-case
 "内側の binder の rp を実引数へ書くと落ちる"
 (define outside-core
   '(Scope ()
           (Yield (Scope () 0)
                  (RegionLam (a)
                    (RegionApp (RegionLam (b) (Lam User g (x) 1))
                               ((RParam b)))))))
 (define outside-ir (build-region-ir (erase-core outside-core)))
 (define outside-ctx (region-ctx outside-ir '() (hash) (hash)))
 ;; 実引数の位置は (RegionLam (b) ...) の外側なので b は束縛されていない。
 (match-define (list 'fail key _node _details)
   (type-of/raw outside-core '() forall-callables '() outside-ctx))
 (check-equal? key 'region-arg-not-live))

(test-case
 "どの binder も束縛していない rp を実引数へ書くと落ちる"
 (define unbound-core
   '(Scope ()
           (Yield (Scope () 0)
                  (RegionApp (RegionLam (b) (Lam User g (x) 1))
                             ((RParam z))))))
 (define unbound-ir (build-region-ir (erase-core unbound-core)))
 (define unbound-ctx (region-ctx unbound-ir '() (hash) (hash)))
 (match-define (list 'fail key _node _details)
   (type-of/raw unbound-core '() forall-callables '() unbound-ctx))
 (check-equal? key 'region-arg-not-live))

(test-case
 "Lam の境界を越えた RParam の RegionApp は落ちる"
 (define boundary-core
   '(Scope ()
           (Yield (Scope () 0)
                  (RegionLam (a)
                    (Lam User outer (z)
                         (Let (r let (NFn (Int) Int () ()))
                              (RegionApp
                               (RegionLam (b) (Lam User g (x) 1))
                               ((RParam a)))
                              1))))))
 (define boundary-ir (build-region-ir (erase-core boundary-core)))
 (define boundary-ctx (region-ctx boundary-ir '() (hash) (hash)))
 ;; Lam の本体では bound-region-params が空へ戻るため、閉包の外側へ
 ;; 持ち出せる前提の委譲は成立せず E-REG-003 になる。
 (match-define (list 'fail key _node _details)
   (type-of/raw boundary-core '() boundary-callables '() boundary-ctx))
 (check-equal? key 'region-arg-not-live))

(test-case
 "RecurVal の境界を越えた RParam の RegionApp は落ちる"
 (define recur-value-core
   '(Scope ()
           (Yield (Scope () 0)
                  (RegionLam (a)
                    (RecurVal outer h (z)
                      (Let (r let (NFn (Int) Int () ()))
                           (RegionApp
                            (RegionLam (b) (Lam User g (x) 1))
                            ((RParam a)))
                           1))))))
 (define recur-value-ir
   (build-region-ir (erase-core recur-value-core)))
 (define recur-value-ctx
   (region-ctx recur-value-ir '() (hash) (hash)))
 (match-define (list 'fail key _node _details)
   (type-of/raw recur-value-core '() boundary-callables '() recur-value-ctx))
 (check-equal? key 'region-arg-not-live))

(test-case
 "Recur の境界を越えた RParam の RegionApp は落ちる"
 (define recur-core
   '(Scope ()
           (Yield (Scope () 0)
                  (RegionLam (a)
                    (Recur outer h (z)
                      (Let (r let (NFn (Int) Int () ()))
                           (RegionApp
                            (RegionLam (b) (Lam User g (x) 1))
                            ((RParam a)))
                           1)
                      0)))))
 (define recur-ir (build-region-ir (erase-core recur-core)))
 (define recur-ctx (region-ctx recur-ir '() (hash) (hash)))
 (match-define (list 'fail key _node _details)
   (type-of/raw recur-core '() boundary-callables '() recur-ctx))
 (check-equal? key 'region-arg-not-live))

(test-case
 "ir が無い Λ では実引数の生存を示せないため落とす"
 (match-define (list 'fail key _node _details)
   (type-of/raw '(RegionApp (RegionLam (a) (Lam User g (x) 1)) (0))
                '() forall-callables))
 (check-equal? key 'region-arg-not-live))

(test-case
 "region-arg-collector を忘れた経路は要求を捨てず error にする"
 (check-exn #px"region-arg-collector が parameterize されていない"
            (lambda ()
              (emit-region-arg-request! 0 '() 'node))))

#lang racket

(require rackunit
         "../typing.rkt"
         "../region-param.rkt")

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

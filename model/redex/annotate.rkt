#lang racket

(provide annotate-core
         annotate-surface)

;; 前順の通し番号で #:synthetic の空 span を作る。同じ入力からは常に同じ並びになる。
;; sourceId を差し替えられるようにしない。持ち上げる fixture は source text を
;; 持たず、利用者の sourceId を与えると実在しない coordinate を作ってしまう。
(define (make-span-source)
  (define counter (box 0))
  (λ ()
    (define i (unbox counter))
    (set-box! counter (add1 i))
    (list '#:span '#:synthetic i i)))

(define (literal? t)
  (or (exact-integer? t) (string? t) (eq? t 'unit)))

(define (annotate-core t)
  (define next (make-span-source))
  (define (ann t)
    (match t
      [(? literal?) (list '#:lit t (next))]
      [(? symbol?) (list '#:var t (next))]
      [(list 'Apply c ...) (list* 'Apply (next) (map ann c))]
      [(list 'Let (list x type) c_1 c_2)
       (list 'Let (next) (list (bind x) (ty type)) (ann c_1) (ann c_2))]
      [(list 'Construct type K c ...)
       (list* 'Construct (next) (ty type) K (map ann c))]
      [(list 'Eliminate c (list br ...))
       (list 'Eliminate (next) (ann c) (map ann-br br))]
      [(list 'Perform op c) (list 'Perform (next) (ann-op op) (ann c))]
      [(list 'Handle op h c)
       (list 'Handle (next) (ann-op op) (ann-h h) (ann c))]
      [(list 'Scope pi c) (list 'Scope (next) pi (ann c))]
      [(list 'Recur cid f (list x ...) c_1 c_2)
       (list 'Recur (next) cid (bind f) (map bind x) (ann c_1) (ann c_2))]
      [(list 'Yield c_1 c_2) (list 'Yield (next) (ann c_1) (ann c_2))]
      [(list 'Suspend c) (list 'Suspend (next) (ann c))]
      [(list 'Move w) (list 'Move (next) (ann w))]
      [(list 'Drop c) (list 'Drop (next) (ann c))]
      [(list 'Curry c_1 c_2) (list 'Curry (next) (ann c_1) (ann c_2))]
      [(list 'OwnLeaf c) (list 'OwnLeaf (next) (ann c))]
      [(list 'resource n) (list 'resource (next) n)]
      [(list 'Lam O cid (list x ...) c)
       (list 'Lam (next) O cid (map bind x) (ann c))]
      [(list 'PrimVal O nm) (list 'PrimVal (next) O nm)]
      [(list 'CurryVal O v_1 v_2) (list 'CurryVal (next) O (ann v_1) (ann v_2))]
      [(list 'RecurVal cid f (list x ...) c)
       (list 'RecurVal (next) cid (bind f) (map bind x) (ann c))]
      [(list 'TypeRep O t kappa) (list 'TypeRep (next) O t kappa)]
      [(list 'ProofRep O phi) (list 'ProofRep (next) O phi)]
      [(list 'Let (list x bmode type) c_1 c_2)
       (list 'Let (next) (list (bind x) bmode (ty type)) (ann c_1) (ann c_2))]
      [(list 'Rec (list (list label m c) ...))
       (list 'Rec (next) (for/list ([l (in-list label)]
                                    [mode (in-list m)]
                                    [body (in-list c)])
                           (list (lbl l) mode (ann body))))]
      [(list 'Proj c label) (list 'Proj (next) (ann c) (lbl label))]
      [(list 'Discharge (list 'ProofRep O phi) c)
       (list 'Discharge (next) (list 'ProofRep (next) O phi) (ann c))]
      [(list 'UVal v) (list 'UVal (next) (ann v))]
      [(list 'RVal (list 'ProofRep O phi) v)
       (list 'RVal (next) (list 'ProofRep (next) O phi) (ann v))]
      [_ (error 'annotate-core "未対応の production: ~a" t)]))
  (define (bind x) (list '#:bind x (next)))
  (define (lbl label) (list '#:lbl label (next)))
  (define (ty type) (list '#:ty type (next)))
  (define (ann-op op)
    (match op
      [(list 'Return b type) (list 'Return b (ty type))]
      [_ (error 'annotate-core "未対応の op: ~a" op)]))
  (define (ann-br br)
    (match br
      [(list K (list x ...) '-> c)
       (list (next) K (map bind x) '-> (ann c))]
      [_ (error 'annotate-core "未対応の br: ~a" br)]))
  (define (ann-h h)
    (match h
      [(list x '-> c) (list (next) (bind x) '-> (ann c))]
      [_ (error 'annotate-core "未対応の h: ~a" h)]))
  (ann t))

(define (annotate-surface t)
  (define next (make-span-source))
  (define (bind x) (list '#:bind x (next)))
  (define (lbl label) (list '#:lbl label (next)))
  (define (ty type) (list '#:ty type (next)))
  (define (ef row) (list '#:ef row (next)))
  (define (ann-ubr ubr)
    (match ubr
      [(list K (list x ...) '-> e)
       (list (next) K (map bind x) '-> (ann e))]
      [_ (error 'annotate-surface "未対応の ubr: ~a" ubr)]))
  (define (ann t)
    (match t
      [(? literal?) (list '#:lit t (next))]
      [(? symbol?) (list '#:var t (next))]
      [(list 'Fn (list (list x type) ...) result row e)
       (list 'Fn (next)
             (for/list ([name (in-list x)] [t_a (in-list type)])
               (list (bind name) (ty t_a)))
             (ty result) (ef row) (ann e))]
      [(list 'Apply e ...) (list* 'Apply (next) (map ann e))]
      [(list 'Let (? symbol? x) e_1 e_2)
       (list 'Let (next) (bind x) (ann e_1) (ann e_2))]
      [(list 'Let (list x bmode type) e_1 e_2)
       (list 'Let (next) (list (bind x) bmode (ty type)) (ann e_1) (ann e_2))]
      [(list 'Rec (list (list label m e) ...))
       (list 'Rec (next) (for/list ([l (in-list label)]
                                    [mode (in-list m)]
                                    [body (in-list e)])
                           (list (lbl l) mode (ann body))))]
      [(list 'Proj e label) (list 'Proj (next) (ann e) (lbl label))]
      [(list 'Construct K (list 'Types type ...) e ...)
       (list* 'Construct (next) K
              (cons 'Types (map ty type))
              (map ann e))]
      [(list 'Construct K e ...) (list* 'Construct (next) K (map ann e))]
      [(list 'Eliminate e (list ubr ...))
       (list 'Eliminate (next) (ann e) (map ann-ubr ubr))]
      [(list 'Return e) (list 'Return (next) (ann e))]
      [(list 'NarrativeExpr e) (list 'NarrativeExpr (next) (ann e))]
      [(list 'Recur f (list (list x type) ...) result row e_1 e_2)
       (list 'Recur (next) (bind f)
             (for/list ([name (in-list x)] [t_a (in-list type)])
               (list (bind name) (ty t_a)))
             (ty result) (ef row) (ann e_1) (ann e_2))]
      [(list 'Yield e_1 e_2) (list 'Yield (next) (ann e_1) (ann e_2))]
      [(list 'Suspend e) (list 'Suspend (next) (ann e))]
      [(list 'Move x) (list 'Move (next) (ann x))]
      [(list 'Drop e) (list 'Drop (next) (ann e))]
      [(list 'Curry e_1 e_2) (list 'Curry (next) (ann e_1) (ann e_2))]
      [(list 'TypeMake spec) (list 'TypeMake (next) (ty spec))]
      [(list 'LetType T (list 'TypeMake spec) e)
       (list 'LetType (next) T (list 'TypeMake (next) (ty spec)) (ann e))]
      [_ (error 'annotate-surface "未対応の production: ~a" t)]))
  (ann t))

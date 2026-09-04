#lang racket

(require rackunit
         "../classify.rkt")

(define structural-callables
  '((list-loop-id (NFn ((List Int)) Int () ()))))

(define structural-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> (Apply loop tail))))
          (Apply loop (Construct (List Int) nil))))

(test-case "REC-001: no recursion and structural descent are Finite"
  (check-equal? (classify '(Apply (PrimVal (Reserved o-add) add) 1 2)
                          '() '())
                '(Finite no-recursion))
  (check-equal? (classify structural-loop '() structural-callables)
                '(Finite structural))

  ;; The non-recursive mapper comes from the outer elaboration Γ.
  (define map-environment
    '((mapper (NFn (Int) Int () ()))))
  (define map-callables
    '((map-loop-id (NFn ((List Int)) (List Int) () ()))))
  (define map-loop
    '(Recur map-loop-id go (values)
            (Eliminate values
             ((nil () -> (Construct (List Int) nil))
              (cons (head tail) ->
                    (Construct (List Int) cons
                               (Apply mapper head)
                               (Apply go tail)))))
            (Apply go (Construct (List Int) nil))))
  (check-equal? (classify map-loop map-environment map-callables)
                '(Finite structural)))

(test-case "REC-001: structural calls require one common decreasing position"
  (define callables
    '((pair-loop-id
       (NFn ((List Int) (List Int) Bool) Int () ()))))
  (define no-common-position
    '(Recur pair-loop-id loop (xs ys choose-left)
            (Eliminate choose-left
             ((true () ->
                    (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Apply loop tail ys choose-left)))))
              (false () ->
                     (Eliminate ys
                      ((nil () -> 0)
                       (cons (head tail) ->
                             (Apply loop xs tail choose-left)))))))
            (Apply loop (Construct (List Int) nil)
                   (Construct (List Int) nil)
                   (Construct Bool true))))
  (check-equal? (classify no-common-position '() callables) 'Unknown))

(test-case "REC-001: structural descent follows fields, not arbitrary uses of f"
  (define callables
    '((nested-loop-id (NFn ((List Int)) Int () ()))))
  (define nested-descent
    '(Recur nested-loop-id loop (values)
            (Eliminate values
             ((nil () -> 0)
              (cons (head tail) ->
                    (Eliminate tail
                     ((nil () -> 0)
                      (cons (next rest) -> (Apply loop rest)))))))
            (Apply loop (Construct (List Int) nil))))
  (check-equal? (classify nested-descent '() callables)
                '(Finite structural))

  (define non-call-use
    '(Recur curry-loop-id loop (left right)
            (Let (saved (NFn (Int) Int () ()))
                 (Curry loop left)
                 0)
            (Apply loop 0 0)))
  (check-equal?
   (classify non-call-use '()
             '((curry-loop-id (NFn (Int Int) Int () ()))))
   'Unknown))

(define guarded-callables
  '((nats-id (NFn (Int) Unit ((Yield Int)) ()))))

(define guarded-loop
  '(Recur nats-id nats (n)
          (Yield n
                 (Apply nats
                        (Apply (PrimVal (Reserved o-add) add) n 1)))
          (Apply nats 0)))

(test-case "REC-002: Yield followed by a tail call is Productive"
  (check-equal? (classify guarded-loop '() guarded-callables)
                '(Productive guarded)))

(test-case "REC-002: f-free and Suspend bodies are not guards"
  (define callables '((loop-id (NFn () Unit (Partial) ()))))
  (check-equal?
   (classify '(Recur loop-id loop () unit (Apply loop)) '() callables)
   'Unknown)
  (check-equal?
   (classify
    '(Recur loop-id loop () (Suspend (Apply loop)) (Apply loop))
    '() callables)
   'Unknown))

(test-case "REC-002: a guarded body still requires the initial tail call"
  (define callables
    '((loop-id (NFn () Unit ((Yield Int)) ()))))
  (check-equal?
   (classify
    '(Recur loop-id loop ()
            (Yield 1 (Apply loop))
            unit)
    '() callables)
   'Unknown))

(define (guard-component-loop callable callee-labels)
  (define callables
    `((,callable (NFn () Unit (,@callee-labels (Yield Int)) ()))
      (callee-id (NFn () Int ,callee-labels ()))))
  (define environment
    `((callee (NFn () Int ,callee-labels ()))))
  (values
   `(Recur ,callable loop ()
           (Yield (Apply callee) (Apply loop))
           (Apply loop))
   environment
   callables))

(test-case "REC-002: guard components reject Own and Return, not Compile"
  (define-values (own-loop own-environment own-callables)
    (guard-component-loop 'own-loop-id '(Own)))
  (check-equal?
   (classify own-loop own-environment own-callables)
   'Unknown)

  (define-values (return-loop return-environment return-callables)
    (guard-component-loop
     'return-loop-id '((Return outer-boundary Int))))
  (check-equal?
   (classify return-loop return-environment return-callables)
   'Unknown)

  (define-values (compile-loop compile-environment compile-callables)
    (guard-component-loop 'compile-loop-id '(Compile)))
  (check-equal?
   (classify compile-loop compile-environment compile-callables)
   '(Productive guarded)))

(test-case "REC-001/REC-002: pre rejects nested Partial and Yield rows"
  (for ([labels (in-list '((Partial) ((Yield Int))))]
        [callable (in-list '(partial-outer-id yield-outer-id))])
    (define-values (core environment callables)
      (guard-component-loop callable labels))
    (check-equal? (classify core environment callables) 'Unknown))

  (for ([inner-row (in-list '((Partial) ((Yield Int))))]
        [outer-id (in-list '(nested-partial-id nested-yield-id))]
        [inner-id (in-list '(inner-partial-id inner-yield-id))])
    (define inner-body
      (if (member 'Partial inner-row)
          1
          `(Yield 1 (Apply inner))))
    (define outer-row
      (if (member 'Partial inner-row)
          '(Partial (Yield Int))
          '((Yield Int))))
    (define core
      `(Recur ,outer-id outer ()
              (Yield
               (Recur ,inner-id inner ()
                      ,inner-body
                      (Apply inner))
               (Apply outer))
              (Apply outer)))
    (define callables
      `((,outer-id (NFn () Unit ,outer-row ()))
        (,inner-id (NFn () Int ,inner-row ()))))
    (check-equal? (classify core '() callables) 'Unknown)))

(test-case "PRF-002/PRF-003: type equality is structural and opaque"
  (check-true
   (type-equiv?
    '(NFn ((List Int)) (Proof TypeNarrativeCap)
          (Own (Yield Int)) ())
    '(NFn ((List Int)) (Proof TypeNarrativeCap)
          ((Yield Int) Own) ())))
  (check-false
   (type-equiv? '(Proof TypeNarrativeCap)
                '(Proof ValidNarrativeTrait)))

  ;; This zero-argument Recur is conservatively Unknown but reduces to unit.
  ;; Opaque comparison must not normalize it to the second type expression.
  (define unknown-calculation
    '(Recur opaque-id compute () unit unit))
  (check-equal? (classify unknown-calculation '()
                          '((opaque-id (NFn () Unit () ()))))
                'Unknown)
  (check-true
   (type-equiv? `(Opaque ,unknown-calculation)
                `(Opaque ,unknown-calculation)))
  (check-false
   (type-equiv? `(Opaque ,unknown-calculation)
                '(Opaque unit))))

;; G5c5c。署名そのものが ForallRegion である再帰の分類。
(define region-structural-callables
  '((rlist-loop-id (ForallRegion (a)
                     (NFn ((List Int) (BorrowedMut Int (RParam a)))
                          Int () ())))))

(define region-structural-loop
  '(Recur rlist-loop-id loop (xs r)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> (Apply loop tail r))))
          (Apply (RegionApp loop ((RParam a)))
                 (Construct (List Int) nil) r)))

(define region-guarded-callables
  '((rnats-id (ForallRegion (a) (NFn (Int) Unit ((Yield Int)) ())))))

(define region-guarded-loop
  '(Recur rnats-id nats (n)
          (Yield n
                 (Apply nats
                        (Apply (PrimVal (Reserved o-add) add) n 1)))
          (Apply (RegionApp nats ((RParam a))) 0)))

(test-case "G5c5c: region 多相な再帰も構造的減少と保護つきで分類できる"
  (check-equal? (classify region-structural-loop '()
                          region-structural-callables)
                '(Finite structural))
  (check-equal? (classify region-guarded-loop '() region-guarded-callables)
                '(Productive guarded)))

;; G5c5c。再帰の中に対象でない region 多相な関数の呼出しがある場合。
(define region-other-call-environment
  '((bump (ForallRegion (b) (NFn (Int) Int () ())))))

(define region-other-call-loop
  '(Recur rlist-loop-id loop (xs r)
     (Eliminate xs
       ((nil () -> (Apply (RegionApp bump ((RParam a))) 0))
        (cons (head tail) -> (Apply loop tail r))))
     (Apply (RegionApp loop ((RParam a)))
            (Construct (List Int) nil) r)))

(test-case "G5c5c: 対象でない region 多相な呼出しがあっても分類できる"
  (check-equal? (classify region-other-call-loop
                          region-other-call-environment
                          region-structural-callables)
                '(Finite structural)))

;; G5c5c。項の中に RegionLam を置いた場合。3 つの走査に RegionLam の節が
;; 無いと、この形は分類できない。
(define region-lam-environment
  '((plus1 (NFn (Int) Int () ()))))

(define region-lam-loop
  '(Recur rlist-loop-id loop (xs r)
     (Eliminate xs
       ((nil () -> (Apply (RegionApp (RegionLam (b) plus1) ((RParam a))) 0))
        (cons (head tail) -> (Apply loop tail r))))
     (Apply (RegionApp loop ((RParam a)))
            (Construct (List Int) nil) r)))

(test-case "G5c5c: 項の中の RegionLam を越えて分類できる"
  (check-equal? (classify region-lam-loop
                          region-lam-environment
                          region-structural-callables)
                '(Finite structural)))

(test-case "G5c5c: Lam は ForallRegion を剥がさない"
  (check-equal?
   (classify
    '(Recur list-loop-id loop (values)
       (Eliminate values
        ((nil () -> (Lam User f (x) 0))
         (cons (head tail) -> (Apply loop tail))))
       (Apply loop (Construct (List Int) nil)))
    '((f (ForallRegion (a) (NFn (Int) Int () ()))))
    structural-callables)
   'Unknown))

(test-case "G5c5c: RegionLam 内の再帰呼出しを見落とさない"
  ;; RegionLam の内側に減少しない再帰呼出しを置く。target-uses がこの
  ;; 位置を歩かないと、guard component が target-free と誤認される。
  (check-equal?
   (classify
    '(Recur nats-id nats (n)
       (Yield n
              (Apply nats
                     (RegionLam (a)
                       (Let (u let Unit) (Apply nats 1) 0))))
       (Apply nats 0))
    '() guarded-callables)
   'Unknown))

(test-case "G5c5c: 継続の包みの数が署名と合わないと保護つきにならない"
  ;; 形 ii なのに継続が包みを剥がさずに呼ぶ。
  (check-equal?
   (classify '(Recur rnats-id nats (n)
                     (Yield n
                            (Apply nats
                                   (Apply (PrimVal (Reserved o-add) add)
                                          n 1)))
                     (Apply nats 0))
             '() region-guarded-callables)
   'Unknown)
  ;; 形 i なのに継続が包みを剥がす。
  (check-equal?
   (classify '(Recur nats-id nats (n)
                     (Yield n
                            (Apply nats
                                   (Apply (PrimVal (Reserved o-add) add)
                                          n 1)))
                     (Apply (RegionApp nats ((RParam a))) 0))
             '() guarded-callables)
   'Unknown))

(define c4-owned-callables
  '((c4-owned-loop-id (NFn ((Owned (List Int))) Int () ()))))

(define c4-owned-loop
  '(Recur c4-owned-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> 0)))
          (Apply loop (Construct (Owned (List Int)) nil))))

(test-case "C4-002: Owned を包んだ走査対象の Eliminate が分類できる"
  (check-equal? (classify c4-owned-loop '() c4-owned-callables)
                '(Finite structural)))

(define (c4-borrowed-callables wrapper)
  `((c4-borrowed-loop-id (NFn (,wrapper) Int () ()))))

(define (c4-borrowed-loop wrapper)
  `(Recur c4-borrowed-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> (Apply loop tail))))
          (Apply loop (Construct ,wrapper nil))))

;; 欄の rewrap を落とすと、Borrowed で包まれた関数を素の NFn として
;; 誤って適用できる。latent-row-safe? がこの差を検出する fixture である。
;; Unknown は latent-row-safe? の fail-closed な既定によるため、包みつきの関数欄を
;; 将来受理する変更を入れるときは、この期待値も見直す。
(define c4-borrowed-function-type
  '(Borrowed (Option (NFn (Int) Int () ())) 0))

(define c4-borrowed-function-loop
  `(Recur c4-borrowed-loop-id loop (xs)
          (Eliminate xs
                     ((none () -> 0)
                      (some (f) -> (Apply f 0))))
          (Apply loop (Construct ,c4-borrowed-function-type none))))

(define (c4-borrowed-function-callables type)
  `((c4-borrowed-loop-id (NFn (,type) Int () ()))))

(test-case "C4-006c: 分類器は Borrowed を剥がし BorrowedMut を剥がさない"
  (check-equal?
   (classify (c4-borrowed-loop '(Borrowed (List Int) 0))
             '()
             (c4-borrowed-callables '(Borrowed (List Int) 0)))
   '(Finite structural))
  (check-equal?
   (classify c4-borrowed-function-loop
             '()
             (c4-borrowed-function-callables c4-borrowed-function-type))
   'Unknown)
  (check-equal?
   (classify (c4-borrowed-loop '(BorrowedMut (List Int) 0))
             '()
             (c4-borrowed-callables '(BorrowedMut (List Int) 0)))
   'Unknown))

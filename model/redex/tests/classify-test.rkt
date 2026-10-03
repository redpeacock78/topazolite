#lang racket

(require rackunit
         racket/match
         "../classify.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt")

(define (classify-ucore source)
  (match (elab source)
    [(list core _ _ callables) (classify (erase-core core) '() callables)]
    [`(err ,_) 'elaboration-error]))

(define (elaborate-code-of source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define structural-callables
  '((list-loop-id (NFn ((List Int)) Int () () () User))))

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
    '((mapper (NFn (Int) Int () () () User))))
  (define map-callables
    '((map-loop-id (NFn ((List Int)) (List Int) () () () User))))
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

(define union-list-type '(Union (List Int) String))
(define union-list-callables
  `((union-list-loop-id (NFn (,union-list-type) Int () () () User))))
(define union-list-loop
  `(Recur union-list-loop-id loop (xs)
     (UnionEliminate xs
       (((List Int) items ->
         (Eliminate items
           ((nil () -> 0)
            (cons (head tail) ->
              (Apply loop (UnionInject ,union-list-type (List Int) tail))))))
        (String text -> 0)))
     (Apply loop
       (UnionInject ,union-list-type (List Int)
                    (Construct (List Int) nil)))))
(define union-list-loop-extra-recursion
  `(Recur union-list-loop-id loop (xs)
     (UnionEliminate xs
       (((List Int) items ->
         (Eliminate items
           ((nil () -> 0)
            (cons (head tail) ->
              (Apply loop (UnionInject ,union-list-type (List Int) tail))))))
        (String text -> 0)
        (Bool extra -> (Apply loop xs))))
     (Apply loop
       (UnionInject ,union-list-type (List Int)
                    (Construct (List Int) nil)))))

(test-case "REC-001: UnionEliminate の payload は構造的減少で全枝を調べる"
  (check-equal? (classify union-list-loop '() union-list-callables)
                '(Finite structural))
  (check-equal?
   (classify union-list-loop-extra-recursion '() union-list-callables)
   'Unknown))

(define union-yield-callables
  '((union-yield-id (NFn ((Union Int String)) Unit () ((Yield Int)) () User))))
(define union-yield-loop
  '(Recur union-yield-id loop (value)
     (UnionEliminate value
       ((Int number -> (Yield number (Apply loop value)))
        (String text -> (Yield 0 (Apply loop value)))))
     (Apply loop initial)))

(test-case "REC-002: guarded-body? は UnionEliminate の全枝を調べる"
  (check-equal?
   (classify union-yield-loop '((initial (Union Int String)))
             union-yield-callables)
                '(Productive guarded)))

(test-case "REC-001: spec §4.1 の Partial の knot は Finite にならない"
  (check-equal?
   (classify-ucore
    '(Let (cell mut (NFn (Int) Int (Partial) ())) (Fn ((x Int)) Int () x)
       (Let f (Fn ((y Int)) Int (Partial) (Apply cell y))
         (Let ignored (Reassign cell f) (Apply cell 1)))))
   'Unknown))

(test-case "REC-001: 環境の Partial の callable を Recur 無しで呼ぶ項は Unknown"
  (check-equal?
   (classify '(Apply loop-id unit)
             '((loop-id (NFn () Unit () (Partial) () User)))
             '())
   'Unknown))

(test-case "REC-001: 環境の Yield の callable を Recur 無しで呼ぶ項は Unknown"
  (check-equal?
   (classify '(Apply gen-id unit)
             '((gen-id (NFn () Unit () ((Yield Int)) () User)))
             '())
   'Unknown))

(test-case "REC-001: Partial の slot を呼ぶ手書きの Core は Unknown"
  (check-equal?
   (classify '(Let (cell mut (NFn (Int) Int () (Partial) () User)) g0
                (Let (ignored Unit) (Reassign cell f) (Apply cell 1)))
             '((g0 (NFn (Int) Int () (Partial) () User))
               (f (NFn (Int) Int () (Partial) () User)))
             '())
   'Unknown))

(test-case "REC-001: Partial の callable を continuation で呼ぶだけなら gate は Partial を求めない"
  (define source
    '(Let (cell mut (NFn (Int) Int (Partial) ())) (Fn ((x Int)) Int () x)
       (Recur h ((y Int)) Int () y
         (Apply cell 1))))
  (check-equal? (elaborate-code-of source) 'ok)
  ;; whole-term は継続の Partial を見るので Unknown のままである。
  (check-equal? (classify-ucore source) 'Unknown))

;; P2i3b spec §6.1。継続の無関係な Partial は f の宣言 row に載せない。
(test-case "REC-001: 継続にある別の Recur の Partial は f の gate に効かない"
  (define source
    '(Let p (Recur g () Unit (Partial Suspend) (Suspend (Apply g)) g)
       (Recur f () Unit () unit (Apply p))))
  (check-equal? (elaborate-code-of source) 'ok)
  (check-equal? (classify-ucore source) 'Unknown))

(test-case "REC-001: 継続が f を値として返す structural な本体は Partial なしで通る"
  (define source
    '(Recur loop ((xs (List Int))) Int ()
            (Eliminate xs
             ((nil () -> 0)
              (cons (head tail) -> (Apply loop tail))))
            loop))
  (check-equal? (elaborate-code-of source) 'ok)
  (check-equal? (classify-ucore source) 'Unknown))

(test-case "REC-002: 継続が f の適用でない guarded な本体は Partial なしで通る"
  (define source
    '(Recur nats ((n Int)) Unit ((Yield Int))
            (Yield n (Apply nats (Apply add n 1)))
            nats))
  (check-equal? (elaborate-code-of source) 'ok)
  (check-equal? (classify-ucore source) 'Unknown))

(test-case "REC-001: 本体が Unknown の Recur は E-REC-002 のまま"
  (check-equal?
   (elaborate-code-of
    '(Recur loop ((n Int)) Int () (Apply loop n) (Apply loop 0)))
   (diagnostic-code-of 'elaborate 'unknown-recur-requires-partial))
  ;; 推論の節。本体が Yield の callable を呼ぶので B-NoSelf にならない。
  (check-equal?
   (elaborate-code-of
    '(Let k (Fn () Unit ((Yield Int)) (Yield 1 unit))
       (Recur h ((y Int)) #:infer ((Yield Int)) (Apply k) 0)))
   (diagnostic-code-of 'elaborate 'unknown-recur-requires-partial)))

(test-case "REC-001: gate の helper 化で診断の順序が変わらない"
  ;; 継続の検査は gate より先に出る。
  (check-equal?
   (elaborate-code-of
    '(Recur loop ((n Int)) Int () (Apply loop n) (Apply 1 0)))
   (elaborate-code-of '(Apply 1 0)))
  ;; 本体の row の検査は gate より先に出る。
  (check-equal?
   (elaborate-code-of
    '(Recur loop ((n Int)) Int ()
            (Let z (Yield 1 unit) (Apply loop n))
            (Apply loop 0)))
   (diagnostic-code-of 'elaborate 'undeclared-recur-effect)))

;; P2i3a の knot は、gate が本体だけを見るようになっても書込みで落ちる。
(test-case "REC-001: Recur の外で純粋な slot に h を書く knot は E-TYP-027 のまま"
  (check-equal?
   (elaborate-code-of
    '(Let (cell mut (NFn (Int) Int () ())) (Fn ((x Int)) Int () x)
       (Recur h ((y Int)) Int () (Apply cell y)
         (Let ignored (Reassign cell h) (Apply cell 1)))))
   (diagnostic-code-of 'elaborate 'mutable-callable-storage-requires-partial)))

(test-case "REC-001: Recur の外の knot で h の row が Partial なら Unknown"
  (check-equal?
   (classify-ucore
    '(Let (cell mut (NFn (Int) Int (Partial) ())) (Fn ((x Int)) Int () x)
       (Recur h ((y Int)) Int (Partial) (Apply cell y)
         (Let ignored (Reassign cell h) (Apply cell 1)))))
   'Unknown))

(test-case "REC-001: Reassign を含み Partial の callee を呼ばない項は Finite no-recursion"
  (check-equal?
   (classify '(Let (cell mut (NFn (Int) Int () (Partial) () User)) g0
                (Let (ignored Unit) (Reassign cell f) 1))
             '((g0 (NFn (Int) Int () (Partial) () User))
               (f (NFn (Int) Int () (Partial) () User)))
             '())
   '(Finite no-recursion)))

(test-case "REC-001: Borrow した純粋な関数を Read して呼ぶ項は Finite no-recursion"
  (check-equal?
   (classify '(Let (r (Borrowed (NFn (Int) Int () () () User) 0))
                (Borrow g0)
                (Apply (Read r) 1))
             '((g0 (Owned (NFn (Int) Int () () () User))))
             '())
   '(Finite no-recursion)))

(test-case "REC-001: Borrow した Partial の関数を Read して呼ぶ項は Unknown"
  (check-equal?
   (classify '(Let (r (Borrowed (NFn (Int) Int () (Partial) () User) 0))
                (Borrow g0)
                (Apply (Read r) 1))
             '((g0 (Owned (NFn (Int) Int () (Partial) () User))))
             '())
   'Unknown))

(test-case "REC-001: Owned の関数を借用して Read で呼ぶ項は Finite no-recursion"
  (check-equal?
   (classify '(Apply (Read (Borrow f)) 1)
             '((f (Owned (NFn (Int) Int () () () User))))
             '())
   '(Finite no-recursion)))

(test-case "REC-001: structural calls require one common decreasing position"
  (define callables
    '((pair-loop-id
       (NFn ((List Int) (List Int) Bool) Int () () () User))))
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
    '((nested-loop-id (NFn ((List Int)) Int () () () User))))
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
            (Let (saved (NFn (Int) Int () () () User))
                 (Curry loop left)
                 0)
            (Apply loop 0 0)))
  (check-equal?
   (classify non-call-use '()
             '((curry-loop-id (NFn (Int Int) Int () () () User))))
   'Unknown))

(define guarded-callables
  '((nats-id (NFn (Int) Unit () ((Yield Int)) () User))))

(test-case "REC-002: guard の成分が target を借用する Recur は Productive にならない"
  (check-equal?
   (classify '(Recur nats-id nats (n)
                (Yield (Let (alias (Borrowed (NFn (Int) Unit () ((Yield Int)) () User) 0))
                            (Borrow nats)
                            n)
                       (Apply nats (Apply (PrimVal (Reserved o-add) add) n 1)))
                (Apply nats 0))
             '()
             guarded-callables)
   'Unknown))

(define guarded-loop
  '(Recur nats-id nats (n)
          (Yield n
                 (Apply nats
                        (Apply (PrimVal (Reserved o-add) add) n 1)))
          (Apply nats 0)))

(test-case "REC-002: Yield followed by a tail call is Productive"
  (check-equal? (classify guarded-loop '() guarded-callables)
                '(Productive guarded)))

(test-case "REC-002: f-free な本体は C-NoSelf、Suspend の本体は guard にならない"
  (define callables '((loop-id (NFn () Unit () (Partial) () User))))
  (check-equal?
   (classify '(Recur loop-id loop () unit (Apply loop)) '() callables)
   '(Finite no-self-reference))
  (check-equal?
   (classify
    '(Recur loop-id loop () (Suspend (Apply loop)) (Apply loop))
    '() callables)
   'Unknown))

(test-case "REC-002: a guarded body still requires the initial tail call"
  (define callables
    '((loop-id (NFn () Unit () ((Yield Int)) () User))))
  (check-equal?
   (classify
    '(Recur loop-id loop ()
            (Yield 1 (Apply loop))
            unit)
    '() callables)
   'Unknown))

(define (guard-component-loop callable callee-labels)
  (define callables
    `((,callable (NFn () Unit () (,@callee-labels (Yield Int)) () User))
      (callee-id (NFn () Int () ,callee-labels () User))))
  (define environment
    `((callee (NFn () Int () ,callee-labels () User))))
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
      `((,outer-id (NFn () Unit () ,outer-row () User))
        (,inner-id (NFn () Int () ,inner-row () User))))
    (check-equal? (classify core '() callables) 'Unknown)))

(test-case "PRF-002/PRF-003: type equality is structural and opaque"
  (check-true
   (type-equiv?
    '(NFn ((List Int)) (Proof TypeNarrativeCap)
          () (Own (Yield Int)) () User)
    '(NFn ((List Int)) (Proof TypeNarrativeCap)
          () ((Yield Int) Own) () User)))
  (check-false
   (type-equiv? '(Proof TypeNarrativeCap)
                '(Proof ValidNarrativeTrait)))

  ;; この仮引数 0 個の Recur は本体に compute が現れず、C-NoSelf で Finite になる。
  ;; Opaque の比較は分類に関係なく、2 つ目の型式へ正規化してはならない。
  (define unknown-calculation
    '(Recur opaque-id compute () unit unit))
  (check-equal? (classify unknown-calculation '()
                          '((opaque-id (NFn () Unit () () () User))))
                '(Finite no-self-reference))
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
                          Int () () () User)))))

(define region-structural-loop
  '(Recur rlist-loop-id loop (xs r)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> (Apply loop tail r))))
          (Apply (RegionApp loop ((RParam a)))
                 (Construct (List Int) nil) r)))

(define region-guarded-callables
  '((rnats-id (ForallRegion (a) (NFn (Int) Unit () ((Yield Int)) () User)))))

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
  '((bump (ForallRegion (b) (NFn (Int) Int () () () User)))))

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
  '((plus1 (NFn (Int) Int () () () User))))

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
    '((f (ForallRegion (a) (NFn (Int) Int () () () User))))
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
  '((c4-owned-loop-id (NFn ((Owned (List Int))) Int () () () User))))

(define c4-owned-loop
  '(Recur c4-owned-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) -> 0)))
          (Apply loop (Construct (Owned (List Int)) nil))))

(test-case "C4-002: Owned を包んだ走査対象の Eliminate が分類できる"
  (check-equal? (classify c4-owned-loop '() c4-owned-callables)
                '(Finite no-self-reference)))

;; P2i3b。C-NoSelf は binder を考慮し、継続の f に直接適用を課さない。
(define no-self-callables
  '((ns-id (NFn (Int) Int () () () User))))

(test-case "REC-001: 継続が f を値として返す f-free な Recur は C-NoSelf"
  (check-equal?
   (classify '(Recur ns-id f (x) x f) '() no-self-callables)
   '(Finite no-self-reference)))

(test-case "REC-001: 本体で束縛し直した f は自由な出現でない"
  (check-equal?
   (classify '(Recur ns-id f (x) (Let (f Int) x f) (Apply f 0))
             '() no-self-callables)
   '(Finite no-self-reference)))

(test-case "REC-001: 仮引数のある f-free な本体は structural より先に C-NoSelf"
  (check-equal?
   (classify '(Recur ns-id f (x) x (Apply f 0)) '() no-self-callables)
   '(Finite no-self-reference)))

(test-case "REC-001: 継続が Partial の callable を呼ぶと C-NoSelf にならない"
  (check-equal?
   (classify '(Recur ns-id f (x) x (Apply g 0))
             '((g (NFn (Int) Int () (Partial) () User)))
             no-self-callables)
   'Unknown))

;; 現行でも Unknown の安全性の回帰。C-NoSelf から pre(f, c1) を落とすと Finite になる。
(test-case "REC-001: 本体が Partial の callable を呼ぶと C-NoSelf にならない"
  (check-equal?
   (classify '(Recur ns-id f (x) (Apply g 0) (Apply f 0))
             '((g (NFn (Int) Int () (Partial) () User)))
             no-self-callables)
   'Unknown))

(define (c4-borrowed-callables wrapper)
  `((c4-borrowed-loop-id (NFn (,wrapper) Int () () () User))))

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
  '(Borrowed (Option (NFn (Int) Int () () () User)) 0))

(define c4-borrowed-function-loop
  `(Recur c4-borrowed-loop-id loop (xs)
          (Eliminate xs
                     ((none () -> 0)
                      (some (f) -> (Apply f 0))))
          (Apply loop (Construct ,c4-borrowed-function-type none))))

(define (c4-borrowed-function-callables type)
  `((c4-borrowed-loop-id (NFn (,type) Int () () () User))))

(test-case "C4-006c: 分類器は Borrowed も BorrowedMut も剥がす"
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
   ;; decreases-at? の walk には Assign の節がなく catch-all が #f なので、
   ;; 借用越しの書き換え本体は構造的減少の判定へ到達せず、Finite structural は健全である。
   (classify (c4-borrowed-loop '(BorrowedMut (List Int) 0))
             '()
             (c4-borrowed-callables '(BorrowedMut (List Int) 0)))
   '(Finite structural)))

(define owned-list-callables
  '((owned-list-id (NFn ((Owned (List Int))) Int () () () User))))

;; Scope と Let の連なりに包まれ、Move を挟んで分解と再帰呼び出しを行う本体。
(define owned-move-loop
  '(Recur owned-list-id loop (xs)
          (Scope ()
                 (Let (ys (Owned (List Int))) xs
                      (Eliminate (Move ys)
                                 ((nil () -> 0)
                                  (cons (head tail) -> (Apply loop (Move tail)))))))
          (Apply loop (Construct (Owned (List Int)) nil))))

(test-case "C4-003: 別名を跨ぎ Move を挟んだ構造的減少が Finite になる"
  (check-equal? (classify owned-move-loop '() owned-list-callables)
                '(Finite structural)))

;; Move で束縛した名前は別名ではない。所有が移るのは同じだが、
;; bound が記号でないため根の同一性を引き継がない。
(define owned-move-alias-loop
  '(Recur owned-list-id loop (xs)
          (Let (ys (Owned (List Int))) (Move xs)
               (Eliminate ys
                          ((nil () -> 0)
                           (cons (head tail) -> (Apply loop tail)))))
          (Apply loop (Construct (Owned (List Int)) nil))))

(test-case "C4-004: Move で束縛した名前は根の別名にならない"
  (check-not-equal? (classify owned-move-alias-loop '() owned-list-callables)
                    '(Finite structural)))

;; P2i3b spec §6.2。gate 用の本体分類は継続を見ない。
(test-case "REC-001: classify-recur-body は f-free な本体を B-NoSelf にする"
  (check-equal?
   (classify-recur-body 'f '(x) 'x
                        '((x Int) (f (NFn (Int) Int () () () User)))
                        '())
   '(Finite no-self-reference)))

(test-case "REC-001: classify-recur-body は継続なしで構造的減少を認める"
  (check-equal?
   (classify-recur-body
    'loop '(xs)
    '(Eliminate xs
                ((nil () -> 0)
                 (cons (head tail) -> (Apply loop tail))))
    '((xs (List Int)) (loop (NFn ((List Int)) Int () () () User)))
    structural-callables)
   '(Finite structural)))

(test-case "REC-002: classify-recur-body は初回の tail call なしで guarded を認める"
  (define signature '(NFn () Unit () ((Yield Int)) () User))
  (check-equal?
   (classify-recur-body 'loop '() '(Yield 1 (Apply loop))
                        `((loop ,signature))
                        `((loop-id ,signature)))
   '(Productive guarded)))

(test-case "REC-002: classify-recur-body でも guard の成分が target を借用すれば Unknown"
  (check-equal?
   (classify-recur-body
    'nats '(n)
    '(Yield (Let (alias (Borrowed (NFn (Int) Unit () ((Yield Int)) () User) 0))
                 (Borrow nats)
                 n)
            (Apply nats (Apply (PrimVal (Reserved o-add) add) n 1)))
    '((n Int) (nats (NFn (Int) Unit () ((Yield Int)) () User)))
    guarded-callables)
   'Unknown))

(test-case "REC-001: classify-recur-body は自己適用の繰返しを Unknown にする"
  (check-equal?
   (classify-recur-body 'loop '(n) '(Apply loop n)
                        '((n Int) (loop (NFn (Int) Int () () () User)))
                        '())
   'Unknown))

(test-case "REC-001: classify-recur-body は未知の形に Unknown を返す"
  (check-equal?
   (classify-recur-body 'f '() '(Mystery 1)
                        '((f (NFn () Unit () () () User)))
                        '())
   'Unknown))

#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../annotate.rkt"
         "../borrow.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../region.rkt"
         "../typing.rkt"
         "../borrow-gen.rkt")

(define owner-type '(Record ((n Int imm) (owned (Owned Res) imm))))
(define mutable-owner-type
  '(Record ((n (Option Int) mut) (owned (Owned Res) imm))))

(define (contains? tree wanted)
  (or (equal? tree wanted)
      (and (pair? tree)
           (or (contains? (car tree) wanted)
               (contains? (cdr tree) wanted)))))

(define (replace-omitted-with-placeholder tree)
  (match tree
    [`(RParam %omitted) 'ph]
    [(? pair?) (cons (replace-omitted-with-placeholder (car tree))
                     (replace-omitted-with-placeholder (cdr tree)))]
    [_ tree]))

(define (find-projborrow-label tree)
  (match tree
    [`(ProjBorrow ,_ ,_ ,label) label]
    [(? pair?) (or (find-projborrow-label (car tree))
                   (find-projborrow-label (cdr tree)))]
    [_ #f]))

(define (find-span tree head)
  (cond
    [(and (list? tree) (pair? tree) (eq? (first tree) head))
     (second tree)]
    [(pair? tree)
     (or (find-span (car tree) head)
         (find-span (cdr tree) head))]
    [else #f]))

(define (check-typed-rejection source head expected-id)
  (define annotated (annotate-surface source))
  (define expected-span (find-span annotated head))
  (check-not-false expected-span (format "~a の span が無い: ~s" head annotated))
  (define (check-diagnostic result)
    (check-true (diagnostic? result) (format "診断を期待: ~s" result))
    (check-equal? (diagnostic-id result) expected-id (format "診断: ~s" result))
    (check-equal? (diagnostic-primary-span result) expected-span))
  (match (elab annotated)
    [(list core _type _row callables)
     (check-diagnostic (core-type-of/regions core '() callables))]
    [`(err ,diagnostic) (check-diagnostic diagnostic)]))

(define (borrowed-field-function)
  `(Fn ((p ,owner-type)) Int (Own)
       (LexicalScope
        (Let (x let ,owner-type) (Move p)
          (Let (b let (Borrowed ,owner-type Omitted)) (Borrow x)
            (Read (Proj b n)))))))

(define (elab-success expression)
  (match (elab expression)
    [(list core type row callables) (values core type row callables)]
    [`(err ,diagnostic)
     (fail (format "elaboration が拒否した: ~s" diagnostic))]
    [other (fail (format "elaboration の結果形式が不正: ~s" other))]))

(define (region-check core callables expected)
  (define typed (core-type-of/regions core '() callables))
  (check-true (region-typed? typed) (format "region 型付け: ~s" typed))
  (when expected
    (check-equal? (region-typed-type typed) expected)))

(test-case "借用式を含む UCore 関数が elaboration と region 型付けを通る"
  (match (elab (borrowed-field-function))
    [(list core function-type _row callables)
     (check-true (contains? core 'Borrow))
     (check-true (contains? core 'ProjBorrow))
     (check-true (contains? core '(RParam %omitted)))
     (region-check core callables function-type)
     (check-true (contains? function-type 'Int))
     ]
    [`(err ,diagnostic)
     (fail (format "elaboration が拒否した: ~a" (diagnostic-id diagnostic)))]))

(test-case "span 付きの借用射影は label span を region 注釈後も保つ"
  (define-values (core function-type _row callables)
    (elab-success (annotate-surface (borrowed-field-function))))
  (define label (find-projborrow-label core))
  (check-true
   (match label
     [`(#:lbl n (#:span #:synthetic ,_ ,_)) #t]
     [_ #f])
   (format "Core: ~s; label: ~s" core label))
  (region-check core callables function-type)
  (define annotated (annotate-regions core (build-region-ir core)))
  (define (find-projborrow-at-label tree)
    (match tree
      [`(ProjBorrowAt ,_ ,_ ,_ ,label) label]
      [(? pair?) (or (find-projborrow-at-label (car tree))
                     (find-projborrow-at-label (cdr tree)))]
      [_ #f]))
  (check-equal? (find-projborrow-at-label annotated) label))

(test-case "注釈なしの let の &x は合成型に省略寿命を保つ"
  (define expression
    `(Fn ((p ,owner-type)) Int (Own)
         (LexicalScope
          (Let (x let ,owner-type) (Move p)
            (Let (b let) (Borrow x)
              (Read (Proj b n)))))))
  (define-values (core function-type _row callables)
    (elab-success expression))
  (check-true (contains? core `(Borrowed ,owner-type (RParam %omitted))))
  (region-check core callables function-type))

(test-case "可変借用の欄へ代入した後に値を読み出す"
  (define expression
    `(Fn ((p ,mutable-owner-type)) (Option Int) (Own Mutation)
         (LexicalScope
          (Let (x let ,mutable-owner-type) (Move p)
          (Let (b let (BorrowedMut ,mutable-owner-type Omitted))
                 (BorrowMut x)
              (Let ignored
                   (Assign (Proj b n)
                           (LexicalScope (Construct some 42)))
                (Read (Proj b n))))))))
  (define-values (core function-type _row callables)
    (elab-success expression))
  (check-true (contains? core 'BorrowMut))
  (check-true (contains? core 'Assign))
  (check-true (contains? core 'ProjBorrow))
  (region-check core callables function-type))

(test-case "Reborrow の子を読めて親は子の生存中に書けない"
  (define expression
    '(Fn ((p (Owned Int))) Int (Own Mutation)
         (LexicalScope
          (Let (x let (Owned Int)) (Move p)
            (Let (b let (BorrowedMut Int Omitted)) (BorrowMut x)
              (Let (child let (Borrowed Int Omitted)) (Reborrow b)
                (Read child)))))))
  (define-values (core function-type _row callables)
    (elab-success expression))
  (check-true (contains? core 'Reborrow))
  (check-true (contains? core 'BorrowMut))
  (check-match function-type `(NFn ((Owned Int)) Int ,_ ,_ ,_ User))
  (define omitted-result (core-type-of/regions core '() callables))
  (check-true (region-typed? omitted-result)
              (format "Omitted の型付け: ~s" omitted-result))
  (define placeholder-core
    (replace-omitted-with-placeholder (erase-core core)))
  (define ir (build-region-ir placeholder-core))
  (define filled (fill-region-placeholders placeholder-core ir))
  (define filled-result (core-type-of/regions filled '() callables #:ir ir))
  (check-true (region-typed? filled-result)
              (format "placeholder の型付け: ~s" filled-result))
  (define parent-write-expression
    '(Fn ((p (Owned Int))) Int (Own Mutation)
         (LexicalScope
          (Let (x let (Owned Int)) (Move p)
            (Let (b let (BorrowedMut Int Omitted)) (BorrowMut x)
              (Let (child let (Borrowed Int Omitted)) (Reborrow b)
                (Let ignored (Assign b 18) (Read child))))))))
  (define-values (parent-write _parent-type _parent-row _parent-calls)
    (elab-success parent-write-expression))
  (define parent-write-result
    (core-type-of/regions parent-write '() callables))
  (check-true (diagnostic? parent-write-result))
  (check-equal? (diagnostic-id parent-write-result) "E-BOR-025"))

(test-case "Core の Reborrow は omitted と placeholder で同じ型検査結果になる"
  (define core
    '(Scope ()
       (Let (x let (Owned Int)) 17
         (Let (b let (BorrowedMut Int (RParam %omitted))) (BorrowMut x)
           (Let (child let (Borrowed Int (RParam %omitted))) (Reborrow b)
             (Read child))))))
  (define omitted (core-type-of/regions core '() '()))
  (define placeholder-core (replace-omitted-with-placeholder core))
  (define ir (build-region-ir placeholder-core))
  (define filled
    (fill-region-placeholders placeholder-core ir))
  (define placeholder
    (core-type-of/regions filled '() '() #:ir ir))
  (check-true (region-typed? omitted)
              (format "omitted: ~s" omitted))
  (check-true (region-typed? placeholder)
              (format "placeholder: ~s" placeholder)))

(test-case "Eliminate の両枝で借用を返しても省略寿命のまま合流する"
  (define expression
    `(Fn ((p ,owner-type) (q ,owner-type) (condition Bool)) Int (Own)
         (LexicalScope
          (Let (x let ,owner-type) (Move p)
            (Let (y let ,owner-type) (Move q)
              (Let (b let (Borrowed ,owner-type Omitted))
                   (Eliminate condition
                     ((true () -> (Borrow x))
                      (false () -> (Borrow y))))
                (Read (Proj b n))))))))
  (define-values (core function-type _row callables)
    (elab-success expression))
  (check-true (contains? core 'Eliminate))
  (check-true (contains? core 'ProjBorrow))
  (check-true (contains? core '(RParam %omitted)))
  (check-false (contains? core 'RVar))
  (region-check core callables function-type))

(test-case "Option の Eliminate の両枝で借用を返して when 形へ合流する"
  (define expression
    `(Fn ((p ,owner-type) (q ,owner-type)) Int (Own)
         (LexicalScope
          (Let (x let ,owner-type) (Move p)
            (Let (y let ,owner-type) (Move q)
              (Let (option let (Option Int)) (Construct some (Types Int) 1)
                (Let (chosen let (Borrowed ,owner-type Omitted))
                       (Eliminate option
                         ((none () -> (Borrow y))
                          (some (selected) -> (Borrow x))))
                  (Read (Proj chosen n)))))))))
  (define-values (core function-type _row callables)
    (elab-success expression))
  (check-true (contains? core 'Eliminate))
  (check-true (contains? core 'none))
  (check-true (contains? core 'some))
  (region-check core callables function-type))

(test-case "関数の合成戻り値に借用が残る場合は E-BOR-013 で宣言全体を指す"
  (define surface
    `(Fn ((p ,owner-type)) #:infer #:infer (Borrow p)))
  (define annotated (annotate-surface surface))
  (define fn-span (second annotated))
  (match (elab annotated)
    [(list core _function-type _row callables)
     (define result (core-type-of/regions core '() callables))
     (check-true (diagnostic? result) (format "診断を期待: ~s" result))
     (check-equal? (diagnostic-id result) "E-BOR-013")
     (check-equal? (diagnostic-primary-span result) fn-span)]
    [`(err ,diagnostic)
     (fail (format "elaboration が先に拒否した: ~a"
                   (diagnostic-id diagnostic)))]))

(test-case "借用を含む元関数の adapter は region-aware 型付けを通る"
  (define source
    `(Let (adapted const
                   (NFn (,owner-type) (Union Int String) (Own) ()))
          ,(borrowed-field-function)
          adapted))
  (define-values (core function-type _row callables)
    (elab-success source))
  (check-true (contains? core 'Curry) (format "adapter Core が無い: ~s" core))
  (check-true (contains? core 'Borrow) (format "借用する元関数が無い: ~s" core))
  (region-check core callables function-type)
  (define without-regions
    (core-type-of/diagnostic core '() callables))
  (check-true (diagnostic? without-regions))
  (check-equal? (diagnostic-id without-regions) "E-SYN-004"))

(test-case "借用でない値への Read は節点 span の E-BOR-018"
  (check-typed-rejection '(Read 1) 'Read "E-BOR-018"))

(test-case "可変借用でない値への Reborrow は節点 span の E-BOR-009"
  (check-typed-rejection '(Reborrow 1) 'Reborrow "E-BOR-009"))

(test-case "共有借用を通す Assign は節点 span の E-BOR-015"
  (check-typed-rejection
   '(Fn ((p (Owned Int))) Unit (Own Mutation)
        (LexicalScope
         (Let (b let (Borrowed Int Omitted)) (Borrow p)
           (Assign b 1))))
   'Assign "E-BOR-015"))

(test-case "借用でない値への Assign は節点 span の E-BOR-019"
  (check-typed-rejection
   '(Fn ((p Int)) Unit (Mutation) (Assign p 1))
   'Assign "E-BOR-019"))

(test-case "借用射影の未知 label は Proj span の E-BOR-017"
  (define owner owner-type)
  (check-typed-rejection
   `(Fn ((p ,owner)) Int (Own)
        (LexicalScope
         (Let (x let ,owner) (Move p)
           (Let (b let (Borrowed ,owner Omitted)) (Borrow x)
             (Read (Proj b missing))))))
   'Proj "E-BOR-017"))

(test-case "通常の record 射影は Proj のままである"
  (define-values (core function-type _row callables)
    (elab-success '(Fn ((value (Record ((n Int imm))))) Int () (Proj value n))))
  (check-true (contains? core 'Proj))
  (check-false (contains? core 'ProjBorrow))
  (check-equal? (core-type-of core '() callables)
                (list function-type '())))

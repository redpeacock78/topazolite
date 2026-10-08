#lang racket

;; [REQ: OWN-004] 構造型 narrowing が余剰 Owned field を失う場合の拒否。
;; 引き金は余剰欄が在ることではなく、余剰の affine 資源を失うことである。

(require rackunit
         racket/match
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../compat.rkt"
         "../ownership.rkt"
         "../region.rkt"
         "../resource-type.rkt"
         "../typing.rkt")

;; 関数引数の実型が余剰 Owned 欄を持つ Record になる環境。
(define owned '(Owned Res))
(define (always-compatible _actual _expected) #t)

(define (elaborate-code-of source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define nested-actual
  `(Record ((a (Record ((y Int imm) (z ,owned imm))) imm))))
(define nested-no-z
  '(Record ((a (Record ((y Int imm))) imm))))
(define nested-with-residual
  `(Record ((a (Record ((y Int imm) (z ,owned imm))) imm)
            (x ,owned imm))))
(define union-nested-actual
  `(Record ((a (Union (Record ((x ,owned imm) (y Int imm))) Bool) imm))))
(define union-nested-expected
  '(Record ((a (Union (Record ((y Int imm))) Bool) imm))))
(define rejected-nfn-actual
  `(NFn (Unit) ,nested-actual () () () User))
(define rejected-nfn-expected
  `(NFn (Unit) ,nested-no-z () () () User))
(define surface-rejected-nfn-actual
  `(NFn (Unit) ,nested-actual () ()))
(define surface-rejected-nfn-expected
  `(NFn (Unit) ,nested-no-z () ()))

(define (fixture-value type)
  (if (resource-type? type)
      '(Apply fixture-source unit)
      (match type
        [`Int 1]
        [`Bool '(Construct Bool true)]
        [`(Record ,fields)
         `(Rec ,(for/list ([field (in-list fields)])
                  `(,(first field) imm ,(fixture-value (second field)))))]
        [`(Union ,members ...)
         (define member (first members))
         `(UnionInject ,type ,member ,(fixture-value member))]
        [`(NFn . ,_rest) 'source]
        [_ (error 'fixture-value "試験用の値を構成できない型: ~s" type)])))

(define (fixture-environment type)
  (cond
    [(resource-type? type)
     `((fixture-source (NFn (Unit) ,type () (Own) () User)))]
    [(match type [`(NFn . ,_rest) #t] [_ #f]) `((source ,type))]
    [else '()]))

(define simple-actual-type `(Record ((x ,owned imm) (y Int imm))))
(define simple-actual-value (fixture-value simple-actual-type))
(define narrowing-environment
  (append
   '((f (NFn ((Record ((y Int imm)))) Unit () () () User)))
   (fixture-environment simple-actual-type)))

(define (apply-key actual expected)
  (key-of `(Apply f ,(fixture-value actual))
          (append `((f (NFn (,expected) Unit () () () User)))
                  (fixture-environment actual))))

(define (apply-union-key actual expected member)
  (key-of `(Apply f (UnionInject ,expected ,member ,(fixture-value actual)))
          (append `((f (NFn (,expected) Unit () () () User)))
                  (fixture-environment actual))))

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (code-of core [environment '()])
  (diagnostic-id
   (core-type-of/diagnostic core '() '() environment (empty-region-ctx))))

(define (contains-rsd? tree)
  (or (and (pair? tree)
           (eq? (car tree) 'Discharge)
           (regexp-match? #rx"RemainderSafelyDropped" (format "~s" tree)))
      (and (pair? tree) (ormap contains-rsd? tree))))

;; 余剰欄が Int だけの width narrowing は従来どおり通る。
(test-case "余剰欄が Int だけの narrowing は受理する"
  (check-equal?
   (key-of '(Let (r (Record ((y Int imm))))
                 (Rec ((x imm 1) (y imm 2)))
                 1))
   'ok))

;; 余剰欄が Owned を含むと Proof を求める。通常の Rec は Owned 欄を拒否するため、
;; 関数引数の照合で Record 型の narrowing を直接通す。
(test-case "余剰 Owned 欄を落とす narrowing は Proof を求める"
  (define core `(Apply f ,simple-actual-value))
  (check-equal? (key-of core narrowing-environment) 'owned-narrowing-needs-proof)
  (check-equal? (code-of core narrowing-environment) "E-OWN-030"))

(test-case "余剰 Owned 欄を落とす narrowing は既定で Proof を求める"
  (check-equal? (key-of `(Apply f ,simple-actual-value) narrowing-environment)
                'owned-narrowing-needs-proof))

(test-case "Proof を求める診断は expected と found を分けて持つ"
  (define diagnostic
    (core-type-of/diagnostic `(Apply f ,simple-actual-value) '() '()
                             narrowing-environment
                             (empty-region-ctx)))
  (check-equal? (diagnostic-expected diagnostic)
                '(Record ((y Int imm))))
  (check-equal? (diagnostic-found diagnostic)
                `(Record ((x ,owned imm) (y Int imm)))))

(test-case "入れ子の record の narrowing は Proof を要求する"
  (check-equal?
   (apply-key
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) imm)))
    '(Record ((a (Record ((y Int imm))) imm))))
   'owned-narrowing-needs-proof))

(test-case "optional 欄の内側の narrowing は Proof を要求する"
  (check-equal?
   (apply-key
    `(Record ((a (Record ((payload ,owned imm))) imm)))
    '(Record ((a (Record ()) imm opt))))
   'owned-narrowing-needs-proof))

(test-case "NFn の返り値の narrowing を拒否する"
  (check-equal?
   (apply-key
    `(NFn (Int) (Record ((x ,owned imm) (y Int imm))) () () () User)
    '(NFn (Int) (Record ((y Int imm))) () () () User))
   'owned-narrowing-rejected))

(test-case "NFn の引数の narrowing を拒否する"
  (check-equal?
   (apply-key
    '(NFn ((Record ((y Int imm)))) Int () () () User)
    `(NFn ((Record ((x ,owned imm) (y Int imm)))) Int () () () User))
   'owned-narrowing-rejected))

(test-case "Union は安全な候補が一つあれば受理する"
  (check-equal?
   (apply-union-key
    `(Record ((x ,owned imm) (y Int imm)))
    `(Union (Record ((x ,owned imm) (y Int imm)))
            (Record ((y Int imm))))
    `(Record ((x ,owned imm) (y Int imm))))
   'ok))

(test-case "Owned を失う Union member への inject は Proof を要する"
  (check-equal?
   (apply-union-key
    `(Record ((x ,owned imm) (y Int imm)))
    '(Union (Record ((y Int imm))) (Record ((z Int imm))))
    '(Record ((y Int imm))))
   'owned-narrowing-needs-proof))

(test-case "elaboration 用の Union 判定は成分の最上位で残余損失を認める"
  (define actual
    `(Record ((a Int imm) (o ,owned imm))))
  (define expected
    '(Union (Record ((a (Union Int String) imm))) String))
  (check-equal? (owned-narrowing-kind actual expected compat?) 'reject)
  (check-equal?
   (owned-narrowing-kind/for-elaboration actual expected compat?)
   'ok)
  ;; mode は呼び出しの動的範囲だけに限る。
  (check-equal? (owned-narrowing-kind actual expected compat?) 'reject))

(test-case "elaboration 用の Union 判定は安全な別成分を維持する"
  (define actual
    `(Record ((a Int imm) (o ,owned imm))))
  (define expected
    `(Union (Record ((a Int imm)))
            (Record ((a (Union Int Bool) imm) (o ,owned imm)))))
  (check-equal? (owned-narrowing-kind actual expected compat?) 'ok)
  (check-equal?
   (owned-narrowing-kind/for-elaboration actual expected compat?)
   'ok))

(test-case "elaboration 用の Union 判定は NFn 内側の損失を拒否する"
  (define actual
    `(NFn (Unit) ,nested-actual () () () User))
  (define expected
    `(Union (NFn (Unit) ,nested-no-z () () () User) String))
  (check-equal?
   (owned-narrowing-kind/for-elaboration actual expected compat?)
   'reject))

(test-case "elaboration 用の Union 判定は imm 鎖の nested-drop を認める"
  (define actual
    `(Record ((a (Record ((o ,owned imm) (tag Int imm))) imm))))
  (define expected-member
    '(Record ((a (Record ((tag (Union Int Bool) imm))) imm))))
  (define expected `(Union ,expected-member String))
  (check-equal? (owned-narrowing-kind actual expected compat?) 'reject)
  (check-equal?
   (owned-narrowing-kind/for-elaboration actual expected compat?)
   'ok))

(test-case "Union 欄と imm 鎖の残余損失は呼び出し全体の鍵を返す"
  (define actual
    `(Record ((a (Record ((o ,owned imm) (tag Int imm))) imm))))
  (define expected
    '(Record ((a (Record ((tag (Union Int Bool) imm))) imm))))
  (define result
    (owned-narrowing-kind/for-elaboration actual expected compat?))
  (check-equal? result `(drop-obligation ,actual ,expected))
  (check-true
   (check-narrowing-return (list actual expected compat?) (list result))))

(test-case "actual Union から root Owned への特例は elaboration mode でも通る"
  (define actual '(Union Int Bool))
  (define expected '(Owned (Union Int Bool)))
  (check-equal?
   (owned-narrowing-kind/for-elaboration actual expected always-compatible)
   'ok))

(test-case "elaboration 用の actual Union 判定は各成分の drop-obligation を認める"
  (define actual
    `(Union (Record ((x ,owned imm) (y Int imm))) Bool))
  (define expected
    '(Union (Record ((y Int imm))) Bool))
  (check-equal? (owned-narrowing-kind actual expected compat?) 'reject)
  (check-equal?
   (owned-narrowing-kind/for-elaboration actual expected compat?) 'ok))

(test-case "elaboration 用の actual Union 判定は内側の reject を保つ"
  (define actual
    `(Union (NFn (Unit) ,nested-actual () () () User) Bool))
  (define expected
    `(Union (NFn (Unit) ,nested-no-z () () () User) Bool))
  (check-equal?
   (owned-narrowing-kind/for-elaboration actual expected compat?)
   'reject))

(test-case "Union の唯一の compatible member は RSD を挿入して受理する"
  (match (elab
          '(Fn ((p (Record ((x (Owned Res) imm) (y Int imm)))))
               (Union (Record ((y Int imm))) (Record ((z Int imm))))
               (Own)
               (Move p)))
    [(list core type row callables)
     (define erased (erase-core core))
     (check-true (contains-rsd? erased))
     (check-equal? (core-type-of erased '() callables) (list type row))]
    [`(err ,diagnostic)
     (fail-check (format "RSD を挿入する Union member が拒否された: ~s"
                         diagnostic))]))

(test-case "3 要素 binder は residual を束縛へ残す"
  (check-equal?
   (key-of '(Let (r let (Record ((y Int imm))))
                 (Rec ((x imm 1) (y imm 2)))
                 1))
   'ok))

(test-case "let binder は最上位の Owned residual を保持する"
  (check-equal?
   (key-of `(Let (r let (Record ((y Int imm)))) ,simple-actual-value 1)
           narrowing-environment)
   'ok))

(test-case "binding-context の入れ子 narrowing は Proof を要求する"
  (check-equal?
   (key-of `(Let (r let (Record ((a (Record ((y Int imm))) imm))))
                 ,(fixture-value nested-actual) 1)
           (fixture-environment nested-actual))
   'owned-narrowing-needs-proof))

(test-case "const binder の入れ子 narrowing は Proof を要求する"
  (check-equal?
   (key-of `(Let (r const (Record ((a (Record ((y Int imm))) imm))))
                 ,(fixture-value nested-actual) 1)
           (fixture-environment nested-actual))
   'owned-narrowing-needs-proof))

(test-case "Union 成分内の損失は ownership より前の Apply tag gate で type-mismatch になる"
  (check-equal?
   (apply-key union-nested-actual union-nested-expected)
   'type-mismatch))

(test-case "Union 成分内の損失は ownership より前の let binder tag gate で拒否される"
  (check-equal?
   (key-of `(Let (r let ,union-nested-expected)
                 ,(fixture-value union-nested-actual)
                 1)
           (fixture-environment union-nested-actual))
   'record-binding-incompatible))

(test-case "Union 成分内の損失は ownership より前の const binder tag gate で拒否される"
  (check-equal?
   (key-of `(Let (r const ,union-nested-expected)
                 ,(fixture-value union-nested-actual)
                 1)
           (fixture-environment union-nested-actual))
   'record-binding-incompatible))

(test-case "NFn の返り値内の残余損失は Apply 引数で reject する"
  (check-equal?
   (apply-key rejected-nfn-actual rejected-nfn-expected)
   'owned-narrowing-rejected))

(test-case "NFn の返り値内の残余損失は let binder で reject する"
  (check-equal?
   (key-of `(Let (r let ,rejected-nfn-expected)
                 ,(fixture-value rejected-nfn-actual)
                 1)
           (fixture-environment rejected-nfn-actual))
   'owned-narrowing-rejected))

(test-case "NFn の返り値内の残余損失は const binder で reject する"
  (check-equal?
   (key-of `(Let (r const ,rejected-nfn-expected)
                 ,(fixture-value rejected-nfn-actual)
                 1)
           (fixture-environment rejected-nfn-actual))
   'owned-narrowing-rejected))

(test-case "互換でない型は narrowing 拒否ではなく type-mismatch になる"
  (check-equal?
   (apply-key '(Record ((y Int imm)))
              '(Record ((z Int imm))))
   'type-mismatch))

(test-case "actual が Never なら narrowing を受理する"
  (check-equal?
   (key-of '(Apply f s)
           '((f (NFn ((Record ((y Int imm)))) Unit () () () User))
             (s Never)))
   'ok))

(test-case "elaborate は入れ子 Record narrowing の Owned 残余を回収する"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-actual)) ,nested-no-z (Own) (Move p)))
   'ok))

(test-case "elaborate の Apply 引数で NFn 内の残余損失を E-OWN-029 にする"
  (check-equal?
   (elaborate-code-of
    `(Fn ((source ,surface-rejected-nfn-actual)) Int ()
         (Apply (Fn ((p ,surface-rejected-nfn-expected)) Int () 1)
                source)))
   "E-OWN-029"))

(test-case "elaborate の注釈付き Let で NFn 内の残余損失を E-OWN-029 にする"
  (check-equal?
   (elaborate-code-of
    `(Fn ((source ,surface-rejected-nfn-actual)) Int ()
         (Let (r let ,surface-rejected-nfn-expected) source 1)))
   "E-OWN-029"))

(test-case "elaborate の const binder で NFn 内の残余損失を E-OWN-029 にする"
  (check-equal?
   (elaborate-code-of
    `(Fn ((source ,surface-rejected-nfn-actual)) Int ()
         (Let (r const ,surface-rejected-nfn-expected) source 1)))
   "E-OWN-029"))

(test-case "elaborate は最上位の余剰 Owned を RSD で回収する"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p (Record ((x ,owned imm) (y Int imm)))))
         (Record ((y Int imm))) (Own) (Move p)))
   'ok))

(test-case "余剰 Owned を保つ形は elaborate を通る"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-actual)) ,nested-actual (Own) (Move p)))
   'ok))

(test-case "let binder は最上位の Owned residual を保持する（elaborate）"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-with-residual)) Int (Own)
         (Let (q let ,nested-actual) (Move p) 1)))
   'ok))

(test-case "注釈付き Let の入れ子 Record narrowing は RSD で受理する"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-with-residual)) Int (Own)
         (Let (q let ,nested-no-z) (Move p) 1)))
   'ok))

(test-case "const binder の入れ子 Record narrowing は RSD で受理する"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-actual)) Int (Own)
         (Let (q const ,nested-no-z) (Move p) 1)))
   'ok))

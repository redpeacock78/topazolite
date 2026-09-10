#lang racket

;; [REQ: OWN-004] 構造型 narrowing が余剰 Owned field を失う場合の拒否。
;; 引き金は余剰欄が在ることではなく、余剰の affine 資源を失うことである。

(require rackunit
         racket/match
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../region.rkt"
         "../typing.rkt")

;; 関数引数の実型が余剰 Owned 欄を持つ Record になる環境。
(define narrowing-environment
  (list (list 'f '(NFn ((Record ((y Int imm)))) Unit () ()))
        (list 's '(Record ((x (Owned Res) imm) (y Int imm))))))
(define let-residual-environment
  '((s (Record ((x (Owned Res) imm) (y Int imm))))))
(define let-nested-environment
  '((s (Record ((a (Record ((y Int imm) (z (Owned Res) imm))) imm))))))
(define owned '(Owned Res))

(define (elaborate-code-of source)
  (match (elab source)
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ 'ok]))

(define nested-actual
  '(Record ((a (Record ((y Int imm) (z (Owned Res) imm))) imm))))
(define nested-no-z
  '(Record ((a (Record ((y Int imm))) imm))))
(define nested-with-residual
  '(Record ((a (Record ((y Int imm) (z (Owned Res) imm))) imm)
            (x (Owned Res) imm))))

(define (apply-key actual expected)
  (key-of '(Apply f s)
          `((f (NFn (,expected) Unit () ()))
            (s ,actual))))

(define (key-of core [environment '()])
  (match (type-of/raw core '() '() environment (empty-region-ctx))
    [(list 'fail key _node _details ...) key]
    [(list 'ok _) 'ok]))

(define (code-of core [environment '()])
  (diagnostic-id
   (core-type-of/diagnostic core '() '() environment (empty-region-ctx))))

;; 余剰欄が Int だけの width narrowing は従来どおり通る。
(test-case "余剰欄が Int だけの narrowing は受理する"
  (check-equal?
   (key-of '(Let (r (Record ((y Int imm))))
                 (Rec ((x imm 1) (y imm 2)))
                 1))
   'ok))

;; 余剰欄が Owned を含むと拒否する。通常の Rec は Owned 欄を拒否するため、
;; 関数引数の照合で Record 型の narrowing を直接通す。
(test-case "余剰 Owned 欄を落とす narrowing は拒否する"
  (define core '(Apply f s))
  (check-equal? (key-of core narrowing-environment) 'owned-narrowing-rejected)
  (check-equal? (code-of core narrowing-environment) "E-OWN-028"))

(test-case "拒否の診断は expected と found を分けて持つ"
  (define diagnostic
    (core-type-of/diagnostic '(Apply f s) '() '()
                             narrowing-environment
                             (empty-region-ctx)))
  (check-equal? (diagnostic-expected diagnostic)
                '(Record ((y Int imm))))
  (check-equal? (diagnostic-found diagnostic)
                '(Record ((x (Owned Res) imm) (y Int imm)))))

(test-case "入れ子の record の narrowing も拒否する"
  (check-equal?
   (apply-key
    `(Record ((a (Record ((x ,owned imm) (y Int imm))) imm)))
    '(Record ((a (Record ((y Int imm))) imm))))
   'owned-narrowing-rejected))

(test-case "NFn の返り値の narrowing を拒否する"
  (check-equal?
   (apply-key
    `(NFn (Int) (Record ((x ,owned imm) (y Int imm))) () ())
    '(NFn (Int) (Record ((y Int imm))) () ()))
   'owned-narrowing-rejected))

(test-case "NFn の引数の narrowing を拒否する"
  (check-equal?
   (apply-key
    '(NFn ((Record ((y Int imm)))) Int () ())
    `(NFn ((Record ((x ,owned imm) (y Int imm)))) Int () ()))
   'owned-narrowing-rejected))

(test-case "Union は安全な候補が一つあれば受理する"
  (check-equal?
   (apply-key
    `(Record ((x ,owned imm) (y Int imm)))
    `(Union (Record ((x ,owned imm) (y Int imm)))
            (Record ((y Int imm)))))
   'ok))

(test-case "Union に安全な候補が無ければ拒否する"
  (check-equal?
   (apply-key
    `(Record ((x ,owned imm) (y Int imm)))
    '(Union (Record ((y Int imm))) (Record ((z Int imm)))))
   'owned-narrowing-rejected))

(test-case "3 要素 binder は residual を束縛へ残す"
  (check-equal?
   (key-of '(Let (r let (Record ((y Int imm))))
                 (Rec ((x imm 1) (y imm 2)))
                 1))
   'ok))

(test-case "let binder は最上位の Owned residual を保持する"
  (check-equal?
   (key-of '(Let (r let (Record ((y Int imm)))) s 1)
           let-residual-environment)
   'ok))

(test-case "binding-context の入れ子 narrowing は拒否する"
  (check-equal?
   (key-of '(Let (r let (Record ((a (Record ((y Int imm))) imm)))) s 1)
           let-nested-environment)
   'owned-narrowing-rejected))

(test-case "const binder の入れ子 narrowing も拒否する"
  (check-equal?
   (key-of '(Let (r const (Record ((a (Record ((y Int imm))) imm)))) s 1)
           let-nested-environment)
   'owned-narrowing-rejected))

(test-case "互換でない型は narrowing 拒否ではなく type-mismatch になる"
  (check-equal?
   (apply-key '(Record ((y Int imm)))
              '(Record ((z Int imm))))
   'type-mismatch))

(test-case "actual が Never なら narrowing を受理する"
  (check-equal?
   (key-of '(Apply f s)
           '((f (NFn ((Record ((y Int imm)))) Unit () ()))
             (s Never)))
   'ok))

(test-case "elaborate 側の拒否の code は E-OWN-029 である"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-actual)) ,nested-no-z () p))
   "E-OWN-029"))

(test-case "余剰 Owned を保つ形は elaborate を通る"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-actual)) ,nested-actual () p))
   'ok))

(test-case "let binder は最上位の Owned residual を保持する（elaborate）"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-with-residual)) Int ()
         (Let (q let ,nested-actual) p 1)))
   'ok))

(test-case "注釈付き Let の入れ子 narrowing は拒否する"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-with-residual)) Int ()
         (Let (q let ,nested-no-z) p 1)))
   "E-OWN-029"))

(test-case "const binder の入れ子 narrowing も拒否する（elaborate）"
  (check-equal?
   (elaborate-code-of
    `(Fn ((p ,nested-actual)) Int ()
         (Let (q const ,nested-no-z) p 1)))
   "E-OWN-029"))

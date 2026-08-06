#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../elaborate.rkt"
         "../span.rkt"
         "../erase.rkt"
         "../annotate.rkt")

;; span 機構の head と紛らわしい 9 語。%foo と %synthetic は、記号 literal を
;; 使う案を採っていたら除外されていた名前である。
(define collision-names '(Var Lit Bind Lbl Ty Ef span %foo %synthetic))

;; redex-match? は言語と非終端を構文として取るため、非終端ごとにマクロで展開する。
;; 非終端を実行時の変数で渡すと、その変数名そのものが pattern の記号になる。
(define-syntax-rule (check-same-acceptance base spanful nt)
  (for ([name (in-list collision-names)])
    (check-true (and (redex-match? base nt name) #t)
                (format "~a を ~a として ~a が受理する" name 'nt 'base))
    (check-equal? (and (redex-match? spanful nt name) #t)
                  (and (redex-match? base nt name) #t)
                  (format "~a を ~a として ~a と ~a で比べる"
                          name 'nt 'base 'spanful))))

(test-case "識別子の受理集合が G1 と G1+ で一致する"
  (check-same-acceptance G1 G1+ x)
  (check-same-acceptance G1 G1+ f)
  (check-same-acceptance G1 G1+ b)
  (check-same-acceptance G1 G1+ K)
  (check-same-acceptance G1 G1+ nm)
  (check-same-acceptance G1 G1+ id)
  (check-same-acceptance G1 G1+ cid))

(test-case "識別子の受理集合が G2 と G2+ で一致する"
  (check-same-acceptance G2 G2+ x)
  (check-same-acceptance G2 G2+ f)
  (check-same-acceptance G2 G2+ b)
  (check-same-acceptance G2 G2+ K)
  (check-same-acceptance G2 G2+ nm)
  (check-same-acceptance G2 G2+ id)
  (check-same-acceptance G2 G2+ cid)
  (check-same-acceptance G2 G2+ label))

(test-case "識別子の受理集合が UCore と UCore+ で一致する"
  (check-same-acceptance UCore UCore+ x)
  (check-same-acceptance UCore UCore+ f)
  (check-same-acceptance UCore UCore+ b)
  (check-same-acceptance UCore UCore+ K)
  (check-same-acceptance UCore UCore+ nm)
  (check-same-acceptance UCore UCore+ id)
  (check-same-acceptance UCore UCore+ cid)
  (check-same-acceptance UCore UCore+ label)
  (check-same-acceptance UCore UCore+ T))

(test-case "9 語は 5 つの位置すべてで受理され、注釈と erase が往復する"
  (for ([name (in-list collision-names)])
    ;; 位置 1: 変数名。
    (define as-variable (term (Let (,name Int) 1 ,name)))
    ;; 位置 2: ADT tag。
    (define as-tag (term (Construct (Option Int) ,name 1)))
    ;; 位置 3: field label。
    (define as-label (term (Rec ((,name imm 1)))))
    ;; 位置 4: 境界名。
    (define as-boundary (term (Perform (Return ,name Int) 1)))
    (for ([core (in-list (list as-variable as-tag as-boundary))])
      (check-true (redex-match? G1 c core) (format "~a" core))
      (define lifted (annotate-core core))
      (check-true (redex-match? G1+ c lifted) (format "~a" lifted))
      (check-equal? (erase-core lifted) core))
    (check-true (redex-match? G2 c as-label) (format "~a" as-label))
    (define lifted-label (annotate-core as-label))
    (check-true (redex-match? G2+ c lifted-label) (format "~a" lifted-label))
    (check-equal? (erase-core lifted-label) as-label)
    ;; 位置 5: usid。
    (check-true (redex-match? Span s (term (#:span ,name 0 0))))
    (check-true (span-ok? (term (#:span ,name 0 0))))))

(test-case "9 語は UCore の位置でも受理され、注釈と erase が往復する"
  (for ([name (in-list collision-names)])
    (for ([expr (in-list (list (term (Let ,name 1 ,name))
                               (term (Construct ,name 1))
                               (term (Rec ((,name imm 1))))))])
      (check-true (redex-match? UCore e expr) (format "~a" expr))
      (define lifted (annotate-surface expr))
      (check-true (redex-match? UCore+ e lifted) (format "~a" lifted))
      (check-equal? (erase-surface lifted) expr))))

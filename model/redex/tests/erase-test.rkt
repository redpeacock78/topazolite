#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../elaborate.rkt"
         "../span.rkt"
         "../erase.rkt")

(define s0 (term (#:span main.tz 0 4)))
(define s1 (term (#:span main.tz 5 9)))
(define s2 (term (#:span other.tz 11 30)))

(define core+
  (term (Let ,s0 ((#:bind x ,s1) (#:ty Int ,s1))
             (#:lit 1 ,s1)
             (Apply ,s1 (Lam ,s1 User lam-id ((#:bind y ,s1)) (#:var y ,s1))
                    (#:var x ,s1)))))
(define core
  (term (Let (x Int) 1 (Apply (Lam User lam-id (y) y) x))))

(define surface+
  (term (Fn ,s0 (((#:bind x ,s1) (#:ty Int ,s1)))
            (#:ty Int ,s1) (#:ef () ,s1)
            (Rec ,s1 (((#:lbl a ,s1) imm (#:var x ,s1)))))))
(define surface
  (term (Fn ((x Int)) Int () (Rec ((a imm x))))))

;; 法則 1: 全域性。
(test-case "erase-core は Core+ の全構成子で定義される"
  (for ([term+ (in-list
                (list (term (Apply ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                      (term (Construct ,s0 (#:ty (Option Int) ,s1) some (#:lit 1 ,s1)))
                      (term (Eliminate ,s0 (#:var x ,s1)
                                       ((,s1 some ((#:bind y ,s1)) -> (#:var y ,s1)))))
                      (term (Perform ,s0 (Return b (#:ty Int ,s1)) (#:lit 1 ,s1)))
                      (term (Handle ,s0 (Return b (#:ty Int ,s1))
                                    (,s1 (#:bind x ,s1) -> (#:var x ,s1))
                                    (#:lit 1 ,s1)))
                      (term (Scope ,s0 () (#:lit 1 ,s1)))
                      (term (Recur ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                                   (#:var x ,s1)
                                   (Apply ,s1 (#:var f ,s1) (#:lit 0 ,s1))))
                      (term (Yield ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                      (term (Suspend ,s0 (#:lit 1 ,s1)))
                      (term (Move ,s0 (#:var x ,s1)))
                      (term (Drop ,s0 (#:lit 1 ,s1)))
                      (term (Curry ,s0 (#:lit 1 ,s1) (#:lit 2 ,s1)))
                      (term (resource ,s0 0))
                      (term (PrimVal ,s0 (Reserved o-lt) lt))
                      (term (CurryVal ,s0 User (#:lit 1 ,s1) (#:lit 2 ,s1)))
                      (term (RecurVal ,s0 recur-id (#:bind f ,s1) ((#:bind x ,s1))
                                      (#:var x ,s1)))
                      (term (TypeRep ,s0 User Int Type))
                      (term (ProofRep ,s0 User ValidNarrativeTrait))
                      (term (Rec ,s0 (((#:lbl a ,s1) imm (#:lit 1 ,s1)))))
                      (term (Proj ,s0 (#:var x ,s1) (#:lbl a ,s1)))
                      (term (Let ,s0 ((#:bind x ,s1) const (#:ty Int ,s1))
                                 (#:lit 1 ,s1) (#:var x ,s1)))
                      (term (Discharge ,s0 (ProofRep ,s1 User ValidNarrativeTrait)
                                       (#:lit 1 ,s1)))
                      (term (UVal ,s0 (#:lit 1 ,s1)))
                      (term (RVal ,s0 (ProofRep ,s1 User (Prop p)) (#:lit 1 ,s1)))))])
    (define erased (erase-core term+))
    (check-true (or (and (redex-match? G2 c erased) #t)
                    (and (redex-match? G2 v erased) #t))
                (format "~a -> ~a" term+ erased))))

(test-case "erase-core は投影として正しい値を返す"
  (check-equal? (erase-core core+) core))

(test-case "erase-surface は投影として正しい値を返す"
  (check-equal? (erase-surface surface+) surface)
  (check-true (redex-match? UCore e (erase-surface surface+))))

;; 法則 2: 冪等性。spanless な入力では恒等写像である。
(test-case "erase は冪等であり spanless な入力で恒等である"
  (check-equal? (erase-core (erase-core core+)) (erase-core core+))
  (check-equal? (erase-core core) core)
  (check-equal? (erase-surface (erase-surface surface+)) (erase-surface surface+))
  (check-equal? (erase-surface surface) surface))

;; 法則 3: span 違いの一致。
(test-case "span だけが違う 2 項は同じ erase 結果を持つ"
  (define core-other
    (term (Let ,s2 ((#:bind x ,s2) (#:ty Int ,s2))
               (#:lit 1 ,s2)
               (Apply ,s2 (Lam ,s2 User lam-id ((#:bind y ,s2)) (#:var y ,s2))
                      (#:var x ,s2)))))
  (check-equal? (erase-core core+) (erase-core core-other)))

;; 法則 4: span 残留なし。
(test-case "erase の出力に span 機構の head が残らない"
  (define heads '(#:span #:bind #:lbl #:ty #:ef #:var #:lit))
  (define (contains-head? t)
    (cond [(pair? t) (or (and (memq (car t) heads) #t)
                         (ormap contains-head? t))]
          [else #f]))
  (check-false (contains-head? (erase-core core+)))
  (check-false (contains-head? (erase-surface surface+))))

;; 閉世界。7 つの head だけを知り、それ以外の keyword head は誤りとする。
(test-case "span は列の要素として落ち 6 つの包みは開かれる"
  (check-equal? (erase-core (term (Suspend ,s0 (#:lit 1 ,s1)))) (term (Suspend 1)))
  (check-equal? (erase-core (term (#:var x ,s1))) (term x))
  (check-equal? (erase-core (term (#:lit 1 ,s1))) 1)
  (check-equal? (erase-core (term (#:bind x ,s1))) (term x))
  (check-equal? (erase-core (term (#:lbl a ,s1))) (term a))
  (check-equal? (erase-core (term (#:ty (Option Int) ,s1))) (term (Option Int)))
  (check-equal? (erase-core (term (#:ef ((eff (Return b Int))) ,s1)))
                (term ((eff (Return b Int))))))

(test-case "span が項の位置に現れたら誤りである"
  (check-exn exn:fail? (lambda () (erase-core s0)))
  (check-exn exn:fail? (lambda () (erase-surface s0))))

(test-case "知らない keyword head は黙って通さない"
  (check-exn exn:fail?
             (lambda () (erase-core (term (#:unknown (#:lit 1 ,s1) ,s1)))))
  (check-exn exn:fail?
             (lambda () (erase-core (term (Suspend ,s0 (#:unknown 1 ,s1))))))
  (check-exn exn:fail?
             (lambda () (erase-surface (term (#:unknown 1 ,s1))))))

(test-case "形の崩れた包みは黙って通さない"
  (check-exn exn:fail? (lambda () (erase-core (term (#:bind x)))))
  (check-exn exn:fail? (lambda () (erase-core (term (#:ty Int)))))
  (check-exn exn:fail? (lambda () (erase-core (term (#:var x ,s1 ,s1)))))
  (check-exn exn:fail? (lambda () (erase-core (term (#:span main.tz 0))))))

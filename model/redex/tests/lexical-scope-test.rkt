#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../annotate.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../typing.rkt"
         "../ucore.rkt")

(define s '(#:span src 0 1))

(define (elaborated expression)
  (match (elab expression)
    [(list core type row callables)
     (check-equal? (core-type-of/diagnostic (erase-core core) '() callables)
                   (list type row))
     (list (erase-core core) type row)]
    [other (fail-check (format "elaboration success を期待したが ~s" other))]))

(define (count-form tree wanted)
  (+ (if (and (pair? tree) (eq? (car tree) wanted)) 1 0)
     (if (pair? tree)
         (apply + (map (λ (part) (count-form part wanted)) tree))
         0)))

(test-case "LexicalScope は UCore から UCore+ へ注釈され往復する"
  (define raw '(LexicalScope 1))
  (check-true (redex-match? UCore e raw))
  (define annotated (annotate-surface raw))
  (check-true (redex-match? UCore+ e annotated))
  (check-match annotated `(LexicalScope (#:span ,_ ,_ ,_) (#:lit 1 (#:span ,_ ,_ ,_))))
  (check-equal? (erase-surface annotated) raw))

(test-case "LexicalScope の synth は Scope を出し型と row を保つ"
  (define plain (elaborated '(Apply (Fn () Int (Partial) 1))))
  (define scoped
    (elaborated '(LexicalScope (Apply (Fn () Int (Partial) 1)))))
  (check-equal? (second scoped) (second plain))
  (check-equal? (third scoped) (third plain))
  (check-equal? (second scoped) 'Int)
  (check-equal? (third scoped) '(Partial))
  (check-match (first scoped) `(Scope () (Apply . ,_))))

(test-case "LexicalScope の check も Scope を出し型と row を保つ"
  (define plain
    (elaborated '(Apply (Fn () Int (Partial) 1))))
  (define scoped
    (elaborated '(Apply (Fn () Int (Partial) (LexicalScope 1)))))
  (check-equal? (second scoped) (second plain))
  (check-equal? (third scoped) (third plain))
  (check-equal? (second scoped) 'Int)
  (check-equal? (third scoped) '(Partial))
  (check-equal? (count-form (first scoped) 'Scope)
                (add1 (count-form (first plain) 'Scope))))

(test-case "LexicalScope は内側の Let を Scope 内へ置く"
  (define core
    (first (elaborated '(LexicalScope (Let (x const) 1 x)))))
  (check-true
   (match core
     [`(Scope () (Let . ,_)) #t]
     [_ #f])))

(test-case "validate-loop-shape! は実際の for の LexicalScope を透過する"
  ;; lower-for-loop の cons 枝と同じ順序: BlockBody を持つ %stmt Let の後に再帰する。
  (define loop
    '(Fn ((xs (List Int))) Unit ()
       (Loop %for-loop ((%for-rest (List Int))) Unit #:infer
         (Eliminate %for-rest
           ((nil () -> unit)
            (cons (x tail) ->
              (Let (%stmt const Unit)
                   (BlockBody (LexicalScope unit))
                   (Apply %for-loop tail)))))
         (xs))))
  (void (elaborated loop)))

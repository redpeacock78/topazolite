#lang racket/base

(require racket/match
         rackunit
         redex/reduction-semantics
         "../elaborate.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../typing.rkt")

(define empty '())

(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) 40)
    [`(cfg ,result () () ()) result]
    [other (fail-check (format "unexpected run-g2 result: ~s" other))]))

(define (check-surface-application source expected-type expected-value)
  (match (elab source)
    [(list core type row callables)
     (check-equal? type expected-type)
     (check-equal? row empty)
     (check-equal? (term (verify-initial-origins ,R0 ,core)) 'ok)
     (check-equal? (core-type-of core empty callables)
                   (list expected-type empty))
     (define result (run-g2-core core))
     (check-equal? result expected-value)
     (check-equal? (term (verify-origins ,R0 ,result)) 'ok)]
    [other (fail-check (format "elaboration failed: ~s" other))]))

(test-case "TRT-002: impl Apply elaborates, types, reduces, and verifies"
  (check-surface-application
   '(Apply impl-printable-int
      (Rec ((print imm (Fn ((x Int)) String () "ok")))))
   '(Proof (Implements Int Printable))
   '(ProofRep (Reserved o-impl-printable-int)
              (Implements Int Printable))))

(test-case "TRT-002: derive Apply follows the same integrated path"
  (check-surface-application
   '(Apply derive-sizable-int
      (Rec ((size imm (Fn ((x Int)) Int () 1)))))
   '(Proof (Implements Int Sizable))
   '(ProofRep (Reserved o-derive-sizable-int)
              (Implements Int Sizable))))

(test-case "trait intersection Apply returns an explicit composite proof"
  (check-surface-application
   '(Apply intersect-printable-sizable Printable-trait Sizable-trait)
   '(Proof (RequiresBoth Printable Sizable))
   '(ProofRep (Reserved o-intersect-print-size)
              (RequiresBoth Printable Sizable))))

(test-case "trait intersection is implicitly dischargeable"
  ;; 設計 §5.3: intersect 行は Γ-pc⁰ へ RequiresBoth 候補を供給する。
  ;; G2e ではここが check-false であった。反転がそのまま証拠である。
  ;; 要件 ID は search-compose-test.rkt 側に置く。
  (check-true
   (obligations-dischargeable?
    '((RequiresBoth Printable Sizable))
    Γ-pc0))
  ;; 左右を入れ替えても同じ候補で解ける。正準鍵が symbol 順に並べるためである。
  (check-true
   (obligations-dischargeable?
    '((RequiresBoth Sizable Printable))
    Γ-pc0))
  ;; 正典表に無い組は依然として解けない。
  (check-false
   (obligations-dischargeable?
    '((RequiresBoth Sizable PrintableTaggable))
    Γ-pc0)))

(define (check-apply-obligation proposition expected branch)
  (reset-search-log!)
  (define callables
    `((proof-call (NFn () Int () (,proposition)))))
  (check-equal?
   (core-type-of '(Apply (Lam User proof-call () 1))
                 empty
                 callables)
   expected)
  (check-true (hash-ref (search-log-snapshot) branch #f)))

(test-case "TRT-003: Apply distinguishes resolved, absent, and ambiguous goals"
  (check-apply-obligation '(Implements Int Printable)
                          '(Int ())
                          'finite-resolved-accept)
  (check-apply-obligation '(Implements Bool Printable)
                          'ill-typed
                          'finite-absent-reject)
  (check-apply-obligation '(Implements String Printable)
                          'ill-typed
                          'finite-ambiguous-reject))
